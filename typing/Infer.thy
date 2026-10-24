theory Infer
  imports Typing
begin

section \<open>The inference algorithm\<close>

text \<open>Algorithm W over the surface \<^cite>\<open>\<open>Sect. 4\<close> in milner1997\<close>, with rows as in
  \<^cite>\<open>\<open>Sect. 3.3\<close> in leijen2017\<close>, in the substitution-application style:
  every function returns the substitution it found,
  already applied to what it returns, and the caller applies it to what it
  holds. One counter supplies type variables, row variables and stamps.
  Implicit module arguments are inserted as placeholders and resolved
  after the enclosing top-level binding is inferred \<^cite>\<open>\<open>Sect. 5.1\<close> in white2014\<close>,
  from the types unification assigned to the parameter's abstract types; the
  pending resolutions travel with the inference and their variables are never
  generalised \<^cite>\<open>\<open>Sect. 4.1\<close> in white2014\<close>.\<close>

subsection \<open>Pending implicit resolutions\<close>

text \<open>A pending request records the placeholder's name, the binder's
  abstract types with the unification variables standing for them, the
  elaborated parameter signature, the candidates in scope at the request
  and, once resolved, the instance chosen. The scope is the request's,
  not the binding's, so an implicit parameter of an enclosing binder is a
  candidate \<^cite>\<open>\<open>Sect. 2.2.2\<close> in white2014\<close>. A request that mentions a binder's
  abstract types is resolved when the binder closes; the rest wait for the
  enclosing binding.\<close>

type_synonym pend =
  \<open>(name \<times> tvar list \<times> (tvar \<times> kty) list \<times> tenv \<times> (name \<times> tenv) list \<times> name option) list\<close>

definition sub_pend :: \<open>ksub \<Rightarrow> pend \<Rightarrow> pend\<close> where
  \<open>sub_pend s = map (\<lambda>(x, K, \<phi>, E, cs, r). (x, K, map (apsnd (sapp s)) \<phi>, E, cs, r))\<close>

definition ftv_pend :: \<open>pend \<Rightarrow> tvar set\<close> where
  \<open>ftv_pend pd = (\<Union>(x, K, \<phi>, E, cs, r) \<in> set pd. \<Union>(k, t) \<in> set \<phi>. ftv t)\<close>

definition frv_pend :: \<open>pend \<Rightarrow> rvar set\<close> where
  \<open>frv_pend pd = (\<Union>(x, K, \<phi>, E, cs, r) \<in> set pd. \<Union>(k, t) \<in> set \<phi>. frv t)\<close>

text \<open>The abstract types the open requests mention.\<close>

definition ktv_pend :: \<open>pend \<Rightarrow> tvar set\<close> where
  \<open>ktv_pend pd = (\<Union>(x, K, \<phi>, E, cs, r) \<in> set pd. if r = None then (\<Union>(k, t) \<in> set \<phi>. ktv t) else {})\<close>

text \<open>At a binder's exit, the open requests mentioning its abstract types
  are resolved from their own scope.\<close>

fun resolve_inner :: \<open>tvar list \<Rightarrow> pend \<Rightarrow> pend option\<close> where
  \<open>resolve_inner K [] = Some []\<close>
| \<open>resolve_inner K ((x, K', \<phi>, E, cs, r) # pd) =
     resolve_inner K pd \<bind> (\<lambda>pd'.
       (if r = None \<and> set K \<inter> (\<Union>(k, t) \<in> set \<phi>. ktv t) \<noteq> {}
        then imp_res cs K' E \<phi> \<bind> (\<lambda>P. Some ((x, K', \<phi>, E, cs, Some P) # pd'))
        else Some ((x, K', \<phi>, E, cs, r) # pd')))\<close>

lemmas resolve_inner_induct = resolve_inner.induct[named_cases resolve_inner]

text \<open>Placeholder names are reserved: a prefix no identifier lexes to,
  followed by the counter as one code point.\<close>

definition imp_name :: \<open>nat \<Rightarrow> name\<close> where
  \<open>imp_name k = str ''%imp.'' @ [k]\<close>

definition reserved :: \<open>name \<Rightarrow> bool\<close> where
  \<open>reserved x \<longleftrightarrow> take 5 x = str ''%imp.''\<close>

text \<open>Generalisation that keeps the variables of pending resolutions
  monomorphic, and generalises only the variables the binding itself
  minted, from the counter \<open>n\<close> it started at: an older variable free in
  the result but not in the context is dead \<^cite>\<open>\<open>Sect. 4.8\<close> in milner1997\<close>.\<close>

definition gen_p :: \<open>tenv \<Rightarrow> krow \<Rightarrow> pend \<Rightarrow> nat \<Rightarrow> kty \<Rightarrow> tvar set \<times> rvar set\<close> where
  \<open>gen_p B A pd n \<tau> =
     (ftv \<tau> - ftv_env B - ftv_pend pd - set [0 ..< n],
      frv \<tau> - frv_env B - frv_row A - frv_pend pd - set [0 ..< n])\<close>

text \<open>Replacing placeholder module arguments by the resolved instance
  paths.\<close>

fun subst_imp :: \<open>(name \<times> name) list \<Rightarrow> expr \<Rightarrow> expr\<close>
and subst_imp_atom :: \<open>(name \<times> name) list \<Rightarrow> matom \<Rightarrow> matom\<close>
and subst_imp_cls :: \<open>(name \<times> name) list \<Rightarrow> hclause \<Rightarrow> hclause\<close>
where
  \<open>subst_imp tab (ESpine as) = ESpine (map (subst_imp_atom tab) as)\<close>
| \<open>subst_imp tab (EOp as opr e) = EOp (map (subst_imp_atom tab) as) opr (subst_imp tab e)\<close>
| \<open>subst_imp tab (EAnn e ty) = EAnn (subst_imp tab e) ty\<close>
| \<open>subst_imp tab (EFn ps b) = EFn ps (subst_imp tab b)\<close>
| \<open>subst_imp tab (EFnMod b e) = EFnMod b (subst_imp tab e)\<close>
| \<open>subst_imp tab (ELet p e b) = ELet p (subst_imp tab e) (subst_imp tab b)\<close>
| \<open>subst_imp tab (ESeq e\<^sub>1 e\<^sub>2) = ESeq (subst_imp tab e\<^sub>1) (subst_imp tab e\<^sub>2)\<close>
| \<open>subst_imp tab (EIf c t e) =
     EIf (subst_imp tab c) (subst_imp tab t) (map_option (subst_imp tab) e)\<close>
| \<open>subst_imp tab (EMatch e arms) =
     EMatch (subst_imp tab e) (map (\<lambda>(p, b). (p, subst_imp tab b)) arms)\<close>
| \<open>subst_imp tab (EHandle e cls) = EHandle (subst_imp tab e) (map (subst_imp_cls tab) cls)\<close>
| \<open>subst_imp tab (EHandler cls) = EHandler (map (subst_imp_cls tab) cls)\<close>
| \<open>subst_imp tab (EMask l e) = EMask l (subst_imp tab e)\<close>
| \<open>subst_imp tab (EHandlerN cls) = EHandlerN (map (subst_imp_cls tab) cls)\<close>
| \<open>subst_imp tab (EWith x h e) = EWith x (subst_imp tab h) (subst_imp tab e)\<close>
| \<open>subst_imp tab (ELetFun f mbs cls b) =
     ELetFun f mbs (map (\<lambda>(ps, e). (ps, subst_imp tab e)) cls) (subst_imp tab b)\<close>
| \<open>subst_imp tab (EGuards alts) =
     EGuards (map (\<lambda>(gs, e). (map (subst_imp tab) gs, subst_imp tab e)) alts)\<close>
| \<open>subst_imp tab EErr = EErr\<close>
| \<open>subst_imp_atom tab (AParen es) = AParen (map (subst_imp tab) es)\<close>
| \<open>subst_imp_atom tab (AList es) = AList (map (subst_imp tab) es)\<close>
| \<open>subst_imp_atom tab (ARec fs) = ARec (map (\<lambda>(x, e). (x, subst_imp tab e)) fs)\<close>
| \<open>subst_imp_atom tab (ADot a x) = ADot (subst_imp_atom tab a) x\<close>
| \<open>subst_imp_atom tab (AMod p sg) =
     (case path_nms p of
        [x] \<Rightarrow> (case map_of tab x of Some P \<Rightarrow> AMod (MkPath [mk_nm P]) sg | None \<Rightarrow> AMod p sg)
      | _ \<Rightarrow> AMod p sg)\<close>
| \<open>subst_imp_atom tab a = a\<close>
| \<open>subst_imp_cls tab (HOp opn ps k b) = HOp opn ps k (subst_imp tab b)\<close>
| \<open>subst_imp_cls tab (HRet p b) = HRet p (subst_imp tab b)\<close>
| \<open>subst_imp_cls tab c = c\<close>

subsection \<open>Patterns\<close>

text \<open>\<open>infer_pat uf B p n\<close>: the pattern's type, its binders with their
  types, and the substitution constructor arguments forced. An operator pattern is
  inferred as its resolution, which holds no chain, so the algorithm recurses on
  the number of chains in a pattern first (\<^text>\<open>patops\<close>) and its size second.\<close>

fun patops :: \<open>mpat \<Rightarrow> nat\<close> and patops_atom :: \<open>mpatom \<Rightarrow> nat\<close>
and patops_atoms :: \<open>mpatom list \<Rightarrow> nat\<close> and patops_pats :: \<open>mpat list \<Rightarrow> nat\<close>
and patops_fields :: \<open>(nm \<times> mpat) list \<Rightarrow> nat\<close> where
  \<open>patops (PatApp as) = patops_atoms as\<close>
| \<open>patops (PatOp as _ p) = Suc (patops_atoms as + patops p)\<close>
| \<open>patops (PatAs p _) = patops p\<close>
| \<open>patops (PatAnn p _) = patops p\<close>
| \<open>patops_atom (PParen ps) = patops_pats ps\<close>
| \<open>patops_atom (PList ps) = patops_pats ps\<close>
| \<open>patops_atom (PRec fs _) = patops_fields fs\<close>
| \<open>patops_atom _ = 0\<close>
| \<open>patops_atoms [] = 0\<close>
| \<open>patops_atoms (a # as) = patops_atom a + patops_atoms as\<close>
| \<open>patops_pats [] = 0\<close>
| \<open>patops_pats (p # ps) = patops p + patops_pats ps\<close>
| \<open>patops_fields [] = 0\<close>
| \<open>patops_fields ((_, p) # fs) = patops p + patops_fields fs\<close>

lemma patops_pats_0: \<open>patops_pats ps = 0 \<longleftrightarrow> (\<forall>p \<in> set ps. patops p = 0)\<close>
  by (induction ps) auto

lemma tree_pat_patops: \<open>tree_pat ps t = Some q \<Longrightarrow> patops_pats ps = 0 \<Longrightarrow> patops q = 0\<close>
  by (induction ps t arbitrary: q rule: tree_pat.induct)
     (auto simp: bind_eq_Some_conv patops_pats_0 split: if_split_asm)

lemma pat_resolve_patops:
  \<open>pat_resolve B p = Some q \<Longrightarrow> patops q = 0\<close>
  \<open>patom_resolve B a = Some b \<Longrightarrow> patops_atom b = 0\<close>
  \<open>chain_resolve B p = Some (qs, oprs) \<Longrightarrow> patops_pats qs = 0\<close>
  \<open>pats_resolve B ps = Some qs \<Longrightarrow> patops_pats qs = 0\<close>
  \<open>patoms_resolve B as = Some bs \<Longrightarrow> patops_atoms bs = 0\<close>
  \<open>fields_resolve B fs = Some gs \<Longrightarrow> patops_fields gs = 0\<close>
  by (induction B p and B a and B p and B ps and B as and B fs
      arbitrary: q and b and qs oprs and qs and bs and gs rule: pat_resolve_induct)
     (auto simp: bind_eq_Some_conv tree_pat_patops)

function (sequential) infer_pat ::
  \<open>nat \<Rightarrow> tenv \<Rightarrow> mpat \<Rightarrow> nat \<Rightarrow> (ksub \<times> kty \<times> (name \<times> kty) list \<times> nat) option\<close>
and infer_patom ::
  \<open>nat \<Rightarrow> tenv \<Rightarrow> mpatom \<Rightarrow> nat \<Rightarrow> (ksub \<times> kty \<times> (name \<times> kty) list \<times> nat) option\<close>
and infer_patoms ::
  \<open>nat \<Rightarrow> tenv \<Rightarrow> mpatom list \<Rightarrow> nat \<Rightarrow> (ksub \<times> kty list \<times> (name \<times> kty) list \<times> nat) option\<close>
and infer_pats ::
  \<open>nat \<Rightarrow> tenv \<Rightarrow> mpat list \<Rightarrow> nat \<Rightarrow> (ksub \<times> kty list \<times> (name \<times> kty) list \<times> nat) option\<close>
where
  \<open>infer_pat uf B (PatApp [a]) n = infer_patom uf B a n\<close>
| \<open>infer_pat uf B (PatApp (PQid p # as)) n =
     (case tlookup B (path_nms p) of
        Some (TEcon \<sigma> m) \<Rightarrow>
          (if m = length as \<and> as \<noteq> []
           then (case inst_scheme n \<sigma> of (\<tau>\<^sub>c, n\<^sub>1) \<Rightarrow>
                  (case con_ty m \<tau>\<^sub>c of
                     Some (\<tau>s, \<tau>) \<Rightarrow>
                       infer_patoms uf B as n\<^sub>1 \<bind> (\<lambda>(sp, \<tau>s', \<Gamma>, n\<^sub>2).
                         unis uf (zip \<tau>s' (map (sapp sp) \<tau>s)) n\<^sub>2 \<bind> (\<lambda>(s\<^sub>1, n\<^sub>3).
                           Some (s\<^sub>1 \<odot> sp, sapp s\<^sub>1 (sapp sp \<tau>), map (apsnd (sapp s\<^sub>1)) \<Gamma>, n\<^sub>3)))
                   | None \<Rightarrow> None))
           else None)
      | _ \<Rightarrow> None)\<close>
| \<open>infer_pat uf B (PatApp _) n = None\<close>
| \<open>infer_pat uf B (PatAs p x) n =
     (if nm_ok (n_txt x)
      then infer_pat uf B p n \<bind> (\<lambda>(s, \<tau>, \<Gamma>, n'). Some (s, \<tau>, (n_txt x, \<tau>) # \<Gamma>, n'))
      else None)\<close>
| \<open>infer_pat uf B (PatOp as opr p) n =
     (case pat_resolve B (PatOp as opr p) of Some q \<Rightarrow> infer_pat uf B q n | None \<Rightarrow> None)\<close>
| \<open>infer_pat uf B (PatAnn p ty) n =
     infer_pat uf B p n \<bind> (\<lambda>(s, \<tau>, \<Gamma>, n\<^sub>1).
       ty_stat (sappe s B) True ([], []) n\<^sub>1 ty \<bind> (\<lambda>(\<tau>\<^sub>a, _, n\<^sub>2).
         uni uf \<tau> \<tau>\<^sub>a n\<^sub>2 \<bind> (\<lambda>(s\<^sub>2, n\<^sub>3).
           Some (s\<^sub>2 \<odot> s, sapp s\<^sub>2 \<tau>, map (apsnd (sapp s\<^sub>2)) \<Gamma>, n\<^sub>3))))\<close>
| \<open>infer_patom uf B (PWild _) n = Some (sid, TV n, [], Suc n)\<close>
| \<open>infer_patom uf B (PQid (MkPath [x])) n =
     (case tlookup B [n_txt x] of
        Some (TEcon \<sigma> m) \<Rightarrow>
          (if m = 0 then (case inst_scheme n \<sigma> of (\<tau>, n\<^sub>1) \<Rightarrow> Some (sid, \<tau>, [], n\<^sub>1)) else None)
      | _ \<Rightarrow> (if nm_ok (n_txt x) then Some (sid, TV n, [(n_txt x, TV n)], Suc n) else None))\<close>
| \<open>infer_patom uf B (PQid p) n =
     (case tlookup B (path_nms p) of
        Some (TEcon \<sigma> 0) \<Rightarrow> (case inst_scheme n \<sigma> of (\<tau>, n\<^sub>1) \<Rightarrow> Some (sid, \<tau>, [], n\<^sub>1))
      | _ \<Rightarrow> None)\<close>
| \<open>infer_patom uf B (PNum l v None) n = Some (sid, TC int_ty [], [], n)\<close>
| \<open>infer_patom uf B (PNum l v (Some k)) n =
     (if sfx_ok k v then Some (sid, TC (sfx_ty k) [], [], n) else None)\<close>
| \<open>infer_patom uf B (PStr l cs) n = Some (sid, TC string_ty [], [], n)\<close>
| \<open>infer_patom uf B (PChar l c) n = Some (sid, TC char_ty [], [], n)\<close>
| \<open>infer_patom uf B (PParen [p]) n = infer_pat uf B p n\<close>
| \<open>infer_patom uf B (PParen ps) n =
     infer_pats uf B ps n \<bind> (\<lambda>(s, \<tau>s, \<Gamma>, n'). Some (s, tuple \<tau>s, \<Gamma>, n'))\<close>
| \<open>infer_patom uf B (PList ps) n =
     infer_pats uf B ps n \<bind> (\<lambda>(s, \<tau>s, \<Gamma>, n\<^sub>1).
       unis uf (map (\<lambda>\<tau>. (\<tau>, TV n\<^sub>1)) \<tau>s) (Suc n\<^sub>1) \<bind> (\<lambda>(s\<^sub>2, n\<^sub>2).
         Some (s\<^sub>2 \<odot> s, TC list_ty [sapp s\<^sub>2 (TV n\<^sub>1)], map (apsnd (sapp s\<^sub>2)) \<Gamma>, n\<^sub>2)))\<close>
| \<open>infer_patom uf B (PRec _ _) n = None\<close>
| \<open>infer_patoms uf B [] n = Some (sid, [], [], n)\<close>
| \<open>infer_patoms uf B (a # as) n =
     infer_patom uf B a n \<bind> (\<lambda>(s\<^sub>1, \<tau>, \<Gamma>\<^sub>1, n\<^sub>1).
       infer_patoms uf (sappe s\<^sub>1 B) as n\<^sub>1 \<bind> (\<lambda>(s\<^sub>2, \<tau>s, \<Gamma>\<^sub>2, n\<^sub>2).
         Some (s\<^sub>2 \<odot> s\<^sub>1, sapp s\<^sub>2 \<tau> # \<tau>s, map (apsnd (sapp s\<^sub>2)) \<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2, n\<^sub>2)))\<close>
| \<open>infer_pats uf B [] n = Some (sid, [], [], n)\<close>
| \<open>infer_pats uf B (p # ps) n =
     infer_pat uf B p n \<bind> (\<lambda>(s\<^sub>1, \<tau>, \<Gamma>\<^sub>1, n\<^sub>1).
       infer_pats uf (sappe s\<^sub>1 B) ps n\<^sub>1 \<bind> (\<lambda>(s\<^sub>2, \<tau>s, \<Gamma>\<^sub>2, n\<^sub>2).
         Some (s\<^sub>2 \<odot> s\<^sub>1, sapp s\<^sub>2 \<tau> # \<tau>s, map (apsnd (sapp s\<^sub>2)) \<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2, n\<^sub>2)))\<close>

  by pat_completeness auto

termination
  by (relation \<open>measures [\<lambda>x. case x of
        Inl (Inl (uf, B, p, n)) \<Rightarrow> patops p
      | Inl (Inr (uf, B, a, n)) \<Rightarrow> patops_atom a
      | Inr (Inl (uf, B, as, n)) \<Rightarrow> patops_atoms as
      | Inr (Inr (uf, B, ps, n)) \<Rightarrow> patops_pats ps,
      \<lambda>x. case x of
        Inl (Inl (uf, B, p, n)) \<Rightarrow> size p
      | Inl (Inr (uf, B, a, n)) \<Rightarrow> size a
      | Inr (Inl (uf, B, as, n)) \<Rightarrow> size_list size as
      | Inr (Inr (uf, B, ps, n)) \<Rightarrow> size_list size ps]\<close>)
     (auto simp: pat_resolve_patops simp del: pat_resolve.simps)

lemmas infer_pat_induct =
  infer_pat_infer_patom_infer_patoms_infer_pats.induct[named_cases infer_pat]

subsection \<open>Operator trees\<close>

text \<open>An operator tree against the types of its leaves (rules \<open>T_leaf\<close>, \<open>T_var\<close>,
  \<open>T_con\<close>).\<close>

fun infer_tree :: \<open>nat \<Rightarrow> tenv \<Rightarrow> krow \<Rightarrow> kty list \<Rightarrow> optree \<Rightarrow> nat \<Rightarrow> (ksub \<times> kty \<times> nat) option\<close> where
  \<open>infer_tree uf B A \<tau>s (Leaf i) n = (if i < length \<tau>s then Some (sid, \<tau>s ! i, n) else None)\<close>
| \<open>infer_tree uf B A \<tau>s (Node (OVar v) l r) n =
     infer_tree uf B A \<tau>s l n \<bind> (\<lambda>(s\<^sub>1, \<tau>\<^sub>l, n\<^sub>1).
       infer_tree uf (sappe s\<^sub>1 B) (sappr s\<^sub>1 A) (map (sapp s\<^sub>1) \<tau>s) r n\<^sub>1 \<bind> (\<lambda>(s\<^sub>2, \<tau>\<^sub>r, n\<^sub>2).
         (case tlookup (sappe (s\<^sub>2 \<odot> s\<^sub>1) B) [v] of
            Some (TEval \<sigma>) \<Rightarrow>
              (case inst_scheme n\<^sub>2 \<sigma> of (\<tau>\<^sub>f, n\<^sub>3) \<Rightarrow>
                 uni uf \<tau>\<^sub>f
                   (TFn (tuple [sapp s\<^sub>2 \<tau>\<^sub>l, \<tau>\<^sub>r]) (sappr (s\<^sub>2 \<odot> s\<^sub>1) A) (TV n\<^sub>3))
                   (Suc n\<^sub>3) \<bind>
                   (\<lambda>(s\<^sub>3, n\<^sub>4). Some (s\<^sub>3 \<odot> s\<^sub>2 \<odot> s\<^sub>1, sapp s\<^sub>3 (TV n\<^sub>3), n\<^sub>4)))
          | _ \<Rightarrow> None)))\<close>
| \<open>infer_tree uf B A \<tau>s (Node (OCon c) l r) n =
     infer_tree uf B A \<tau>s l n \<bind> (\<lambda>(s\<^sub>1, \<tau>\<^sub>l, n\<^sub>1).
       infer_tree uf (sappe s\<^sub>1 B) (sappr s\<^sub>1 A) (map (sapp s\<^sub>1) \<tau>s) r n\<^sub>1 \<bind> (\<lambda>(s\<^sub>2, \<tau>\<^sub>r, n\<^sub>2).
         (case tlookup (sappe (s\<^sub>2 \<odot> s\<^sub>1) B) [c] of
            Some (TEcon \<sigma> m) \<Rightarrow>
              (if m = 2 then
               (case inst_scheme n\<^sub>2 \<sigma> of (\<tau>\<^sub>c, n\<^sub>3) \<Rightarrow>
                 uni uf \<tau>\<^sub>c
                     (TFn (sapp s\<^sub>2 \<tau>\<^sub>l) (RV n\<^sub>3) (TFn \<tau>\<^sub>r (RV (Suc n\<^sub>3)) (TV (Suc (Suc n\<^sub>3)))))
                     (Suc (Suc (Suc n\<^sub>3))) \<bind>
                   (\<lambda>(s\<^sub>3, n\<^sub>4). Some (s\<^sub>3 \<odot> s\<^sub>2 \<odot> s\<^sub>1, sapp s\<^sub>3 (TV (Suc (Suc n\<^sub>3))), n\<^sub>4)))
               else None)
          | _ \<Rightarrow> None)))\<close>

lemmas infer_tree_induct = infer_tree.induct[named_cases infer_tree]

subsection \<open>Expressions\<close>

text \<open>\<open>infer uf B A pd e n\<close>: under unification fuel \<open>uf\<close>, basis \<open>B\<close>,
  ambient row \<open>A\<close> and pending resolutions \<open>pd\<close>, infer
  \<open>e\<close> from counter \<open>n\<close>; returns the substitution, the elaborated term, the
  type, the pending resolutions and the counter, all under the
  substitution. Rows are kept canonical at the points labels are
  inserted.\<close>

text \<open>An operation on a name, \<open>x.op\<close>: the name's type is unified with a
  handler-name type of the operation's effect at fresh arguments, and the
  operation's scheme is instantiated with them (rule \<open>H_opn\<close>).\<close>

definition infer_opn ::
  \<open>nat \<Rightarrow> tenv \<Rightarrow> pend \<Rightarrow> mpath \<Rightarrow> nat \<Rightarrow> (ksub \<times> matom \<times> kty \<times> pend \<times> nat) option\<close>
where
  \<open>infer_opn uf B pd p n =
     (case path_nms p of
        [x, op] \<Rightarrow>
          (case (tlookup B [x], tlookup B [op]) of
             (Some (TEval \<sigma>), Some (TEop lop ps \<tau>\<^sub>1 \<tau>\<^sub>2)) \<Rightarrow>
               (case eff_of_op B lop of
                  Some (l, ls, ar) \<Rightarrow>
                    (case inst_scheme n \<sigma> of (\<tau>\<^sub>x, n\<^sub>1) \<Rightarrow>
                      (let args = map TV [n\<^sub>1 ..< n\<^sub>1 + length ps]; n\<^sub>2 = n\<^sub>1 + length ps
                       in uni uf \<tau>\<^sub>x (TEv (eff_ty l args) (TV n\<^sub>2) (tuple args)) (Suc n\<^sub>2)
                            \<bind> (\<lambda>(s, n\<^sub>3).
                            Some (s, APath p,
                                  TFn (sapp s (op_inst ps args \<tau>\<^sub>1))
                                      (canon_row (RCons (nlbl lop) (RV n\<^sub>3)))
                                      (sapp s (op_inst ps args \<tau>\<^sub>2)),
                                  sub_pend s pd, Suc n\<^sub>3))))
                | None \<Rightarrow> None)
           | _ \<Rightarrow> None)
      | _ \<Rightarrow> None)\<close>

text \<open>Applying a function to one more argument (rule \<open>G_app\<close>, and the
  installation of a named handler, rule \<open>W_with\<close>): when both the parameter and
  the argument are actions, the parameter's scope binder, when disjoint from the
  basis's abstract types, is renamed to the argument's before unification.\<close>

definition app_arg :: \<open>nat \<Rightarrow> tenv \<Rightarrow> krow \<Rightarrow> pend \<Rightarrow> kty \<Rightarrow> kty \<Rightarrow> nat
                       \<Rightarrow> (ksub \<times> kty \<times> pend \<times> nat) option\<close> where
  \<open>app_arg uf B A pd \<tau>\<^sub>h \<tau>\<^sub>a n =
     (let \<tau>\<^sub>h' = (case (\<tau>\<^sub>h, \<tau>\<^sub>a) of
                   (TFn (TAct lt K \<epsilon>\<^sub>0 \<tau>\<^sub>0) \<epsilon>\<^sub>l \<tau>\<^sub>2, TAct lt' K' \<epsilon>\<^sub>0' \<tau>\<^sub>0') \<Rightarrow>
                     (if length K = length K' \<and> set K \<inter> ktv_env B = {} \<and> set K \<inter> ktv \<tau>\<^sub>0 = {}
                      then TFn (TAct lt K' \<epsilon>\<^sub>0 (ksubst (tsl (zip K (map TK K'))) \<tau>\<^sub>0)) \<epsilon>\<^sub>l \<tau>\<^sub>2
                      else \<tau>\<^sub>h)
                 | _ \<Rightarrow> \<tau>\<^sub>h)
      in uni uf \<tau>\<^sub>h' (TFn \<tau>\<^sub>a A (TV n)) (Suc n) \<bind> (\<lambda>(s, n').
           Some (s, sapp s (TV n), sub_pend s pd, n')))\<close>

text \<open>The variables a pattern binds, as monomorphic entries under a substitution.\<close>

definition mono_env :: \<open>ksub \<Rightarrow> (name \<times> kty) list \<Rightarrow> tenv\<close> where
  \<open>mono_env s \<Gamma> = map (\<lambda>(x, \<tau>). (x, TEval (kmono (sapp s \<tau>)))) \<Gamma>\<close>

text \<open>The local function groups in a term, counted: the termination measure of the
  inference leads with it, since a group is inferred through its lowering, which is
  larger than its clauses.\<close>

fun nlf :: \<open>expr \<Rightarrow> nat\<close> and nlf_atom :: \<open>matom \<Rightarrow> nat\<close> and nlf_cl :: \<open>hclause \<Rightarrow> nat\<close> where
  \<open>nlf (ESpine as) = sum_list (map nlf_atom as)\<close>
| \<open>nlf (EOp as _ e) = sum_list (map nlf_atom as) + nlf e\<close>
| \<open>nlf (EAnn e _) = nlf e\<close>
| \<open>nlf (EFn _ e) = nlf e\<close>
| \<open>nlf (EFnMod _ e) = nlf e\<close>
| \<open>nlf (ELet _ e b) = nlf e + nlf b\<close>
| \<open>nlf (ELetFun _ _ cls b) = Suc (sum_list (map (\<lambda>(_, e). nlf e) cls) + nlf b)\<close>
| \<open>nlf (ESeq a b) = nlf a + nlf b\<close>
| \<open>nlf (EIf c t None) = nlf c + nlf t\<close>
| \<open>nlf (EIf c t (Some e)) = nlf c + nlf t + nlf e\<close>
| \<open>nlf (EMatch e arms) = nlf e + sum_list (map (\<lambda>(_, e). nlf e) arms)\<close>
| \<open>nlf (EGuards alts) = sum_list (map (\<lambda>(gs, e). sum_list (map nlf gs) + nlf e) alts)\<close>
| \<open>nlf (EHandle e cls) = nlf e + sum_list (map nlf_cl cls)\<close>
| \<open>nlf (EHandler cls) = sum_list (map nlf_cl cls)\<close>
| \<open>nlf (EHandlerN cls) = sum_list (map nlf_cl cls)\<close>
| \<open>nlf (EWith _ h e) = nlf h + nlf e\<close>
| \<open>nlf (EMask _ e) = nlf e\<close>
| \<open>nlf EErr = 0\<close>
| \<open>nlf_atom (AParen es) = sum_list (map nlf es)\<close>
| \<open>nlf_atom (AList es) = sum_list (map nlf es)\<close>
| \<open>nlf_atom (ARec fs) = sum_list (map (\<lambda>(_, e). nlf e) fs)\<close>
| \<open>nlf_atom (ADot a _) = nlf_atom a\<close>
| \<open>nlf_atom _ = 0\<close>
| \<open>nlf_cl (HOp _ _ _ e) = nlf e\<close>
| \<open>nlf_cl (HRet _ e) = nlf e\<close>
| \<open>nlf_cl (HFin e) = nlf e\<close>
| \<open>nlf_cl HErr = 0\<close>

lemma nlf_foldr_EFn: \<open>nlf (foldr (\<lambda>a. EFn (g a)) xs e) = nlf e\<close>
  by (induction xs) auto

lemma nlf_dfun_rhs [simp]:
  \<open>nlf (foldr EFnMod mbs (dfun_rhs cls)) = sum_list (map (\<lambda>(_, e). nlf e) cls)\<close>
proof -
  have arms: \<open>(\<lambda>(_, y). nlf y) \<circ> (\<lambda>(ps, y). (f ps, y)) = (\<lambda>(_, y). nlf y)\<close>
    for f :: \<open>mpat list \<Rightarrow> mpat\<close> by auto
  have \<open>nlf (dfun_rhs cls) = sum_list (map (\<lambda>(_, e). nlf e) cls)\<close>
    by (cases cls rule: dfun_rhs.cases)
       (simp_all add: nlf_foldr_EFn Let_def arms o_def[of nlf] case_prod_beta split: list.split)
  then show ?thesis by (induction mbs) auto
qed

text \<open>The alternatives of a guarded term.\<close>

fun guards_of :: \<open>expr \<Rightarrow> (expr list \<times> expr) list\<close> where
  \<open>guards_of (EGuards alts) = alts\<close>
| \<open>guards_of _ = []\<close>

function (sequential) infer :: \<open>nat \<Rightarrow> tenv \<Rightarrow> krow \<Rightarrow> pend \<Rightarrow> expr \<Rightarrow> nat
              \<Rightarrow> (ksub \<times> expr \<times> kty \<times> pend \<times> nat) option\<close>
and infer_head :: \<open>nat \<Rightarrow> tenv \<Rightarrow> krow \<Rightarrow> pend \<Rightarrow> matom \<Rightarrow> nat
              \<Rightarrow> (ksub \<times> matom \<times> kty \<times> pend \<times> nat) option\<close>
and infer_atom :: \<open>nat \<Rightarrow> tenv \<Rightarrow> krow \<Rightarrow> pend \<Rightarrow> matom \<Rightarrow> nat
              \<Rightarrow> (ksub \<times> matom \<times> kty \<times> pend \<times> nat) option\<close>
and infer_args :: \<open>nat \<Rightarrow> tenv \<Rightarrow> krow \<Rightarrow> pend \<Rightarrow> nat \<Rightarrow> kty \<Rightarrow> matom list \<Rightarrow> nat
              \<Rightarrow> (ksub \<times> matom list \<times> kty \<times> pend \<times> nat) option\<close>
and infer_exps :: \<open>nat \<Rightarrow> tenv \<Rightarrow> krow \<Rightarrow> pend \<Rightarrow> expr list \<Rightarrow> nat
              \<Rightarrow> (ksub \<times> expr list \<times> kty list \<times> pend \<times> nat) option\<close>
and infer_chain :: \<open>nat \<Rightarrow> tenv \<Rightarrow> krow \<Rightarrow> pend \<Rightarrow> expr \<Rightarrow> nat
              \<Rightarrow> (ksub \<times> expr \<times> nm list \<times> kty list \<times> pend \<times> nat) option\<close>
and infer_arms :: \<open>nat \<Rightarrow> tenv \<Rightarrow> krow \<Rightarrow> pend \<Rightarrow> kty \<Rightarrow> kty \<Rightarrow> (mpat \<times> expr) list \<Rightarrow> nat
              \<Rightarrow> (ksub \<times> (mpat \<times> expr) list \<times> pend \<times> nat) option\<close>
and infer_cls :: \<open>nat \<Rightarrow> tenv \<Rightarrow> krow \<Rightarrow> pend \<Rightarrow> bool \<Rightarrow> kty \<Rightarrow> kty \<Rightarrow> hclause list \<Rightarrow> nat
              \<Rightarrow> (ksub \<times> hclause list \<times> kty \<times> pend \<times> nat) option\<close>
where
  \<open>infer uf B A pd (ESpine []) n = None\<close>
| \<open>infer uf B A pd (ESpine (a # as)) n =
     infer_head uf B A pd a n \<bind> (\<lambda>(s\<^sub>1, a', \<tau>\<^sub>0, pd\<^sub>1, n\<^sub>1).
       infer_args uf (sappe s\<^sub>1 B) (sappr s\<^sub>1 A) pd\<^sub>1 uf \<tau>\<^sub>0 as n\<^sub>1 \<bind> (\<lambda>(s\<^sub>2, as', \<tau>, pd\<^sub>2, n\<^sub>2).
         Some (s\<^sub>2 \<odot> s\<^sub>1, ESpine (a' # as'), \<tau>, pd\<^sub>2, n\<^sub>2)))\<close>
| \<open>infer uf B A pd (EOp as opr e) n =
     infer_chain uf B A pd (EOp as opr e) n \<bind> (\<lambda>(s\<^sub>1, e', oprs, \<tau>s, pd\<^sub>1, n\<^sub>1).
       chain_tree B oprs \<bind> (\<lambda>tree.
         infer_tree uf (sappe s\<^sub>1 B) (sappr s\<^sub>1 A) \<tau>s tree n\<^sub>1 \<bind> (\<lambda>(s\<^sub>2, \<tau>, n\<^sub>2).
           Some (s\<^sub>2 \<odot> s\<^sub>1, e', \<tau>, sub_pend s\<^sub>2 pd\<^sub>1, n\<^sub>2))))\<close>
| \<open>infer uf B A pd (EAnn e ty) n =
     infer uf B A pd e n \<bind> (\<lambda>(s\<^sub>1, e', \<tau>, pd\<^sub>1, n\<^sub>1).
       ty_stat (sappe s\<^sub>1 B) True ([], []) n\<^sub>1 ty \<bind> (\<lambda>(\<tau>\<^sub>a, _, n\<^sub>2).
         uni uf \<tau> (ann_ty (sappe s\<^sub>1 B) \<tau> \<tau>\<^sub>a) n\<^sub>2 \<bind> (\<lambda>(s\<^sub>2, n\<^sub>3).
           Some (s\<^sub>2 \<odot> s\<^sub>1, EAnn e' ty, sapp s\<^sub>2 \<tau>, sub_pend s\<^sub>2 pd\<^sub>1, n\<^sub>3))))\<close>
| \<open>infer uf B A pd (EFn ps b) n =
     infer_pats uf B ps n \<bind> (\<lambda>(sp, \<tau>s, \<Gamma>, n\<^sub>1).
       infer uf (mono_env sid \<Gamma> @ sappe sp B) (RV n\<^sub>1) (sub_pend sp pd) b (Suc n\<^sub>1) \<bind>
         (\<lambda>(s\<^sub>2, b', \<tau>\<^sub>b, pd\<^sub>2, n\<^sub>2).
           (let s = s\<^sub>2 \<odot> sp; \<tau>\<^sub>a = sapp s\<^sub>2 (fn_ty \<tau>s)
            in (if covers (sappe s B) \<tau>\<^sub>a [fn_pat ps]
                then Some (s, EFn ps b', TFn \<tau>\<^sub>a (sappr s\<^sub>2 (RV n\<^sub>1)) \<tau>\<^sub>b, pd\<^sub>2, n\<^sub>2)
                else None))))\<close>
| \<open>infer uf B A pd (EFnMod b e) n =
     sig_stat B n (mbind_sig b) \<bind> (\<lambda>((T, E), _).
       dep_env B n (mbind_sig b) (length T) \<bind> (\<lambda>(K, E\<^sub>K, n\<^sub>2).
         infer uf
               ((mbind_nm b,
                 if is_imp b then TEinst (param_env E\<^sub>K) else TEstr (param_env E\<^sub>K)) # B)
               (RV n\<^sub>2) pd e (Suc n\<^sub>2) \<bind> (\<lambda>(s, e', \<tau>, pd\<^sub>1, n\<^sub>3).
           resolve_inner K pd\<^sub>1 \<bind> (\<lambda>pd'.
             (if list_all (\<lambda>a. set K \<inter> ktv (fst s a) = {}) [0 ..< Suc n\<^sub>2] \<and>
                 set K \<inter> ktv_env B = {} \<and>
                 named_sig (mbind_sig b) \<and> nm_ok (mbind_nm b)
              then Some (sproj (Suc n\<^sub>2) s, EFnMod b e',
                         TDep (is_imp b) (mbind_sig b) (length T)
                           (sappr s (RV n\<^sub>2)) (kclose K \<tau>), pd', n\<^sub>3)
              else None)))))\<close>
| \<open>infer uf B A pd (ELet p e b) n =
     infer uf B A pd e n \<bind> (\<lambda>(s\<^sub>1, e', \<tau>\<^sub>e, pd\<^sub>1, n\<^sub>1).
       infer_pat uf (sappe s\<^sub>1 B) p n\<^sub>1 \<bind> (\<lambda>(sp, \<tau>\<^sub>p, \<Gamma>, n\<^sub>2).
         uni uf (sapp sp \<tau>\<^sub>e) \<tau>\<^sub>p n\<^sub>2 \<bind> (\<lambda>(s\<^sub>2, n\<^sub>3).
           (let s = s\<^sub>2 \<odot> sp \<odot> s\<^sub>1; B' = sappe s B; A' = sappr s A; pd' = sub_pend (s\<^sub>2 \<odot> sp) pd\<^sub>1;
                \<tau>\<^sub>e' = sapp s\<^sub>2 \<tau>\<^sub>p;
                (as, rs) = (if val_exp B e' then gen_p B' A' pd' n \<tau>\<^sub>e' else ({}, {}));
                \<Gamma>' = map (\<lambda>(x, \<tau>). (x, TEval (close_sch as rs (sapp s\<^sub>2 \<tau>)))) \<Gamma>
            in (if covers B' \<tau>\<^sub>e' [p] \<and> btv_list \<tau>\<^sub>e' = [] \<and> brv_list \<tau>\<^sub>e' = []
                then infer uf (\<Gamma>' @ B') A' pd' b n\<^sub>3 \<bind> (\<lambda>(s\<^sub>3, b', \<tau>, pd\<^sub>3, n\<^sub>4).
                       Some (s\<^sub>3 \<odot> s, ELet p e' b', \<tau>, pd\<^sub>3, n\<^sub>4))
                else None)))))\<close>
| \<open>infer uf B A pd (ESeq e\<^sub>1 e\<^sub>2) n =
     infer uf B A pd e\<^sub>1 n \<bind> (\<lambda>(s\<^sub>1, e\<^sub>1', \<tau>\<^sub>1, pd\<^sub>1, n\<^sub>1).
       infer uf (sappe s\<^sub>1 B) (sappr s\<^sub>1 A) pd\<^sub>1 e\<^sub>2 n\<^sub>1 \<bind> (\<lambda>(s\<^sub>2, e\<^sub>2', \<tau>, pd\<^sub>2, n\<^sub>2).
         Some (s\<^sub>2 \<odot> s\<^sub>1, ESeq e\<^sub>1' e\<^sub>2', \<tau>, pd\<^sub>2, n\<^sub>2)))\<close>
| \<open>infer uf B A pd (EIf c t (Some e)) n =
     infer uf B A pd c n \<bind> (\<lambda>(s\<^sub>1, c', \<tau>\<^sub>c, pd\<^sub>1, n\<^sub>1).
       uni uf \<tau>\<^sub>c (TC bool_ty []) n\<^sub>1 \<bind> (\<lambda>(s\<^sub>2, n\<^sub>2).
         (let s = s\<^sub>2 \<odot> s\<^sub>1 in
          infer uf (sappe s B) (sappr s A) (sub_pend s\<^sub>2 pd\<^sub>1) t n\<^sub>2 \<bind> (\<lambda>(s\<^sub>3, t', \<tau>\<^sub>t, pd\<^sub>3, n\<^sub>3).
            (let s' = s\<^sub>3 \<odot> s in
             infer uf (sappe s' B) (sappr s' A) pd\<^sub>3 e n\<^sub>3 \<bind> (\<lambda>(s\<^sub>4, e', \<tau>\<^sub>e, pd\<^sub>4, n\<^sub>4).
               uni uf \<tau>\<^sub>e (sapp s\<^sub>4 \<tau>\<^sub>t) n\<^sub>4 \<bind> (\<lambda>(s\<^sub>5, n\<^sub>5).
                 Some (s\<^sub>5 \<odot> s\<^sub>4 \<odot> s', EIf c' t' (Some e'), sapp s\<^sub>5 (sapp s\<^sub>4 \<tau>\<^sub>t),
                       sub_pend s\<^sub>5 pd\<^sub>4, n\<^sub>5))))))))\<close>
| \<open>infer uf B A pd (EIf c t None) n =
     infer uf B A pd c n \<bind> (\<lambda>(s\<^sub>1, c', \<tau>\<^sub>c, pd\<^sub>1, n\<^sub>1).
       uni uf \<tau>\<^sub>c (TC bool_ty []) n\<^sub>1 \<bind> (\<lambda>(s\<^sub>2, n\<^sub>2).
         (let s = s\<^sub>2 \<odot> s\<^sub>1 in
          infer uf (sappe s B) (sappr s A) (sub_pend s\<^sub>2 pd\<^sub>1) t n\<^sub>2 \<bind> (\<lambda>(s\<^sub>3, t', \<tau>\<^sub>t, pd\<^sub>3, n\<^sub>3).
            uni uf \<tau>\<^sub>t unit_ty n\<^sub>3 \<bind> (\<lambda>(s\<^sub>4, n\<^sub>4).
              Some (s\<^sub>4 \<odot> s\<^sub>3 \<odot> s, EIf c' t' None, unit_ty, sub_pend s\<^sub>4 pd\<^sub>3, n\<^sub>4))))))\<close>
| \<open>infer uf B A pd (EMatch e arms) n =
     infer uf B A pd e n \<bind> (\<lambda>(s\<^sub>1, e', \<tau>\<^sub>0, pd\<^sub>1, n\<^sub>1).
       infer_arms uf (sappe s\<^sub>1 B) (sappr s\<^sub>1 A) pd\<^sub>1 \<tau>\<^sub>0 (TV n\<^sub>1) arms (Suc n\<^sub>1) \<bind>
         (\<lambda>(s\<^sub>2, arms', pd\<^sub>2, n\<^sub>2).
           (if covers (sappe (s\<^sub>2 \<odot> s\<^sub>1) B) (sapp s\<^sub>2 \<tau>\<^sub>0) (map fst arms)
            then Some (s\<^sub>2 \<odot> s\<^sub>1, EMatch e' arms', sapp s\<^sub>2 (TV n\<^sub>1), pd\<^sub>2, n\<^sub>2)
            else None)))\<close>
| \<open>infer uf B A pd (EHandle e cls) n =
     (if list_all (plain_eff B) (hlabels B cls) then
        infer uf B (canon_row (rext (hlabels B cls) A)) pd e n \<bind> (\<lambda>(s\<^sub>1, e', \<tau>\<^sub>0, pd\<^sub>1, n\<^sub>1).
          infer_cls uf (sappe s\<^sub>1 B) (sappr s\<^sub>1 A) pd\<^sub>1 False \<tau>\<^sub>0 (tuple []) cls n\<^sub>1 \<bind>
            (\<lambda>(s\<^sub>2, cls', \<tau>, pd\<^sub>2, n\<^sub>2).
            Some (s\<^sub>2 \<odot> s\<^sub>1, EHandle e' cls', \<tau>, pd\<^sub>2, n\<^sub>2)))
      else None)\<close>
| \<open>infer uf B A pd (EHandler cls) n =
     (if list_all (plain_eff B) (hlabels B cls) then
        infer_cls uf B (RV n) pd False (TV (Suc n)) (tuple []) cls (Suc (Suc n)) \<bind>
          (\<lambda>(s, cls', \<tau>, pd', n').
          Some (s, EHandler cls',
                TFn (TFn unit_ty (sappr s (canon_row (rext (hlabels B cls) (RV n))))
                         (sapp s (TV (Suc n))))
                    (sappr s (RV n)) \<tau>,
                pd', n'))
      else None)\<close>
| \<open>infer uf B A pd (EMask l e) n =
     (case tlookup B [n_txt l] of
        Some (TEop lbl ps \<tau>\<^sub>1 \<tau>\<^sub>2) \<Rightarrow>
          uni_row A (canon_row (RCons lbl (RV n))) (Suc n) \<bind> (\<lambda>(s\<^sub>1, n\<^sub>1).
            infer uf (sappe s\<^sub>1 B) (sappr s\<^sub>1 (RV n)) (sub_pend s\<^sub>1 pd) e n\<^sub>1 \<bind>
              (\<lambda>(s\<^sub>2, e', \<tau>, pd\<^sub>2, n\<^sub>2).
              Some (s\<^sub>2 \<odot> s\<^sub>1, EMask l e', \<tau>, pd\<^sub>2, n\<^sub>2)))
      | _ \<Rightarrow> None)\<close>
| \<open>infer uf B A pd (ELetFun f mbs cls b) n =
     (let r = foldr EFnMod mbs (dfun_rhs cls)
      in (if cls = [] \<or> \<not> is_fn r \<or> \<not> nm_ok (n_txt f) then None else
          infer uf ((n_txt f, TEval (kmono (TV n))) # B) A pd r (Suc n) \<bind>
            (\<lambda>(s\<^sub>1, r', \<tau>', pd\<^sub>1, n\<^sub>1).
            uni uf (sapp s\<^sub>1 (TV n)) \<tau>' n\<^sub>1 \<bind> (\<lambda>(s\<^sub>2, n\<^sub>2).
              (let s = s\<^sub>2 \<odot> s\<^sub>1; B' = sappe s B; A' = sappr s A; pd' = sub_pend s\<^sub>2 pd\<^sub>1;
                   \<tau> = sapp s\<^sub>2 \<tau>'; (as, rs) = gen_p B' A' pd' n \<tau>
               in (if btv_list \<tau> = [] \<and> brv_list \<tau> = []
                   then infer uf ((n_txt f, TEval (close_sch as rs \<tau>)) # B') A' pd' b n\<^sub>2 \<bind>
                          (\<lambda>(s\<^sub>3, b', \<tau>\<^sub>b, pd\<^sub>3, n\<^sub>3).
                          Some (s\<^sub>3 \<odot> s, ELetFun f [] [([], r')] b', \<tau>\<^sub>b, pd\<^sub>3, n\<^sub>3))
                   else None))))))\<close>
| \<open>infer uf B A pd (EGuards []) n = None\<close>
| \<open>infer uf B A pd (EGuards ((gs, e) # alts)) n =
     infer_exps uf B A pd gs n \<bind> (\<lambda>(s\<^sub>1, gs', \<tau>s, pd\<^sub>1, n\<^sub>1).
       unis uf (map (\<lambda>\<tau>. (\<tau>, TC bool_ty [])) \<tau>s) n\<^sub>1 \<bind> (\<lambda>(s\<^sub>2, n\<^sub>2).
         (let s = s\<^sub>2 \<odot> s\<^sub>1 in
          infer uf (sappe s B) (sappr s A) (sub_pend s\<^sub>2 pd\<^sub>1) e n\<^sub>2 \<bind> (\<lambda>(s\<^sub>3, e', \<tau>\<^sub>e, pd\<^sub>3, n\<^sub>3).
            (if alts = [] then Some (s\<^sub>3 \<odot> s, EGuards [(gs', e')], \<tau>\<^sub>e, pd\<^sub>3, n\<^sub>3)
             else (let s' = s\<^sub>3 \<odot> s in
               infer uf (sappe s' B) (sappr s' A) pd\<^sub>3 (EGuards alts) n\<^sub>3 \<bind>
                 (\<lambda>(s\<^sub>4, g', \<tau>\<^sub>g, pd\<^sub>4, n\<^sub>4).
                 uni uf \<tau>\<^sub>g (sapp s\<^sub>4 \<tau>\<^sub>e) n\<^sub>4 \<bind> (\<lambda>(s\<^sub>5, n\<^sub>5).
                   Some (s\<^sub>5 \<odot> s\<^sub>4 \<odot> s', EGuards ((gs', e') # guards_of g'),
                         sapp s\<^sub>5 \<tau>\<^sub>g, sub_pend s\<^sub>5 pd\<^sub>4, n\<^sub>5)))))))))\<close>
| \<open>infer uf B A pd EErr n = None\<close>

| \<open>infer_head uf B A pd (APath p) n =
     (case tlookup B (path_nms p) of
        Some (TEval \<sigma>) \<Rightarrow> (case inst_scheme n \<sigma> of (\<tau>, n') \<Rightarrow> Some (sid, APath p, \<tau>, pd, n'))
      | Some (TEcon \<sigma> m) \<Rightarrow> (case inst_scheme n \<sigma> of (\<tau>, n') \<Rightarrow> Some (sid, APath p, \<tau>, pd, n'))
      | Some (TEop l ps \<tau>\<^sub>1 \<tau>\<^sub>2) \<Rightarrow>
          (if ps = []
           then Some (sid, APath p, TFn \<tau>\<^sub>1 (canon_row (RCons l (RV n))) \<tau>\<^sub>2, pd, Suc n)
           else None)
      | Some (TEffi s \<sigma>) \<Rightarrow> (case inst_scheme n \<sigma> of (\<tau>, n') \<Rightarrow> Some (sid, APath p, \<tau>, pd, n'))
      | Some _ \<Rightarrow> None
      | None \<Rightarrow> infer_opn uf B pd p n)\<close>
| \<open>infer_head uf B A pd a n = infer_atom uf B A pd a n\<close>

| \<open>infer_atom uf B A pd (APath p) n =
     (case tlookup B (path_nms p) of
        Some (TEval \<sigma>) \<Rightarrow> (case inst_scheme n \<sigma> of (\<tau>, n') \<Rightarrow> Some (sid, APath p, \<tau>, pd, n'))
      | Some (TEcon \<sigma> m) \<Rightarrow> (case inst_scheme n \<sigma> of (\<tau>, n') \<Rightarrow> Some (sid, APath p, \<tau>, pd, n'))
      | Some (TEop l ps \<tau>\<^sub>1 \<tau>\<^sub>2) \<Rightarrow>
          (if ps = []
           then Some (sid, APath p, TFn \<tau>\<^sub>1 (canon_row (RCons l (RV n))) \<tau>\<^sub>2, pd, Suc n)
           else None)
      | Some (TEffi s \<sigma>) \<Rightarrow> (case inst_scheme n \<sigma> of (\<tau>, n') \<Rightarrow> Some (sid, APath p, \<tau>, pd, n'))
      | Some _ \<Rightarrow> None
      | None \<Rightarrow> infer_opn uf B pd p n)\<close>
| \<open>infer_atom uf B A pd (ANum l v None) n = Some (sid, ANum l v None, TC int_ty [], pd, n)\<close>
| \<open>infer_atom uf B A pd (ANum l v (Some k)) n =
     (if sfx_ok k v then Some (sid, ANum l v (Some k), TC (sfx_ty k) [], pd, n) else None)\<close>
| \<open>infer_atom uf B A pd (AFloat x) n = Some (sid, AFloat x, TC f64_ty [], pd, n)\<close>
| \<open>infer_atom uf B A pd (AStr l cs) n = Some (sid, AStr l cs, TC string_ty [], pd, n)\<close>
| \<open>infer_atom uf B A pd (AChar l c) n = Some (sid, AChar l c, TC char_ty [], pd, n)\<close>
| \<open>infer_atom uf B A pd (AParen [e]) n =
     infer uf B A pd e n \<bind> (\<lambda>(s, e', \<tau>, pd', n'). Some (s, AParen [e'], \<tau>, pd', n'))\<close>
| \<open>infer_atom uf B A pd (AParen es) n =
     infer_exps uf B A pd es n \<bind> (\<lambda>(s, es', \<tau>s, pd', n'). Some (s, AParen es', tuple \<tau>s, pd', n'))\<close>
| \<open>infer_atom uf B A pd (AList es) n =
     infer_exps uf B A pd es n \<bind> (\<lambda>(s\<^sub>1, es', \<tau>s, pd\<^sub>1, n\<^sub>1).
       unis uf (map (\<lambda>\<tau>. (\<tau>, TV n\<^sub>1)) \<tau>s) (Suc n\<^sub>1) \<bind> (\<lambda>(s\<^sub>2, n\<^sub>2).
         Some (s\<^sub>2 \<odot> s\<^sub>1, AList es', TC list_ty [sapp s\<^sub>2 (TV n\<^sub>1)], sub_pend s\<^sub>2 pd\<^sub>1, n\<^sub>2)))\<close>
| \<open>infer_atom uf B A pd (ARec _) n = None\<close>
| \<open>infer_atom uf B A pd (ADot _ _) n = None\<close>
| \<open>infer_atom uf B A pd (AMod p sg) n = None\<close>
| \<open>infer_atom uf B A pd (ABind _ _) n = None\<close>

| \<open>infer_args uf B A pd d \<tau>\<^sub>0 as n =
     (case \<tau>\<^sub>0 of
        TDep True sg m \<epsilon>\<^sub>l \<tau>' \<Rightarrow>
          (if d = 0 then None else
          dep_env B n sg m \<bind> (\<lambda>(K, E\<^sub>K, n\<^sub>1).
            (if set K \<inter> ktv_env B \<noteq> {} then None else
            (let \<alpha>s = [n\<^sub>1 ..< n\<^sub>1 + m]; \<phi> = zip K (map TV \<alpha>s); n\<^sub>2 = n\<^sub>1 + m
             in uni_row \<epsilon>\<^sub>l A n\<^sub>2 \<bind> (\<lambda>(s\<^sub>1, n\<^sub>3).
                  (let x = imp_name n\<^sub>3;
                       pd' = (x, K, map (apsnd (sapp s\<^sub>1)) \<phi>, E\<^sub>K, cands B, None) # sub_pend s\<^sub>1 pd
                   in infer_args uf (sappe s\<^sub>1 B) (sappr s\<^sub>1 A) pd' (d - 1)
                        (sapp s\<^sub>1 (kopen (tsp K \<phi>) \<tau>')) as (Suc n\<^sub>3)
                        \<bind> (\<lambda>(s\<^sub>2, as', \<tau>, pd\<^sub>2, n\<^sub>4).
                          Some (s\<^sub>2 \<odot> s\<^sub>1, AMod (MkPath [mk_nm x]) sg # as', \<tau>, pd\<^sub>2, n\<^sub>4))))))))
      | TDep False sg m \<epsilon>\<^sub>l \<tau>' \<Rightarrow>
          (case as of
             APath P # rest \<Rightarrow>
               (if list_ex reserved (path_nms P) then None else
               case tlookup B (path_nms P) of
                  Some ent \<Rightarrow>
                    (case (case ent of TEstr E \<Rightarrow> Some E | TEinst E \<Rightarrow> Some E | _ \<Rightarrow> None) of
                       Some E\<^sub>P \<Rightarrow>
                         dep_env B n sg m \<bind> (\<lambda>(K, E\<^sub>K, n\<^sub>1).
                           (if set K \<inter> ktv_env B \<noteq> {} then None else
                           match_dep E\<^sub>P K E\<^sub>K \<bind> (\<lambda>\<phi>.
                             (if enrich E\<^sub>P (kenv (tsl \<phi>) E\<^sub>K)
                              then uni_row \<epsilon>\<^sub>l A n\<^sub>1 \<bind> (\<lambda>(s\<^sub>1, n\<^sub>2).
                                     infer_args uf (sappe s\<^sub>1 B) (sappr s\<^sub>1 A) (sub_pend s\<^sub>1 pd) d
                                                (sapp s\<^sub>1 (kopen (tsp K \<phi>) \<tau>')) rest n\<^sub>2 \<bind>
                                       (\<lambda>(s\<^sub>2, rest', \<tau>, pd\<^sub>2, n\<^sub>3).
                                         Some (s\<^sub>2 \<odot> s\<^sub>1, AMod P sg # rest', \<tau>, pd\<^sub>2, n\<^sub>3)))
                              else None))))
                     | None \<Rightarrow> None)
                | None \<Rightarrow> None)
           | _ \<Rightarrow> None)
      | _ \<Rightarrow>
          (case as of
             [] \<Rightarrow> Some (sid, [], \<tau>\<^sub>0, pd, n)
           | a # rest \<Rightarrow>
               infer_atom uf B A pd a n \<bind> (\<lambda>(s\<^sub>1, a', \<tau>\<^sub>a, pd\<^sub>1, n\<^sub>1).
                 app_arg uf (sappe s\<^sub>1 B) (sappr s\<^sub>1 A) pd\<^sub>1 (sapp s\<^sub>1 \<tau>\<^sub>0) \<tau>\<^sub>a n\<^sub>1 \<bind>
                   (\<lambda>(s\<^sub>2, \<tau>\<^sub>r, pd\<^sub>2, n\<^sub>2).
                   (let s = s\<^sub>2 \<odot> s\<^sub>1 in
                    infer_args uf (sappe s B) (sappr s A) pd\<^sub>2 d \<tau>\<^sub>r rest n\<^sub>2 \<bind>
                      (\<lambda>(s\<^sub>3, rest', \<tau>, pd\<^sub>3, n\<^sub>3).
                        Some (s\<^sub>3 \<odot> s, a' # rest', \<tau>, pd\<^sub>3, n\<^sub>3)))))))\<close>

| \<open>infer_exps uf B A pd [] n = Some (sid, [], [], pd, n)\<close>
| \<open>infer_exps uf B A pd (e # es) n =
     infer uf B A pd e n \<bind> (\<lambda>(s\<^sub>1, e', \<tau>, pd\<^sub>1, n\<^sub>1).
       infer_exps uf (sappe s\<^sub>1 B) (sappr s\<^sub>1 A) pd\<^sub>1 es n\<^sub>1 \<bind> (\<lambda>(s\<^sub>2, es', \<tau>s, pd\<^sub>2, n\<^sub>2).
         Some (s\<^sub>2 \<odot> s\<^sub>1, e' # es', sapp s\<^sub>2 \<tau> # \<tau>s, pd\<^sub>2, n\<^sub>2)))\<close>

| \<open>infer_chain uf B A pd (EOp (a # as) opr e) n =
     infer_head uf B A pd a n \<bind> (\<lambda>(s\<^sub>1, a', \<tau>\<^sub>0, pd\<^sub>1, n\<^sub>1).
       infer_args uf (sappe s\<^sub>1 B) (sappr s\<^sub>1 A) pd\<^sub>1 uf \<tau>\<^sub>0 as n\<^sub>1 \<bind> (\<lambda>(s\<^sub>2, as', \<tau>, pd\<^sub>2, n\<^sub>2).
         (let s = s\<^sub>2 \<odot> s\<^sub>1 in
          (if is_eop e
           then infer_chain uf (sappe s B) (sappr s A) pd\<^sub>2 e n\<^sub>2 \<bind>
                  (\<lambda>(s\<^sub>3, e', oprs, \<tau>s, pd\<^sub>3, n\<^sub>3).
                  Some (s\<^sub>3 \<odot> s, EOp (a' # as') opr e', opr # oprs, sapp s\<^sub>3 \<tau> # \<tau>s, pd\<^sub>3, n\<^sub>3))
           else infer uf (sappe s B) (sappr s A) pd\<^sub>2 e n\<^sub>2 \<bind> (\<lambda>(s\<^sub>3, e', \<tau>\<^sub>l, pd\<^sub>3, n\<^sub>3).
                  Some (s\<^sub>3 \<odot> s, EOp (a' # as') opr e', [opr], [sapp s\<^sub>3 \<tau>, \<tau>\<^sub>l], pd\<^sub>3, n\<^sub>3))))))\<close>
| \<open>infer_chain uf B A pd _ n = None\<close>

| \<open>infer_arms uf B A pd \<tau>\<^sub>0 \<tau>\<^sub>r [] n = Some (sid, [], pd, n)\<close>
| \<open>infer_arms uf B A pd \<tau>\<^sub>0 \<tau>\<^sub>r ((p, b) # arms) n =
     infer_pat uf B p n \<bind> (\<lambda>(sp, \<tau>\<^sub>p, \<Gamma>, n\<^sub>1).
       uni uf (sapp sp \<tau>\<^sub>0) \<tau>\<^sub>p n\<^sub>1 \<bind> (\<lambda>(s\<^sub>1, n\<^sub>2).
         (let s = s\<^sub>1 \<odot> sp in
          infer uf (mono_env s\<^sub>1 \<Gamma> @ sappe s B) (sappr s A) (sub_pend s pd) b n\<^sub>2 \<bind>
            (\<lambda>(s\<^sub>2, b', \<tau>\<^sub>b, pd\<^sub>2, n\<^sub>3).
              uni uf \<tau>\<^sub>b (sapp (s\<^sub>2 \<odot> s) \<tau>\<^sub>r) n\<^sub>3 \<bind> (\<lambda>(s\<^sub>3, n\<^sub>4).
                (let s' = s\<^sub>3 \<odot> s\<^sub>2 \<odot> s in
                 infer_arms uf (sappe s' B) (sappr s' A) (sub_pend s\<^sub>3 pd\<^sub>2)
                   (sapp s' \<tau>\<^sub>0) (sapp s' \<tau>\<^sub>r) arms n\<^sub>4 \<bind>
                   (\<lambda>(s\<^sub>4, arms', pd\<^sub>4, n\<^sub>5).
                     Some (s\<^sub>4 \<odot> s', (p, b') # arms', pd\<^sub>4, n\<^sub>5))))))))\<close>

| \<open>infer_cls uf B A pd nm \<tau>\<^sub>0 targs [] n = Some (sid, [], \<tau>\<^sub>0, pd, n)\<close>
| \<open>infer_cls uf B A pd nm \<tau>\<^sub>0 targs (HOp opn ps k b # cls) n =
     (case (tlookup B [n_txt opn], targs) of
        (Some (TEop l eps \<tau>\<^sub>1\<^sub>0 \<tau>\<^sub>2\<^sub>0), TC c args) \<Rightarrow>
          (if c = tuple_ty (length eps) \<and> length args = length eps then
          (let \<tau>\<^sub>1 = op_inst eps args \<tau>\<^sub>1\<^sub>0; \<tau>\<^sub>2 = op_inst eps args \<tau>\<^sub>2\<^sub>0 in
          infer_pats uf B ps n \<bind> (\<lambda>(sp, \<tau>s, \<Gamma>, n\<^sub>1).
            uni uf (fn_ty \<tau>s) (sapp sp \<tau>\<^sub>1) n\<^sub>1 \<bind> (\<lambda>(s\<^sub>1, n\<^sub>2).
              (let s = s\<^sub>1 \<odot> sp; B' = sappe s B;
                   \<epsilon>' = (if nm then sappr s A else canon_row (rext (hlabels B cls) (sappr s A)));
                   \<tau>\<^sub>0' = sapp s \<tau>\<^sub>0;
                   \<Gamma>' = (case k of
                           None \<Rightarrow> mono_env s\<^sub>1 \<Gamma>
                         | Some kn \<Rightarrow> (n_txt kn,
                                      TEval (kmono (TFn (sapp s \<tau>\<^sub>2) \<epsilon>' \<tau>\<^sub>0'))) # mono_env s\<^sub>1 \<Gamma>)
               in (if covers B' (sapp s\<^sub>1 (fn_ty \<tau>s)) [fn_pat ps] \<and>
                      (case k of None \<Rightarrow> True
                       | Some kn \<Rightarrow> n_txt kn \<notin> set (map fst \<Gamma>) \<and> nm_ok (n_txt kn))
                   then infer uf (\<Gamma>' @ B') \<epsilon>' (sub_pend s pd) b n\<^sub>2 \<bind> (\<lambda>(s\<^sub>2, b', \<tau>\<^sub>b, pd\<^sub>2, n\<^sub>3).
                          uni uf \<tau>\<^sub>b (case k of None \<Rightarrow> sapp (s\<^sub>2 \<odot> s) \<tau>\<^sub>2
                                      | Some _ \<Rightarrow> sapp s\<^sub>2 \<tau>\<^sub>0') n\<^sub>3 \<bind>
                            (\<lambda>(s\<^sub>3, n\<^sub>4).
                              (let s' = s\<^sub>3 \<odot> s\<^sub>2 \<odot> s in
                               infer_cls uf (sappe s' B) (sappr s' A) (sub_pend s\<^sub>3 pd\<^sub>2)
                                 nm (sapp s' \<tau>\<^sub>0) (sapp s' targs) cls n\<^sub>4 \<bind>
                                 (\<lambda>(s\<^sub>4, cls', \<tau>, pd\<^sub>4, n\<^sub>5).
                                   Some (s\<^sub>4 \<odot> s', HOp opn ps k b' # cls', \<tau>, pd\<^sub>4, n\<^sub>5)))))
                   else None)))))
          else None)
      | _ \<Rightarrow> None)\<close>
| \<open>infer_cls uf B A pd nm \<tau>\<^sub>0 targs (HRet p b # cls) n =
     infer_pat uf B p n \<bind> (\<lambda>(sp, \<tau>\<^sub>p, \<Gamma>, n\<^sub>1).
       uni uf (sapp sp \<tau>\<^sub>0) \<tau>\<^sub>p n\<^sub>1 \<bind> (\<lambda>(s\<^sub>1, n\<^sub>2).
         (let s = s\<^sub>1 \<odot> sp; B' = sappe s B;
              \<epsilon>' = (if nm then sappr s A else canon_row (rext (hlabels B cls) (sappr s A)))
          in (if covers B' (sapp s\<^sub>1 \<tau>\<^sub>p) [p] \<and> (nm \<longrightarrow> hlabels B cls = [])
              then infer uf (mono_env s\<^sub>1 \<Gamma> @ B') \<epsilon>' (sub_pend s pd) b n\<^sub>2 \<bind>
                     (\<lambda>(s\<^sub>2, b', \<tau>', pd\<^sub>2, n\<^sub>3).
                     (let s' = s\<^sub>2 \<odot> s in
                      infer_cls uf (sappe s' B) (sappr s' A) pd\<^sub>2 nm \<tau>' (sapp s' targs) cls n\<^sub>3 \<bind>
                        (\<lambda>(s\<^sub>3, cls', \<tau>, pd\<^sub>3, n\<^sub>4).
                        Some (s\<^sub>3 \<odot> s', HRet p b' # cls', \<tau>, pd\<^sub>3, n\<^sub>4))))
              else None))))\<close>
| \<open>infer_cls uf B A pd nm \<tau>\<^sub>0 targs (HFin b # cls) n =
     infer uf B A pd b n \<bind> (\<lambda>(s\<^sub>1, b', \<tau>\<^sub>f, pd\<^sub>1, n\<^sub>1).
       uni uf \<tau>\<^sub>f unit_ty n\<^sub>1 \<bind> (\<lambda>(s\<^sub>2, n\<^sub>2).
         (let s = s\<^sub>2 \<odot> s\<^sub>1 in
          infer_cls uf (sappe s B) (sappr s A) (sub_pend s\<^sub>2 pd\<^sub>1) nm (sapp s \<tau>\<^sub>0) (sapp s targs)
            cls n\<^sub>2 \<bind>
            (\<lambda>(s\<^sub>3, cls', \<tau>, pd\<^sub>3, n\<^sub>3). Some (s\<^sub>3 \<odot> s, HFin b' # cls', \<tau>, pd\<^sub>3, n\<^sub>3)))))\<close>
| \<open>infer_cls uf B A pd nm \<tau>\<^sub>0 targs (_ # cls) n = None\<close>

  \<comment> \<open>Named handlers: a first-class named handler (\<open>W_handlern\<close>), and its
     installation (\<open>W_with\<close>): the handler is applied as by \<^const>\<open>app_arg\<close> to an
     action with one scope variable and a fresh effect, row and type, so that the
     name's effect is known when the body is inferred (and so may be named in its
     annotations); the body is then unified with the action's result type. The scope
     variable must not escape into the substitution on the variables older than
     the body; the variables the body minted are projected away.\<close>
| \<open>infer uf B A pd (EHandlerN cls) n =
     (case hlabels B cls of
        [] \<Rightarrow> None
      | lbl # _ \<Rightarrow>
          (case eff_of_op B lbl of
             None \<Rightarrow> None
           | Some (l, ls, ar) \<Rightarrow>
               (if set (hlabels B cls) = set (map (mangle l) ls)
                then (let args = map TV [n ..< n + ar]; k = n + ar;
                          n\<^sub>1 = Suc (n + ar); n\<^sub>2 = Suc n\<^sub>1
                      in (if k \<in> ktv_env B then None else
                          infer_cls uf B (RV n\<^sub>1) pd True (TV n\<^sub>2) (tuple args) cls (Suc n\<^sub>2) \<bind>
                            (\<lambda>(s, cls', \<tau>, pd', n').
                            (let \<epsilon>' = sappr s (RV n\<^sub>1); \<tau>\<^sub>0 = sapp s (TV n\<^sub>2)
                             in (if k \<notin> ktv \<tau>\<^sub>0 \<and> k \<notin> ktv \<tau> \<and> k \<notin> ktv (sapp s (tuple args)) \<and>
                                    list_all (\<lambda>a. k \<notin> ktv (fst s a)) [0 ..< Suc n\<^sub>2]
                                 then Some (s, EHandlerN cls',
                                            TFn (TAct (eff_ty l (map (sapp s) args)) [k]
                                                 (canon_row (rext (map (nlbl \<circ> mangle l) ls) \<epsilon>'))
                                                 \<tau>\<^sub>0)
                                                \<epsilon>' \<tau>,
                                            pd', n')
                                 else None)))))
                else None)))\<close>
| \<open>infer uf B A pd (EWith x h e) n =
     infer uf B A pd h n \<bind> (\<lambda>(s\<^sub>1, h', \<tau>\<^sub>h, pd\<^sub>1, n\<^sub>1).
       (let B\<^sub>1 = sappe s\<^sub>1 B; k = n\<^sub>1; lt = TV (Suc n\<^sub>1); targs = TV (Suc (Suc n\<^sub>1));
            \<epsilon>\<^sub>0 = RV (Suc (Suc (Suc n\<^sub>1))); \<tau>\<^sub>0 = TV (Suc (Suc (Suc (Suc n\<^sub>1))));
            n\<^sub>2 = Suc (Suc (Suc (Suc (Suc n\<^sub>1))))
        in (if k \<in> ktv_env B\<^sub>1 \<or> \<not> nm_ok (n_txt x) then None else
            app_arg uf B\<^sub>1 (sappr s\<^sub>1 A) pd\<^sub>1 \<tau>\<^sub>h (TAct lt [k] \<epsilon>\<^sub>0 \<tau>\<^sub>0) n\<^sub>2 \<bind> (\<lambda>(s\<^sub>2, \<tau>, pd\<^sub>2, n\<^sub>3).
              (let B\<^sub>2 = sappe s\<^sub>2 B\<^sub>1; lt' = sapp s\<^sub>2 lt
               in infer uf (name_env B\<^sub>2 (n_txt x) lt' @
                            (n_txt x, TEval (kmono (TEv lt' (TK k) (sapp s\<^sub>2 targs)))) # B\<^sub>2)
                     (sappr s\<^sub>2 \<epsilon>\<^sub>0) pd\<^sub>2 e n\<^sub>3 \<bind> (\<lambda>(s\<^sub>3, e', \<tau>\<^sub>0', pd\<^sub>3, n\<^sub>4).
                 uni uf (sapp (s\<^sub>3 \<odot> s\<^sub>2) \<tau>\<^sub>0) \<tau>\<^sub>0' n\<^sub>4 \<bind> (\<lambda>(s\<^sub>4, n\<^sub>5).
                   (let s' = s\<^sub>4 \<odot> s\<^sub>3
                    in (if list_all (\<lambda>a. k \<notin> ktv (fst s' a)) [0 ..< n\<^sub>3]
                        then Some (sproj n\<^sub>3 s' \<odot> s\<^sub>2 \<odot> s\<^sub>1, EWith x h' e', sapp (sproj n\<^sub>3 s') \<tau>,
                                   sub_pend s\<^sub>4 pd\<^sub>3, n\<^sub>5)
                        else None)))))))))\<close>
  by pat_completeness auto

termination
  by (relation \<open>measures [\<lambda>x. case x of
        Inl (Inl (Inl (uf, B, A, pd, e, n))) \<Rightarrow> nlf e
      | Inl (Inl (Inr (uf, B, A, pd, a, n))) \<Rightarrow> nlf_atom a
      | Inl (Inr (Inl (uf, B, A, pd, a, n))) \<Rightarrow> nlf_atom a
      | Inl (Inr (Inr (uf, B, A, pd, d, \<tau>\<^sub>0, as, n))) \<Rightarrow> sum_list (map nlf_atom as)
      | Inr (Inl (Inl (uf, B, A, pd, es, n))) \<Rightarrow> sum_list (map nlf es)
      | Inr (Inl (Inr (uf, B, A, pd, e, n))) \<Rightarrow> nlf e
      | Inr (Inr (Inl (uf, B, A, pd, \<tau>\<^sub>0, \<tau>\<^sub>r, arms, n))) \<Rightarrow>
          sum_list (map (\<lambda>(_, e). nlf e) arms)
      | Inr (Inr (Inr (uf, B, A, pd, nm, \<tau>\<^sub>0, targs, cls, n))) \<Rightarrow> sum_list (map nlf_cl cls),
      \<lambda>x. case x of
        Inl (Inl (Inl (uf, B, A, pd, e, n))) \<Rightarrow> 2 * size e + 1
      | Inl (Inl (Inr (uf, B, A, pd, a, n))) \<Rightarrow> 2 * size a + 1
      | Inl (Inr (Inl (uf, B, A, pd, a, n))) \<Rightarrow> 2 * size a
      | Inl (Inr (Inr (uf, B, A, pd, d, \<tau>\<^sub>0, as, n))) \<Rightarrow> 2 * size_list size as
      | Inr (Inl (Inl (uf, B, A, pd, es, n))) \<Rightarrow> 2 * size_list size es
      | Inr (Inl (Inr (uf, B, A, pd, e, n))) \<Rightarrow> 2 * size e
      | Inr (Inr (Inl (uf, B, A, pd, \<tau>\<^sub>0, \<tau>\<^sub>r, arms, n))) \<Rightarrow>
          2 * size_list (size_prod (\<lambda>_. 0) size) arms
      | Inr (Inr (Inr (uf, B, A, pd, nm, \<tau>\<^sub>0, targs, cls, n))) \<Rightarrow> 2 * size_list size cls,
      \<lambda>x. case x of
        Inl (Inr (Inr (uf, B, A, pd, d, \<tau>\<^sub>0, as, n))) \<Rightarrow> d
      | _ \<Rightarrow> 0]\<close>) (auto, (drule (1) bspec; simp)+)

lemmas infer_induct =
  infer_infer_head_infer_atom_infer_args_infer_exps_infer_chain_infer_arms_infer_cls.induct[
    named_cases infer]

text \<open>The equation of \<^const>\<open>infer_args\<close> at an argument whose function type is not
  dependent, unfolded once; the lemmas about the algorithm take it apart with this
  instead of splitting the whole equation.\<close>

lemma infer_args_Cons_plain:
  assumes \<open>\<forall>i sg m \<epsilon> t. \<tau>\<^sub>0 \<noteq> TDep i sg m \<epsilon> t\<close>
  shows \<open>infer_args uf B A pd d \<tau>\<^sub>0 (a # rest) n =
    infer_atom uf B A pd a n \<bind> (\<lambda>(s\<^sub>1, a', \<tau>\<^sub>a, pd\<^sub>1, n\<^sub>1).
      app_arg uf (sappe s\<^sub>1 B) (sappr s\<^sub>1 A) pd\<^sub>1 (sapp s\<^sub>1 \<tau>\<^sub>0) \<tau>\<^sub>a n\<^sub>1 \<bind>
        (\<lambda>(s\<^sub>2, \<tau>\<^sub>r, pd\<^sub>2, n\<^sub>2).
        infer_args uf (sappe (s\<^sub>2 \<odot> s\<^sub>1) B) (sappr (s\<^sub>2 \<odot> s\<^sub>1) A) pd\<^sub>2 d \<tau>\<^sub>r rest n\<^sub>2 \<bind>
          (\<lambda>(s\<^sub>3, rest', \<tau>, pd\<^sub>3, n\<^sub>3). Some (s\<^sub>3 \<odot> (s\<^sub>2 \<odot> s\<^sub>1), a' # rest', \<tau>, pd\<^sub>3, n\<^sub>3))))\<close>
  using assms by (subst infer_args.simps) (cases \<tau>\<^sub>0; simp only: kty.case list.case Let_def; blast)

lemma infer_args_TDep_APath:
  \<open>infer_args uf B A pd d (TDep False sg m \<epsilon>\<^sub>l \<tau>') (APath P # rest) n =
    (if list_ex reserved (path_nms P) then None else
    case tlookup B (path_nms P) of
       Some ent \<Rightarrow>
         (case (case ent of TEstr E \<Rightarrow> Some E | TEinst E \<Rightarrow> Some E | _ \<Rightarrow> None) of
            Some E\<^sub>P \<Rightarrow>
              dep_env B n sg m \<bind> (\<lambda>(K, E\<^sub>K, n\<^sub>1).
                (if set K \<inter> ktv_env B \<noteq> {} then None else
                match_dep E\<^sub>P K E\<^sub>K \<bind> (\<lambda>\<phi>.
                  (if enrich E\<^sub>P (kenv (tsl \<phi>) E\<^sub>K)
                   then uni_row \<epsilon>\<^sub>l A n\<^sub>1 \<bind> (\<lambda>(s\<^sub>1, n\<^sub>2).
                          infer_args uf (sappe s\<^sub>1 B) (sappr s\<^sub>1 A) (sub_pend s\<^sub>1 pd) d
                                     (sapp s\<^sub>1 (kopen (tsp K \<phi>) \<tau>')) rest n\<^sub>2 \<bind>
                            (\<lambda>(s\<^sub>2, rest', \<tau>, pd\<^sub>2, n\<^sub>3).
                              Some (s\<^sub>2 \<odot> s\<^sub>1, AMod P sg # rest', \<tau>, pd\<^sub>2, n\<^sub>3)))
                   else None))))
          | None \<Rightarrow> None)
     | None \<Rightarrow> None)\<close>
  by (subst infer_args.simps) (simp only: kty.case list.case matom.case bool.case)

lemma infer_args_TDep_True:
  \<open>infer_args uf B A pd d (TDep True sg m \<epsilon>\<^sub>l \<tau>') as n =
    (if d = 0 then None else
    dep_env B n sg m \<bind> (\<lambda>(K, E\<^sub>K, n\<^sub>1).
      (if set K \<inter> ktv_env B \<noteq> {} then None else
      (let \<alpha>s = [n\<^sub>1 ..< n\<^sub>1 + m]; \<phi> = zip K (map TV \<alpha>s); n\<^sub>2 = n\<^sub>1 + m
       in uni_row \<epsilon>\<^sub>l A n\<^sub>2 \<bind> (\<lambda>(s\<^sub>1, n\<^sub>3).
            (let x = imp_name n\<^sub>3;
                 pd' = (x, K, map (apsnd (sapp s\<^sub>1)) \<phi>, E\<^sub>K, cands B, None) # sub_pend s\<^sub>1 pd
             in infer_args uf (sappe s\<^sub>1 B) (sappr s\<^sub>1 A) pd' (d - 1)
                  (sapp s\<^sub>1 (kopen (tsp K \<phi>) \<tau>')) as (Suc n\<^sub>3)
                  \<bind> (\<lambda>(s\<^sub>2, as', \<tau>, pd\<^sub>2, n\<^sub>4).
                    Some (s\<^sub>2 \<odot> s\<^sub>1, AMod (MkPath [mk_nm x]) sg # as', \<tau>, pd\<^sub>2, n\<^sub>4))))))))\<close>
  by (subst infer_args.simps) (simp only: kty.case bool.case)

subsection \<open>Resolving pending implicit arguments\<close>

text \<open>After the enclosing binding: each pending request is resolved from
  its scope at the types unification found for the parameter's abstract
  types \<^cite>\<open>\<open>Sect. 2.2.2, 5.1\<close> in white2014\<close>; a request whose types are still
  variables finds no instance.\<close>

fun resolve_pend :: \<open>pend \<Rightarrow> ((name \<times> name) list) option\<close> where
  \<open>resolve_pend [] = Some []\<close>
| \<open>resolve_pend ((x, K, \<phi>, E, cs, r) # pd) =
     (if reserved x \<and> x \<notin> set (map fst pd)
      then imp_res cs K E \<phi> \<bind> (\<lambda>P.
             (if r = None \<or> r = Some P
              then resolve_pend pd \<bind> (\<lambda>tab. Some ((x, P) # tab))
              else None))
      else None)\<close>

subsection \<open>Declarations and modules\<close>

text \<open>A top-level binding is inferred under the closed row with no pending
  resolutions, its resolutions resolved, placeholders replaced, and its type
  generalised against the basis; the basis is closed, so the substitution
  does not touch it.\<close>

text \<open>Closed and bound-variable-free bases, decided on lists: the checker demands both
  of the basis it starts from and of the entries each declaration adds
  \<^cite>\<open>\<open>Sect. 4.8\<close> in milner1997\<close>.\<close>

definition closed_env :: \<open>tenv \<Rightarrow> bool\<close> where
  \<open>closed_env B \<longleftrightarrow> ftv_env B = {} \<and> frv_env B = {}\<close>

definition bfree_x :: \<open>kty \<Rightarrow> bool\<close> where
  \<open>bfree_x t \<longleftrightarrow> btv_list t = [] \<and> brv_list t = []\<close>

fun bfree_sch_x :: \<open>scheme \<Rightarrow> bool\<close> where
  \<open>bfree_sch_x (Sch t) = True\<close>
| \<open>bfree_sch_x (Mono t) = bfree_x t\<close>

fun bfree_ent_x :: \<open>tentry \<Rightarrow> bool\<close>
and bfree_env_x :: \<open>tenv \<Rightarrow> bool\<close>
where
  \<open>bfree_ent_x (TEval \<sigma>) = bfree_sch_x \<sigma>\<close>
| \<open>bfree_ent_x (TEcon \<sigma> n) = bfree_sch_x \<sigma>\<close>
| \<open>bfree_ent_x (TEffi s \<sigma>) = bfree_sch_x \<sigma>\<close>
| \<open>bfree_ent_x (TEop l ps t\<^sub>1 t\<^sub>2) =
     (set (btv_list t\<^sub>1) \<subseteq> set ps \<and> brv_list t\<^sub>1 = [] \<and>
      set (btv_list t\<^sub>2) \<subseteq> set ps \<and> brv_list t\<^sub>2 = [])\<close>
| \<open>bfree_ent_x (TEstr ex) = bfree_env_x ex\<close>
| \<open>bfree_ent_x (TEinst ex) = bfree_env_x ex\<close>
| \<open>bfree_ent_x (TEsig (T, E)) = bfree_env_x E\<close>
| \<open>bfree_ent_x (TEfun ps (T, E)) = (list_all (\<lambda>(x, T, E). bfree_env_x E) ps \<and> bfree_env_x E)\<close>
| \<open>bfree_ent_x e = True\<close>
| \<open>bfree_env_x [] = True\<close>
| \<open>bfree_env_x ((x, e) # ex) = (bfree_ent_x e \<and> bfree_env_x ex)\<close>

text \<open>A value declaration \<open>let x [: ty] = e\<close>. A function is inferred with \<open>x\<close> in
  scope at a fresh type; any other right-hand side is generalised only when it is a
  syntactic value or its type has no variables beyond the basis's
  \<^cite>\<open>wright1995\<close>.\<close>

definition infer_let ::
  \<open>nat \<Rightarrow> tenv \<Rightarrow> nm \<Rightarrow> expr \<Rightarrow> nat \<Rightarrow> (mdecl \<times> tenv \<times> nat) option\<close>
where
  \<open>infer_let uf B x e n =
     (if is_fn e
      then infer uf ((n_txt x, TEval (kmono (TV n))) # B) RNil [] e (Suc n) \<bind>
             (\<lambda>(s\<^sub>1, e', \<tau>', pd, n\<^sub>1).
             uni uf (sapp s\<^sub>1 (TV n)) \<tau>' n\<^sub>1 \<bind> (\<lambda>(s\<^sub>2, n\<^sub>2).
               resolve_pend (sub_pend s\<^sub>2 pd) \<bind> (\<lambda>tab.
                 (let \<tau> = sapp s\<^sub>2 \<tau>'
                  in (if \<not> bfree_x \<tau> then None else
                      Some (DLet x (subst_imp tab e'), [(n_txt x, TEval (gen B RNil \<tau>))], n\<^sub>2))))))
      else infer uf B RNil [] e n \<bind> (\<lambda>(s\<^sub>1, e', \<tau>, pd, n\<^sub>1).
             resolve_pend pd \<bind> (\<lambda>tab.
               (if \<not> bfree_x \<tau> \<or> \<not> ((ftv \<tau> \<subseteq> ftv_env B \<and> frv \<tau> \<subseteq> frv_env B) \<or> val_exp B e')
                then None
                else Some (DLet x (subst_imp tab e'), [(n_txt x, TEval (gen B RNil \<tau>))], n\<^sub>1)))))\<close>

text \<open>Declarations, declaration lists and module expressions under the module prefix
  \<open>pre\<close>: each returns the elaborated syntax, the basis it adds and its foreign
  declarations.\<close>

function (sequential) infer_decl ::
  \<open>nat \<Rightarrow> tenv \<Rightarrow> name \<Rightarrow> mdecl \<Rightarrow> nat \<Rightarrow> (mdecl \<times> tenv \<times> fenv \<times> nat) option\<close>
and infer_decls ::
  \<open>nat \<Rightarrow> tenv \<Rightarrow> name \<Rightarrow> mdecl list \<Rightarrow> nat \<Rightarrow> (mdecl list \<times> tenv \<times> fenv \<times> nat) option\<close>
and infer_mexp ::
  \<open>nat \<Rightarrow> tenv \<Rightarrow> name \<Rightarrow> mexpr \<Rightarrow> nat \<Rightarrow> (mexpr \<times> tentry \<times> fenv \<times> nat) option\<close>
where
  \<open>infer_decl uf B pre (DLet x e) n =
     (if rebind_ok B (n_txt x) \<and> nm_ok (n_txt x)
      then infer_let uf B x e n \<bind> (\<lambda>(d', E, n'). Some (d', E, [], n'))
      else None)\<close>
| \<open>infer_decl uf B pre (DFun f mbs cls) n =
     (if cls = [] \<or> \<not> rebind_ok B (n_txt f) \<or> \<not> nm_ok (n_txt f) then None
      else infer_let uf B f (foldr EFnMod mbs (dfun_rhs cls)) n \<bind>
             (\<lambda>(d', E, n'). Some (d', E, [], n')))\<close>
| \<open>infer_decl uf B pre (DExtern x ty sy) n =
     (if take (length functor_pre) pre \<noteq> functor_pre then
       ty_stat B True ([], []) n ty \<bind> (\<lambda>(\<tau>, _, n').
         (case \<tau> of
            TFn _ _ _ \<Rightarrow>
              (let \<sigma> = close_sch (set [n ..< n']) (set [n ..< n']) \<tau>
               in (if name_free \<tau>
                   then Some (DExtern x ty sy, [(n_txt x, TEffi (n_txt sy) \<sigma>)], [(n_txt sy, \<sigma>)], n')
                   else None))
          | _ \<Rightarrow> None)) else None)\<close>
| \<open>infer_decl uf B pre (DType t as ty) n =
     (let ps = [n ..< n + length as]
      in ty_stat B False (zip (map n_txt as) (map TV ps), []) (n + length as) ty \<bind> (\<lambda>(\<tau>, _, n').
           Some (DType t as ty, [(n_txt t, TEtyp (TyFn ps (close_ty (set ps) {} \<tau>)))], [], n')))\<close>
| \<open>infer_decl uf B pre (DData t as alts) n =
     (let ps = [Suc n ..< Suc n + length as];
          c = (n, n_txt t, map (\<lambda>(cn, args). (n_txt cn, length args)) alts);
          ent = (n_txt t, TEtyp (TyAbs c (length as)))
      in (if distinct (map (n_txt \<circ> fst) alts) \<and> n \<notin> stamps_env B \<and>
             list_all (\<lambda>(cn, _). rebind_ok B (n_txt cn)) alts \<and>
             list_all (\<lambda>(cn, _). nm_ok (n_txt cn)) alts
          then cons_stat (ent # B) (zip (map n_txt as) (map TV ps), [])
                 ps c (Suc n + length as) alts \<bind>
                 (\<lambda>(cs, n'). Some (DData t as alts, cs @ [ent], [], n'))
          else None))\<close>
| \<open>infer_decl uf B pre (DFix f prec opr) n =
     read_nat (n_txt prec) \<bind>
       (\<lambda>p. Some (DFix f prec opr, [(fix_key (n_txt opr), TEfix f p)], [], n))\<close>
| \<open>infer_decl uf B pre (DEff x as ops) n =
     (if distinct (map n_txt as) \<and> take (length functor_pre) pre \<noteq> functor_pre \<and>
         eff_lookup B (mangle pre (n_txt x)) = None \<and>
         nm_ok (n_txt x) \<and> list_all (\<lambda>(opn, _). nm_ok (n_txt opn)) ops
      then ops_stat B (mangle pre (n_txt x)) (eff_ps as n) (eff_ve as n) (n + length as) ops \<bind>
             (\<lambda>(es, n').
             Some (DEff x as ops,
                   es @ [(n_txt x, TEeff (mangle pre (n_txt x)) (map fst es)
                                     (length as))], [], n'))
      else None)\<close>
| \<open>infer_decl uf B pre (DMod x [] so m) n =
     (if fresh_mod B (n_txt x) \<and> nm_ok (n_txt x) then
     infer_mexp uf B (mangle pre (n_txt x)) m n \<bind> (\<lambda>(m', ent, F, n\<^sub>1).
       (case ent of
          TEstr E \<Rightarrow> sealo_stat B n\<^sub>1 so E \<bind> (\<lambda>(E', n').
                       (if set [n\<^sub>1 ..< n'] \<inter> stamps_env B = {}
                        then Some (DMod x [] so m', [(n_txt x, TEstr E')], F, n') else None))
        | TEfun ps res \<Rightarrow> (case so of None \<Rightarrow> Some (DMod x [] so m', [(n_txt x, ent)], F, n\<^sub>1)
                          | _ \<Rightarrow> None)
        | _ \<Rightarrow> None)) else None)\<close>
| \<open>infer_decl uf B pre (DMod x (q # qs) so m) n =
     params_stat B n (q # qs) \<bind> (\<lambda>(ps, B\<^sub>p, n\<^sub>1).
       (if set [n ..< n\<^sub>1] \<inter> stamps_env B = {} \<and> closed_env B\<^sub>p \<and> bfree_env_x B\<^sub>p \<and>
           list_all (\<lambda>(y, T, E). eff_free E) ps \<and> list_all (\<lambda>(y, _). nm_ok (n_txt y)) (q # qs)
        then infer_mexp uf B\<^sub>p functor_pre m n\<^sub>1 \<bind> (\<lambda>(m', ent, F, n\<^sub>2).
         (case ent of
            TEstr E \<Rightarrow>
              sealo_stat B\<^sub>p n\<^sub>2 so E \<bind> (\<lambda>(E', n').
                (let T' = filter (\<lambda>k. k \<notin> stamps_env B\<^sub>p) (sorted_list_of_set (stamps_env E'))
                 in (if set [n\<^sub>2 ..< n'] \<inter> stamps_env B\<^sub>p = {} \<and> sig_free E' \<and> res_names E' T'
                     then Some (DMod x (q # qs) so m', [(n_txt x, TEfun ps (T', E'))], F, n')
                     else None)))
          | _ \<Rightarrow> None))
        else None))\<close>
| \<open>infer_decl uf B pre (DImpl x [] so m) n =
     (if fresh_mod B (n_txt x) \<and> nm_ok (n_txt x) then
     infer_mexp uf B (mangle pre (n_txt x)) m n \<bind> (\<lambda>(m', ent, F, n\<^sub>1).
       (case ent of
          TEstr E \<Rightarrow> sealo_stat B n\<^sub>1 so E \<bind> (\<lambda>(E', n').
                       (if set [n\<^sub>1 ..< n'] \<inter> stamps_env B = {}
                        then Some (DImpl x [] so m', [(n_txt x, TEinst E')], F, n') else None))
        | TEfun ps res \<Rightarrow> (case so of None \<Rightarrow> Some (DImpl x [] so m', [(n_txt x, ent)], F, n\<^sub>1)
                          | _ \<Rightarrow> None)
        | _ \<Rightarrow> None)) else None)\<close>
| \<open>infer_decl uf B pre (DImpl x (q # qs) so m) n =
     params_stat B n (q # qs) \<bind> (\<lambda>(ps, B\<^sub>p, n\<^sub>1).
       (if set [n ..< n\<^sub>1] \<inter> stamps_env B = {} \<and> closed_env B\<^sub>p \<and> bfree_env_x B\<^sub>p \<and>
           list_all (\<lambda>(y, T, E). eff_free E) ps \<and> list_all (\<lambda>(y, _). nm_ok (n_txt y)) (q # qs)
        then infer_mexp uf B\<^sub>p functor_pre m n\<^sub>1 \<bind> (\<lambda>(m', ent, F, n\<^sub>2).
         (case ent of
            TEstr E \<Rightarrow>
              sealo_stat B\<^sub>p n\<^sub>2 so E \<bind> (\<lambda>(E', n').
                (let T' = filter (\<lambda>k. k \<notin> stamps_env B\<^sub>p) (sorted_list_of_set (stamps_env E'))
                 in (if set [n\<^sub>2 ..< n'] \<inter> stamps_env B\<^sub>p = {} \<and> sig_free E' \<and> res_names E' T'
                     then Some (DImpl x (q # qs) so m', [(n_txt x, TEfun ps (T', E'))], F, n')
                     else None)))
          | _ \<Rightarrow> None))
        else None))\<close>
| \<open>infer_decl uf B pre (DSig x sg) n =
     sig_stat B n sg \<bind> (\<lambda>(\<Sigma>, n').
       (if set [n ..< n'] \<inter> stamps_env B = {} \<and> fresh_sig B (n_txt x) \<and> sig_wf (snd \<Sigma>) \<and>
           take (length functor_pre) pre \<noteq> functor_pre
        then Some (DSig x sg, [(n_txt x, TEsig \<Sigma>)], [], n') else None))\<close>
| \<open>infer_decl uf B pre (DOpen p) n =
     (case tlookup B (path_nms p) of Some (TEstr E) \<Rightarrow> Some (DOpen p, E, [], n) | _ \<Rightarrow> None)\<close>
| \<open>infer_decl uf B pre (DInc m) n =
     infer_mexp uf B pre m n \<bind> (\<lambda>(m', ent, F, n').
       (case ent of TEstr E \<Rightarrow> Some (DInc m', E, F, n') | _ \<Rightarrow> None))\<close>
| \<open>infer_decl uf B pre DErr n = None\<close>

| \<open>infer_decls uf B pre [] n = Some ([], [], [], n)\<close>
| \<open>infer_decls uf B pre (d # ds) n =
     infer_decl uf B pre d n \<bind> (\<lambda>(d', E, F, n\<^sub>1).
       (if closed_env E \<and> bfree_env_x E \<and> gaps_ok E B
        then infer_decls uf (E @ B) pre ds n\<^sub>1 \<bind>
               (\<lambda>(ds', Es, Fs, n\<^sub>2). Some (d' # ds', Es @ E, Fs @ F, n\<^sub>2))
        else None))\<close>

| \<open>infer_mexp uf B pre (MPath p) n =
     tlookup B (path_nms p) \<bind> (\<lambda>ent. Some (MPath p, ent, [], n))\<close>
| \<open>infer_mexp uf B pre (MStruct ds) n =
     infer_decls uf B pre ds n \<bind> (\<lambda>(ds', E, F, n'). Some (MStruct ds', TEstr E, F, n'))\<close>
| \<open>infer_mexp uf B pre (MApp f a) n =
     infer_mexp uf B pre f n \<bind> (\<lambda>(f', fe, F\<^sub>f, n\<^sub>1).
       (case fe of
          TEfun ((px, \<Sigma>\<^sub>p) # ps) res \<Rightarrow>
            infer_mexp uf B (mangle functor_pre px) a n\<^sub>1 \<bind> (\<lambda>(a', ae, F\<^sub>a, n\<^sub>2).
              (case ae of
                 TEstr E\<^sub>a \<Rightarrow>
                   (let K' = [n\<^sub>2 ..< n\<^sub>2 + length (fst res)]
                    in (if set K' \<inter> (stamps_env (E\<^sub>a @ B) \<union>
                                     stamps_ent (TEfun ((px, \<Sigma>\<^sub>p) # ps) res)) = {} \<and>
                           stamps_ent (TEfun ((px, \<Sigma>\<^sub>p) # ps) res) \<inter> stamps_env E\<^sub>a \<subseteq> stamps_env B \<and>
                           fun_binders ((px, \<Sigma>\<^sub>p) # ps) res \<inter> stamps_env E\<^sub>a = {}
                        then fun_app ((px, \<Sigma>\<^sub>p) # ps) res E\<^sub>a K' \<bind> (\<lambda>ent.
                               Some (MApp f' a', ent, F\<^sub>a @ F\<^sub>f, n\<^sub>2 + length (fst res)))
                        else None))
               | _ \<Rightarrow> None))
        | _ \<Rightarrow> None))\<close>
| \<open>infer_mexp uf B pre (MSeal m sg) n =
     infer_mexp uf B pre m n \<bind> (\<lambda>(m', ent, F, n\<^sub>1).
       (case ent of
          TEstr E \<Rightarrow> seal_stat B n\<^sub>1 sg E \<bind> (\<lambda>(E', n').
                       (if set [n\<^sub>1 ..< n'] \<inter> stamps_env B = {}
                        then Some (MSeal m' sg, TEstr E', F, n')
                        else None))
        | _ \<Rightarrow> None))\<close>
| \<open>infer_mexp uf B pre MErr n = None\<close>
  by pat_completeness auto

termination
  by (relation \<open>measure (\<lambda>x. case x of
        Inl (uf, B, pre, d, n) \<Rightarrow> size d
      | Inr (Inl (uf, B, pre, ds, n)) \<Rightarrow> size_list size ds
      | Inr (Inr (uf, B, pre, m, n)) \<Rightarrow> size m)\<close>) auto

subsection \<open>The type checker\<close>

text \<open>A bound on every variable and stamp of a basis, where the counter
  starts.\<close>

fun bnd_sch :: \<open>scheme \<Rightarrow> nat\<close> where
  \<open>bnd_sch (Sch t) = Max ({kty_bnd t} \<union> Suc ` stamps t)\<close>
| \<open>bnd_sch (Mono t) = Max ({kty_bnd t} \<union> Suc ` stamps t)\<close>

fun bnd_tydef :: \<open>tydef \<Rightarrow> nat\<close> where
  \<open>bnd_tydef (TyAbs c k) = Suc (stamp c)\<close>
| \<open>bnd_tydef (TyFn ps t) = Max ({kty_bnd t, Suc (Max (insert 0 (set ps)))} \<union> Suc ` stamps t)\<close>

fun bnd_ent :: \<open>tentry \<Rightarrow> nat\<close>
and bnd_env :: \<open>tenv \<Rightarrow> nat\<close>
where
  \<open>bnd_ent (TEval \<sigma>) = bnd_sch \<sigma>\<close>
| \<open>bnd_ent (TEcon \<sigma> n) = bnd_sch \<sigma>\<close>
| \<open>bnd_ent (TEtyp d) = bnd_tydef d\<close>
| \<open>bnd_ent (TEstr ex) = bnd_env ex\<close>
| \<open>bnd_ent (TEfun ps (T, E)) =
     Max (insert (bnd_env E) (insert (Suc (Max (insert 0 (set T))))
            (set (map (\<lambda>(x, T, E). max (bnd_env E) (Suc (Max (insert 0 (set T))))) ps))))\<close>
| \<open>bnd_ent (TEsig (T, E)) = max (bnd_env E) (Suc (Max (insert 0 (set T))))\<close>
| \<open>bnd_ent (TEfix f p) = 0\<close>
| \<open>bnd_ent (TEinst ex) = bnd_env ex\<close>
| \<open>bnd_ent (TEop l ps t\<^sub>1 t\<^sub>2) = Max ({kty_bnd t\<^sub>1, kty_bnd t\<^sub>2} \<union> Suc ` (stamps t\<^sub>1 \<union> stamps t\<^sub>2))\<close>
| \<open>bnd_ent (TEffi s \<sigma>) = bnd_sch \<sigma>\<close>
| \<open>bnd_ent (TEeff l ls ar) = 0\<close>
| \<open>bnd_env [] = first_stamp\<close>
| \<open>bnd_env ((x, e) # ex) = max (bnd_ent e) (bnd_env ex)\<close>

text \<open>The checker also returns the program's foreign declarations, each symbol
  with the scheme it was declared at, wherever in the program it was declared.\<close>

definition typecheck_ffi :: \<open>tenv \<Rightarrow> mdecl list \<Rightarrow> (tenv \<times> fenv \<times> mdecl list) option\<close> where
  \<open>typecheck_ffi B ds =
     (if closed_env B \<and> bfree_env_x B
      then infer_decls 1000 B [] ds (bnd_env B) \<bind> (\<lambda>(ds', E, F, _).
             (if has_main ds' then Some (E @ B, F, ds') else None))
      else None)\<close>

text \<open>The checker without the foreign declarations.\<close>

definition typecheck :: \<open>tenv \<Rightarrow> mdecl list \<Rightarrow> (tenv \<times> mdecl list) option\<close> where
  \<open>typecheck B ds = map_option (\<lambda>(B', F, ds'). (B', ds')) (typecheck_ffi B ds)\<close>

end
