theory Grades
  imports Unify Desugar
begin

section \<open>Protocol grades: the operations an action performs on a name\<close>

text \<open>A named handler of an effect with a protocol runs an action \<open>fn[x] e\<close>
  whose operations on \<open>x\<close> must follow the protocol (names as in
  \<^cite>\<open>\<open>Sect. 2.3\<close> in xie2021names\<close>, formulas as in \<^theory>\<open>CaraML_Syntax.Protocol\<close>).
  The check is static: \<^text>\<open>synth\<close> reads a regular expression over the
  operation names off the explicit surface of \<open>e\<close>, the language of every
  trace the action can perform on \<open>x\<close>, and \<^const>\<open>check_rl\<close> decides that
  every word of it satisfies the protocol. The analysis over-approximates:
  sequencing concatenates, branches alternate, a name flowing where its uses
  cannot be followed (into a data structure, a function, a nested action, a
  handler clause) rejects, and a \<open>let\<close>-bound function taking a name is
  analysed once with the name as parameter and its trace substituted at
  every call. An inner handler inside the action must have linear clauses.
  The main results are \<open>prot_le_sound\<close>, \<open>prot_ok_sound\<close> and \<open>act_ok_sound\<close>.\<close>

subsection \<open>Effects of a basis\<close>

text \<open>The effect entries of a basis, nested through structures; the effect
  owning a label prefix, and the one owning an operation label. An effect
  is \<^emph>\<open>plain\<close> when it has neither type parameters nor a protocol: only
  those may be handled by an unnamed handler.\<close>

fun effs :: \<open>tenv \<Rightarrow> (name \<times> name list \<times> nat \<times> name ltlf option) list\<close>
and effs_ent :: \<open>tentry \<Rightarrow> (name \<times> name list \<times> nat \<times> name ltlf option) list\<close> where
  \<open>effs [] = []\<close>
| \<open>effs ((x, e) # ex) = effs_ent e @ effs ex\<close>
| \<open>effs_ent (TEeff l ls ar pr) = [(l, ls, ar, pr)]\<close>
| \<open>effs_ent (TEstr ex) = effs ex\<close>
| \<open>effs_ent (TEinst ex) = effs ex\<close>
| \<open>effs_ent _ = []\<close>

definition eff_lookup :: \<open>tenv \<Rightarrow> name \<Rightarrow> (name list \<times> nat \<times> name ltlf option) option\<close> where
  \<open>eff_lookup B l = map_of (effs B) l\<close>

definition eff_of_op :: \<open>tenv \<Rightarrow> name \<Rightarrow> (name \<times> name list \<times> nat \<times> name ltlf option) option\<close> where
  \<open>eff_of_op B lbl = find (\<lambda>(l, ls, _, _). lbl \<in> set (map (mangle l) ls)) (effs B)\<close>

definition plain_eff :: \<open>tenv \<Rightarrow> name \<Rightarrow> bool\<close> where
  \<open>plain_eff B lbl \<longleftrightarrow>
     (case eff_of_op B lbl of Some (l, ls, ar, pr) \<Rightarrow> ar = 0 \<and> pr = None | None \<Rightarrow> False)\<close>

subsection \<open>Comparing protocols\<close>

text \<open>A structure matches a specification's effect when its protocol admits
  every trace the specification's admits: a client typed against the
  specification follows the specification's protocol, and the structure's
  handler enforces its own.\<close>

definition prot_le :: \<open>name list \<Rightarrow> name ltlf option \<Rightarrow> name ltlf option \<Rightarrow> bool\<close> where
  \<open>prot_le ls pr\<^sub>s pr =
     (case (pr, pr\<^sub>s) of
        (None, None) \<Rightarrow> True
      | (None, Some _) \<Rightarrow> False
      | (Some _, None) \<Rightarrow> True
      | (Some \<phi>, Some \<psi>) \<Rightarrow> \<phi> = \<psi> \<or> incl_ll ls \<phi> \<psi>)\<close>

lemma prot_le_sound:
  \<open>prot_le ls (Some \<psi>) (Some \<phi>) \<Longrightarrow> set w \<subseteq> set ls \<Longrightarrow> sat w \<phi> \<Longrightarrow> sat w \<psi>\<close>
  by (auto simp: prot_le_def intro: incl_ll_sound)

lemma prot_le_refl[simp]: \<open>prot_le ls pr pr\<close>
  by (cases pr) (auto simp: prot_le_def)

subsection \<open>Linear clauses\<close>

text \<open>A clause is linear when its resumption is applied at most once: the
  resumption occurs once, as the head of an application, and that
  application is not replayed. An occurrence in any other position (passed
  as an argument, aliased by a binding, returned or matched on) counts
  twice, since the resumption may then be applied any number of times. So
  does an occurrence under a lambda, in a handler clause, or in the body of a
  handler one of whose clauses is not linear, since such code runs more than
  once.\<close>

fun lin :: \<open>name \<Rightarrow> expr \<Rightarrow> nat\<close>
and lin_spine :: \<open>name \<Rightarrow> matom list \<Rightarrow> nat\<close>
and lin_atom :: \<open>name \<Rightarrow> matom \<Rightarrow> nat\<close>
and lin_cls :: \<open>name \<Rightarrow> hclause \<Rightarrow> nat\<close>
and linear_cls :: \<open>hclause \<Rightarrow> bool\<close>
and linear_clss :: \<open>hclause list \<Rightarrow> bool\<close> where
  \<open>lin k (ESpine as) = lin_spine k as\<close>
| \<open>lin k (EOp as opr e) = lin_spine k as + (if n_txt opr = k then 1 else 0) + lin k e\<close>
| \<open>lin k (EAnn e _) = lin k e\<close>
| \<open>lin k (EFn _ b) = 2 * lin k b\<close>
| \<open>lin k (EFnMod _ b) = 2 * lin k b\<close>
| \<open>lin k (ELet _ e b) = lin k e + lin k b\<close>
| \<open>lin k (EBind _ e b) = lin k e + lin k b\<close>
| \<open>lin k (ESeq e\<^sub>1 e\<^sub>2) = lin k e\<^sub>1 + lin k e\<^sub>2\<close>
| \<open>lin k (EIf c t None) = lin k c + lin k t\<close>
| \<open>lin k (EIf c t (Some e)) = lin k c + max (lin k t) (lin k e)\<close>
| \<open>lin k (EMatch e arms) = lin k e + fold max (map (\<lambda>(_, b). lin k b) arms) 0\<close>
| \<open>lin k (EHandle e cls) =
     (if linear_clss cls then lin k e else 2 * lin k e) + fold max (map (lin_cls k) cls) 0\<close>
| \<open>lin k (EHandler cls) = 2 * fold max (map (lin_cls k) cls) 0\<close>
| \<open>lin k (EMask _ e) = lin k e\<close>
| \<open>lin k (EFnName _ b) = 2 * lin k b\<close>
| \<open>lin k (EHandlerN cls) = 2 * fold max (map (lin_cls k) cls) 0\<close>
| \<open>lin k (EHandleN _ cls e) =
     (if linear_clss cls then lin k e else 2 * lin k e) + fold max (map (lin_cls k) cls) 0\<close>
| \<open>lin k EErr = 0\<close>
| \<open>lin_spine k (APath (MkPath (y # ys)) # as) =
     (if n_txt y = k then (if as = [] then 2 else 1) else 0) + sum_list (map (lin_atom k) as)\<close>
| \<open>lin_spine k as = sum_list (map (lin_atom k) as)\<close>
| \<open>lin_atom k (APath (MkPath xs)) = (case xs of x # _ \<Rightarrow> (if n_txt x = k then 2 else 0) | [] \<Rightarrow> 0)\<close>
| \<open>lin_atom k (AParen es) = sum_list (map (lin k) es)\<close>
| \<open>lin_atom k (AList es) = sum_list (map (lin k) es)\<close>
| \<open>lin_atom k _ = 0\<close>
| \<open>lin_cls k (HOp _ _ _ b) = 2 * lin k b\<close>
| \<open>lin_cls k (HRet _ b) = lin k b\<close>
| \<open>lin_cls k (HFin e) = lin k e\<close>
| \<open>lin_cls k HErr = 0\<close>
| \<open>linear_cls (HOp _ _ (Some k) b) \<longleftrightarrow> lin (n_txt k) b \<le> 1\<close>
| \<open>linear_cls _ = True\<close>
| \<open>linear_clss [] = True\<close>
| \<open>linear_clss (c # cls) \<longleftrightarrow> linear_cls c \<and> linear_clss cls\<close>  (* ~20s *)

lemma linear_clss_iff: \<open>linear_clss cls \<longleftrightarrow> list_all linear_cls cls\<close>
  by (induction cls) simp_all

subsection \<open>Synthesising the trace of a name\<close>

text \<open>Whether a pattern may bind a name: a single-segment path is a binder
  unless it is a constructor, which the syntax does not know, so it counts.\<close>

fun pshadows :: \<open>name \<Rightarrow> mpat \<Rightarrow> bool\<close>
and pshadows_atom :: \<open>name \<Rightarrow> mpatom \<Rightarrow> bool\<close> where
  \<open>pshadows x (PatApp as) \<longleftrightarrow> (\<exists>a \<in> set as. pshadows_atom x a)\<close>
| \<open>pshadows x (PatAs as y) \<longleftrightarrow> n_txt y = x \<or> (\<exists>a \<in> set as. pshadows_atom x a)\<close>
| \<open>pshadows x (PatAnn p _) = pshadows x p\<close>
| \<open>pshadows_atom x (PQid (MkPath ys)) \<longleftrightarrow> map n_txt ys = [x]\<close>
| \<open>pshadows_atom x (PParen ps) \<longleftrightarrow> (\<exists>p \<in> set ps. pshadows x p)\<close>
| \<open>pshadows_atom x (PList ps) \<longleftrightarrow> (\<exists>p \<in> set ps. pshadows x p)\<close>
| \<open>pshadows_atom x _ = False\<close>

text \<open>Whether a name occurs at all in an expression, by the use count of
  \<^const>\<open>kuses\<close>.\<close>

abbreviation occurs :: \<open>name \<Rightarrow> expr \<Rightarrow> bool\<close> where
  \<open>occurs x e \<equiv> kuses x e \<noteq> 0\<close>

type_synonym fenv = \<open>(name \<times> name rexp) list\<close>

text \<open>The explicit form of the sugar \<open>handle[x] cls e\<close>: a handler literal applied
  to an action literal (rule \<open>W_handlen\<close>). The analysis treats it as the
  sugar, since the handler is known at the application and the inner action
  cannot escape it, so the outer name may occur in \<open>e\<close>.\<close>

fun sugar_spine :: \<open>matom list \<Rightarrow> (hclause list \<times> nm \<times> expr) option\<close> where
  \<open>sugar_spine [AParen [EHandlerN cls], AParen [EFnName y e]] = Some (cls, y, e)\<close>
| \<open>sugar_spine _ = None\<close>  (* ~10s *)

lemma sugar_spine_size: \<open>sugar_spine as = Some (cls, y, e) \<Longrightarrow> size e < size_list size as\<close>
  by (cases as rule: sugar_spine.cases) auto

text \<open>\<open>synth fe x e\<close>: the trace of \<open>x\<close> in \<open>e\<close>, given the traces \<open>fe\<close> of the
  \<open>let\<close>-bound functions in scope that take a name as their first argument.
  \<open>x.op a\<close> is \<open>Atom op\<close> after the trace of \<open>a\<close>, a spine \<open>f x as\<close> with \<open>f \<in> fe\<close>
  is \<open>f\<close>'s trace, and any other occurrence of \<open>x\<close> as a value rejects.\<close>

function (sequential) synth :: \<open>fenv \<Rightarrow> name \<Rightarrow> expr \<Rightarrow> name rexp option\<close>
and synth_spine :: \<open>fenv \<Rightarrow> name \<Rightarrow> matom list \<Rightarrow> name rexp option\<close>
and synth_atom :: \<open>fenv \<Rightarrow> name \<Rightarrow> matom \<Rightarrow> name rexp option\<close>
and synth_atoms :: \<open>fenv \<Rightarrow> name \<Rightarrow> matom list \<Rightarrow> name rexp option\<close>
and synth_exps :: \<open>fenv \<Rightarrow> name \<Rightarrow> expr list \<Rightarrow> name rexp option\<close>
and synth_arms :: \<open>fenv \<Rightarrow> name \<Rightarrow> (mpat \<times> expr) list \<Rightarrow> name rexp option\<close>
and synth_bind :: \<open>fenv \<Rightarrow> name \<Rightarrow> mpat \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> name rexp option\<close> where
  \<open>synth fe x (ESpine as) = synth_spine fe x as\<close>
| \<open>synth fe x (EOp as opr e) =
     (if n_txt opr = x then None
      else synth_atoms fe x as \<bind> (\<lambda>r\<^sub>1. synth fe x e \<bind> (\<lambda>r\<^sub>2. Some (r\<^sub>1 ~~ r\<^sub>2))))\<close>
| \<open>synth fe x (EAnn e _) = synth fe x e\<close>
| \<open>synth fe x (EFn ps b) = (if occurs x (EFn ps b) then None else Some One)\<close>
| \<open>synth fe x (EFnMod b e) = (if occurs x (EFnMod b e) then None else Some One)\<close>
| \<open>synth fe x (EFnName y e) = (if occurs x (EFnName y e) then None else Some One)\<close>
| \<open>synth fe x (ELet p e b) = synth_bind fe x p e b\<close>
| \<open>synth fe x (EBind p e b) = synth_bind fe x p e b\<close>
| \<open>synth fe x (ESeq e\<^sub>1 e\<^sub>2) = synth fe x e\<^sub>1 \<bind> (\<lambda>r\<^sub>1. synth fe x e\<^sub>2 \<bind> (\<lambda>r\<^sub>2. Some (r\<^sub>1 ~~ r\<^sub>2)))\<close>
| \<open>synth fe x (EIf c t None) = synth fe x c \<bind> (\<lambda>r\<^sub>c. synth fe x t \<bind> (\<lambda>r\<^sub>t. Some (r\<^sub>c ~~ Plus r\<^sub>t One)))\<close>
| \<open>synth fe x (EIf c t (Some e)) =
     synth fe x c \<bind> (\<lambda>r\<^sub>c. synth fe x t \<bind> (\<lambda>r\<^sub>t. synth fe x e \<bind> (\<lambda>r\<^sub>e. Some (r\<^sub>c ~~ Plus r\<^sub>t r\<^sub>e))))\<close>
| \<open>synth fe x (EMatch e arms) = synth fe x e \<bind> (\<lambda>r\<^sub>e. synth_arms fe x arms \<bind> (\<lambda>r\<^sub>a. Some (r\<^sub>e ~~ r\<^sub>a)))\<close>
| \<open>synth fe x (EHandle e cls) =
     (if list_all linear_cls cls \<and> (\<forall>c \<in> set cls. kuses_cls x c = 0) then synth fe x e else None)\<close>
| \<open>synth fe x (EHandler cls) = (if occurs x (EHandler cls) then None else Some One)\<close>
| \<open>synth fe x (EMask l e) = synth fe x e\<close>
| \<open>synth fe x (EHandlerN cls) = (if occurs x (EHandlerN cls) then None else Some One)\<close>
| \<open>synth fe x (EHandleN y cls e) =
     (if list_all linear_cls cls \<and> (\<forall>c \<in> set cls. kuses_cls x c = 0)
      then (if n_txt y = x then Some One else synth (filter (\<lambda>(f, _). f \<noteq> n_txt y) fe) x e)
      else None)\<close>
| \<open>synth fe x EErr = None\<close>

| \<open>synth_spine fe x [] = None\<close>
| \<open>synth_spine fe x (APath (MkPath ys) # as) =
     (case map n_txt ys of
        [y, op] \<Rightarrow>
          (if y = x then synth_atoms fe x as \<bind> (\<lambda>r. Some (r ~~ Atom op))
           else synth_atoms fe x as)
      | [f] \<Rightarrow>
          (if f = x then None
           else (case map_of fe f of
                   Some r\<^sub>f \<Rightarrow>
                     (case as of
                        APath (MkPath [z]) # rest \<Rightarrow>
                          (if n_txt z = x then synth_atoms fe x rest \<bind> (\<lambda>r. Some (r\<^sub>f ~~ r))
                           else synth_atoms fe x as)
                      | _ \<Rightarrow> synth_atoms fe x as)
                 | None \<Rightarrow> synth_atoms fe x as))
      | _ \<Rightarrow> synth_atoms fe x as)\<close>
| \<open>synth_spine fe x (a # as) =
     (case sugar_spine (a # as) of
        Some (cls, y, e) \<Rightarrow>
          (if list_all linear_cls cls \<and> (\<forall>c \<in> set cls. kuses_cls x c = 0)
           then (if n_txt y = x then Some One
                 else synth (filter (\<lambda>(f, _). f \<noteq> n_txt y) fe) x e)
           else None)
      | None \<Rightarrow> synth_atom fe x a \<bind> (\<lambda>r\<^sub>1. synth_atoms fe x as \<bind> (\<lambda>r\<^sub>2. Some (r\<^sub>1 ~~ r\<^sub>2))))\<close>

| \<open>synth_atom fe x (APath (MkPath ys)) =
     (if map n_txt ys \<noteq> [] \<and> hd (map n_txt ys) = x then None else Some One)\<close>
| \<open>synth_atom fe x (AParen es) = synth_exps fe x es\<close>
| \<open>synth_atom fe x (AList es) = synth_exps fe x es\<close>
| \<open>synth_atom fe x _ = Some One\<close>

| \<open>synth_atoms fe x [] = Some One\<close>
| \<open>synth_atoms fe x (a # as) =
     synth_atom fe x a \<bind> (\<lambda>r\<^sub>1. synth_atoms fe x as \<bind> (\<lambda>r\<^sub>2. Some (r\<^sub>1 ~~ r\<^sub>2)))\<close>

| \<open>synth_exps fe x [] = Some One\<close>
| \<open>synth_exps fe x (e # es) =
     synth fe x e \<bind> (\<lambda>r\<^sub>1. synth_exps fe x es \<bind> (\<lambda>r\<^sub>2. Some (r\<^sub>1 ~~ r\<^sub>2)))\<close>

| \<open>synth_arms fe x [] = Some Zero\<close>
| \<open>synth_arms fe x ((p, b) # arms) =
     (if pshadows x p then Some One else synth (filter (\<lambda>(f, _). \<not> pshadows f p) fe) x b) \<bind> (\<lambda>r\<^sub>1.
       synth_arms fe x arms \<bind> (\<lambda>r\<^sub>2. Some (Plus r\<^sub>1 r\<^sub>2)))\<close>

| \<open>synth_bind fe x p e b =
     synth fe x e \<bind> (\<lambda>r\<^sub>e.
       (if pshadows x p then Some (r\<^sub>e ~~ One)
        else (let fe\<^sub>0 = filter (\<lambda>(f, _). \<not> pshadows f p) fe;
                  fe' = (case (p, e) of
                          (PatApp [PQid (MkPath [f])], EFn [PatApp [PQid (MkPath [y])]] body) \<Rightarrow>
                            (case synth fe (n_txt y) body of
                               Some r\<^sub>f \<Rightarrow> (n_txt f, r\<^sub>f) # fe\<^sub>0
                             | None \<Rightarrow> fe\<^sub>0)
                        | _ \<Rightarrow> fe\<^sub>0)
              in synth fe' x b \<bind> (\<lambda>r\<^sub>b. Some (r\<^sub>e ~~ r\<^sub>b)))))\<close>  (* ~21s *)
  by pat_completeness auto  (* ~9s *)

termination
  by (relation \<open>measure (\<lambda>s. case s of
        Inl (Inl (fe, x, e)) \<Rightarrow> 2 * size e
      | Inl (Inr (Inl (fe, x, as))) \<Rightarrow> 2 * size_list size as
      | Inl (Inr (Inr (fe, x, a))) \<Rightarrow> 2 * size a
      | Inr (Inl (Inl (fe, x, as))) \<Rightarrow> 2 * size_list size as
      | Inr (Inl (Inr (fe, x, es))) \<Rightarrow> 2 * size_list size es
      | Inr (Inr (Inl (fe, x, arms))) \<Rightarrow> 2 * size_list (size_prod (\<lambda>_. 0) size) arms
      | Inr (Inr (Inr (fe, x, p, e, b))) \<Rightarrow> 2 * size e + 2 * size b + 1)\<close>)
     (auto dest!: sugar_spine_size)

text \<open>An action conforms to a protocol when its synthesised trace language
  is included in the protocol's; the application rule demands it of a
  literal action \<open>fn[x] e\<close> whenever the handler's effect has a protocol.\<close>

definition prot_ok :: \<open>name \<Rightarrow> expr \<Rightarrow> name ltlf \<Rightarrow> bool\<close> where
  \<open>prot_ok x e \<phi> \<longleftrightarrow> (case synth [] x e of Some r \<Rightarrow> check_rl r \<phi> | None \<Rightarrow> False)\<close>

text \<open>At an application, an argument for a handler of an effect with a protocol
  must be a literal action that conforms.\<close>

definition prot_arg :: \<open>tenv \<Rightarrow> name \<Rightarrow> matom \<Rightarrow> bool\<close> where
  \<open>prot_arg B l a \<longleftrightarrow>
     (case eff_lookup B l of
        Some (ls, ar, Some \<phi>) \<Rightarrow> (case a of AParen [EFnName x e] \<Rightarrow> prot_ok (n_txt x) e \<phi> | _ \<Rightarrow> False)
      | _ \<Rightarrow> True)\<close>

lemma prot_ok_sound: \<open>prot_ok x e \<phi> \<Longrightarrow> synth [] x e = Some r \<Longrightarrow> w \<in> lang r \<Longrightarrow> sat w \<phi>\<close>
  by (auto simp: prot_ok_def intro: check_rl_sound)

text \<open>The check at the action itself, \<open>fn[x] e\<close> (rule \<open>W_fnname\<close>): the
  action's trace is checked against the protocol of the name's effect where
  the action is written, not where it is applied, and the trace must exist
  whether or not the effect has a protocol. So names are second-class: they
  occur only in \<open>x.op a\<close> and as the first argument of a \<open>let\<close>-bound
  name-taking function.\<close>

definition act_ok :: \<open>tenv \<Rightarrow> kty \<Rightarrow> name \<Rightarrow> expr \<Rightarrow> bool\<close> where
  \<open>act_ok B lt x e \<longleftrightarrow>
     (case eff_of_ty lt of
        None \<Rightarrow> False
      | Some l \<Rightarrow>
          (case (eff_lookup B l, synth [] x e) of
             (Some (ls, ar, pr), Some r) \<Rightarrow> (case pr of Some \<phi> \<Rightarrow> check_rl r \<phi> | None \<Rightarrow> True)
           | _ \<Rightarrow> False))\<close>

lemma eff_of_ty_Some:
  assumes E: \<open>eff_of_ty t = Some l\<close> shows \<open>\<exists>ts. t = eff_ty l ts\<close>
proof (cases t)
  case (TC c ts)
  obtain st nm cs where c: \<open>c = (st, nm, cs)\<close> by (cases c)
  have f: \<open>st = 0\<close> \<open>cs = []\<close> \<open>l = drop 5 nm\<close> and pre: \<open>take 5 nm = str ''%eff.''\<close>
    using E unfolding TC c by (auto split: if_split_asm)
  have \<open>nm = str ''%eff.'' @ drop 5 nm\<close> using append_take_drop_id[of 5 nm] pre by simp
  with f show ?thesis unfolding TC c eff_ty_def by (intro exI[of _ ts]) simp
qed (use E in simp_all)

lemma act_ok_eff: \<open>act_ok B lt x e \<Longrightarrow> \<exists>ts. lt = eff_ty (the (eff_of_ty lt)) ts\<close>
  by (auto simp: act_ok_def dest: eff_of_ty_Some split: option.split_asm)

text \<open>The check does not depend on the effect's type arguments. The
  argument-free form is a constant of its own, so that the rewrite below does
  not turn \<open>eff_ty l []\<close> into itself:\<close>

definition act_ok0 :: \<open>tenv \<Rightarrow> name \<Rightarrow> name \<Rightarrow> expr \<Rightarrow> bool\<close> where
  \<open>act_ok0 B l x e \<longleftrightarrow>
     (case (eff_lookup B l, synth [] x e) of
        (Some (ls, ar, pr), Some r) \<Rightarrow> (case pr of Some \<phi> \<Rightarrow> check_rl r \<phi> | None \<Rightarrow> True)
      | _ \<Rightarrow> False)\<close>

lemma act_ok_eff_ty[simp]: \<open>act_ok B (eff_ty l ts) x e \<longleftrightarrow> act_ok0 B l x e\<close>
  by (simp add: act_ok_def act_ok0_def)

lemma act_ok_sound:
  \<open>act_ok B lt x e \<Longrightarrow> eff_lookup B (the (eff_of_ty lt)) = Some (ls, ar, Some \<phi>) \<Longrightarrow>
   synth [] x e = Some r \<Longrightarrow> w \<in> lang r \<Longrightarrow> sat w \<phi>\<close>
  by (auto simp: act_ok_def intro: check_rl_sound split: option.split_asm prod.split_asm)

end
