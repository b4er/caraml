theory Unify
  imports Basis "HOL-Library.List_Lexorder"
begin

section \<open>Row and type unification\<close>

text \<open>Unification of effect rows up to \<open>\<approx>\<close> and of types up to \<open>\<simeq>\<close>. A row is its
  label multiset plus its optional tail variable (@{thm [source] row_eq_iff}), so two
  rows unify by cancelling common labels and solving the tails
  \<^cite>\<open>\<open>Sect. 3.3\<close> in leijen2017\<close>:

    \<^item> both closed: unifiable iff the label multisets agree;
    \<^item> open against closed: the open side's labels must be contained in the
      closed side's; the tail variable absorbs the difference;
    \<^item> both open with the \<^emph>\<open>same\<close> tail: the labels must agree;
    \<^item> both open with distinct tails: always unifiable, each tail absorbing
      the other side's surplus, sharing a fresh tail variable.

  The main results: the row unifier \<open>runify\<close> is sound and complete
  (\<open>runify_sound\<close>, \<open>runify_complete\<close>), so unifiability of rows is decidable;
  canonical forms decide \<open>\<approx>\<close> and \<open>\<simeq>\<close> (\<open>canon_row_iff\<close>, \<open>canon_ty_eq_iff\<close>); the
  type unifier \<open>kunify\<close> is sound (\<open>kunify_sound\<close>); instantiation yields an
  instance (\<open>inst_scheme_sinst\<close>).\<close>

subsection \<open>Rows from label lists\<close>

text \<open>A row's labels as a list, and multiset difference on lists.\<close>

fun row_list :: \<open>krow \<Rightarrow> name list\<close> where
  \<open>row_list RNil = []\<close>
| \<open>row_list (RV v) = []\<close>
| \<open>row_list (RB v) = []\<close>
| \<open>row_list (RCons l r) = l # row_list r\<close>

lemma mset_row_list: \<open>mset (row_list r) = row_labels r\<close>
  by (induction r) auto

definition ldiff :: \<open>'a list \<Rightarrow> 'a list \<Rightarrow> 'a list\<close> where
  \<open>ldiff xs ys = foldl (\<lambda>acc y. remove1 y acc) xs ys\<close>

lemma ldiff_Nil[simp]: \<open>ldiff xs [] = xs\<close>
  by (simp add: ldiff_def)

lemma ldiff_Cons[simp]: \<open>ldiff xs (y # ys) = ldiff (remove1 y xs) ys\<close>
  by (simp add: ldiff_def)

lemma mset_ldiff: \<open>mset (ldiff xs ys) = mset xs - mset ys\<close>
  by (induction ys arbitrary: xs) (auto simp: diff_diff_add)

text \<open>A row from a label list and a tail; the tail is a row's end, closed
  or a variable.\<close>

definition mk_row :: \<open>name list \<Rightarrow> krow \<Rightarrow> krow\<close> where
  \<open>mk_row xs t = foldr RCons xs t\<close>

fun is_tail :: \<open>krow \<Rightarrow> bool\<close> where
  \<open>is_tail (RCons l r) = False\<close>
| \<open>is_tail r = True\<close>

lemma row_tail_is_tail: \<open>is_tail (row_tail r)\<close>
  by (induction r) auto

lemma is_tail_labels: \<open>is_tail t \<Longrightarrow> row_labels t = {#}\<close>
  by (cases t) auto

lemma is_tail_tail: \<open>is_tail t \<Longrightarrow> row_tail t = t\<close>
  by (cases t) auto

lemma mk_row_labels[simp]: \<open>is_tail t \<Longrightarrow> row_labels (mk_row xs t) = mset xs\<close>
proof -
  have \<open>row_labels (foldr RCons xs r) = mset xs + row_labels r\<close> for r
    by (induction xs) auto
  then show \<open>is_tail t \<Longrightarrow> ?thesis\<close> by (simp add: mk_row_def is_tail_labels)
qed

lemma mk_row_tail[simp]: \<open>is_tail t \<Longrightarrow> row_tail (mk_row xs t) = t\<close>
proof -
  have \<open>row_tail (foldr RCons xs r) = row_tail r\<close> for r
    by (induction xs) auto
  then show \<open>is_tail t \<Longrightarrow> ?thesis\<close> by (simp add: mk_row_def is_tail_tail)
qed

subsection \<open>Substitution acts canonically\<close>

text \<open>A substitution adds the labels of the tail's image and replaces the tail.\<close>

lemma rsubst_labels:
  \<open>row_labels (rsubst g r) =
     row_labels r + (case row_tail r of RV v \<Rightarrow> row_labels (g v) | _ \<Rightarrow> {#})\<close>
  by (induction r) auto

lemma rsubst_tail:
  \<open>row_tail (rsubst g r) = (case row_tail r of RV v \<Rightarrow> row_tail (g v) | t \<Rightarrow> t)\<close>
  by (induction r) auto

lemma mset_diff_exchange: \<open>(M :: 'a multiset) + (N - M) = N + (M - N)\<close>
proof (rule multiset_eqI)
  fix a
  show \<open>count (M + (N - M)) a = count (N + (M - N)) a\<close>
    unfolding count_union count_diff by linarith
qed

subsection \<open>The row unifier\<close>

text \<open>The four cases of the decomposition above; two open rows share the fresh
  tail variable \<open>n\<close>.\<close>

definition runify :: \<open>nat \<Rightarrow> krow \<Rightarrow> krow \<Rightarrow> (rsub \<times> nat) option\<close> where
  \<open>runify n r\<^sub>1 r\<^sub>2 =
     (case (row_tail r\<^sub>1, row_tail r\<^sub>2) of
        (RV v\<^sub>1, RV v\<^sub>2) \<Rightarrow>
          (if v\<^sub>1 = v\<^sub>2
           then (if row_labels r\<^sub>1 = row_labels r\<^sub>2 then Some (Map.empty, n) else None)
           else Some
             ([v\<^sub>1 \<mapsto> mk_row (ldiff (row_list r\<^sub>2) (row_list r\<^sub>1)) (RV n),
               v\<^sub>2 \<mapsto> mk_row (ldiff (row_list r\<^sub>1) (row_list r\<^sub>2)) (RV n)],
              Suc n))
      | (RV v, t) \<Rightarrow>
          (if row_labels r\<^sub>1 \<subseteq># row_labels r\<^sub>2
           then Some ([v \<mapsto> mk_row (ldiff (row_list r\<^sub>2) (row_list r\<^sub>1)) t], n)
           else None)
      | (t, RV v) \<Rightarrow>
          (if row_labels r\<^sub>2 \<subseteq># row_labels r\<^sub>1
           then Some ([v \<mapsto> mk_row (ldiff (row_list r\<^sub>1) (row_list r\<^sub>2)) t], n)
           else None)
      | (t\<^sub>1, t\<^sub>2) \<Rightarrow>
          (if t\<^sub>1 = t\<^sub>2 \<and> row_labels r\<^sub>1 = row_labels r\<^sub>2 then Some (Map.empty, n) else None))\<close>

theorem runify_sound:
  assumes \<open>runify n r\<^sub>1 r\<^sub>2 = Some (\<sigma>, n')\<close>
  shows \<open>rsubst (mk_rsub \<sigma>) r\<^sub>1 \<approx> rsubst (mk_rsub \<sigma>) r\<^sub>2\<close>
  using assms row_tail_is_tail[of r\<^sub>1] row_tail_is_tail[of r\<^sub>2]
  unfolding runify_def row_eq_iff
  by (auto simp: rsubst_labels rsubst_tail mk_rsub_def mset_ldiff mset_row_list
                 subset_mset.diff_add mset_diff_exchange[symmetric] union_commute
                 Diff_eq_empty_iff_mset
           split: krow.splits if_split_asm)

theorem runify_complete:
  assumes \<open>rsubst g r\<^sub>1 \<approx> rsubst g r\<^sub>2\<close>
  shows \<open>runify n r\<^sub>1 r\<^sub>2 \<noteq> None\<close>
  using assms
  unfolding row_eq_iff runify_def
  by (auto simp: rsubst_labels rsubst_tail split: krow.splits
           dest: sym intro: mset_subset_eq_add_left)

corollary runify_unifiable:
  \<open>runify n r\<^sub>1 r\<^sub>2 \<noteq> None \<longleftrightarrow> (\<exists>g. rsubst g r\<^sub>1 \<approx> rsubst g r\<^sub>2)\<close>
proof
  assume \<open>runify n r\<^sub>1 r\<^sub>2 \<noteq> None\<close>
  then obtain \<sigma> n' where \<open>runify n r\<^sub>1 r\<^sub>2 = Some (\<sigma>, n')\<close> by auto
  from runify_sound[OF this] show \<open>\<exists>g. rsubst g r\<^sub>1 \<approx> rsubst g r\<^sub>2\<close> by blast
next
  assume \<open>\<exists>g. rsubst g r\<^sub>1 \<approx> rsubst g r\<^sub>2\<close>
  then show \<open>runify n r\<^sub>1 r\<^sub>2 \<noteq> None\<close> by (blast dest: runify_complete)
qed

subsection \<open>Canonical rows and types\<close>

text \<open>The canonical-forms discipline: the theory of rows is modulo \<open>\<approx>\<close>, but
  the algorithm keeps every row in canonical form, labels sorted and tail
  unchanged, so that on the algorithm's types \<open>\<approx>\<close> coincides with syntactic
  equality; the declarative rules compare with \<open>\<approx>\<close> and \<open>\<simeq>\<close>.\<close>

definition canon_row :: \<open>krow \<Rightarrow> krow\<close> where
  \<open>canon_row r = mk_row (sort (row_list r)) (row_tail r)\<close>

lemma canon_row_labels[simp]: \<open>row_labels (canon_row r) = row_labels r\<close>
  by (simp add: canon_row_def mset_row_list row_tail_is_tail)

lemma canon_row_tail[simp]: \<open>row_tail (canon_row r) = row_tail r\<close>
  by (simp add: canon_row_def row_tail_is_tail)

lemma canon_row_req: \<open>canon_row r \<approx> r\<close>
  by (simp add: row_eq_iff)

lemma sort_mset_cong: \<open>mset xs = mset ys \<Longrightarrow> sort xs = sort ys\<close>
  by (rule properties_for_sort) simp_all

theorem canon_row_iff: \<open>r \<approx> r' \<longleftrightarrow> canon_row r = canon_row r'\<close>
proof
  assume \<open>r \<approx> r'\<close>
  then have \<open>mset (row_list r) = mset (row_list r')\<close> \<open>row_tail r = row_tail r'\<close>
    by (auto simp: row_eq_iff mset_row_list)
  then show \<open>canon_row r = canon_row r'\<close>
    by (fastforce simp: canon_row_def dest: sort_mset_cong)
next
  assume \<open>canon_row r = canon_row r'\<close>
  from arg_cong[OF this, of row_labels] arg_cong[OF this, of row_tail]
  show \<open>r \<approx> r'\<close> by (simp add: row_eq_iff)
qed

lemma row_eq_code[code]: \<open>r \<approx> r' \<longleftrightarrow> canon_row r = canon_row r'\<close>
  by (rule canon_row_iff)

lemma canon_row_idem[simp]: \<open>canon_row (canon_row r) = canon_row r\<close>
  using canon_row_iff canon_row_req by blast

fun canon_ty :: \<open>kty \<Rightarrow> kty\<close> where
  \<open>canon_ty (TV a) = TV a\<close>
| \<open>canon_ty (TB a) = TB a\<close>
| \<open>canon_ty (TK a) = TK a\<close>
| \<open>canon_ty (TA k i) = TA k i\<close>
| \<open>canon_ty (TC c ts) = TC c (map canon_ty ts)\<close>
| \<open>canon_ty (TApp t\<^sub>1 t\<^sub>2) = TApp (canon_ty t\<^sub>1) (canon_ty t\<^sub>2)\<close>
| \<open>canon_ty (TFn t\<^sub>1 e t\<^sub>2) = TFn (canon_ty t\<^sub>1) (canon_row e) (canon_ty t\<^sub>2)\<close>
| \<open>canon_ty (TDep i sg T e t) = TDep i sg T (canon_row e) (canon_ty t)\<close>
| \<open>canon_ty (TEv l s t) = TEv (canon_ty l) (canon_ty s) (canon_ty t)\<close>
| \<open>canon_ty (TAct l K e t) = TAct (canon_ty l) K (canon_row e) (canon_ty t)\<close>

text \<open>Canonical equality is structural equivalence: \<^const>\<open>canon_row\<close>
  decides \<open>\<approx>\<close> and \<^const>\<open>canon_ty\<close> is otherwise structural, like \<open>\<simeq>\<close>.\<close>

lemma canon_ty_eq_iff: \<open>canon_ty t = canon_ty u \<longleftrightarrow> t \<simeq> u\<close>
proof (induction t arbitrary: u)
  case (TC c ts)
  show ?case
  proof (cases u)
    case (TC c' us)
    have \<open>map canon_ty ts = map canon_ty us \<longleftrightarrow> ts [\<simeq>] us\<close>
      using TC.IH
    proof (induction ts arbitrary: us)
      case Nil
      show ?case by (cases us) auto
    next
      case (Cons a ts')
      show ?case
      proof (cases us)
        case (Cons b us')
        have \<open>canon_ty a = canon_ty b \<longleftrightarrow> a \<simeq> b\<close>
          using Cons.prems by simp
        moreover have \<open>map canon_ty ts' = map canon_ty us' \<longleftrightarrow> ts' [\<simeq>] us'\<close>
          by (rule Cons.IH) (use Cons.prems in simp)
        ultimately show ?thesis using Cons by auto
      qed auto
    qed
    with TC show ?thesis by auto
  qed auto
qed (case_tac u; auto simp: canon_row_iff)+

subsection \<open>Substitution composition\<close>

lemma rsubst_RV[simp]: \<open>rsubst RV r = r\<close>
  by (induction r) auto

lemma tsubst_TV_RV[simp]: \<open>tsubst TV RV t = t\<close>
  by (induction t) (auto intro: map_idI)

lemma rsubst_comp:
  \<open>rsubst g\<^sub>2 (rsubst g\<^sub>1 r) = rsubst (\<lambda>v. rsubst g\<^sub>2 (g\<^sub>1 v)) r\<close>
  by (induction r) auto

lemma tsubst_comp:
  \<open>tsubst \<theta>\<^sub>2 \<rho>\<^sub>2 (tsubst \<theta>\<^sub>1 \<rho>\<^sub>1 t) =
   tsubst (\<lambda>a. tsubst \<theta>\<^sub>2 \<rho>\<^sub>2 (\<theta>\<^sub>1 a)) (\<lambda>v. rsubst \<rho>\<^sub>2 (\<rho>\<^sub>1 v)) t\<close>
  by (induction t) (auto simp: rsubst_comp)

lemma row_eq_subst: \<open>r \<approx> r' \<Longrightarrow> rsubst g r \<approx> rsubst g r'\<close>
  by (auto simp: row_eq_iff rsubst_labels rsubst_tail)

text \<open>The single-point substitution used by variable elimination, and its
  vanishing on terms avoiding the variable.\<close>

definition sing :: \<open>tvar \<Rightarrow> kty \<Rightarrow> tvar \<Rightarrow> kty\<close> where
  \<open>sing a u = (\<lambda>b. if b = a then u else TV b)\<close>

lemma tsubst_sing_absent:
  \<open>a \<notin> ftv t \<Longrightarrow> tsubst (sing a u) RV t = t\<close>
  by (induction t) (auto simp: sing_def intro: map_idI)

subsection \<open>Type unification, delegating rows to \<^const>\<open>runify\<close>\<close>

text \<open>Constraint-list unification in the substitution-application style,
  fueled; the effect positions of \<^const>\<open>TFn\<close> unify through
  \<^const>\<open>runify\<close> and the resulting row substitution is composed in. Two
  module-dependent arrows unify on the same binder, then on their rows and
  results \<^cite>\<open>\<open>Sect. 4\<close> in vivien2024\<close>; a \<^const>\<open>TDep\<close> never unifies with a
  function type or with an application by guessing, and a variable unifies
  with it only as a whole. Application of a variable head is unified by
  congruence only. A bound variable or an abstract type is a constant.\<close>

text \<open>The free variables of a constraint list.\<close>

definition ftv_cs :: \<open>(kty \<times> kty) list \<Rightarrow> tvar set\<close> where
  \<open>ftv_cs cs = (\<Union>(t, u) \<in> set cs. ftv t \<union> ftv u)\<close>

text \<open>Two action types unify only on the same binder list; their bodies unify
  with the bound abstract types as constants, and a solution that binds a
  variable of the constraints to a type mentioning one of them is rejected as
  a skolem escape \<^cite>\<open>\<open>Sect. 4.2\<close> in vivien2024\<close> (the bound types mean nothing
  outside their binder).\<close>

fun kunify :: \<open>nat \<Rightarrow> (kty \<times> kty) list \<Rightarrow> nat
               \<Rightarrow> ((tvar \<Rightarrow> kty) \<times> (rvar \<Rightarrow> krow) \<times> nat) option\<close>
and kbind :: \<open>nat \<Rightarrow> tvar \<Rightarrow> kty \<Rightarrow> (kty \<times> kty) list \<Rightarrow> nat
              \<Rightarrow> ((tvar \<Rightarrow> kty) \<times> (rvar \<Rightarrow> krow) \<times> nat) option\<close>
where
  \<open>kunify 0 cs n = None\<close>
| \<open>kunify (Suc f) [] n = Some (TV, RV, n)\<close>
| \<open>kunify (Suc f) ((TV a, t) # cs) n = kbind f a t cs n\<close>
| \<open>kunify (Suc f) ((t, TV a) # cs) n = kbind f a t cs n\<close>
| \<open>kunify (Suc f) ((TB a, TB a') # cs) n = (if a = a' then kunify f cs n else None)\<close>
| \<open>kunify (Suc f) ((TK a, TK a') # cs) n = (if a = a' then kunify f cs n else None)\<close>
| \<open>kunify (Suc f) ((TA k i, TA k' i') # cs) n =
     (if k = k' \<and> i = i' then kunify f cs n else None)\<close>
| \<open>kunify (Suc f) ((TC c ts, TC c' ts') # cs) n =
     (if c = c' \<and> length ts = length ts'
      then kunify f (zip ts ts' @ cs) n else None)\<close>
| \<open>kunify (Suc f) ((TFn u\<^sub>1 e u\<^sub>2, TFn w\<^sub>1 g w\<^sub>2) # cs) n =
     (case runify n e g of
        None \<Rightarrow> None
      | Some (\<rho>m, n') \<Rightarrow>
          (case kunify f
                  (map (\<lambda>(x, y). (tsubst TV (mk_rsub \<rho>m) x,
                                  tsubst TV (mk_rsub \<rho>m) y))
                       ((u\<^sub>1, w\<^sub>1) # (u\<^sub>2, w\<^sub>2) # cs)) n' of
             None \<Rightarrow> None
           | Some (\<theta>, \<rho>, n'') \<Rightarrow>
               Some (\<theta>, (\<lambda>v. rsubst \<rho> (mk_rsub \<rho>m v)), n'')))\<close>
| \<open>kunify (Suc f) ((TDep i sg m e u, TDep i' sg' m' g w) # cs) n =
     (if i = i' \<and> sg = sg' \<and> m = m'
      then (case runify n e g of
              None \<Rightarrow> None
            | Some (\<rho>m, n') \<Rightarrow>
                (case kunify f
                        (map (\<lambda>(x, y). (tsubst TV (mk_rsub \<rho>m) x,
                                        tsubst TV (mk_rsub \<rho>m) y))
                             ((u, w) # cs)) n' of
                   None \<Rightarrow> None
                 | Some (\<theta>, \<rho>, n'') \<Rightarrow>
                     Some (\<theta>, (\<lambda>v. rsubst \<rho> (mk_rsub \<rho>m v)), n'')))
      else None)\<close>
| \<open>kunify (Suc f) ((TApp u\<^sub>1 u\<^sub>2, TApp w\<^sub>1 w\<^sub>2) # cs) n =
     kunify f ((u\<^sub>1, w\<^sub>1) # (u\<^sub>2, w\<^sub>2) # cs) n\<close>
| \<open>kunify (Suc f) ((TEv l u\<^sub>1 u\<^sub>2, TEv l' w\<^sub>1 w\<^sub>2) # cs) n =
     kunify f ((l, l') # (u\<^sub>1, w\<^sub>1) # (u\<^sub>2, w\<^sub>2) # cs) n\<close>
| \<open>kunify (Suc f) ((TAct l T e u, TAct l' T' g w) # cs) n =
     (if T = T'
      then (case runify n e g of
              None \<Rightarrow> None
            | Some (\<rho>m, n') \<Rightarrow>
                (case kunify f
                        (map (\<lambda>(x, y). (tsubst TV (mk_rsub \<rho>m) x,
                                        tsubst TV (mk_rsub \<rho>m) y))
                             ((l, l') # (u, w) # cs)) n' of
                   None \<Rightarrow> None
                 | Some (\<theta>, \<rho>, n'') \<Rightarrow>
                     (if \<forall>a \<in> ftv_cs ((l, l') # (u, w) # cs). set T \<inter> ktv (\<theta> a) = {}
                      then Some (\<theta>, (\<lambda>v. rsubst \<rho> (mk_rsub \<rho>m v)), n'')
                      else None)))
      else None)\<close>
| \<open>kunify (Suc f) (c # cs) n = None\<close>

| \<open>kbind 0 a u cs n = None\<close>
| \<open>kbind (Suc f) a u cs n =
     (if u = TV a then kunify f cs n
      else if a \<in> ftv u \<or> \<not> taclosed u then None
      else (case kunify f (map (\<lambda>(x, y). (tsubst (sing a u) RV x,
                                          tsubst (sing a u) RV y)) cs) n of
              None \<Rightarrow> None
            | Some (\<theta>, \<rho>, n') \<Rightarrow>
                Some ((\<lambda>b. tsubst \<theta> \<rho> (sing a u b)), \<rho>, n')))\<close>  (* ~38s *)

lemmas kunify_induct = kunify_kbind.induct[named_cases kunify]

lemma zip_all_map_eq:
  \<open>length xs = length ys \<Longrightarrow> (\<forall>(x, y) \<in> set (zip xs ys). h x = h' y) \<Longrightarrow>
   map h xs = map h' ys\<close>
  by (induction xs ys rule: list_induct2) auto

theorem kunify_sound:
  \<open>kunify f cs n = Some (\<theta>, \<rho>, n') \<Longrightarrow>
     \<forall>(t\<^sub>1, t\<^sub>2) \<in> set cs. canon_ty (tsubst \<theta> \<rho> t\<^sub>1) = canon_ty (tsubst \<theta> \<rho> t\<^sub>2)\<close>
  and kbind_sound: \<open>kbind f a u cs n = Some (\<theta>, \<rho>, n') \<Longrightarrow>
     canon_ty (tsubst \<theta> \<rho> (TV a)) = canon_ty (tsubst \<theta> \<rho> u) \<and>
     (\<forall>(t\<^sub>1, t\<^sub>2) \<in> set cs. canon_ty (tsubst \<theta> \<rho> t\<^sub>1) = canon_ty (tsubst \<theta> \<rho> t\<^sub>2))\<close>
proof (induction f cs n and f a u cs n
       arbitrary: \<theta> \<rho> n' and \<theta> \<rho> n' rule: kunify_induct)
  case (kunify_Cons_TC_TC f c ts c' ts' cs n)
  then have len: \<open>length ts = length ts'\<close> and
    rec: \<open>\<forall>(t\<^sub>1, t\<^sub>2) \<in> set (zip ts ts' @ cs).
            canon_ty (tsubst \<theta> \<rho> t\<^sub>1) = canon_ty (tsubst \<theta> \<rho> t\<^sub>2)\<close>
    by (auto split: if_split_asm)
  from rec have \<open>map (canon_ty \<circ> tsubst \<theta> \<rho>) ts = map (canon_ty \<circ> tsubst \<theta> \<rho>) ts'\<close>
    using zip_all_map_eq[OF len, of \<open>canon_ty \<circ> tsubst \<theta> \<rho>\<close> \<open>canon_ty \<circ> tsubst \<theta> \<rho>\<close>]
    by auto
  with kunify_Cons_TC_TC.prems len rec show ?case
    by (auto split: if_split_asm)
next
  case (kunify_Cons_TFn_TFn f u\<^sub>1 e u\<^sub>2 w\<^sub>1 g w\<^sub>2 cs n)
  from kunify_Cons_TFn_TFn.prems obtain \<rho>m n\<^sub>1 \<theta>\<^sub>1 \<rho>\<^sub>1 where
    rm: \<open>runify n e g = Some (\<rho>m, n\<^sub>1)\<close> and
    ku: \<open>kunify f (map (\<lambda>(x, y). (tsubst TV (mk_rsub \<rho>m) x,
                                  tsubst TV (mk_rsub \<rho>m) y))
                       ((u\<^sub>1, w\<^sub>1) # (u\<^sub>2, w\<^sub>2) # cs)) n\<^sub>1 = Some (\<theta>\<^sub>1, \<rho>\<^sub>1, n')\<close> and
    \<theta>: \<open>\<theta> = \<theta>\<^sub>1\<close> and \<rho>: \<open>\<rho> = (\<lambda>v. rsubst \<rho>\<^sub>1 (mk_rsub \<rho>m v))\<close>
    by (auto split: option.split_asm)
  have IH: \<open>\<forall>(t\<^sub>1, t\<^sub>2) \<in> set ((u\<^sub>1, w\<^sub>1) # (u\<^sub>2, w\<^sub>2) # cs).
              canon_ty (tsubst \<theta>\<^sub>1 \<rho>\<^sub>1 (tsubst TV (mk_rsub \<rho>m) t\<^sub>1)) =
              canon_ty (tsubst \<theta>\<^sub>1 \<rho>\<^sub>1 (tsubst TV (mk_rsub \<rho>m) t\<^sub>2))\<close>
    using kunify_Cons_TFn_TFn.IH[OF rm _ ku] rm by fastforce
  have comp: \<open>\<And>t. tsubst \<theta>\<^sub>1 \<rho>\<^sub>1 (tsubst TV (mk_rsub \<rho>m) t) = tsubst \<theta> \<rho> t\<close>
    unfolding \<theta> \<rho> by (simp add: tsubst_comp)
  have rowcomp: \<open>\<And>r. rsubst \<rho>\<^sub>1 (rsubst (mk_rsub \<rho>m) r) = rsubst \<rho> r\<close>
    unfolding \<rho> by (simp add: rsubst_comp)
  have rows: \<open>canon_row (rsubst \<rho> e) = canon_row (rsubst \<rho> g)\<close>
    unfolding canon_row_iff[symmetric] rowcomp[symmetric]
    using runify_sound[OF rm] row_eq_subst by simp
  from IH comp have
    \<open>canon_ty (tsubst \<theta> \<rho> u\<^sub>1) = canon_ty (tsubst \<theta> \<rho> w\<^sub>1)\<close>
    \<open>canon_ty (tsubst \<theta> \<rho> u\<^sub>2) = canon_ty (tsubst \<theta> \<rho> w\<^sub>2)\<close>
    \<open>\<forall>(t\<^sub>1, t\<^sub>2) \<in> set cs. canon_ty (tsubst \<theta> \<rho> t\<^sub>1) = canon_ty (tsubst \<theta> \<rho> t\<^sub>2)\<close>
    by fastforce+
  with rows show ?case by auto
next
  case (kunify_Cons_TDep_TDep f i sg T e u i' sg' T' g w cs n)
  from kunify_Cons_TDep_TDep.prems obtain \<rho>m n\<^sub>1 \<theta>\<^sub>1 \<rho>\<^sub>1 where
    eq: \<open>i = i'\<close> \<open>sg = sg'\<close> \<open>T = T'\<close> and
    rm: \<open>runify n e g = Some (\<rho>m, n\<^sub>1)\<close> and
    ku: \<open>kunify f (map (\<lambda>(x, y). (tsubst TV (mk_rsub \<rho>m) x,
                                  tsubst TV (mk_rsub \<rho>m) y))
                       ((u, w) # cs)) n\<^sub>1 = Some (\<theta>\<^sub>1, \<rho>\<^sub>1, n')\<close> and
    \<theta>: \<open>\<theta> = \<theta>\<^sub>1\<close> and \<rho>: \<open>\<rho> = (\<lambda>v. rsubst \<rho>\<^sub>1 (mk_rsub \<rho>m v))\<close>
    by (auto split: option.split_asm if_split_asm)
  have IH: \<open>\<forall>(t\<^sub>1, t\<^sub>2) \<in> set ((u, w) # cs).
              canon_ty (tsubst \<theta>\<^sub>1 \<rho>\<^sub>1 (tsubst TV (mk_rsub \<rho>m) t\<^sub>1)) =
              canon_ty (tsubst \<theta>\<^sub>1 \<rho>\<^sub>1 (tsubst TV (mk_rsub \<rho>m) t\<^sub>2))\<close>
    using kunify_Cons_TDep_TDep.IH[OF _ rm _ ku] eq rm by fastforce
  have comp: \<open>\<And>t. tsubst \<theta>\<^sub>1 \<rho>\<^sub>1 (tsubst TV (mk_rsub \<rho>m) t) = tsubst \<theta> \<rho> t\<close>
    unfolding \<theta> \<rho> by (simp add: tsubst_comp)
  have rowcomp: \<open>\<And>r. rsubst \<rho>\<^sub>1 (rsubst (mk_rsub \<rho>m) r) = rsubst \<rho> r\<close>
    unfolding \<rho> by (simp add: rsubst_comp)
  have rows: \<open>canon_row (rsubst \<rho> e) = canon_row (rsubst \<rho> g)\<close>
    unfolding canon_row_iff[symmetric] rowcomp[symmetric]
    using runify_sound[OF rm] row_eq_subst by simp
  from IH comp have
    \<open>canon_ty (tsubst \<theta> \<rho> u) = canon_ty (tsubst \<theta> \<rho> w)\<close>
    \<open>\<forall>(t\<^sub>1, t\<^sub>2) \<in> set cs. canon_ty (tsubst \<theta> \<rho> t\<^sub>1) = canon_ty (tsubst \<theta> \<rho> t\<^sub>2)\<close>
    by fastforce+
  with rows eq show ?case by auto
next
  case (kunify_Cons_TAct_TAct f l T e u l' T' g w cs n)
  from kunify_Cons_TAct_TAct.prems obtain \<rho>m n\<^sub>1 \<theta>\<^sub>1 \<rho>\<^sub>1 where
    eq: \<open>T = T'\<close> and
    rm: \<open>runify n e g = Some (\<rho>m, n\<^sub>1)\<close> and
    ku: \<open>kunify f (map (\<lambda>(x, y). (tsubst TV (mk_rsub \<rho>m) x,
                                  tsubst TV (mk_rsub \<rho>m) y))
                       ((l, l') # (u, w) # cs)) n\<^sub>1 = Some (\<theta>\<^sub>1, \<rho>\<^sub>1, n')\<close> and
    \<theta>: \<open>\<theta> = \<theta>\<^sub>1\<close> and \<rho>: \<open>\<rho> = (\<lambda>v. rsubst \<rho>\<^sub>1 (mk_rsub \<rho>m v))\<close>
    by (auto split: option.split_asm if_split_asm)
  have IH: \<open>\<forall>(t\<^sub>1, t\<^sub>2) \<in> set ((l, l') # (u, w) # cs).
              canon_ty (tsubst \<theta>\<^sub>1 \<rho>\<^sub>1 (tsubst TV (mk_rsub \<rho>m) t\<^sub>1)) =
              canon_ty (tsubst \<theta>\<^sub>1 \<rho>\<^sub>1 (tsubst TV (mk_rsub \<rho>m) t\<^sub>2))\<close>
    using kunify_Cons_TAct_TAct.IH[OF _ rm _ ku] eq rm by fastforce
  have comp: \<open>\<And>t. tsubst \<theta>\<^sub>1 \<rho>\<^sub>1 (tsubst TV (mk_rsub \<rho>m) t) = tsubst \<theta> \<rho> t\<close>
    unfolding \<theta> \<rho> by (simp add: tsubst_comp)
  have rowcomp: \<open>\<And>r. rsubst \<rho>\<^sub>1 (rsubst (mk_rsub \<rho>m) r) = rsubst \<rho> r\<close>
    unfolding \<rho> by (simp add: rsubst_comp)
  have rows: \<open>canon_row (rsubst \<rho> e) = canon_row (rsubst \<rho> g)\<close>
    unfolding canon_row_iff[symmetric] rowcomp[symmetric]
    using runify_sound[OF rm] row_eq_subst by simp
  from IH comp have
    \<open>canon_ty (tsubst \<theta> \<rho> l) = canon_ty (tsubst \<theta> \<rho> l')\<close>
    \<open>canon_ty (tsubst \<theta> \<rho> u) = canon_ty (tsubst \<theta> \<rho> w)\<close>
    \<open>\<forall>(t\<^sub>1, t\<^sub>2) \<in> set cs. canon_ty (tsubst \<theta> \<rho> t\<^sub>1) = canon_ty (tsubst \<theta> \<rho> t\<^sub>2)\<close>
    by fastforce+
  with rows eq show ?case by auto
next
  case (kbind_Suc f a u cs n)
  show ?case
  proof (cases \<open>u = TV a\<close>)
    case True
    with kbind_Suc.prems have \<open>kunify f cs n = Some (\<theta>, \<rho>, n')\<close> by simp
    with True show ?thesis by (auto dest: kbind_Suc.IH)
  next
    case False
    with kbind_Suc.prems have occ: \<open>\<not> (a \<in> ftv u \<or> \<not> taclosed u)\<close>
      by (auto split: if_split_asm option.split_asm)
    then have occ': \<open>a \<notin> ftv u\<close> by simp
    from kbind_Suc.prems False occ obtain \<theta>\<^sub>1 \<rho>\<^sub>1 where
      ku: \<open>kunify f (map (\<lambda>(x, y). (tsubst (sing a u) RV x,
                                    tsubst (sing a u) RV y)) cs) n
           = Some (\<theta>\<^sub>1, \<rho>\<^sub>1, n')\<close> and
      \<theta>: \<open>\<theta> = (\<lambda>b. tsubst \<theta>\<^sub>1 \<rho>\<^sub>1 (sing a u b))\<close> and \<rho>: \<open>\<rho> = \<rho>\<^sub>1\<close>
      by (auto split: option.split_asm if_split_asm)
    have IH: \<open>\<forall>(t\<^sub>1, t\<^sub>2) \<in> set cs.
                canon_ty (tsubst \<theta>\<^sub>1 \<rho>\<^sub>1 (tsubst (sing a u) RV t\<^sub>1)) =
                canon_ty (tsubst \<theta>\<^sub>1 \<rho>\<^sub>1 (tsubst (sing a u) RV t\<^sub>2))\<close>
      using False occ ku by (fastforce dest: kbind_Suc.IH)
    have comp: \<open>\<And>t. tsubst \<theta>\<^sub>1 \<rho>\<^sub>1 (tsubst (sing a u) RV t) = tsubst \<theta> \<rho> t\<close>
      unfolding \<theta> \<rho> by (simp add: tsubst_comp)
    have head: \<open>canon_ty (tsubst \<theta> \<rho> (TV a)) = canon_ty (tsubst \<theta> \<rho> u)\<close>
    proof -
      have \<open>tsubst \<theta> \<rho> (TV a) = tsubst \<theta>\<^sub>1 \<rho>\<^sub>1 u\<close>
        unfolding \<theta> \<rho> by (simp add: sing_def)
      moreover have \<open>tsubst \<theta> \<rho> u = tsubst \<theta>\<^sub>1 \<rho>\<^sub>1 u\<close>
        using comp[of u] tsubst_sing_absent[OF occ', of u] by simp
      ultimately show ?thesis by simp
    qed
    from IH comp head show ?thesis by fastforce
  qed
qed (auto split: if_split_asm option.split_asm)

subsection \<open>Substitutions of the algorithm\<close>

text \<open>Substitutions are pairs of total functions, composed and applied
  directly; schemes and the basis substitute under their binders.\<close>

type_synonym ksub = \<open>(tvar \<Rightarrow> kty) \<times> (rvar \<Rightarrow> krow)\<close>

definition \<open>sid = (TV, RV)\<close>

text \<open>Projecting a substitution to the variables below a bound: the fresh
  variables a scoped construct mints are dead outside it, and their images may
  mention the construct's own rigid abstract types, so a module binder returns
  its body substitution restricted to the variables in scope at entry
  \<^cite>\<open>\<open>Sect. 5.6\<close> in milner1997\<close>: the abstract types stay confined to the functor.\<close>

definition sproj :: \<open>nat \<Rightarrow> ksub \<Rightarrow> ksub\<close> where
  \<open>sproj m s = ((\<lambda>a. if a < m then fst s a else TV a), snd s)\<close>

fun sapp :: \<open>ksub \<Rightarrow> kty \<Rightarrow> kty\<close> where
  \<open>sapp (\<theta>, \<rho>) t = tsubst \<theta> \<rho> t\<close>

fun sappr :: \<open>ksub \<Rightarrow> krow \<Rightarrow> krow\<close> where
  \<open>sappr (\<theta>, \<rho>) r = rsubst \<rho> r\<close>

fun sapps :: \<open>ksub \<Rightarrow> scheme \<Rightarrow> scheme\<close> where
  \<open>sapps (\<theta>, \<rho>) \<sigma> = sub_scheme \<theta> \<rho> \<sigma>\<close>

fun sappe :: \<open>ksub \<Rightarrow> tenv \<Rightarrow> tenv\<close> where
  \<open>sappe (\<theta>, \<rho>) E = sub_env \<theta> \<rho> E\<close>

fun scomp :: \<open>ksub \<Rightarrow> ksub \<Rightarrow> ksub\<close>  (infixl \<open>\<odot>\<close> 60) where
  \<open>(\<theta>\<^sub>2, \<rho>\<^sub>2) \<odot> (\<theta>\<^sub>1, \<rho>\<^sub>1) = ((\<lambda>a. tsubst \<theta>\<^sub>2 \<rho>\<^sub>2 (\<theta>\<^sub>1 a)), (\<lambda>v. rsubst \<rho>\<^sub>2 (\<rho>\<^sub>1 v)))\<close>

lemma sapp_scomp: \<open>sapp (s\<^sub>2 \<odot> s\<^sub>1) t = sapp s\<^sub>2 (sapp s\<^sub>1 t)\<close>
  by (cases s\<^sub>1; cases s\<^sub>2) (simp add: tsubst_comp)

lemma sappr_scomp: \<open>sappr (s\<^sub>2 \<odot> s\<^sub>1) r = sappr s\<^sub>2 (sappr s\<^sub>1 r)\<close>
  by (cases s\<^sub>1; cases s\<^sub>2) (simp add: rsubst_comp)

lemma sapps_scomp: \<open>sapps (s\<^sub>2 \<odot> s\<^sub>1) \<sigma> = sapps s\<^sub>2 (sapps s\<^sub>1 \<sigma>)\<close>
  by (cases s\<^sub>1; cases s\<^sub>2; cases \<sigma>) (simp_all add: tsubst_comp)

lemma sub_scheme_comp:
  \<open>sub_scheme \<theta>\<^sub>2 \<rho>\<^sub>2 (sub_scheme \<theta>\<^sub>1 \<rho>\<^sub>1 \<sigma>) =
   sub_scheme (\<lambda>a. tsubst \<theta>\<^sub>2 \<rho>\<^sub>2 (\<theta>\<^sub>1 a)) (\<lambda>v. rsubst \<rho>\<^sub>2 (\<rho>\<^sub>1 v)) \<sigma>\<close>
  by (cases \<sigma>) (simp_all add: tsubst_comp)

lemma sub_ent_comp:
  \<open>sub_ent \<theta>\<^sub>2 \<rho>\<^sub>2 (sub_ent \<theta>\<^sub>1 \<rho>\<^sub>1 e) =
   sub_ent (\<lambda>a. tsubst \<theta>\<^sub>2 \<rho>\<^sub>2 (\<theta>\<^sub>1 a)) (\<lambda>v. rsubst \<rho>\<^sub>2 (\<rho>\<^sub>1 v)) e\<close>
  by (cases e) (simp_all add: sub_scheme_comp)

lemma sub_env_comp:
  \<open>sub_env \<theta>\<^sub>2 \<rho>\<^sub>2 (sub_env \<theta>\<^sub>1 \<rho>\<^sub>1 E) =
   sub_env (\<lambda>a. tsubst \<theta>\<^sub>2 \<rho>\<^sub>2 (\<theta>\<^sub>1 a)) (\<lambda>v. rsubst \<rho>\<^sub>2 (\<rho>\<^sub>1 v)) E\<close>
  by (induction E) (auto simp: sub_env_def sub_ent_comp)

lemma sappe_scomp: \<open>sappe (s\<^sub>2 \<odot> s\<^sub>1) E = sappe s\<^sub>2 (sappe s\<^sub>1 E)\<close>
  by (cases s\<^sub>1; cases s\<^sub>2) (simp add: sub_env_comp)

lemma sapp_sid[simp]: \<open>sapp sid t = t\<close>
  by (simp add: sid_def)

lemma sappr_sid[simp]: \<open>sappr sid r = r\<close>
  by (simp add: sid_def)

lemma sapps_sid[simp]: \<open>sapps sid \<sigma> = \<sigma>\<close>
  by (cases \<sigma>) (simp_all add: sid_def)

lemma sub_scheme_id[simp]: \<open>sub_scheme TV RV \<sigma> = \<sigma>\<close>
  by (cases \<sigma>) simp_all

lemma sub_ent_id[simp]: \<open>sub_ent TV RV e = e\<close>
  by (cases e) simp_all

lemma sub_env_id[simp]: \<open>sub_env TV RV E = E\<close>
  by (induction E) (auto simp: sub_env_def)

lemma sappe_sid[simp]: \<open>sappe sid E = E\<close>
  by (simp add: sid_def)

lemma sub_env_append: \<open>sub_env \<theta> \<rho> (E\<^sub>1 @ E\<^sub>2) = sub_env \<theta> \<rho> E\<^sub>1 @ sub_env \<theta> \<rho> E\<^sub>2\<close>
  by (simp add: sub_env_def)

lemma sappe_append: \<open>sappe s (E\<^sub>1 @ E\<^sub>2) = sappe s E\<^sub>1 @ sappe s E\<^sub>2\<close>
  by (cases s) (simp add: sub_env_append)

subsection \<open>Unification wrappers\<close>

definition unis :: \<open>nat \<Rightarrow> (kty \<times> kty) list \<Rightarrow> nat \<Rightarrow> (ksub \<times> nat) option\<close> where
  \<open>unis f cs n =
     (case kunify f cs n of None \<Rightarrow> None | Some (\<theta>, \<rho>, n') \<Rightarrow> Some ((\<theta>, \<rho>), n'))\<close>

definition uni :: \<open>nat \<Rightarrow> kty \<Rightarrow> kty \<Rightarrow> nat \<Rightarrow> (ksub \<times> nat) option\<close> where
  \<open>uni f t\<^sub>1 t\<^sub>2 n = unis f [(t\<^sub>1, t\<^sub>2)] n\<close>

definition uni_row :: \<open>krow \<Rightarrow> krow \<Rightarrow> nat \<Rightarrow> (ksub \<times> nat) option\<close> where
  \<open>uni_row r\<^sub>1 r\<^sub>2 n =
     (case runify n r\<^sub>1 r\<^sub>2 of
        None \<Rightarrow> None | Some (\<rho>m, n') \<Rightarrow> Some ((TV, mk_rsub \<rho>m), n'))\<close>

text \<open>The wrappers lift @{thm [source] kunify_sound} and @{thm [source] runify_sound} to the
  applied-substitution form the soundness induction uses.\<close>

lemma unis_sound:
  assumes \<open>unis f cs n = Some (s, n')\<close>
  shows \<open>\<forall>(t\<^sub>1, t\<^sub>2) \<in> set cs. sapp s t\<^sub>1 \<simeq> sapp s t\<^sub>2\<close>
proof -
  from assms obtain \<theta> \<rho> where
    s: \<open>s = (\<theta>, \<rho>)\<close> and ku: \<open>kunify f cs n = Some (\<theta>, \<rho>, n')\<close>
    unfolding unis_def by (auto split: option.split_asm)
  show ?thesis
    using kunify_sound[OF ku] unfolding s by (auto simp: canon_ty_eq_iff)
qed

lemma uni_sound:
  assumes \<open>uni f t\<^sub>1 t\<^sub>2 n = Some (s, n')\<close>
  shows \<open>sapp s t\<^sub>1 \<simeq> sapp s t\<^sub>2\<close>
  using unis_sound[OF assms[unfolded uni_def]] by simp

lemma uni_row_sound:
  assumes \<open>uni_row r\<^sub>1 r\<^sub>2 n = Some (s, n')\<close>
  shows \<open>sappr s r\<^sub>1 \<approx> sappr s r\<^sub>2\<close>
proof -
  from assms obtain \<sigma> where
    s: \<open>s = (TV, mk_rsub \<sigma>)\<close> and ru: \<open>runify n r\<^sub>1 r\<^sub>2 = Some (\<sigma>, n')\<close>
    unfolding uni_row_def by (auto split: option.split_asm)
  show ?thesis using runify_sound[OF ru] unfolding s by simp
qed

subsection \<open>Fresh variables, instantiation, generalisation\<close>

text \<open>Instantiation replaces the bound variables of a scheme by fresh
  unification variables, in the order of their numbers; generalisation
  renames the chosen unification variables into bound ones
  \<^cite>\<open>\<open>Sect. 4.5, 4.8\<close> in milner1997\<close>. Both are renamings between sorts.\<close>

definition close_ty :: \<open>tvar set \<Rightarrow> rvar set \<Rightarrow> kty \<Rightarrow> kty\<close> where
  \<open>close_ty as rs t =
     tsubst (\<lambda>a. if a \<in> as then TB a else TV a) (\<lambda>v. if v \<in> rs then RB v else RV v) t\<close>

definition close_sch :: \<open>tvar set \<Rightarrow> rvar set \<Rightarrow> kty \<Rightarrow> scheme\<close> where
  \<open>close_sch as rs t = Sch (close_ty as rs t)\<close>

fun btv_list :: \<open>kty \<Rightarrow> tvar list\<close> where
  \<open>btv_list (TV a) = []\<close>
| \<open>btv_list (TB a) = [a]\<close>
| \<open>btv_list (TK a) = []\<close>
| \<open>btv_list (TA k i) = []\<close>
| \<open>btv_list (TC c ts) = concat (map btv_list ts)\<close>
| \<open>btv_list (TApp t\<^sub>1 t\<^sub>2) = btv_list t\<^sub>1 @ btv_list t\<^sub>2\<close>
| \<open>btv_list (TFn t\<^sub>1 e t\<^sub>2) = btv_list t\<^sub>1 @ btv_list t\<^sub>2\<close>
| \<open>btv_list (TDep i sg K e t) = btv_list t\<close>
| \<open>btv_list (TEv l s t) = btv_list l @ btv_list s @ btv_list t\<close>
| \<open>btv_list (TAct l K e t) = btv_list l @ btv_list t\<close>

fun brv_list_row :: \<open>krow \<Rightarrow> rvar list\<close> where
  \<open>brv_list_row RNil = []\<close>
| \<open>brv_list_row (RV v) = []\<close>
| \<open>brv_list_row (RB v) = [v]\<close>
| \<open>brv_list_row (RCons l r) = brv_list_row r\<close>

fun brv_list :: \<open>kty \<Rightarrow> rvar list\<close> where
  \<open>brv_list (TV a) = []\<close>
| \<open>brv_list (TB a) = []\<close>
| \<open>brv_list (TK a) = []\<close>
| \<open>brv_list (TA k i) = []\<close>
| \<open>brv_list (TC c ts) = concat (map brv_list ts)\<close>
| \<open>brv_list (TApp t\<^sub>1 t\<^sub>2) = brv_list t\<^sub>1 @ brv_list t\<^sub>2\<close>
| \<open>brv_list (TFn t\<^sub>1 e t\<^sub>2) = brv_list t\<^sub>1 @ brv_list_row e @ brv_list t\<^sub>2\<close>
| \<open>brv_list (TDep i sg K e t) = brv_list_row e @ brv_list t\<close>
| \<open>brv_list (TEv l s t) = brv_list l @ brv_list s @ brv_list t\<close>
| \<open>brv_list (TAct l K e t) = brv_list l @ brv_list_row e @ brv_list t\<close>

lemma set_btv_list[simp]: \<open>set (btv_list t) = btv t\<close>
  by (induction t) auto

lemma set_brv_list_row[simp]: \<open>set (brv_list_row r) = brv_row r\<close>
  by (induction r) auto

lemma set_brv_list[simp]: \<open>set (brv_list t) = brv t\<close>
  by (induction t) auto

declare imatch.simps[code del]

lemma imatch_code[code]:
  \<open>imatch (Sch t) \<tau> =
     (case tmatch t \<tau> (Map.empty, Map.empty) of
        None \<Rightarrow> False
      | Some (\<theta>', \<rho>') \<Rightarrow> btv_list \<tau> = [] \<and> brv_list \<tau> = [] \<and>
          list_all (\<lambda>a. case \<theta>' a of Some u \<Rightarrow> taclosed u | None \<Rightarrow> True) (btv_list t))\<close>
  \<open>imatch (Mono t) \<tau> \<longleftrightarrow> \<tau> = t\<close>
  by (simp_all add: list_all_iff flip: set_btv_list set_brv_list split: option.split)

fun inst_scheme :: \<open>nat \<Rightarrow> scheme \<Rightarrow> kty \<times> nat\<close> where
  \<open>inst_scheme n (Mono t) = (t, n)\<close>
| \<open>inst_scheme n (Sch t) =
     (let avs = remdups (sort (btv_list t)); rvs = remdups (sort (brv_list t));
          \<theta> = (\<lambda>a. case map_of (zip avs (map TV [n ..< n + length avs])) a of
                     Some \<tau> \<Rightarrow> \<tau> | None \<Rightarrow> TB a);
          \<rho> = (\<lambda>v. case map_of (zip rvs
                       (map RV [n + length avs ..< n + length avs + length rvs])) v of
                     Some r \<Rightarrow> r | None \<Rightarrow> RB v)
      in (bsubst \<theta> \<rho> t, n + length avs + length rvs))\<close>

text \<open>Instantiation yields an instance of the scheme.\<close>

lemma inst_scheme_sinst:
  assumes \<open>inst_scheme n \<sigma> = (\<tau>, n')\<close>
  shows \<open>\<sigma> \<succeq> \<tau>\<close>
proof (cases \<sigma>)
  case (Sch t)
  define avs where \<open>avs = remdups (sort (btv_list t))\<close>
  define rvs where \<open>rvs = remdups (sort (brv_list t))\<close>
  define \<theta> where
    \<open>\<theta> = (\<lambda>a. case map_of (zip avs (map TV [n ..< n + length avs])) a of
               Some \<tau> \<Rightarrow> \<tau> | None \<Rightarrow> TB a)\<close>
  define \<rho> where
    \<open>\<rho> = (\<lambda>v. case map_of (zip rvs (map RV [n + length avs ..< n + length avs + length rvs])) v of
               Some r \<Rightarrow> r | None \<Rightarrow> RB v)\<close>
  have \<tau>: \<open>\<tau> = bsubst \<theta> \<rho> t\<close>
    using assms[unfolded Sch inst_scheme.simps Let_def, THEN iffD1[OF prod.inject], THEN conjunct1]
    unfolding \<theta>_def \<rho>_def avs_def rvs_def by (rule sym)
  have \<theta>: \<open>btv (\<theta> a) = {} \<and> brv (\<theta> a) = {}\<close> if \<open>a \<in> btv t\<close> for a
  proof -
    have \<open>a \<in> set avs\<close> using that by (simp add: avs_def)
    then obtain y where y: \<open>map_of (zip avs (map TV [n ..< n + length avs])) a = Some y\<close>
      using map_of_zip_is_Some[of avs \<open>map TV [n ..< n + length avs]\<close>] by auto
    then have \<open>y \<in> set (map TV [n ..< n + length avs])\<close> by (blast dest: map_of_SomeD set_zip_rightD)
    then show ?thesis unfolding \<theta>_def y by auto
  qed
  have \<theta>f: \<open>taclosed (\<theta> a)\<close> for a
  proof (cases \<open>map_of (zip avs (map TV [n ..< n + length avs])) a\<close>)
    case None show ?thesis unfolding \<theta>_def None by simp
  next
    case (Some y)
    then have \<open>y \<in> set (map TV [n ..< n + length avs])\<close> by (blast dest: map_of_SomeD set_zip_rightD)
    then show ?thesis unfolding \<theta>_def Some by auto
  qed
  have \<rho>: \<open>brv_row (\<rho> v) = {}\<close> if \<open>v \<in> brv t\<close> for v
  proof -
    have \<open>v \<in> set rvs\<close> using that by (simp add: rvs_def)
    then obtain y where
      y: \<open>map_of (zip rvs (map RV [n + length avs ..< n + length avs + length rvs])) v = Some y\<close>
      using map_of_zip_is_Some[of rvs \<open>map RV [n + length avs ..< n + length avs + length rvs]\<close>]
      by auto
    then have \<open>y \<in> set (map RV [n + length avs ..< n + length avs + length rvs])\<close>
      by (blast dest: map_of_SomeD set_zip_rightD)
    then show ?thesis unfolding \<rho>_def y by auto
  qed
  show ?thesis unfolding Sch sinst_Sch \<tau> by (auto simp: btv_bsubst brv_bsubst \<theta> \<theta>f \<rho>)
qed (use assms in auto)

text \<open>Generalisation by set difference against the free variables of the
  basis and the ambient row \<^cite>\<open>\<open>Sect. 4.8\<close> in milner1997\<close>
  \<^cite>\<open>\<open>Sect. 3.1\<close> in leijen2017\<close>.\<close>

definition gen_sets :: \<open>tenv \<Rightarrow> krow \<Rightarrow> kty \<Rightarrow> tvar set \<times> rvar set\<close> where
  \<open>gen_sets B A \<tau> = (ftv \<tau> - ftv_env B, frv \<tau> - frv_env B - frv_row A)\<close>

definition gen :: \<open>tenv \<Rightarrow> krow \<Rightarrow> kty \<Rightarrow> scheme\<close> where
  \<open>gen B A \<tau> = (case gen_sets B A \<tau> of (as, rs) \<Rightarrow> close_sch as rs \<tau>)\<close>

text \<open>An upper bound on the variables of a type, for choosing fresh ones.\<close>

fun krow_bnd :: \<open>krow \<Rightarrow> nat\<close> where
  \<open>krow_bnd RNil = 0\<close>
| \<open>krow_bnd (RV v) = Suc v\<close>
| \<open>krow_bnd (RB v) = Suc v\<close>
| \<open>krow_bnd (RCons l r) = krow_bnd r\<close>

fun kty_bnd :: \<open>kty \<Rightarrow> nat\<close> where
  \<open>kty_bnd (TV a) = Suc a\<close>
| \<open>kty_bnd (TB a) = Suc a\<close>
| \<open>kty_bnd (TK a) = Suc a\<close>
| \<open>kty_bnd (TA k i) = 0\<close>
| \<open>kty_bnd (TC c ts) = fold max (map kty_bnd ts) 0\<close>
| \<open>kty_bnd (TApp t\<^sub>1 t\<^sub>2) = max (kty_bnd t\<^sub>1) (kty_bnd t\<^sub>2)\<close>
| \<open>kty_bnd (TFn t\<^sub>1 e t\<^sub>2) = max (kty_bnd t\<^sub>1) (max (krow_bnd e) (kty_bnd t\<^sub>2))\<close>
| \<open>kty_bnd (TDep i sg T e t) = max (krow_bnd e) (kty_bnd t)\<close>
| \<open>kty_bnd (TEv l s t) = max (kty_bnd l) (max (kty_bnd s) (kty_bnd t))\<close>
| \<open>kty_bnd (TAct l K e t) = max (kty_bnd l) (max (krow_bnd e) (kty_bnd t))\<close>

end
