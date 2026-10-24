theory Infer_Confinement
  imports Infer_Invariants
begin

section \<open>Confinement of the inference algorithm\<close>

text \<open>The well-formedness invariant of \<^const>\<open>infer\<close>, the confinement half of the
  soundness proof of algorithm W \<^cite>\<open>naraschewski1999\<close>.

    \<^item> \<^text>\<open>infer_wf\<close>: on well-formed inputs (\<^text>\<open>inwf\<close>) the algorithm returns a
      well-formed output (\<^text>\<open>outwf\<close>) and a type fresh for the new counter.

    \<^item> The same for the parts it calls, e.g. operator trees (\<^text>\<open>infer_tree_wf\<close>).

    \<^item> Lookups under a substitution: a value entry substitutes, every other
      entry is invariant (and so is exhaustiveness, \<^text>\<open>covers_sapp\<close>).\<close>

declare scomp.simps[simp del]

subsection \<open>Substitution stability of the declarative judgement\<close>

text \<open>The basis side of transporting a typing derivation along a
  substitution \<open>s\<close>. The bound variables of a scheme are a separate sort that
  \<open>tsubst\<close> never touches, so no renaming is needed (as long as the ranges of
  \<open>s\<close> are free of bound variables, \<open>bfree_sub s\<close>). Value entries substitute,
  the other entries are closed and read invariantly:\<close>

lemma tlookup_val_sapp:
  \<open>cenv B \<Longrightarrow> tlookup B p = Some (TEval \<sigma>) \<Longrightarrow> tlookup (sappe s B) p = Some (TEval (sapps s \<sigma>))\<close>
  using tlookup_sappe_val by blast

lemma tlookup_other_sapp:
  \<open>cenv B \<Longrightarrow> tlookup B p = Some e \<Longrightarrow> \<forall>\<sigma>. e \<noteq> TEval \<sigma> \<Longrightarrow> tlookup (sappe s B) p = Some e\<close>
  using tlookup_sappe_other by blast

text \<open>\<open>covers\<close> and the operator-chain tree read only the head stamp of the
  scrutinee and the basis's lookups (both invariant).\<close>

lemma covers_sapp: \<open>cenv B \<Longrightarrow> covers B \<tau> ps \<Longrightarrow> covers (sappe s B) (sapp s \<tau>) ps\<close>
proof -
  assume c: \<open>cenv B\<close> and \<open>covers B \<tau> ps\<close>
  then have \<open>covers B (sapp s \<tau>) ps\<close>
    by (cases \<tau>) (auto simp: covers_def split: prod.split)
  then show \<open>covers (sappe s B) (sapp s \<tau>) ps\<close>
    unfolding covers_eq[OF lookup_eq_sappe[OF c], symmetric] .
qed
lemma sapp_TDep[simp]: \<open>sapp s (TDep i sg K e t) = TDep i sg K (sappr s e) (sapp s t)\<close>
  by (cases s) simp

lemma sapp_TOff[simp]: \<open>sapp s (TOff x r t) = TOff x (sapp s r) (sapp s t)\<close>
  by (cases s) simp

lemma sapp_tuple_from[simp]: \<open>sapp s (tuple_from i \<tau>s) = tuple_from i (map (sapp s) \<tau>s)\<close>
  by (cases s) simp

subsection \<open>Confinement of the expression algorithm\<close>

text \<open>Well-formed inputs to \<open>infer\<close>: the basis is closed and bound-free with
  its abstract types inside \<open>FK\<close>. The ambient row and the pending requests
  mention only variables below the counter and abstract types inside \<open>FK\<close>.\<close>

lemma ftv_pend_append [simp]: \<open>ftv_pend (pd @ pd') = ftv_pend pd \<union> ftv_pend pd'\<close>
  by (auto simp: ftv_pend_def)

lemma frv_pend_append [simp]: \<open>frv_pend (pd @ pd') = frv_pend pd \<union> frv_pend pd'\<close>
  by (auto simp: frv_pend_def)

lemma ftv_pend_mono: \<open>set pd \<subseteq> set pd' \<Longrightarrow> ftv_pend pd \<subseteq> ftv_pend pd'\<close>
  by (auto simp: ftv_pend_def)

lemma frv_pend_mono: \<open>set pd \<subseteq> set pd' \<Longrightarrow> frv_pend pd \<subseteq> frv_pend pd'\<close>
  by (auto simp: frv_pend_def)

lemma ktv_rows_mono: \<open>set pd \<subseteq> set pd' \<Longrightarrow> ktv_rows pd \<subseteq> ktv_rows pd'\<close>
  by (auto simp: ktv_rows_def)

lemma pend_row_bounds:
  assumes m: \<open>(v, POff x r) \<in> set pd\<close>
  shows \<open>ftv r \<subseteq> ftv_pend pd\<close> \<open>frv r \<subseteq> frv_pend pd\<close> \<open>ktv r \<subseteq> ktv_rows pd\<close>
proof -
  have \<open>ftv_preq (POff x r) \<subseteq> ftv_pend pd\<close> \<open>frv_preq (POff x r) \<subseteq> frv_pend pd\<close>
    \<open>ktv_req (POff x r) \<subseteq> ktv_rows pd\<close>
    using m unfolding ftv_pend_def frv_pend_def ktv_rows_def by force+
  then show \<open>ftv r \<subseteq> ftv_pend pd\<close> \<open>frv r \<subseteq> frv_pend pd\<close> \<open>ktv r \<subseteq> ktv_rows pd\<close> by simp_all
qed

lemma ktv_rows_sub_pend:
  assumes kh: \<open>khyg s FK\<close> and pk: \<open>ktv_rows pd \<subseteq> FK\<close>
  shows \<open>ktv_rows (sub_pend s pd) \<subseteq> FK\<close>
proof -
  have \<open>ktv_req (sub_preq s q) \<subseteq> FK\<close> if m: \<open>(v, q) \<in> set pd\<close> for v q
  proof (cases q)
    case (POff l r)
    have \<open>ktv r \<subseteq> FK\<close> using pk m POff by (fastforce simp: ktv_rows_def)
    then show ?thesis using khyg_sapp[OF kh] POff by simp
  qed simp
  then show ?thesis unfolding ktv_rows_def sub_pend_def by fastforce
qed

lemma off_evs_ktv_rows:
  \<open>off_evs n \<tau>\<^sub>0 = (evs, pdo, \<tau>, n') \<Longrightarrow> ktv_rows pdo \<subseteq> ktv \<tau>\<^sub>0\<close>
  by (induction n \<tau>\<^sub>0 arbitrary: evs pdo \<tau> n' rule: off_evs.induct)
     (auto split: prod.split_asm)

definition inwf :: \<open>tenv \<Rightarrow> krow \<Rightarrow> pend \<Rightarrow> tvar set \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>inwf B A pd FK n \<longleftrightarrow>
     cenv B \<and> bfree_env B \<and> ktv_env B \<subseteq> FK \<and> ftv_env B \<subseteq> {..< n} \<and> frv_env B \<subseteq> {..< n} \<and>
     frv_row A \<subseteq> {..< n} \<and> brv_row A = {} \<and>
     ftv_pend pd \<subseteq> {..< n} \<and> frv_pend pd \<subseteq> {..< n} \<and> ktv_rows pd \<subseteq> FK\<close>

definition outwf :: \<open>ksub \<Rightarrow> pend \<Rightarrow> tvar set \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>outwf s pd' FK n' \<longleftrightarrow>
     sconf s {..< n'} {..< n'} \<and> khyg s FK \<and> bfree_sub s \<and>
     ftv_pend pd' \<subseteq> {..< n'} \<and> frv_pend pd' \<subseteq> {..< n'} \<and> ktv_rows pd' \<subseteq> FK\<close>

lemma outwf_sid: \<open>inwf B A pd FK n \<Longrightarrow> outwf sid pd FK n\<close>
  by (auto simp: inwf_def outwf_def)

text \<open>Projecting a substitution to the variables below a bound keeps
  confinement and \<open>bfree\<close>. Its hygiene reduces to the images of the kept
  variables (a module binder drops the dead body variables that carry its
  abstract types).\<close>

lemma sconf_sproj: \<open>sconf s V R \<Longrightarrow> sconf (sproj m s) V R\<close>
  by (auto simp: sconf_def sproj_def)

lemma bfree_sub_sproj: \<open>bfree_sub s \<Longrightarrow> bfree_sub (sproj m s)\<close>
  by (auto simp: bfree_sub_def sproj_def bfree_def)

lemma khyg_sproj: \<open>(\<forall>a < m. ktv (fst s a) \<subseteq> FK) \<Longrightarrow> khyg (sproj m s) FK\<close>
  by (auto simp: khyg_def sproj_def)

lemma bfree_env_param_env: \<open>bfree_env E \<Longrightarrow> bfree_env (param_env E)\<close>
  by (induction E rule: param_env.induct) auto

lemma fresh_ok_TC_nil[simp]: \<open>fresh_ok (TC c []) n\<^sub>0 n FK\<close>
  by (simp add: fresh_ok_def bfree_def)

lemma outwf_sid_mono:
  assumes \<open>inwf B A pd FK n\<close> \<open>n \<le> m\<close>
  shows \<open>outwf sid pd FK m\<close>
  using assms by (fastforce simp: inwf_def outwf_def)

lemma fresh_ok_weaken0: \<open>fresh_ok \<tau> m n' FK \<Longrightarrow> fresh_ok \<tau> 0 n' FK\<close>
  by (auto simp: fresh_ok_def)

lemma sch_inst_fresh:
  assumes ft: \<open>ftv_sch \<sigma> \<subseteq> {..< n}\<close> and fr: \<open>frv_sch \<sigma> \<subseteq> {..< n}\<close>
    and kt: \<open>ktv_sch \<sigma> \<subseteq> FK\<close> and bf: \<open>bfree_sch \<sigma>\<close> and inst: \<open>inst_scheme n \<sigma> = (\<tau>, m)\<close>
  shows \<open>n \<le> m \<and> fresh_ok \<tau> 0 m FK\<close>
proof -
  note w = inst_scheme_wf[OF inst bf]
  have le: \<open>n \<le> m\<close> using w by simp
  have \<open>ftv \<tau> \<subseteq> {..< m}\<close>
    using w ft by (auto simp: subset_iff intro: less_le_trans[OF _ le])
  moreover have \<open>frv \<tau> \<subseteq> {..< m}\<close>
    using w fr by (auto simp: subset_iff intro: less_le_trans[OF _ le])
  ultimately show ?thesis using w kt by (auto simp: fresh_ok_def)
qed

lemma fresh_ok_sapp0:
  assumes f: \<open>fresh_ok \<tau> 0 m FK\<close> and O: \<open>outwf s pd FK n\<close> and le: \<open>m \<le> n\<close>
  shows \<open>fresh_ok (sapp s \<tau>) 0 n FK\<close>
proof -
  from O have sc: \<open>sconf s {..< n} {..< n}\<close> and kh: \<open>khyg s FK\<close> and bf: \<open>bfree_sub s\<close>
    by (auto simp: outwf_def)
  have \<open>fresh_ok \<tau> 0 n FK\<close> using fresh_ok_mono[OF f le_refl le] .
  then show ?thesis using fresh_ok_sapp[of \<tau> 0 n FK s] sc kh bf by (simp add: atLeast0LessThan)
qed

lemma ftv_preq_sub_preq:
  assumes s: \<open>sconf s {..< n} {..< n}\<close> and h: \<open>ftv_preq q \<subseteq> {..< n}\<close>
  shows \<open>ftv_preq (sub_preq s q) \<subseteq> {..< n}\<close>
  using h ftv_sapp_sconf[OF s] by (cases q) (fastforce simp: case_prod_beta)+

lemma ftv_pend_sub_pend:
  assumes s: \<open>sconf s {..< n} {..< n}\<close> and h: \<open>ftv_pend pd \<subseteq> {..< n}\<close>
  shows \<open>ftv_pend (sub_pend s pd) \<subseteq> {..< n}\<close>
  using h ftv_preq_sub_preq[OF s] unfolding ftv_pend_def sub_pend_def by fastforce

lemma frv_preq_sub_preq:
  assumes s: \<open>sconf s {..< n} {..< n}\<close>
    and h: \<open>ftv_preq q \<subseteq> {..< n}\<close> \<open>frv_preq q \<subseteq> {..< n}\<close>
  shows \<open>frv_preq (sub_preq s q) \<subseteq> {..< n}\<close>
  using h frv_sapp_sconf[OF s] by (cases q) (fastforce simp: case_prod_beta)+

lemma frv_pend_sub_pend:
  assumes s: \<open>sconf s {..< n} {..< n}\<close>
    and h: \<open>ftv_pend pd \<subseteq> {..< n}\<close> \<open>frv_pend pd \<subseteq> {..< n}\<close>
  shows \<open>frv_pend (sub_pend s pd) \<subseteq> {..< n}\<close>
  using h frv_preq_sub_preq[OF s] unfolding ftv_pend_def frv_pend_def sub_pend_def by fastforce

lemma outwf_of_uni:
  assumes sc: \<open>sconf s {..< n} {..< n}\<close> and \<open>khyg s FK\<close> \<open>bfree_sub s\<close>
    and ft: \<open>ftv_pend pd \<subseteq> {..< m}\<close> and fr: \<open>frv_pend pd \<subseteq> {..< m}\<close> and le: \<open>m \<le> n\<close>
    and kr: \<open>ktv_rows pd \<subseteq> FK\<close>
  shows \<open>outwf s (sub_pend s pd) FK n\<close>
proof -
  have sub: \<open>{..< m} \<subseteq> {..< n}\<close> using le by simp
  show ?thesis unfolding outwf_def
    using assms ftv_pend_sub_pend[OF sc subset_trans[OF ft sub]]
      frv_pend_sub_pend[OF sc subset_trans[OF ft sub] subset_trans[OF fr sub]]
      ktv_rows_sub_pend[OF \<open>khyg s FK\<close> kr]
    by simp
qed

lemma ktv_env_append[simp]: \<open>ktv_env (E\<^sub>1 @ E\<^sub>2) = ktv_env E\<^sub>1 \<union> ktv_env E\<^sub>2\<close>
  by (induction E\<^sub>1) auto

lemma mono_env_sid[simp]: \<open>mono_env sid \<Gamma> = binders \<Gamma>\<close>
  by (simp add: mono_env_def)

lemma mono_env_binders: \<open>mono_env s \<Gamma> = binders (map (apsnd (sapp s)) \<Gamma>)\<close>
  by (induction \<Gamma>) (auto simp: mono_env_def)

lemma ftv_env_binders: \<open>ftv_env (binders \<Gamma>) = (\<Union>(x, \<tau>)\<in>set \<Gamma>. ftv \<tau>)\<close>
  by (induction \<Gamma>) auto

lemma frv_env_binders: \<open>frv_env (binders \<Gamma>) = (\<Union>(x, \<tau>)\<in>set \<Gamma>. frv \<tau>)\<close>
  by (induction \<Gamma>) auto

lemma ktv_env_binders: \<open>ktv_env (binders \<Gamma>) = (\<Union>(x, \<tau>)\<in>set \<Gamma>. ktv \<tau>)\<close>
  by (induction \<Gamma>) auto

lemma ftv_env_binders_ok: \<open>binds_ok \<Gamma> n n\<^sub>1 FK \<Longrightarrow> ftv_env (binders \<Gamma>) \<subseteq> {n ..< n\<^sub>1}\<close>
  by (fastforce simp: ftv_env_binders binds_ok_def fresh_ok_def)

lemma frv_env_binders_ok: \<open>binds_ok \<Gamma> n n\<^sub>1 FK \<Longrightarrow> frv_env (binders \<Gamma>) \<subseteq> {n ..< n\<^sub>1}\<close>
  by (fastforce simp: frv_env_binders binds_ok_def fresh_ok_def)

lemma ktv_env_binders_ok: \<open>binds_ok \<Gamma> n n\<^sub>1 FK \<Longrightarrow> ktv_env (binders \<Gamma>) \<subseteq> FK\<close>
  by (fastforce simp: ktv_env_binders binds_ok_def fresh_ok_def)

lemma ftv_close_ty_sub: \<open>ftv (close_ty as rs t) \<subseteq> ftv t\<close>
  by (auto simp: close_ty_def ftv_tsubst split: if_split_asm)

lemma frv_close_ty_sub: \<open>frv (close_ty as rs t) \<subseteq> frv t\<close>
  by (auto simp: close_ty_def frv_tsubst frv_tsubst_TV split: if_split_asm)

lemma ktv_close_ty_sub: \<open>ktv (close_ty as rs t) \<subseteq> ktv t\<close>
  using ktv_tsubst[of \<open>\<lambda>a. if a \<in> as then TB a else TV a\<close> \<open>\<lambda>v. if v \<in> rs then RB v else RV v\<close> t]
  by (auto simp: close_ty_def split: if_split_asm)

lemma ftv_sch_close: \<open>ftv_sch (close_sch as rs t) \<subseteq> ftv t\<close>
  using ftv_close_ty_sub by (simp add: close_sch_def)

lemma frv_sch_close: \<open>frv_sch (close_sch as rs t) \<subseteq> frv t\<close>
  using frv_close_ty_sub by (simp add: close_sch_def)

lemma ktv_sch_close: \<open>ktv_sch (close_sch as rs t) \<subseteq> ktv t\<close>
  using ktv_close_ty_sub by (simp add: close_sch_def)

lemma bfree_sch_close[simp]: \<open>bfree_sch (close_sch as rs t)\<close>
  by (simp add: close_sch_def)

lemma ftv_close_ty: \<open>ftv (close_ty as rs t) = ftv t - as\<close>
  by (auto simp: close_ty_def ftv_tsubst split: if_split_asm)

lemma frv_close_ty: \<open>frv (close_ty as rs t) = frv t - rs\<close>
  by (auto simp: close_ty_def frv_tsubst split: if_split_asm)

lemma ftv_sch_close_eq: \<open>ftv_sch (close_sch as rs t) = ftv t - as\<close>
  by (simp add: close_sch_def ftv_close_ty)

lemma frv_sch_close_eq: \<open>frv_sch (close_sch as rs t) = frv t - rs\<close>
  by (simp add: close_sch_def frv_close_ty)

text \<open>A generalised binder frame, what a \<open>let\<close> adds to the basis: the bound
  values' schemes, abstracted over the offset requests \<open>reqs\<close> and closed over
  \<open>as\<close>/\<open>rs\<close>.\<close>

definition gen_env :: \<open>ksub \<Rightarrow> tvar set \<Rightarrow> rvar set \<Rightarrow> reqs \<Rightarrow> (name \<times> kty) list \<Rightarrow> tenv\<close> where
  \<open>gen_env s\<^sub>2 as rs reqs \<Gamma> =
     map (\<lambda>(x, \<tau>). (x, TEval (close_sch as rs (offs reqs (sapp s\<^sub>2 \<tau>))))) \<Gamma>\<close>

lemma cenv_gen_env[simp]: \<open>cenv (gen_env s\<^sub>2 as rs reqs \<Gamma>)\<close>
  by (induction \<Gamma>) (auto simp: gen_env_def)

lemma bfree_env_gen_env[simp]: \<open>bfree_env (gen_env s\<^sub>2 as rs reqs \<Gamma>)\<close>
  by (induction \<Gamma>) (auto simp: gen_env_def)

lemma ftv_env_gen_env:
  \<open>ftv_env (gen_env s\<^sub>2 as rs reqs \<Gamma>)
     \<subseteq> (\<Union>(x, \<tau>)\<in>set \<Gamma>. ftv (sapp s\<^sub>2 \<tau>)) \<union> (\<Union>(v, x, r)\<in>set reqs. ftv r)\<close>
proof (induction \<Gamma>)
  case (Cons a \<Gamma>) obtain x \<tau> where a: \<open>a = (x, \<tau>)\<close> by fastforce
  have \<open>ftv_env (gen_env s\<^sub>2 as rs reqs (a # \<Gamma>))
          = ftv_sch (close_sch as rs (offs reqs (sapp s\<^sub>2 \<tau>))) \<union> ftv_env (gen_env s\<^sub>2 as rs reqs \<Gamma>)\<close>
    by (simp add: gen_env_def a)
  also have \<open>... \<subseteq> ftv (sapp s\<^sub>2 \<tau>) \<union> (\<Union>(v, x, r)\<in>set reqs. ftv r)
                  \<union> ((\<Union>(x, \<tau>)\<in>set \<Gamma>. ftv (sapp s\<^sub>2 \<tau>)) \<union> (\<Union>(v, x, r)\<in>set reqs. ftv r))\<close>
    using ftv_sch_close[of as rs \<open>offs reqs (sapp s\<^sub>2 \<tau>)\<close>, unfolded offs_ftv] Cons by blast
  also have \<open>... = (\<Union>(x, \<tau>)\<in>set (a # \<Gamma>). ftv (sapp s\<^sub>2 \<tau>)) \<union> (\<Union>(v, x, r)\<in>set reqs. ftv r)\<close>
    by (auto simp: a)
  finally show ?case .
qed (simp add: gen_env_def)

lemma frv_env_gen_env:
  \<open>frv_env (gen_env s\<^sub>2 as rs reqs \<Gamma>)
     \<subseteq> (\<Union>(x, \<tau>)\<in>set \<Gamma>. frv (sapp s\<^sub>2 \<tau>)) \<union> (\<Union>(v, x, r)\<in>set reqs. frv r)\<close>
proof (induction \<Gamma>)
  case (Cons a \<Gamma>) obtain x \<tau> where a: \<open>a = (x, \<tau>)\<close> by fastforce
  have \<open>frv_env (gen_env s\<^sub>2 as rs reqs (a # \<Gamma>))
          = frv_sch (close_sch as rs (offs reqs (sapp s\<^sub>2 \<tau>))) \<union> frv_env (gen_env s\<^sub>2 as rs reqs \<Gamma>)\<close>
    by (simp add: gen_env_def a)
  also have \<open>... \<subseteq> frv (sapp s\<^sub>2 \<tau>) \<union> (\<Union>(v, x, r)\<in>set reqs. frv r)
                  \<union> ((\<Union>(x, \<tau>)\<in>set \<Gamma>. frv (sapp s\<^sub>2 \<tau>)) \<union> (\<Union>(v, x, r)\<in>set reqs. frv r))\<close>
    using frv_sch_close[of as rs \<open>offs reqs (sapp s\<^sub>2 \<tau>)\<close>, unfolded offs_frv] Cons by blast
  also have \<open>... = (\<Union>(x, \<tau>)\<in>set (a # \<Gamma>). frv (sapp s\<^sub>2 \<tau>)) \<union> (\<Union>(v, x, r)\<in>set reqs. frv r)\<close>
    by (auto simp: a)
  finally show ?case .
qed (simp add: gen_env_def)

lemma ktv_env_gen_env:
  \<open>ktv_env (gen_env s\<^sub>2 as rs reqs \<Gamma>)
     \<subseteq> (\<Union>(x, \<tau>)\<in>set \<Gamma>. ktv (sapp s\<^sub>2 \<tau>)) \<union> (\<Union>(v, x, r)\<in>set reqs. ktv r)\<close>
proof (induction \<Gamma>)
  case (Cons a \<Gamma>) obtain x \<tau> where a: \<open>a = (x, \<tau>)\<close> by fastforce
  have \<open>ktv_env (gen_env s\<^sub>2 as rs reqs (a # \<Gamma>))
          = ktv_sch (close_sch as rs (offs reqs (sapp s\<^sub>2 \<tau>))) \<union> ktv_env (gen_env s\<^sub>2 as rs reqs \<Gamma>)\<close>
    by (simp add: gen_env_def a)
  also have \<open>... \<subseteq> ktv (sapp s\<^sub>2 \<tau>) \<union> (\<Union>(v, x, r)\<in>set reqs. ktv r)
                  \<union> ((\<Union>(x, \<tau>)\<in>set \<Gamma>. ktv (sapp s\<^sub>2 \<tau>)) \<union> (\<Union>(v, x, r)\<in>set reqs. ktv r))\<close>
    using ktv_sch_close[of as rs \<open>offs reqs (sapp s\<^sub>2 \<tau>)\<close>, unfolded offs_ktv] Cons by blast
  also have \<open>... = (\<Union>(x, \<tau>)\<in>set (a # \<Gamma>). ktv (sapp s\<^sub>2 \<tau>)) \<union> (\<Union>(v, x, r)\<in>set reqs. ktv r)\<close>
    by (auto simp: a)
  finally show ?case .
qed (simp add: gen_env_def)

lemma binds_ok_sapp0:
  assumes bo: \<open>binds_ok \<Gamma> n n\<^sub>1 FK\<close> and sc: \<open>sconf s {..< m} {..< m}\<close>
    and kh: \<open>khyg s FK\<close> and bf: \<open>bfree_sub s\<close> and le: \<open>n\<^sub>1 \<le> m\<close>
  shows \<open>binds_ok (map (apsnd (sapp s)) \<Gamma>) 0 m FK\<close>
  unfolding binds_ok_def
proof (intro allI impI)
  fix x t assume \<open>(x, t) \<in> set (map (apsnd (sapp s)) \<Gamma>)\<close>
  then obtain t\<^sub>0 where mem: \<open>(x, t\<^sub>0) \<in> set \<Gamma>\<close> and t: \<open>t = sapp s t\<^sub>0\<close> by auto
  have \<open>fresh_ok t\<^sub>0 n n\<^sub>1 FK\<close> using bo mem by (auto simp: binds_ok_def)
  then have f0: \<open>fresh_ok t\<^sub>0 0 m FK\<close> by (rule fresh_ok_mono[OF _ le0 le])
  have sc0: \<open>sconf s {0 ..< m} {0 ..< m}\<close> using sc by (simp add: atLeast0LessThan)
  show \<open>fresh_ok t 0 m FK\<close> unfolding t by (rule fresh_ok_sapp[OF f0 sc0 kh bf])
qed

text \<open>Carrying \<^const>\<open>inwf\<close> along a run: after a step's substitution, the
  basis extended by the step's binders (\<open>binders\<close>) or by a generalised frame
  (\<^const>\<open>gen_env\<close>) is well formed at the new counter. \<^const>\<open>outwf\<close> composes.\<close>

lemma inwf_binders:
  assumes I: \<open>inwf B A pd FK n\<close>
    and sc: \<open>sconf s {..< n\<^sub>1} {..< n\<^sub>1}\<close> and kh: \<open>khyg s FK\<close> and bf: \<open>bfree_sub s\<close>
    and bo: \<open>binds_ok \<Gamma> 0 n\<^sub>1 FK\<close>
    and af: \<open>frv_row A' \<subseteq> {..< m}\<close> and ab: \<open>brv_row A' = {}\<close>
    and pf: \<open>ftv_pend pd' \<subseteq> {..< m}\<close> and pr: \<open>frv_pend pd' \<subseteq> {..< m}\<close>
    and pk: \<open>ktv_rows pd' \<subseteq> FK\<close>
    and le: \<open>n \<le> n\<^sub>1\<close> and le2: \<open>n\<^sub>1 \<le> m\<close>
  shows \<open>inwf (binders \<Gamma> @ sappe s B) A' pd' FK m\<close>
proof -
  have subnn1: \<open>{..< n} \<subseteq> {..< n\<^sub>1}\<close> using le by simp
  have subn1m: \<open>{..< n\<^sub>1} \<subseteq> {..< m}\<close> using le2 by simp
  from I have iC: \<open>cenv B\<close> and iB: \<open>bfree_env B\<close> and iK: \<open>ktv_env B \<subseteq> FK\<close>
    and iFt0: \<open>ftv_env B \<subseteq> {..< n}\<close> and iFr0: \<open>frv_env B \<subseteq> {..< n}\<close> by (auto simp: inwf_def)
  have iFt: \<open>ftv_env B \<subseteq> {..< n\<^sub>1}\<close> using subset_trans[OF iFt0 subnn1] .
  have iFr: \<open>frv_env B \<subseteq> {..< n\<^sub>1}\<close> using subset_trans[OF iFr0 subnn1] .
  have esf: \<open>ftv_env (sappe s B) \<subseteq> {..< m}\<close>
    using subset_trans[OF ftv_sappe_sconf[OF sc iFt] subn1m] .
  have esr: \<open>frv_env (sappe s B) \<subseteq> {..< m}\<close>
    using subset_trans[OF frv_sappe_sconf[OF sc iFt iFr] subn1m] .
  have fb: \<open>ftv_env (binders \<Gamma>) \<subseteq> {..< m}\<close>
    using subset_trans[OF ftv_env_binders_ok[OF bo, unfolded atLeast0LessThan] subn1m] .
  have rb: \<open>frv_env (binders \<Gamma>) \<subseteq> {..< m}\<close>
    using subset_trans[OF frv_env_binders_ok[OF bo, unfolded atLeast0LessThan] subn1m] .
  show ?thesis unfolding inwf_def
    using cenv_binders cenv_sappe[OF iC] bfree_env_binders[OF bo] bfree_env_sappe[OF bf iB]
      ktv_env_binders_ok[OF bo] ktv_env_sappe[OF kh iK]
      fb esf rb esr af ab pf pr pk by simp
qed

lemma fresh_ok_TFn:
  \<open>fresh_ok \<tau>\<^sub>1 0 n' FK \<Longrightarrow> fresh_ok \<tau>\<^sub>2 0 n' FK \<Longrightarrow> frv_row \<epsilon> \<subseteq> {..< n'} \<Longrightarrow> brv_row \<epsilon> = {}
     \<Longrightarrow> fresh_ok (TFn \<tau>\<^sub>1 \<epsilon> \<tau>\<^sub>2) 0 n' FK\<close>
  by (auto simp: fresh_ok_def bfree_def)

lemma fresh_ok_fn_ty:
  \<open>(\<forall>\<tau> \<in> set \<tau>s. fresh_ok \<tau> 0 n' FK) \<Longrightarrow> fresh_ok (fn_ty \<tau>s) 0 n' FK\<close>
  by (cases \<tau>s rule: fn_ty.cases) (auto simp: fresh_ok_tuple fresh_ok_def bfree_def)

lemma gen_env_bounds:
  assumes bo: \<open>binds_ok \<Gamma> 0 m FK\<close> and sc2: \<open>sconf s\<^sub>2 {..< m} {..< m}\<close> and kh2: \<open>khyg s\<^sub>2 FK\<close>
    and rk: \<open>\<And>v x r. (v, x, r) \<in> set reqs \<Longrightarrow> ftv r \<subseteq> {..< m} \<and> frv r \<subseteq> {..< m} \<and> ktv r \<subseteq> FK\<close>
  shows \<open>ftv_env (gen_env s\<^sub>2 as rs reqs \<Gamma>) \<subseteq> {..< m}\<close>
    and \<open>frv_env (gen_env s\<^sub>2 as rs reqs \<Gamma>) \<subseteq> {..< m}\<close>
    and \<open>ktv_env (gen_env s\<^sub>2 as rs reqs \<Gamma>) \<subseteq> FK\<close>
proof -
  have ft: \<open>ftv \<tau> \<subseteq> {..< m}\<close> and fr: \<open>frv \<tau> \<subseteq> {..< m}\<close> and kt: \<open>ktv \<tau> \<subseteq> FK\<close>
    if \<open>(x, \<tau>) \<in> set \<Gamma>\<close> for x \<tau>
    using bo that by (auto simp: binds_ok_def fresh_ok_def atLeast0LessThan)
  have A: \<open>(\<Union>(x, \<tau>)\<in>set \<Gamma>. ftv (sapp s\<^sub>2 \<tau>)) \<subseteq> {..< m}\<close>
    using ft ftv_sapp_sconf[OF sc2] by (fastforce simp: subset_iff)
  have B: \<open>(\<Union>(x, \<tau>)\<in>set \<Gamma>. frv (sapp s\<^sub>2 \<tau>)) \<subseteq> {..< m}\<close>
    using ft fr frv_sapp_sconf[OF sc2] by (fastforce simp: subset_iff)
  have C: \<open>(\<Union>(x, \<tau>)\<in>set \<Gamma>. ktv (sapp s\<^sub>2 \<tau>)) \<subseteq> FK\<close>
    using kt khyg_sapp[OF kh2] by (fastforce simp: subset_iff)
  have RA: \<open>(\<Union>(v, x, r)\<in>set reqs. ftv r) \<subseteq> {..< m}\<close>
    and RB: \<open>(\<Union>(v, x, r)\<in>set reqs. frv r) \<subseteq> {..< m}\<close>
    and RC: \<open>(\<Union>(v, x, r)\<in>set reqs. ktv r) \<subseteq> FK\<close>
    using rk by fastforce+
  show \<open>ftv_env (gen_env s\<^sub>2 as rs reqs \<Gamma>) \<subseteq> {..< m}\<close>
    using subset_trans[OF ftv_env_gen_env Un_mono[OF A RA]] by simp
  show \<open>frv_env (gen_env s\<^sub>2 as rs reqs \<Gamma>) \<subseteq> {..< m}\<close>
    using subset_trans[OF frv_env_gen_env Un_mono[OF B RB]] by simp
  show \<open>ktv_env (gen_env s\<^sub>2 as rs reqs \<Gamma>) \<subseteq> FK\<close>
    using subset_trans[OF ktv_env_gen_env Un_mono[OF C RC]] by simp
qed

lemma inwf_let:
  assumes I: \<open>inwf B A pd FK n\<close>
    and scs: \<open>sconf s {..< m} {..< m}\<close> and khs: \<open>khyg s FK\<close> and bfs: \<open>bfree_sub s\<close>
    and sc2: \<open>sconf s\<^sub>2 {..< m} {..< m}\<close> and kh2: \<open>khyg s\<^sub>2 FK\<close>
    and bo: \<open>binds_ok \<Gamma> 0 m FK\<close>
    and af: \<open>frv_row A' \<subseteq> {..< m}\<close> and ab: \<open>brv_row A' = {}\<close>
    and pf: \<open>ftv_pend pd' \<subseteq> {..< m}\<close> and pr: \<open>frv_pend pd' \<subseteq> {..< m}\<close>
    and pk: \<open>ktv_rows pd' \<subseteq> FK\<close>
    and rk: \<open>\<And>v x r. (v, x, r) \<in> set reqs \<Longrightarrow> ftv r \<subseteq> {..< m} \<and> frv r \<subseteq> {..< m} \<and> ktv r \<subseteq> FK\<close>
    and le: \<open>n \<le> m\<close>
  shows \<open>inwf (gen_env s\<^sub>2 as rs reqs \<Gamma> @ sappe s B) A' pd' FK m\<close>
proof -
  have subn: \<open>{..< n} \<subseteq> {..< m}\<close> using le by simp
  from I have iC: \<open>cenv B\<close> and iB: \<open>bfree_env B\<close> and iK: \<open>ktv_env B \<subseteq> FK\<close>
    and iFt: \<open>ftv_env B \<subseteq> {..< n}\<close> and iFr: \<open>frv_env B \<subseteq> {..< n}\<close> by (auto simp: inwf_def)
  note gb = gen_env_bounds[OF bo sc2 kh2 rk]
  show ?thesis unfolding inwf_def
    using cenv_gen_env cenv_sappe[OF iC] bfree_env_gen_env bfree_env_sappe[OF bfs iB]
      gb(3) ktv_env_sappe[OF khs iK]
      gb(1) ftv_sappe_sconf[OF scs subset_trans[OF iFt subn]]
      gb(2) frv_sappe_sconf[OF scs subset_trans[OF iFt subn] subset_trans[OF iFr subn]]
      af ab pf pr pk by simp
qed

text \<open>The rows a \<open>let\<close> abstracts over come from its pending requests, whichever
  branch of generalisation it takes:\<close>

lemma gen_choice_pend:
  assumes \<open>(as, rs, reqs, pdr) =
    (if c then (if d then gen_off B A pd n \<tau>
                else (case gen_p B A pd n \<tau> of (as, rs) \<Rightarrow> (as, rs, [], pd)))
     else ({}, {}, [], pd))\<close>
  shows \<open>set pdr \<subseteq> set pd\<close> and \<open>\<And>v x r. (v, x, r) \<in> set reqs \<Longrightarrow> (v, POff x r) \<in> set pd\<close>
  using assms gen_off_pend[of B A pd n \<tau> as rs reqs pdr]
  by (auto split: if_split_asm prod.split_asm)

lemma reqs_bounds:
  assumes rq: \<open>\<And>v x r. (v, x, r) \<in> set reqs \<Longrightarrow> (v, POff x r) \<in> set pd\<close>
    and pf: \<open>ftv_pend pd \<subseteq> {..< m}\<close> and pr: \<open>frv_pend pd \<subseteq> {..< m}\<close> and pk: \<open>ktv_rows pd \<subseteq> FK\<close>
  shows \<open>(v, x, r) \<in> set reqs \<Longrightarrow> ftv r \<subseteq> {..< m} \<and> frv r \<subseteq> {..< m} \<and> ktv r \<subseteq> FK\<close>
  using pend_row_bounds[OF rq] pf pr pk by blast

lemma inwf_amb:
  assumes \<open>inwf B A pd FK n\<close> \<open>frv_row A' \<subseteq> {..< n}\<close> \<open>brv_row A' = {}\<close>
  shows \<open>inwf B A' pd FK n\<close>
  using assms by (auto simp: inwf_def)

lemma inwf_mk:
  assumes I: \<open>inwf B A pd FK n\<close>
    and sc: \<open>sconf s {..< m} {..< m}\<close> and kh: \<open>khyg s FK\<close> and bf: \<open>bfree_sub s\<close>
    and af: \<open>frv_row A' \<subseteq> {..< m}\<close> and ab: \<open>brv_row A' = {}\<close>
    and pf: \<open>ftv_pend pd' \<subseteq> {..< m}\<close> and pr: \<open>frv_pend pd' \<subseteq> {..< m}\<close>
    and pk: \<open>ktv_rows pd' \<subseteq> FK\<close>
    and le: \<open>n \<le> m\<close>
  shows \<open>inwf (sappe s B) (sappr s A') pd' FK m\<close>
proof -
  have sub: \<open>{..< n} \<subseteq> {..< m}\<close> using le by simp
  from I have iC: \<open>cenv B\<close> and iB: \<open>bfree_env B\<close> and iK: \<open>ktv_env B \<subseteq> FK\<close>
    and iFt: \<open>ftv_env B \<subseteq> {..< n}\<close> and iFr: \<open>frv_env B \<subseteq> {..< n}\<close> by (auto simp: inwf_def)
  show ?thesis unfolding inwf_def
    using cenv_sappe[OF iC] bfree_env_sappe[OF bf iB] ktv_env_sappe[OF kh iK]
      ftv_sappe_sconf[OF sc subset_trans[OF iFt sub]]
      frv_sappe_sconf[OF sc subset_trans[OF iFt sub] subset_trans[OF iFr sub]]
      frv_sappr_sconf[OF sc af] bfree_sappr[OF bf ab] pf pr pk by simp
qed

lemma fresh_ty_fresh_ok:
  \<open>fresh_ty ([], []) n n' B \<tau> \<Longrightarrow> ktv_env B \<subseteq> FK \<Longrightarrow> fresh_ok \<tau> n n' FK\<close>
  by (auto simp: fresh_ty_def fresh_ok_def tvars_def rvars_def)

lemma inwf_bump:
  assumes I: \<open>inwf B A pd FK n\<close> and le: \<open>n \<le> m\<close> shows \<open>inwf B A pd FK m\<close>
proof -
  have sub: \<open>{..< n} \<subseteq> {..< m}\<close> using le by simp
  show ?thesis using I subset_trans[OF _ sub] by (auto simp: inwf_def)
qed

lemma inwf_step:
  assumes I: \<open>inwf B A pd FK n\<close> and O: \<open>outwf s pd' FK n'\<close> and le: \<open>n \<le> n'\<close>
  shows \<open>inwf (sappe s B) (sappr s A) pd' FK n'\<close>
proof -
  have sub: \<open>{..< n} \<subseteq> {..< n'}\<close> using le by simp
  from I have iC: \<open>cenv B\<close> and iB: \<open>bfree_env B\<close> and iK: \<open>ktv_env B \<subseteq> FK\<close>
    and iFt: \<open>ftv_env B \<subseteq> {..< n}\<close> and iFr: \<open>frv_env B \<subseteq> {..< n}\<close>
    and iA: \<open>frv_row A \<subseteq> {..< n}\<close> and iBA: \<open>brv_row A = {}\<close> by (auto simp: inwf_def)
  from O have oS: \<open>sconf s {..< n'} {..< n'}\<close> and oK: \<open>khyg s FK\<close> and oBf: \<open>bfree_sub s\<close>
    by (auto simp: outwf_def)
  have ft: \<open>ftv_env (sappe s B) \<subseteq> {..< n'}\<close>
    by (rule ftv_sappe_sconf[OF oS subset_trans[OF iFt sub]])
  have fr: \<open>frv_env (sappe s B) \<subseteq> {..< n'}\<close>
    by (rule frv_sappe_sconf[OF oS subset_trans[OF iFt sub] subset_trans[OF iFr sub]])
  have fa: \<open>frv_row (sappr s A) \<subseteq> {..< n'}\<close>
    by (rule frv_sappr_sconf[OF oS subset_trans[OF iA sub]])
  show ?thesis unfolding inwf_def
    using cenv_sappe[OF iC] bfree_env_sappe[OF oBf iB] ktv_env_sappe[OF oK iK]
          ft fr fa bfree_sappr[OF oBf iBA] O by (auto simp: outwf_def)
qed

lemma outwf_scomp:
  assumes O1: \<open>outwf s\<^sub>1 pd\<^sub>1 FK n\<^sub>1\<close> and O2: \<open>outwf s\<^sub>2 pd\<^sub>2 FK n\<^sub>2\<close> and le: \<open>n\<^sub>1 \<le> n\<^sub>2\<close>
  shows \<open>outwf (s\<^sub>2 \<odot> s\<^sub>1) pd\<^sub>2 FK n\<^sub>2\<close>
proof -
  have sub: \<open>{..< n\<^sub>1} \<subseteq> {..< n\<^sub>2}\<close> using le by simp
  from O1 have s1: \<open>sconf s\<^sub>1 {..< n\<^sub>1} {..< n\<^sub>1}\<close> and k1: \<open>khyg s\<^sub>1 FK\<close> and b1: \<open>bfree_sub s\<^sub>1\<close>
    by (auto simp: outwf_def)
  from O2 have s2: \<open>sconf s\<^sub>2 {..< n\<^sub>2} {..< n\<^sub>2}\<close> and k2: \<open>khyg s\<^sub>2 FK\<close> and b2: \<open>bfree_sub s\<^sub>2\<close>
    by (auto simp: outwf_def)
  show ?thesis unfolding outwf_def
    using sconf_scomp_mono[OF s1 s2 sub sub] khyg_scomp[OF k1 k2] bfree_sub_scomp[OF b1 b2] O2
    by (auto simp: outwf_def)
qed

lemma cs_map_bounds:
  assumes \<open>\<forall>\<tau> \<in> set \<tau>s. fresh_ok \<tau> 0 k FK\<close>
  shows \<open>ftv_cs (map (\<lambda>\<tau>. (\<tau>, TV k)) \<tau>s) \<subseteq> {0 ..< Suc k}\<close>
    and \<open>frv_cs (map (\<lambda>\<tau>. (\<tau>, TV k)) \<tau>s) \<subseteq> {0 ..< Suc k}\<close>
    and \<open>ktv_cs (map (\<lambda>\<tau>. (\<tau>, TV k)) \<tau>s) \<subseteq> FK\<close>
    and \<open>bfree_cs (map (\<lambda>\<tau>. (\<tau>, TV k)) \<tau>s)\<close>
proof -
  have ft: \<open>ftv \<tau> \<subseteq> {0 ..< k}\<close> and fr: \<open>frv \<tau> \<subseteq> {0 ..< k}\<close> and kt: \<open>ktv \<tau> \<subseteq> FK\<close>
    and bf: \<open>bfree \<tau>\<close> if \<open>\<tau> \<in> set \<tau>s\<close> for \<tau>
    using assms that by (auto simp: fresh_ok_def)
  show \<open>ftv_cs (map (\<lambda>\<tau>. (\<tau>, TV k)) \<tau>s) \<subseteq> {0 ..< Suc k}\<close>
    unfolding ftv_cs_def by (auto dest: ft[THEN subsetD])
  show \<open>frv_cs (map (\<lambda>\<tau>. (\<tau>, TV k)) \<tau>s) \<subseteq> {0 ..< Suc k}\<close>
    unfolding frv_cs_def by (auto dest: fr[THEN subsetD])
  show \<open>ktv_cs (map (\<lambda>\<tau>. (\<tau>, TV k)) \<tau>s) \<subseteq> FK\<close>
    unfolding ktv_cs_def by (auto dest: kt[THEN subsetD])
  show \<open>bfree_cs (map (\<lambda>\<tau>. (\<tau>, TV k)) \<tau>s)\<close>
    unfolding bfree_cs_def using bf by (auto simp: bfree_def)
qed

lemma fresh_ok_TV: \<open>k < n' \<Longrightarrow> fresh_ok (TV k) 0 n' FK\<close>
  by (auto simp: fresh_ok_def bfree_def)

lemma val_inst_fresh:
  assumes cenvB: \<open>cenv B\<close> and bfB: \<open>bfree_env B\<close> and ktvB: \<open>ktv_env B \<subseteq> FK\<close>
    and ftvB: \<open>ftv_env B \<subseteq> {..< m}\<close> and frvB: \<open>frv_env B \<subseteq> {..< m}\<close>
    and sc: \<open>sconf s {..< m} {..< m}\<close> and kh: \<open>khyg s FK\<close> and bf: \<open>bfree_sub s\<close>
    and lk: \<open>tlookup (sappe s B) p = Some (TEval \<sigma>')\<close> and inst: \<open>inst_scheme m \<sigma>' = (\<tau>, m')\<close>
  shows \<open>m \<le> m' \<and> fresh_ok \<tau> 0 m' FK\<close>
proof -
  from tlookup_sappe_val[OF cenvB] lk obtain \<sigma> where
    \<sigma>: \<open>tlookup B p = Some (TEval \<sigma>)\<close> and \<sigma>': \<open>\<sigma>' = sapps s \<sigma>\<close> by blast
  have f1: \<open>ftv_sch \<sigma> \<subseteq> {..< m}\<close> using ftv_env_tlookup[OF \<sigma>] ftvB by simp
  have f2: \<open>frv_sch \<sigma> \<subseteq> {..< m}\<close> using frv_env_tlookup[OF \<sigma>] frvB by simp
  have k1: \<open>ktv_sch \<sigma> \<subseteq> FK\<close> using ktv_env_tlookup[OF \<sigma>] ktvB by simp
  have b1: \<open>bfree_sch \<sigma>\<close> using bfree_env_tlookup[OF bfB \<sigma>] by simp
  have ftv': \<open>ftv_sch \<sigma>' \<subseteq> {..< m}\<close> unfolding \<sigma>' by (rule ftv_sapps_sconf[OF sc f1])
  have frv': \<open>frv_sch \<sigma>' \<subseteq> {..< m}\<close> unfolding \<sigma>' by (rule frv_sapps_sconf[OF sc f1 f2])
  have ktv': \<open>ktv_sch \<sigma>' \<subseteq> FK\<close>
    unfolding \<sigma>' using ktv_sub_scheme[of \<open>fst s\<close> \<open>snd s\<close> FK \<sigma>] kh k1 by (cases s) auto
  have bfr': \<open>bfree_sch \<sigma>'\<close>
    unfolding \<sigma>' using bfree_sub_scheme[of \<open>fst s\<close> \<open>snd s\<close> \<sigma>] bf b1 by (cases s) auto
  show ?thesis by (rule sch_inst_fresh[OF ftv' frv' ktv' bfr' inst])
qed

text \<open>Operator chains: the tree \<^const>\<open>infer_tree\<close> builds over the operands
  keeps the counter monotone and returns a well-formed output and a fresh
  type.\<close>

lemma infer_tree_wf:
  \<open>infer_tree uf B A \<tau>s tr n = Some (s, \<tau>, n') \<Longrightarrow>
     cenv B \<Longrightarrow> bfree_env B \<Longrightarrow> ktv_env B \<subseteq> FK \<Longrightarrow> ftv_env B \<subseteq> {..< n} \<Longrightarrow> frv_env B \<subseteq> {..< n} \<Longrightarrow>
     frv_row A \<subseteq> {..< n} \<Longrightarrow> brv_row A = {} \<Longrightarrow> (\<forall>\<tau> \<in> set \<tau>s. fresh_ok \<tau> 0 n FK) \<Longrightarrow>
     n \<le> n' \<and> sconf s {..< n'} {..< n'} \<and> khyg s FK \<and> bfree_sub s \<and> fresh_ok \<tau> 0 n' FK\<close>
proof (induction uf B A \<tau>s tr n arbitrary: s \<tau> n' rule: infer_tree_induct)
  case (Leaf uf B A \<tau>s i n)
  then show ?case using nth_mem[of i \<tau>s] by (auto split: if_split_asm)
next
  case (Node_OVar uf B A \<tau>s v l r n)
  have run: \<open>infer_tree uf B A \<tau>s (Node (OVar v) l r) n = Some (s, \<tau>, n')\<close>
    and cB: \<open>cenv B\<close> and bB: \<open>bfree_env B\<close> and kB: \<open>ktv_env B \<subseteq> FK\<close>
    and fB: \<open>ftv_env B \<subseteq> {..< n}\<close> and rB: \<open>frv_env B \<subseteq> {..< n}\<close>
    and fA: \<open>frv_row A \<subseteq> {..< n}\<close> and bA: \<open>brv_row A = {}\<close>
    and fts: \<open>\<forall>\<tau> \<in> set \<tau>s. fresh_ok \<tau> 0 n FK\<close>
    using Node_OVar.prems by blast+
  obtain s\<^sub>1 \<tau>\<^sub>l n\<^sub>1 where t1: \<open>infer_tree uf B A \<tau>s l n = Some (s\<^sub>1, \<tau>\<^sub>l, n\<^sub>1)\<close>
  proof (cases \<open>infer_tree uf B A \<tau>s l n\<close>)
    case None then show ?thesis using run by simp
  next
    case (Some r0) then show ?thesis using that by (cases r0) auto
  qed
  obtain s\<^sub>2 \<tau>\<^sub>r n\<^sub>2 where
    t2: \<open>infer_tree uf (sappe s\<^sub>1 B) (sappr s\<^sub>1 A) (map (sapp s\<^sub>1) \<tau>s) r n\<^sub>1 = Some (s\<^sub>2, \<tau>\<^sub>r, n\<^sub>2)\<close>
  proof (cases \<open>infer_tree uf (sappe s\<^sub>1 B) (sappr s\<^sub>1 A) (map (sapp s\<^sub>1) \<tau>s) r n\<^sub>1\<close>)
    case None then show ?thesis using run
      by (simp add: t1 del: sapp.simps sappe.simps sappr.simps)
  next
    case (Some r0) then show ?thesis using that by (cases r0) auto
  qed
  obtain \<sigma> where lk: \<open>tlookup (sappe (s\<^sub>2 \<odot> s\<^sub>1) B) [v] = Some (TEval \<sigma>)\<close>
  proof (cases \<open>tlookup (sappe (s\<^sub>2 \<odot> s\<^sub>1) B) [v]\<close>)
    case None then show ?thesis using run
      by (simp add: t1 t2 del: sapp.simps sappe.simps sappr.simps)
  next
    case (Some ent) show ?thesis
    proof (cases ent)
      case (TEval \<sigma>) then show ?thesis using Some that by simp
    qed (use run Some t1 t2 in
           \<open>simp_all del: sapp.simps sappe.simps sappr.simps\<close>)
  qed
  have lkm: \<open>map_of (sappe (s\<^sub>2 \<odot> s\<^sub>1) B) v = Some (TEval \<sigma>)\<close> using lk by simp
  obtain \<tau>\<^sub>f n\<^sub>3 where inst: \<open>inst_scheme n\<^sub>2 \<sigma> = (\<tau>\<^sub>f, n\<^sub>3)\<close> by (cases \<open>inst_scheme n\<^sub>2 \<sigma>\<close>) auto
  obtain s\<^sub>3 n\<^sub>4 where
    u1: \<open>uni uf \<tau>\<^sub>f (TFn (tuple [sapp s\<^sub>2 \<tau>\<^sub>l, \<tau>\<^sub>r]) (sappr (s\<^sub>2 \<odot> s\<^sub>1) A) (TV n\<^sub>3)) (Suc n\<^sub>3)
      = Some (s\<^sub>3, n\<^sub>4)\<close>
    and se: \<open>s = s\<^sub>3 \<odot> s\<^sub>2 \<odot> s\<^sub>1\<close> \<open>\<tau> = sapp s\<^sub>3 (TV n\<^sub>3)\<close> \<open>n' = n\<^sub>4\<close>
  proof (cases \<open>uni uf \<tau>\<^sub>f (TFn (tuple [sapp s\<^sub>2 \<tau>\<^sub>l, \<tau>\<^sub>r]) (sappr (s\<^sub>2 \<odot> s\<^sub>1) A) (TV n\<^sub>3)) (Suc n\<^sub>3)\<close>)
    case None then show ?thesis using run
      by (simp add: t1 t2 lkm inst del: sapp.simps sappe.simps sappr.simps)
  next
    case (Some r0) then show ?thesis using that run
      by (cases r0)
        (auto simp: t1 t2 lkm inst simp del: sapp.simps sappe.simps sappr.simps)
  qed
  have wl: \<open>n \<le> n\<^sub>1 \<and> sconf s\<^sub>1 {..< n\<^sub>1} {..< n\<^sub>1} \<and> khyg s\<^sub>1 FK \<and> bfree_sub s\<^sub>1 \<and>
      fresh_ok \<tau>\<^sub>l 0 n\<^sub>1 FK\<close>
    using t1 cB bB kB fB rB fA bA fts by (rule Node_OVar.IH)
  have le1: \<open>n \<le> n\<^sub>1\<close> using wl by simp
  have sc1: \<open>sconf s\<^sub>1 {..< n\<^sub>1} {..< n\<^sub>1}\<close> and kh1: \<open>khyg s\<^sub>1 FK\<close> and bf1: \<open>bfree_sub s\<^sub>1\<close>
    and f\<tau>l: \<open>fresh_ok \<tau>\<^sub>l 0 n\<^sub>1 FK\<close> using wl by simp_all
  have subn1: \<open>{..< n} \<subseteq> {..< n\<^sub>1}\<close> using le1 by simp
  have fts1: \<open>\<forall>t \<in> set (map (sapp s\<^sub>1) \<tau>s). fresh_ok t 0 n\<^sub>1 FK\<close>
  proof (rule ballI)
    fix t assume \<open>t \<in> set (map (sapp s\<^sub>1) \<tau>s)\<close>
    then obtain t0 where t0: \<open>t0 \<in> set \<tau>s\<close> \<open>t = sapp s\<^sub>1 t0\<close> by auto
    have \<open>fresh_ok t0 0 n\<^sub>1 FK\<close>
      using fts t0(1) fresh_ok_mono[of t0 0 n FK 0 n\<^sub>1] le1 by auto
    then show \<open>fresh_ok t 0 n\<^sub>1 FK\<close> unfolding t0(2)
      by (rule fresh_ok_sapp[OF _ sc1[folded atLeast0LessThan] kh1 bf1])
  qed
  have wr: \<open>n\<^sub>1 \<le> n\<^sub>2 \<and> sconf s\<^sub>2 {..< n\<^sub>2} {..< n\<^sub>2} \<and> khyg s\<^sub>2 FK \<and> bfree_sub s\<^sub>2 \<and>
      fresh_ok \<tau>\<^sub>r 0 n\<^sub>2 FK\<close>
    using t1 refl refl t2 cenv_sappe[OF cB] bfree_env_sappe[OF bf1 bB] ktv_env_sappe[OF kh1 kB]
      ftv_sappe_sconf[OF sc1 subset_trans[OF fB subn1]]
      frv_sappe_sconf[OF sc1 subset_trans[OF fB subn1] subset_trans[OF rB subn1]]
      frv_sappr_sconf[OF sc1 subset_trans[OF fA subn1]] bfree_sappr[OF bf1 bA] fts1
    by (rule Node_OVar.IH)
  have le2: \<open>n\<^sub>1 \<le> n\<^sub>2\<close> using wr by simp
  have sc2: \<open>sconf s\<^sub>2 {..< n\<^sub>2} {..< n\<^sub>2}\<close> and kh2: \<open>khyg s\<^sub>2 FK\<close> and bf2: \<open>bfree_sub s\<^sub>2\<close>
    and f\<tau>r: \<open>fresh_ok \<tau>\<^sub>r 0 n\<^sub>2 FK\<close> using wr by simp_all
  have subn12: \<open>{..< n\<^sub>1} \<subseteq> {..< n\<^sub>2}\<close> using le2 by simp
  have subn2: \<open>{..< n} \<subseteq> {..< n\<^sub>2}\<close> using subn1 subn12 by simp
  have scs: \<open>sconf (s\<^sub>2 \<odot> s\<^sub>1) {..< n\<^sub>2} {..< n\<^sub>2}\<close>
    by (rule sconf_scomp_mono[OF sc1 sc2 subn12 subn12])
  have khs: \<open>khyg (s\<^sub>2 \<odot> s\<^sub>1) FK\<close> by (rule khyg_scomp[OF kh1 kh2])
  have bfs: \<open>bfree_sub (s\<^sub>2 \<odot> s\<^sub>1)\<close> by (rule bfree_sub_scomp[OF bf1 bf2])
  note wv = val_inst_fresh[OF cB bB kB subset_trans[OF fB subn2] subset_trans[OF rB subn2]
      scs khs bfs lk inst]
  have le3: \<open>n\<^sub>2 \<le> n\<^sub>3\<close> using wv by simp
  have f\<tau>f: \<open>fresh_ok \<tau>\<^sub>f 0 n\<^sub>3 FK\<close> using wv by simp
  have ln23: \<open>n\<^sub>2 \<le> Suc n\<^sub>3\<close> using le3 by simp
  have subn2s: \<open>{..< n\<^sub>2} \<subseteq> {..< Suc n\<^sub>3}\<close> using le3 by simp
  have ftgt:
    \<open>fresh_ok (TFn (tuple [sapp s\<^sub>2 \<tau>\<^sub>l, \<tau>\<^sub>r]) (sappr (s\<^sub>2 \<odot> s\<^sub>1) A) (TV n\<^sub>3)) 0 (Suc n\<^sub>3) FK\<close>
  proof (rule fresh_ok_TFn)
    have a: \<open>fresh_ok (sapp s\<^sub>2 \<tau>\<^sub>l) 0 n\<^sub>2 FK\<close>
      by (rule fresh_ok_sapp[OF fresh_ok_mono[OF f\<tau>l le0 le2] sc2[folded atLeast0LessThan]
            kh2 bf2])
    show \<open>fresh_ok (tuple [sapp s\<^sub>2 \<tau>\<^sub>l, \<tau>\<^sub>r]) 0 (Suc n\<^sub>3) FK\<close>
      by (rule fresh_ok_tuple) (use a f\<tau>r fresh_ok_mono[OF _ le0 ln23] in auto)
    show \<open>fresh_ok (TV n\<^sub>3) 0 (Suc n\<^sub>3) FK\<close> by (rule fresh_ok_TV) simp
    show \<open>frv_row (sappr (s\<^sub>2 \<odot> s\<^sub>1) A) \<subseteq> {..< Suc n\<^sub>3}\<close>
      by (rule subset_trans[OF frv_sappr_sconf[OF scs subset_trans[OF fA subn2]]
            subn2s])
    show \<open>brv_row (sappr (s\<^sub>2 \<odot> s\<^sub>1) A) = {}\<close> by (rule bfree_sappr[OF bfs bA])
  qed
  have ln33: \<open>n\<^sub>3 \<le> Suc n\<^sub>3\<close> by simp
  note wu = uni_fresh[OF u1 fresh_ok_mono[OF f\<tau>f le0 ln33] ftgt le0]
  have le4: \<open>Suc n\<^sub>3 \<le> n\<^sub>4\<close> using wu by simp
  have sc3: \<open>sconf s\<^sub>3 {..< n\<^sub>4} {..< n\<^sub>4}\<close> and kh3: \<open>khyg s\<^sub>3 FK\<close> and bf3: \<open>bfree_sub s\<^sub>3\<close>
    using wu by (auto simp: atLeast0LessThan)
  have subn24: \<open>{..< n\<^sub>2} \<subseteq> {..< n\<^sub>4}\<close> using le3 le4 by simp
  have le: \<open>n \<le> n'\<close> using le1 le2 le3 le4 se by simp
  have scfin: \<open>sconf (s\<^sub>3 \<odot> s\<^sub>2 \<odot> s\<^sub>1) {..< n\<^sub>4} {..< n\<^sub>4}\<close>
    using sconf_scomp_mono[OF scs sc3 subn24 subn24] by (simp add: scomp_assoc)
  have khfin: \<open>khyg (s\<^sub>3 \<odot> s\<^sub>2 \<odot> s\<^sub>1) FK\<close> by (simp add: khyg_scomp khs kh3 scomp_assoc)
  have bffin: \<open>bfree_sub (s\<^sub>3 \<odot> s\<^sub>2 \<odot> s\<^sub>1)\<close>
    by (simp add: bfree_sub_scomp bfs bf3 scomp_assoc)
  have f\<tau>: \<open>fresh_ok (sapp s\<^sub>3 (TV n\<^sub>3)) 0 n\<^sub>4 FK\<close>
    by (rule fresh_ok_sapp[OF fresh_ok_TV[of n\<^sub>3 n\<^sub>4] sc3[folded atLeast0LessThan] kh3 bf3])
      (use le4 in simp)
  show ?case using se le scfin khfin bffin f\<tau> by simp
next
  case (Node_OCon uf B A \<tau>s c l r n)
  have run: \<open>infer_tree uf B A \<tau>s (Node (OCon c) l r) n = Some (s, \<tau>, n')\<close>
    and cB: \<open>cenv B\<close> and bB: \<open>bfree_env B\<close> and kB: \<open>ktv_env B \<subseteq> FK\<close>
    and fB: \<open>ftv_env B \<subseteq> {..< n}\<close> and rB: \<open>frv_env B \<subseteq> {..< n}\<close>
    and fA: \<open>frv_row A \<subseteq> {..< n}\<close> and bA: \<open>brv_row A = {}\<close>
    and fts: \<open>\<forall>\<tau> \<in> set \<tau>s. fresh_ok \<tau> 0 n FK\<close>
    using Node_OCon.prems by blast+
  obtain s\<^sub>1 \<tau>\<^sub>l n\<^sub>1 where t1: \<open>infer_tree uf B A \<tau>s l n = Some (s\<^sub>1, \<tau>\<^sub>l, n\<^sub>1)\<close>
  proof (cases \<open>infer_tree uf B A \<tau>s l n\<close>)
    case None then show ?thesis using run by simp
  next
    case (Some r0) then show ?thesis using that by (cases r0) auto
  qed
  obtain s\<^sub>2 \<tau>\<^sub>r n\<^sub>2 where
    t2: \<open>infer_tree uf (sappe s\<^sub>1 B) (sappr s\<^sub>1 A) (map (sapp s\<^sub>1) \<tau>s) r n\<^sub>1 = Some (s\<^sub>2, \<tau>\<^sub>r, n\<^sub>2)\<close>
  proof (cases \<open>infer_tree uf (sappe s\<^sub>1 B) (sappr s\<^sub>1 A) (map (sapp s\<^sub>1) \<tau>s) r n\<^sub>1\<close>)
    case None then show ?thesis using run
      by (simp add: t1 del: sapp.simps sappe.simps sappr.simps)
  next
    case (Some r0) then show ?thesis using that by (cases r0) auto
  qed
  obtain \<sigma> where lk: \<open>tlookup (sappe (s\<^sub>2 \<odot> s\<^sub>1) B) [c] = Some (TEcon \<sigma> 2)\<close>
  proof (cases \<open>tlookup (sappe (s\<^sub>2 \<odot> s\<^sub>1) B) [c]\<close>)
    case None then show ?thesis using run
      by (simp add: t1 t2 del: sapp.simps sappe.simps sappr.simps)
  next
    case (Some ent) show ?thesis
    proof (cases ent)
      case (TEcon \<sigma> m) show ?thesis
      proof (cases \<open>m = 2\<close>)
        case True then show ?thesis using TEcon Some that by simp
      next
        case False then show ?thesis using run Some TEcon
          by (simp add: t1 t2 del: sapp.simps sappe.simps sappr.simps)
      qed
    qed (use run Some t1 t2 in
           \<open>simp_all del: sapp.simps sappe.simps sappr.simps\<close>)
  qed
  have lkm: \<open>map_of (sappe (s\<^sub>2 \<odot> s\<^sub>1) B) c = Some (TEcon \<sigma> 2)\<close> using lk by simp
  have lkB: \<open>tlookup B [c] = Some (TEcon \<sigma> 2)\<close>
    using lk tlookup_sappe_other[OF cB, of \<open>TEcon \<sigma> 2\<close> \<open>s\<^sub>2 \<odot> s\<^sub>1\<close> \<open>[c]\<close>] by simp
  obtain \<tau>\<^sub>c n\<^sub>3 where inst: \<open>inst_scheme n\<^sub>2 \<sigma> = (\<tau>\<^sub>c, n\<^sub>3)\<close> by (cases \<open>inst_scheme n\<^sub>2 \<sigma>\<close>) auto
  obtain s\<^sub>3 n\<^sub>4 where
    u1: \<open>uni uf \<tau>\<^sub>c (TFn (sapp s\<^sub>2 \<tau>\<^sub>l) (RV n\<^sub>3) (TFn \<tau>\<^sub>r (RV (Suc n\<^sub>3)) (TV (Suc (Suc n\<^sub>3)))))
             (Suc (Suc (Suc n\<^sub>3))) = Some (s\<^sub>3, n\<^sub>4)\<close>
    and se: \<open>s = s\<^sub>3 \<odot> s\<^sub>2 \<odot> s\<^sub>1\<close> \<open>\<tau> = sapp s\<^sub>3 (TV (Suc (Suc n\<^sub>3)))\<close> \<open>n' = n\<^sub>4\<close>
  proof (cases \<open>uni uf \<tau>\<^sub>c (TFn (sapp s\<^sub>2 \<tau>\<^sub>l) (RV n\<^sub>3) (TFn \<tau>\<^sub>r (RV (Suc n\<^sub>3)) (TV (Suc (Suc n\<^sub>3)))))
                  (Suc (Suc (Suc n\<^sub>3)))\<close>)
    case None then show ?thesis using run
      by (simp add: t1 t2 lkm inst del: sapp.simps sappe.simps sappr.simps)
  next
    case (Some r0) then show ?thesis using that run
      by (cases r0)
        (auto simp: t1 t2 lkm inst simp del: sapp.simps sappe.simps sappr.simps)
  qed
  have wl: \<open>n \<le> n\<^sub>1 \<and> sconf s\<^sub>1 {..< n\<^sub>1} {..< n\<^sub>1} \<and> khyg s\<^sub>1 FK \<and> bfree_sub s\<^sub>1 \<and>
      fresh_ok \<tau>\<^sub>l 0 n\<^sub>1 FK\<close>
    using t1 cB bB kB fB rB fA bA fts by (rule Node_OCon.IH)
  have le1: \<open>n \<le> n\<^sub>1\<close> using wl by simp
  have sc1: \<open>sconf s\<^sub>1 {..< n\<^sub>1} {..< n\<^sub>1}\<close> and kh1: \<open>khyg s\<^sub>1 FK\<close> and bf1: \<open>bfree_sub s\<^sub>1\<close>
    and f\<tau>l: \<open>fresh_ok \<tau>\<^sub>l 0 n\<^sub>1 FK\<close> using wl by simp_all
  have subn1: \<open>{..< n} \<subseteq> {..< n\<^sub>1}\<close> using le1 by simp
  have fts1: \<open>\<forall>t \<in> set (map (sapp s\<^sub>1) \<tau>s). fresh_ok t 0 n\<^sub>1 FK\<close>
  proof (rule ballI)
    fix t assume \<open>t \<in> set (map (sapp s\<^sub>1) \<tau>s)\<close>
    then obtain t0 where t0: \<open>t0 \<in> set \<tau>s\<close> \<open>t = sapp s\<^sub>1 t0\<close> by auto
    have \<open>fresh_ok t0 0 n\<^sub>1 FK\<close>
      using fts t0(1) fresh_ok_mono[of t0 0 n FK 0 n\<^sub>1] le1 by auto
    then show \<open>fresh_ok t 0 n\<^sub>1 FK\<close> unfolding t0(2)
      by (rule fresh_ok_sapp[OF _ sc1[folded atLeast0LessThan] kh1 bf1])
  qed
  have wr: \<open>n\<^sub>1 \<le> n\<^sub>2 \<and> sconf s\<^sub>2 {..< n\<^sub>2} {..< n\<^sub>2} \<and> khyg s\<^sub>2 FK \<and> bfree_sub s\<^sub>2 \<and>
      fresh_ok \<tau>\<^sub>r 0 n\<^sub>2 FK\<close>
    using t1 refl refl t2 cenv_sappe[OF cB] bfree_env_sappe[OF bf1 bB] ktv_env_sappe[OF kh1 kB]
      ftv_sappe_sconf[OF sc1 subset_trans[OF fB subn1]]
      frv_sappe_sconf[OF sc1 subset_trans[OF fB subn1] subset_trans[OF rB subn1]]
      frv_sappr_sconf[OF sc1 subset_trans[OF fA subn1]] bfree_sappr[OF bf1 bA] fts1
    by (rule Node_OCon.IH)
  have le2: \<open>n\<^sub>1 \<le> n\<^sub>2\<close> using wr by simp
  have sc2: \<open>sconf s\<^sub>2 {..< n\<^sub>2} {..< n\<^sub>2}\<close> and kh2: \<open>khyg s\<^sub>2 FK\<close> and bf2: \<open>bfree_sub s\<^sub>2\<close>
    and f\<tau>r: \<open>fresh_ok \<tau>\<^sub>r 0 n\<^sub>2 FK\<close> using wr by simp_all
  have subn12: \<open>{..< n\<^sub>1} \<subseteq> {..< n\<^sub>2}\<close> using le2 by simp
  have scs: \<open>sconf (s\<^sub>2 \<odot> s\<^sub>1) {..< n\<^sub>2} {..< n\<^sub>2}\<close>
    by (rule sconf_scomp_mono[OF sc1 sc2 subn12 subn12])
  have khs: \<open>khyg (s\<^sub>2 \<odot> s\<^sub>1) FK\<close> by (rule khyg_scomp[OF kh1 kh2])
  have bfs: \<open>bfree_sub (s\<^sub>2 \<odot> s\<^sub>1)\<close> by (rule bfree_sub_scomp[OF bf1 bf2])
  note wv = con_inst_fresh[OF cB bB kB lkB inst]
  have le3: \<open>n\<^sub>2 \<le> n\<^sub>3\<close> using wv by simp
  have f\<tau>c: \<open>fresh_ok \<tau>\<^sub>c n\<^sub>2 n\<^sub>3 FK\<close> using wv by simp
  have le23: \<open>n\<^sub>2 \<le> Suc (Suc (Suc n\<^sub>3))\<close> using le3 by simp
  have le33: \<open>n\<^sub>3 \<le> Suc (Suc (Suc n\<^sub>3))\<close> by simp
  have ftgt: \<open>fresh_ok (TFn (sapp s\<^sub>2 \<tau>\<^sub>l) (RV n\<^sub>3) (TFn \<tau>\<^sub>r (RV (Suc n\<^sub>3)) (TV (Suc (Suc n\<^sub>3)))))
                0 (Suc (Suc (Suc n\<^sub>3))) FK\<close>
  proof (rule fresh_ok_TFn)
    show \<open>fresh_ok (sapp s\<^sub>2 \<tau>\<^sub>l) 0 (Suc (Suc (Suc n\<^sub>3))) FK\<close>
    proof (rule fresh_ok_mono[OF _ le0 le23])
      show \<open>fresh_ok (sapp s\<^sub>2 \<tau>\<^sub>l) 0 n\<^sub>2 FK\<close>
        by (rule fresh_ok_sapp[OF fresh_ok_mono[OF f\<tau>l le0 le2] sc2[folded atLeast0LessThan]
              kh2 bf2])
    qed
    show \<open>fresh_ok (TFn \<tau>\<^sub>r (RV (Suc n\<^sub>3)) (TV (Suc (Suc n\<^sub>3)))) 0 (Suc (Suc (Suc n\<^sub>3))) FK\<close>
    proof (rule fresh_ok_TFn)
      show \<open>fresh_ok \<tau>\<^sub>r 0 (Suc (Suc (Suc n\<^sub>3))) FK\<close>
        by (rule fresh_ok_mono[OF f\<tau>r le0]) (use le2 le3 in simp)
      show \<open>fresh_ok (TV (Suc (Suc n\<^sub>3))) 0 (Suc (Suc (Suc n\<^sub>3))) FK\<close> by (rule fresh_ok_TV) simp
      show \<open>frv_row (RV (Suc n\<^sub>3)) \<subseteq> {..< Suc (Suc (Suc n\<^sub>3))}\<close> by simp
      show \<open>brv_row (RV (Suc n\<^sub>3)) = {}\<close> by simp
    qed
    show \<open>frv_row (RV n\<^sub>3) \<subseteq> {..< Suc (Suc (Suc n\<^sub>3))}\<close> by simp
    show \<open>brv_row (RV n\<^sub>3) = {}\<close> by simp
  qed
  note wu = uni_fresh[OF u1 fresh_ok_mono[OF f\<tau>c le0 le33] ftgt le0]
  have le4: \<open>Suc (Suc (Suc n\<^sub>3)) \<le> n\<^sub>4\<close> using wu by simp
  have sc3: \<open>sconf s\<^sub>3 {..< n\<^sub>4} {..< n\<^sub>4}\<close> and kh3: \<open>khyg s\<^sub>3 FK\<close> and bf3: \<open>bfree_sub s\<^sub>3\<close>
    using wu by (auto simp: atLeast0LessThan)
  have subn24: \<open>{..< n\<^sub>2} \<subseteq> {..< n\<^sub>4}\<close> using le3 le4 by simp
  have le: \<open>n \<le> n'\<close> using le1 le2 le3 le4 se by simp
  have scfin: \<open>sconf (s\<^sub>3 \<odot> s\<^sub>2 \<odot> s\<^sub>1) {..< n\<^sub>4} {..< n\<^sub>4}\<close>
    using sconf_scomp_mono[OF scs sc3 subn24 subn24] by (simp add: scomp_assoc)
  have khfin: \<open>khyg (s\<^sub>3 \<odot> s\<^sub>2 \<odot> s\<^sub>1) FK\<close> by (simp add: khyg_scomp khs kh3 scomp_assoc)
  have bffin: \<open>bfree_sub (s\<^sub>3 \<odot> s\<^sub>2 \<odot> s\<^sub>1)\<close>
    by (simp add: bfree_sub_scomp bfs bf3 scomp_assoc)
  have f\<tau>: \<open>fresh_ok (sapp s\<^sub>3 (TV (Suc (Suc n\<^sub>3)))) 0 n\<^sub>4 FK\<close>
    by (rule fresh_ok_sapp[OF fresh_ok_TV[of \<open>Suc (Suc n\<^sub>3)\<close> n\<^sub>4] sc3[folded atLeast0LessThan]
          kh3 bf3])
       (use le4 in simp)
  show ?case using se le scfin khfin bffin f\<tau> by simp
qed

lemma ftv_foldr_arrow:
  \<open>ftv (foldr (\<lambda>(t, r) acc. TFn t (RV r) acc) trs b) = (\<Union>(t, r)\<in>set trs. ftv t) \<union> ftv b\<close>
  by (induction trs) (auto split: prod.splits)

lemma frv_foldr_arrow:
  \<open>frv (foldr (\<lambda>(t, r) acc. TFn t (RV r) acc) trs b) = (\<Union>(t, r)\<in>set trs. frv t \<union> {r}) \<union> frv b\<close>
  by (induction trs) (auto split: prod.splits)

lemma ktv_foldr_arrow:
  \<open>ktv (foldr (\<lambda>(t, r) acc. TFn t (RV r) acc) trs b) = (\<Union>(t, r)\<in>set trs. ktv t) \<union> ktv b\<close>
  by (induction trs) (auto split: prod.splits)

text \<open>A datatype's constructor entries: each scheme is closed over the
  parameters \<open>ps\<close> and the fresh row variables of its arrows. Everything else
  comes from the annotation environment, the fresh range or the basis.\<close>

lemma cons_stat_wf:
  \<open>cons_stat B ve ps c n alts = Some (es, n') \<Longrightarrow> cenv B \<Longrightarrow> tve_ok ve \<Longrightarrow>
     n \<le> n' \<and> ftv_env es \<subseteq> tvars ve \<union> set ps \<union> {n ..< n'} \<and> frv_env es \<subseteq> rvars ve \<union> {n ..< n'} \<and>
     ktv_env es \<subseteq> ktv_env B \<and> bfree_env es\<close>
proof (induction alts arbitrary: n es n')
  case (Cons cna alts)
  have cB: \<open>cenv B\<close> and tok: \<open>tve_ok ve\<close> using Cons.prems by blast+
  obtain cn args where cna: \<open>cna = (cn, args)\<close> by (cases cna)
  obtain ts tvs\<^sub>2 rvs\<^sub>2 n\<^sub>1 where as: \<open>atoms_stat B False ve n args = Some (ts, (tvs\<^sub>2, rvs\<^sub>2), n\<^sub>1)\<close>
  proof (cases \<open>atoms_stat B False ve n args\<close>)
    case None then show ?thesis using Cons.prems cna by simp
  next
    case (Some r) then show ?thesis using that by (cases r) auto
  qed
  define rws where \<open>rws = [n\<^sub>1 ..< n\<^sub>1 + length ts]\<close>
  define \<tau> where \<open>\<tau> = foldr (\<lambda>(t, r) acc. TFn t (RV r) acc) (zip ts rws) (TC c (map TV ps))\<close>
  obtain es' n\<^sub>2 where rec: \<open>cons_stat B ve ps c (n\<^sub>1 + length ts) alts = Some (es', n\<^sub>2)\<close>
    and es: \<open>es =
      (n_txt cn, TEcon (close_sch (set ps) (set [n ..< n\<^sub>1 + length ts]) \<tau>) (length ts)) # es'\<close>
    and n'2: \<open>n' = n\<^sub>2\<close>
  proof (cases \<open>cons_stat B ve ps c (n\<^sub>1 + length ts) alts\<close>)
    case None then show ?thesis using Cons.prems cna as
      by (simp add: bind_eq_Some_conv Let_def rws_def \<tau>_def)
  next
    case (Some r) then show ?thesis using that Cons.prems cna as
      by (cases r) (auto simp: bind_eq_Some_conv Let_def rws_def \<tau>_def)
  qed
  note w = atoms_stat_wf[OF as cB tok]
  have le1: \<open>n \<le> n\<^sub>1\<close> using tve_step_le[OF w[THEN conjunct1]] .
  have fts: \<open>\<forall>t\<in>set ts. ftv t \<subseteq> tvars ve \<union> {n ..< n\<^sub>1} \<and>
      frv t \<subseteq> rvars ve \<union> {n ..< n\<^sub>1} \<and> ktv t \<subseteq> ktv_env B \<and> bfree t\<close>
    using w[THEN conjunct2] unfolding fresh_ty_def by simp
  have ftsF: \<open>t \<in> set ts \<Longrightarrow> frv t \<subseteq> rvars ve \<union> {n ..< n\<^sub>1}\<close> for t using fts by blast
  have zt: \<open>(t, r) \<in> set (zip ts rws) \<Longrightarrow> t \<in> set ts\<close> for t r by (auto dest: set_zip_leftD)
  have zr: \<open>(t, r) \<in> set (zip ts rws) \<Longrightarrow> r \<in> {n\<^sub>1 ..< n\<^sub>1 + length ts}\<close> for t r
    by (auto dest: set_zip_rightD simp: rws_def)
  have bt: \<open>ftv (TC c (map TV ps)) = set ps\<close> by (induction ps) auto
  have br: \<open>frv (TC c (map TV ps)) = {}\<close> by (induction ps) auto
  have bk: \<open>ktv (TC c (map TV ps)) = {}\<close> by (induction ps) auto
  have z1: \<open>(\<Union>(t, r)\<in>set (zip ts rws). ftv t) \<subseteq> tvars ve \<union> {n ..< n\<^sub>1}\<close>
    by (rule UN_least) (use fts zt in auto)
  have z24:
    \<open>(\<Union>(t, r)\<in>set (zip ts rws). frv t \<union> {r}) \<subseteq> rvars ve \<union> {n ..< n\<^sub>1 + length ts}\<close>
  proof (rule UN_least)
    fix x assume xin: \<open>x \<in> set (zip ts rws)\<close>
    obtain t r where x: \<open>x = (t, r)\<close> by (cases x)
    have t: \<open>t \<in> set ts\<close> using zt xin x by simp
    have r: \<open>r \<in> {n\<^sub>1 ..< n\<^sub>1 + length ts}\<close> using zr xin x by simp
    show \<open>(case x of (t, r) \<Rightarrow> frv t \<union> {r}) \<subseteq> rvars ve \<union> {n ..< n\<^sub>1 + length ts}\<close>
      unfolding x using ftsF[OF t] r le1 by auto
  qed
  have z3: \<open>(\<Union>(t, r)\<in>set (zip ts rws). ktv t) \<subseteq> ktv_env B\<close>
    by (rule UN_least) (use fts zt in auto)
  have ft\<tau>: \<open>ftv \<tau> \<subseteq> tvars ve \<union> set ps \<union> {n ..< n\<^sub>1}\<close>
    unfolding \<tau>_def ftv_foldr_arrow bt using z1 by auto
  have fr\<tau>: \<open>frv \<tau> \<subseteq> rvars ve \<union> {n ..< n\<^sub>1 + length ts}\<close>
    unfolding \<tau>_def frv_foldr_arrow br using z24 by auto
  have kt\<tau>: \<open>ktv \<tau> \<subseteq> ktv_env B\<close>
    unfolding \<tau>_def ktv_foldr_arrow bk using z3 by auto
  note ih = Cons.IH[OF rec cB tok]
  have le2: \<open>n\<^sub>1 + length ts \<le> n\<^sub>2\<close> using ih by simp
  have le: \<open>n \<le> n'\<close> using le1 le2 n'2 by simp
  have sub1: \<open>{n ..< n\<^sub>1} \<subseteq> {n ..< n'}\<close> using le1 le2 n'2 by auto
  have sub2: \<open>{n ..< n\<^sub>1 + length ts} \<subseteq> {n ..< n'}\<close> using le2 n'2 by auto
  have e1: \<open>ftv_sch (close_sch (set ps) (set [n ..< n\<^sub>1 + length ts]) \<tau>)
      \<subseteq> tvars ve \<union> set ps \<union> {n ..< n'}\<close>
    by (rule subset_trans[OF subset_trans[OF ftv_sch_close ft\<tau>] Un_mono[OF subset_refl sub1]])
  have e2: \<open>frv_sch (close_sch (set ps) (set [n ..< n\<^sub>1 + length ts]) \<tau>)
      \<subseteq> rvars ve \<union> {n ..< n'}\<close>
    by (rule subset_trans[OF subset_trans[OF frv_sch_close fr\<tau>] Un_mono[OF subset_refl sub2]])
  have e3: \<open>ktv_sch (close_sch (set ps) (set [n ..< n\<^sub>1 + length ts]) \<tau>) \<subseteq> ktv_env B\<close>
    by (rule subset_trans[OF ktv_sch_close kt\<tau>])
  have subrec: \<open>{n\<^sub>1 + length ts ..< n\<^sub>2} \<subseteq> {n ..< n'}\<close> using le1 n'2 by auto
  have Cftv: \<open>ftv_env es \<subseteq> tvars ve \<union> set ps \<union> {n ..< n'}\<close>
  proof -
    have \<open>ftv_env es =
        ftv_sch (close_sch (set ps) (set [n ..< n\<^sub>1 + length ts]) \<tau>) \<union> ftv_env es'\<close>
      unfolding es by simp
    then show ?thesis using e1 ih subrec n'2 by auto
  qed
  have Cfrv: \<open>frv_env es \<subseteq> rvars ve \<union> {n ..< n'}\<close>
  proof -
    have \<open>frv_env es =
        frv_sch (close_sch (set ps) (set [n ..< n\<^sub>1 + length ts]) \<tau>) \<union> frv_env es'\<close>
      unfolding es by simp
    then show ?thesis using e2 ih subrec n'2 by auto
  qed
  have Cktv: \<open>ktv_env es \<subseteq> ktv_env B\<close>
  proof -
    have \<open>ktv_env es =
        ktv_sch (close_sch (set ps) (set [n ..< n\<^sub>1 + length ts]) \<tau>) \<union> ktv_env es'\<close>
      unfolding es by simp
    then show ?thesis using e3 ih by auto
  qed
  have Cbfree: \<open>bfree_env es\<close> using ih unfolding es by simp
  show ?case using le Cftv Cfrv Cktv Cbfree by blast
qed simp

text \<open>A closed annotation (\<open>fr\<close> false) mints no variables: its type only
  mentions the type variables in scope, and the scope is unchanged.\<close>

lemma head_stat_closed:
  assumes h: \<open>head_stat B False (tvs, rvs) n p args = Some (\<tau>, ve', n')\<close> and cB: \<open>cenv B\<close>
    and ar: \<open>\<forall>t \<in> set args. ftv t \<subseteq> tvars (tvs, rvs) \<and> frv t \<subseteq> rvars (tvs, rvs)\<close>
  shows \<open>ftv \<tau> \<subseteq> tvars (tvs, rvs) \<and> frv \<tau> \<subseteq> rvars (tvs, rvs) \<and> ve' = (tvs, rvs) \<and> n' = n\<close>
proof -
  have tv: \<open>\<Union>(ftv ` set args) \<subseteq> tvars (tvs, rvs)\<close> and rv: \<open>\<Union>(frv ` set args) \<subseteq> rvars (tvs, rvs)\<close>
    using ar by auto
  show ?thesis
  proof (cases \<open>tlookup B (path_nms p)\<close>)
    case (Some e)
    show ?thesis
    proof (cases e)
      case (TEtyp d)
      from h Some TEtyp obtain \<open>tydef_arity d = length args\<close> \<open>\<tau> = tydef_app d args\<close>
        \<open>ve' = (tvs, rvs)\<close> \<open>n' = n\<close> by (auto split: if_split_asm)
      moreover have cl: \<open>ftv_tydef d = {}\<close> \<open>frv_tydef d = {}\<close>
        using cenv_tlookup_nonval[OF cB Some[unfolded TEtyp]] by auto
      moreover have \<open>ftv (tydef_app d args) \<subseteq> tvars (tvs, rvs)\<close>
        using tydef_app_ftv[of d args] cl(1) tv by blast
      moreover have \<open>frv (tydef_app d args) \<subseteq> rvars (tvs, rvs)\<close>
        using tydef_app_frv[of d args] cl(2) rv by blast
      ultimately show ?thesis by simp
    qed (use h Some in \<open>simp_all\<close>)
  next
    case None
    with h obtain a t where a: \<open>path_nms p = [a]\<close> \<open>map_of tvs a = Some t\<close>
      \<open>\<tau> = foldl tapp t args\<close> \<open>ve' = (tvs, rvs)\<close> \<open>n' = n\<close>
      by (auto split: list.split_asm option.split_asm if_split_asm)
    have mem: \<open>(a, t) \<in> set tvs\<close> using a(2) by (rule map_of_SomeD)
    have ft: \<open>ftv t \<subseteq> tvars (tvs, rvs)\<close> using mem by (force simp: tvars_def)
    have fr: \<open>frv t \<subseteq> rvars (tvs, rvs)\<close> using mem unfolding rvars_def by fastforce
    show ?thesis using a ft fr tv rv by (simp add: foldl_tapp_vars)
  qed
qed

lemma ty_stat_closed:
  \<open>ty_stat B fr ve n t = Some (\<tau>, ve', n') \<Longrightarrow> cenv B \<Longrightarrow> \<not> fr \<Longrightarrow>
     ftv \<tau> \<subseteq> tvars ve \<and> frv \<tau> \<subseteq> rvars ve \<and> ve' = ve\<close>
  \<open>atoms_stat B fr ve n as = Some (\<tau>s, ve', n') \<Longrightarrow> cenv B \<Longrightarrow> \<not> fr \<Longrightarrow>
     (\<forall>\<tau> \<in> set \<tau>s. ftv \<tau> \<subseteq> tvars ve \<and> frv \<tau> \<subseteq> rvars ve) \<and> ve' = ve\<close>
  \<open>atom_stat B fr ve n a = Some (\<tau>, ve', n') \<Longrightarrow> cenv B \<Longrightarrow> \<not> fr \<Longrightarrow>
     ftv \<tau> \<subseteq> tvars ve \<and> frv \<tau> \<subseteq> rvars ve \<and> ve' = ve\<close>
  \<open>tys_stat B fr ve n ts = Some (\<tau>s, ve', n') \<Longrightarrow> cenv B \<Longrightarrow> \<not> fr \<Longrightarrow>
     (\<forall>\<tau> \<in> set \<tau>s. ftv \<tau> \<subseteq> tvars ve \<and> frv \<tau> \<subseteq> rvars ve) \<and> ve' = ve\<close>
  \<open>spine_stat B fr ve n as = Some (\<tau>, ve', n') \<Longrightarrow> cenv B \<Longrightarrow> \<not> fr \<Longrightarrow>
     ftv \<tau> \<subseteq> tvars ve \<and> frv \<tau> \<subseteq> rvars ve \<and> ve' = ve\<close>
  \<open>row_stat B fr ve n ro = Some (r, ve', n') \<Longrightarrow> cenv B \<Longrightarrow> \<not> fr \<Longrightarrow>
     frv_row r \<subseteq> rvars ve \<and> ve' = ve\<close>
proof (induction B fr ve n t and B fr ve n as and B fr ve n a and B fr ve n ts and B fr ve n as
       and B fr ve n ro
       arbitrary: \<tau> ve' n' and \<tau>s ve' n' and \<tau> ve' n' and \<tau>s ve' n' and \<tau> ve' n' and r ve' n'
       rule: ty_stat_induct)
  case (ty_stat_TArrow B fr ve n as ro t)
  have cB: \<open>cenv B\<close> and nfr: \<open>\<not> fr\<close> using ty_stat_TArrow.prems by blast+
  from ty_stat_TArrow.prems obtain t\<^sub>1 ve\<^sub>1 n\<^sub>1 e ve\<^sub>2 n\<^sub>2 t\<^sub>2 where
    sp: \<open>spine_stat B fr ve n as = Some (t\<^sub>1, ve\<^sub>1, n\<^sub>1)\<close> and
    ro: \<open>row_stat B fr ve\<^sub>1 n\<^sub>1 ro = Some (e, ve\<^sub>2, n\<^sub>2)\<close> and
    tt: \<open>ty_stat B fr ve\<^sub>2 n\<^sub>2 t = Some (t\<^sub>2, ve', n')\<close> and \<tau>: \<open>\<tau> = TFn t\<^sub>1 e t\<^sub>2\<close>
    by (auto split: Option.bind_split_asm prod.split_asm)
  have ih1: \<open>ftv t\<^sub>1 \<subseteq> tvars ve \<and> frv t\<^sub>1 \<subseteq> rvars ve \<and> ve\<^sub>1 = ve\<close>
    using sp cB nfr by (rule ty_stat_TArrow.IH)
  have ih2: \<open>frv_row e \<subseteq> rvars ve\<^sub>1 \<and> ve\<^sub>2 = ve\<^sub>1\<close>
    using sp refl refl ro cB nfr by (rule ty_stat_TArrow.IH)
  have ih3: \<open>ftv t\<^sub>2 \<subseteq> tvars ve\<^sub>2 \<and> frv t\<^sub>2 \<subseteq> rvars ve\<^sub>2 \<and> ve' = ve\<^sub>2\<close>
    using sp refl refl ro refl refl tt cB nfr by (rule ty_stat_TArrow.IH)
  from ih1 ih2 ih3 have veq: \<open>ve\<^sub>1 = ve\<close> \<open>ve\<^sub>2 = ve\<close> \<open>ve' = ve\<close> by simp_all
  show ?case unfolding \<tau> using ih1 ih2 ih3 veq by auto
next
  case (ty_stat_TArrowMod B fr ve n b t)
  have cB: \<open>cenv B\<close> and nfr: \<open>\<not> fr\<close> using ty_stat_TArrowMod.prems by blast+
  obtain p T E n\<^sub>1 t' where
    sg: \<open>mbind_sig b = SPath p []\<close> and lk: \<open>tlookup B (path_nms p) = Some (TEsig (T, E))\<close> and
    ok: \<open>abs_ok T E\<close> and
    tt: \<open>ty_stat
      ((mbind_nm b, TEstr (param_env (real_env (dep_vars T [n ..< n + length T]) E))) # B)
      fr ve (n + length T) t = Some (t', ve', n\<^sub>1)\<close> and
    \<tau>: \<open>\<tau> = TDep (is_imp b) (mbind_sig b) (length T) RNil
              (kclose [n ..< n + length T] t')\<close> and
    n': \<open>n' = n\<^sub>1\<close>
    using ty_stat_TArrowMod.prems
    by (auto simp: Let_def split: msig.split_asm list.split_asm option.split_asm tentry.split_asm
                                  prod.split_asm if_split_asm Option.bind_split_asm)
  have clE: \<open>ftv_env E = {}\<close> \<open>frv_env E = {}\<close>
    using cenv_tlookup_nonval[OF cB lk] by auto
  have kE: \<open>ktv_env E \<subseteq> ktv_env B\<close> using ktv_env_tlookup[OF lk] by simp
  let ?X = \<open>param_env (real_env (dep_vars T [n ..< n + length T]) E)\<close>
  have clX: \<open>ftv_env ?X = {}\<close> \<open>frv_env ?X = {}\<close>
    using param_env_ftv[of \<open>real_env (dep_vars T [n ..< n + length T]) E\<close>]
          param_env_frv[of \<open>real_env (dep_vars T [n ..< n + length T]) E\<close>]
          real_env_ftv[of \<open>dep_vars T [n ..< n + length T]\<close> E]
          real_env_frv[of \<open>dep_vars T [n ..< n + length T]\<close> E]
          clE dep_vars_ftv[of T \<open>[n ..< n + length T]\<close>]
          dep_vars_frv[of T \<open>[n ..< n + length T]\<close>] by auto
  have cX: \<open>cenv ((mbind_nm b, TEstr ?X) # B)\<close> using cB clX by simp
  note ih = ty_stat_TArrowMod.IH[OF sg refl lk refl refl refl refl ok tt cX nfr]
  show ?case unfolding \<tau> using ih nfr by simp
next
  case (spine_stat_Cons B fr ve n a as)
  have cB: \<open>cenv B\<close> and nfr: \<open>\<not> fr\<close> using spine_stat_Cons.prems by blast+
  show ?case
  proof (cases a)
    case (TPath p)
    from spine_stat_Cons.prems obtain ts ve\<^sub>1 n\<^sub>1 where
      at: \<open>atoms_stat B fr ve n as = Some (ts, ve\<^sub>1, n\<^sub>1)\<close> and
      hd: \<open>head_stat B fr ve\<^sub>1 n\<^sub>1 p ts = Some (\<tau>, ve', n')\<close>
      unfolding TPath by (auto split: Option.bind_split_asm prod.split_asm)
    have ih: \<open>(\<forall>t \<in> set ts. ftv t \<subseteq> tvars ve \<and> frv t \<subseteq> rvars ve) \<and> ve\<^sub>1 = ve\<close>
      using TPath at cB nfr by (rule spine_stat_Cons.IH)
    have veq1: \<open>ve\<^sub>1 = ve\<close> using ih by simp
    obtain tvs rvs where ve: \<open>ve = (tvs, rvs)\<close> by (cases ve)
    have args: \<open>\<forall>t \<in> set ts. ftv t \<subseteq> tvars ve \<and> frv t \<subseteq> rvars ve\<close> using ih by simp
    have frF: \<open>fr = False\<close> using nfr by simp
    note hc = head_stat_closed[OF hd[unfolded frF veq1 ve] cB args[unfolded ve]]
    show ?thesis using hc veq1 ve by simp
  next
    case (TWild x)
    then show ?thesis using spine_stat_Cons.prems by (auto split: if_split_asm)
  next
    case (TParen ts)
    with spine_stat_Cons.prems have \<open>as = []\<close> \<open>atom_stat B fr ve n a = Some (\<tau>, ve', n')\<close>
      by (auto split: if_split_asm)
    from TParen this cB nfr show ?thesis by (rule spine_stat_Cons.IH)
  next
    case (TName x)
    with spine_stat_Cons.prems have \<open>as = []\<close> \<open>atom_stat B fr ve n a = Some (\<tau>, ve', n')\<close>
      by (auto split: if_split_asm)
    from TName this cB nfr show ?thesis by (rule spine_stat_Cons.IH)
  qed
next
  case (ty_stat_TArrowName B fr ve n f e ro t)
  have cB: \<open>cenv B\<close> and nfr: \<open>\<not> fr\<close> using ty_stat_TArrowName.prems by blast+
  from ty_stat_TArrowName.prems obtain p as args ve\<^sub>1 n\<^sub>1 l ls \<epsilon> ve\<^sub>2 n\<^sub>2 \<tau>\<^sub>0 ve\<^sub>3 n\<^sub>3 where
    e: \<open>e = TPath p # as\<close> and ok: \<open>nm_ok (n_txt f)\<close> and
    at: \<open>atoms_stat B fr ve n as = Some (args, ve\<^sub>1, n\<^sub>1)\<close> and
    ef: \<open>eff_at B p (length args) = Some (l, ls)\<close> and
    ro: \<open>row_stat ((nkey (n_txt f), TEeff l ls (length args)) # B) fr ve\<^sub>1 n\<^sub>1 ro
           = Some (\<epsilon>, ve\<^sub>2, n\<^sub>2)\<close> and
    tt: \<open>ty_stat ((nkey (n_txt f), TEeff l ls (length args)) # B) fr ve\<^sub>2 n\<^sub>2 t
           = Some (\<tau>\<^sub>0, ve\<^sub>3, n\<^sub>3)\<close> and
    \<tau>: \<open>\<tau> = TAct (eff_ty l args) [n\<^sub>3] (canon_row (rext (map (nlbl \<circ> mangle l) ls) \<epsilon>)) \<tau>\<^sub>0\<close> and
    ve': \<open>ve' = ve\<^sub>3\<close>
    by (auto split: list.split_asm tatom.split_asm if_split_asm Option.bind_split_asm
                    prod.split_asm)
  have cB': \<open>cenv ((nkey (n_txt f), TEeff l ls (length args)) # B)\<close> using cB by simp
  have ih1: \<open>(\<forall>t \<in> set args. ftv t \<subseteq> tvars ve \<and> frv t \<subseteq> rvars ve) \<and> ve\<^sub>1 = ve\<close>
    using e refl ok at cB nfr by (rule ty_stat_TArrowName.IH)
  have ih2: \<open>frv_row \<epsilon> \<subseteq> rvars ve\<^sub>1 \<and> ve\<^sub>2 = ve\<^sub>1\<close>
    using e refl ok at refl refl ef refl ro cB' nfr by (rule ty_stat_TArrowName.IH)
  have ih3: \<open>ftv \<tau>\<^sub>0 \<subseteq> tvars ve\<^sub>2 \<and> frv \<tau>\<^sub>0 \<subseteq> rvars ve\<^sub>2 \<and> ve\<^sub>3 = ve\<^sub>2\<close>
    using e refl ok at refl refl ef refl ro refl refl tt cB' nfr by (rule ty_stat_TArrowName.IH)
  show ?case unfolding \<tau> ve' using ih1 ih2 ih3 by (auto simp: eff_ty_def rext_def)
next
  case (ty_stat_THand B fr ve n e a ro b)
  have cB: \<open>cenv B\<close> and nfr: \<open>\<not> fr\<close> using ty_stat_THand.prems by blast+
  from ty_stat_THand.prems obtain p as args ve\<^sub>1 n\<^sub>1 \<tau>\<^sub>0 ve\<^sub>2 n\<^sub>2 \<epsilon> ve\<^sub>3 n\<^sub>3 \<tau>\<^sub>1 ve\<^sub>4 n\<^sub>4 l ls where
    e: \<open>e = TPath p # as\<close> and
    at: \<open>atoms_stat B fr ve n as = Some (args, ve\<^sub>1, n\<^sub>1)\<close> and
    sp: \<open>spine_stat B fr ve\<^sub>1 n\<^sub>1 a = Some (\<tau>\<^sub>0, ve\<^sub>2, n\<^sub>2)\<close> and
    ro: \<open>row_stat B fr ve\<^sub>2 n\<^sub>2 ro = Some (\<epsilon>, ve\<^sub>3, n\<^sub>3)\<close> and
    sb: \<open>spine_stat B fr ve\<^sub>3 n\<^sub>3 b = Some (\<tau>\<^sub>1, ve\<^sub>4, n\<^sub>4)\<close> and
    \<tau>: \<open>\<tau> = TFn (TAct (eff_ty l args) [n\<^sub>4] (canon_row (rext (map (nlbl \<circ> mangle l) ls) \<epsilon>)) \<tau>\<^sub>0)
             \<epsilon> \<tau>\<^sub>1\<close> and
    ve': \<open>ve' = ve\<^sub>4\<close>
    by (auto split: list.split_asm tatom.split_asm Option.bind_split_asm prod.split_asm)
  have ih1: \<open>(\<forall>t \<in> set args. ftv t \<subseteq> tvars ve \<and> frv t \<subseteq> rvars ve) \<and> ve\<^sub>1 = ve\<close>
    using e refl at cB nfr by (rule ty_stat_THand.IH)
  have ih2: \<open>ftv \<tau>\<^sub>0 \<subseteq> tvars ve\<^sub>1 \<and> frv \<tau>\<^sub>0 \<subseteq> rvars ve\<^sub>1 \<and> ve\<^sub>2 = ve\<^sub>1\<close>
    using e refl at refl refl sp cB nfr by (rule ty_stat_THand.IH)
  have ih3: \<open>frv_row \<epsilon> \<subseteq> rvars ve\<^sub>2 \<and> ve\<^sub>3 = ve\<^sub>2\<close>
    using e refl at refl refl sp refl refl ro cB nfr by (rule ty_stat_THand.IH)
  have ih4: \<open>ftv \<tau>\<^sub>1 \<subseteq> tvars ve\<^sub>3 \<and> frv \<tau>\<^sub>1 \<subseteq> rvars ve\<^sub>3 \<and> ve\<^sub>4 = ve\<^sub>3\<close>
    using e refl at refl refl sp refl refl ro refl refl sb cB nfr by (rule ty_stat_THand.IH)
  show ?case unfolding \<tau> ve' using ih1 ih2 ih3 ih4 by (auto simp: eff_ty_def rext_def)
next
  case (atom_stat_TName B fr ve n e)
  then show ?case by (auto split: list.split_asm tatom.split_asm if_split_asm)
next
  case (atom_stat_TPath B fr ve n p)
  have cB: \<open>cenv B\<close> and nfr: \<open>\<not> fr\<close> using atom_stat_TPath.prems by blast+
  obtain tvs rvs where ve: \<open>ve = (tvs, rvs)\<close> by (cases ve)
  have frF: \<open>fr = False\<close> using nfr by simp
  have h: \<open>head_stat B False (tvs, rvs) n p [] = Some (\<tau>, ve', n')\<close>
    using atom_stat_TPath.prems ve frF by simp
  from head_stat_closed[OF h cB] show ?case using ve by simp
next
  case (atom_stat_TParen B fr ve n ts)
  have cB: \<open>cenv B\<close> and nfr: \<open>\<not> fr\<close> using atom_stat_TParen.prems by blast+
  consider (nil) \<open>ts = []\<close> | (single) t where \<open>ts = [t]\<close>
    | (multi) t t' ts' where \<open>ts = t # t' # ts'\<close>
    by (cases ts; cases \<open>tl ts\<close>) auto
  then show ?case
  proof cases
    case nil then show ?thesis using atom_stat_TParen.prems by (auto simp: tvars_def rvars_def)
  next
    case (single t)
    then have tt: \<open>ty_stat B fr ve n t = Some (\<tau>, ve', n')\<close>
      using atom_stat_TParen.prems by simp
    from single refl tt cB nfr show ?thesis by (rule atom_stat_TParen.IH)
  next
    case (multi t t' ts')
    then obtain \<tau>s where tys: \<open>tys_stat B fr ve n ts = Some (\<tau>s, ve', n')\<close> \<open>\<tau> = tuple \<tau>s\<close>
      using atom_stat_TParen.prems by (auto split: Option.bind_split_asm prod.split_asm)
    have ih: \<open>(\<forall>\<tau> \<in> set \<tau>s. ftv \<tau> \<subseteq> tvars ve \<and> frv \<tau> \<subseteq> rvars ve) \<and> ve' = ve\<close>
      using multi refl tys(1) cB nfr by (rule atom_stat_TParen.IH)
    show ?thesis unfolding tys(2) using ih by auto
  qed
next
  case (atoms_stat_Cons B fr ve n a as)
  have cB: \<open>cenv B\<close> and nfr: \<open>\<not> fr\<close> using atoms_stat_Cons.prems by blast+
  from atoms_stat_Cons.prems obtain t ve\<^sub>1 n\<^sub>1 ts where
    at: \<open>atom_stat B fr ve n a = Some (t, ve\<^sub>1, n\<^sub>1)\<close> and
    ats: \<open>atoms_stat B fr ve\<^sub>1 n\<^sub>1 as = Some (ts, ve', n')\<close> and \<tau>s: \<open>\<tau>s = t # ts\<close>
    by (auto split: Option.bind_split_asm prod.split_asm)
  have ih1: \<open>ftv t \<subseteq> tvars ve \<and> frv t \<subseteq> rvars ve \<and> ve\<^sub>1 = ve\<close>
    using at cB nfr by (rule atoms_stat_Cons.IH)
  have ih2: \<open>(\<forall>\<tau> \<in> set ts. ftv \<tau> \<subseteq> tvars ve\<^sub>1 \<and> frv \<tau> \<subseteq> rvars ve\<^sub>1) \<and> ve' = ve\<^sub>1\<close>
    using at refl refl ats cB nfr by (rule atoms_stat_Cons.IH)
  from ih1 ih2 have veq: \<open>ve\<^sub>1 = ve\<close> \<open>ve' = ve\<close> by simp_all
  show ?case unfolding \<tau>s using ih1 ih2 veq by auto
next
  case (tys_stat_Cons B fr ve n t ts)
  have cB: \<open>cenv B\<close> and nfr: \<open>\<not> fr\<close> using tys_stat_Cons.prems by blast+
  from tys_stat_Cons.prems obtain t' ve\<^sub>1 n\<^sub>1 ts' where
    tt: \<open>ty_stat B fr ve n t = Some (t', ve\<^sub>1, n\<^sub>1)\<close> and
    tts: \<open>tys_stat B fr ve\<^sub>1 n\<^sub>1 ts = Some (ts', ve', n')\<close> and \<tau>s: \<open>\<tau>s = t' # ts'\<close>
    by (auto split: Option.bind_split_asm prod.split_asm)
  have ih1: \<open>ftv t' \<subseteq> tvars ve \<and> frv t' \<subseteq> rvars ve \<and> ve\<^sub>1 = ve\<close>
    using tt cB nfr by (rule tys_stat_Cons.IH)
  have ih2: \<open>(\<forall>\<tau> \<in> set ts'. ftv \<tau> \<subseteq> tvars ve\<^sub>1 \<and> frv \<tau> \<subseteq> rvars ve\<^sub>1) \<and> ve' = ve\<^sub>1\<close>
    using tt refl refl tts cB nfr by (rule tys_stat_Cons.IH)
  from ih1 ih2 have veq: \<open>ve\<^sub>1 = ve\<close> \<open>ve' = ve\<close> by simp_all
  show ?case unfolding \<tau>s using ih1 ih2 veq by auto
next
  case (row_stat_Some B fr ve n rt)
  have run: \<open>row_stat B fr ve n (Some rt) = Some (r, ve', n')\<close> and nfr: \<open>\<not> fr\<close>
    using row_stat_Some.prems by blast+
  obtain tvs rvs where ve: \<open>ve = (tvs, rvs)\<close> by (cases ve)
  have frF: \<open>fr = False\<close> using nfr by simp
  have novar: \<open>n' = n\<close>
    using run[unfolded ve frF]
    by (auto split: ty.split_asm option.split_asm Option.bind_split_asm list.split_asm
                    tatom.split_asm if_split_asm)
  from row_stat_SomeD[OF run[unfolded ve]] show ?case
  proof (elim disjE exE conjE)
    fix ls' assume \<open>r = canon_row (foldr RCons ls' RNil)\<close> \<open>ve' = (tvs, rvs)\<close> \<open>n' = n\<close>
    then show ?case using ve by simp
  next
    fix ls' v r'
    assume a: \<open>r = canon_row (foldr RCons ls' r')\<close> \<open>map_of rvs v = Some r'\<close>
      \<open>ve' = (tvs, rvs)\<close> \<open>n' = n\<close>
    have vr: \<open>(v, r') \<in> set rvs\<close> using a(2) by (rule map_of_SomeD)
    have f: \<open>frv_row r' \<subseteq> rvars ve\<close>
      using vr unfolding ve rvars_def by fastforce
    show ?case using a f ve by simp
  next
    fix ls' v
    assume a: \<open>r = canon_row (foldr RCons ls' (RV n))\<close> \<open>ve' = (tvs, (v, RV n) # rvs)\<close>
      \<open>n' = Suc n\<close>
    then show ?case using novar by simp
  qed
next
  case (ty_stat_TRec B fr ve n fs rt)
  have cB: \<open>cenv B\<close> and nfr: \<open>\<not> fr\<close> and run: \<open>ty_stat B fr ve n (TRec fs rt) = Some (\<tau>, ve', n')\<close>
    using ty_stat_TRec.prems by blast+
  have dist: \<open>distinct (map (n_txt \<circ> fst) fs)\<close> using run by (simp split: if_split_asm)
  from run dist obtain ts ve\<^sub>1 n\<^sub>1 where
    tt: \<open>tys_stat B fr ve n (map snd fs) = Some (ts, ve\<^sub>1, n\<^sub>1)\<close>
    by (auto simp: bind_eq_Some_conv)
  have ih1: \<open>(\<forall>u \<in> set ts. ftv u \<subseteq> tvars ve \<and> frv u \<subseteq> rvars ve) \<and> ve\<^sub>1 = ve\<close>
    using dist tt cB nfr by (rule ty_stat_TRec.IH(1))
  then have fld: \<open>\<forall>l u. (l, u) \<in> set (zip (map (n_txt \<circ> fst) fs) ts) \<longrightarrow>
      ftv u \<subseteq> tvars ve \<and> frv u \<subseteq> rvars ve\<close>
    by (auto dest: set_zip_rightD)
  show ?case
  proof (cases rt)
    case None
    with run dist tt have \<open>\<tau> = rec_of (zip (map (n_txt \<circ> fst) fs) ts) TRNil\<close> \<open>ve' = ve\<^sub>1\<close>
      by simp_all
    then show ?thesis using fld ih1 by (auto split: prod.split)
  next
    case (Some t)
    with run dist tt obtain u v m where
      tu0: \<open>ty_stat B fr ve\<^sub>1 n\<^sub>1 t = Some (u, v, m)\<close> and
      cs: \<open>(case u of TV x \<Rightarrow> Some (rec_of (zip (map (n_txt \<circ> fst) fs) ts) u, v, m)
              | _ \<Rightarrow> None) = Some (\<tau>, ve', n')\<close>
      by (auto simp: bind_eq_Some_conv split: prod.split_asm)
    from cs obtain x where ux: \<open>u = TV x\<close> by (cases u) auto
    with cs have tu: \<open>ty_stat B fr ve\<^sub>1 n\<^sub>1 t = Some (u, ve', n')\<close> and
      \<tau>: \<open>\<tau> = rec_of (zip (map (n_txt \<circ> fst) fs) ts) u\<close>
      using tu0 by auto
    have ih2: \<open>ftv u \<subseteq> tvars ve\<^sub>1 \<and> frv u \<subseteq> rvars ve\<^sub>1 \<and> ve' = ve\<^sub>1\<close>
      using dist tt refl refl Some tu cB nfr by (rule ty_stat_TRec.IH(2))
    show ?thesis unfolding \<tau> using fld ih1 ih2 by auto
  qed
qed (auto simp: tvars_def rvars_def split: if_split_asm)

lemma btv_close_ty: \<open>btv (close_ty as rs t) = btv t \<union> (ftv t \<inter> as)\<close>
  by (auto simp: close_ty_def btv_tsubst split: if_splits)

lemma brv_close_ty: \<open>brv (close_ty as rs t) = brv t \<union> (frv t \<inter> rs)\<close>
  by (auto simp: close_ty_def brv_tsubst split: if_splits)

lemma ktv_close_ty: \<open>ktv (close_ty as rs t) = ktv t\<close>
  unfolding close_ty_def by (induction t) auto

lemma eff_ve_ok:
  \<open>tve_ok (eff_ve as n)\<close> \<open>tvars (eff_ve as n) \<subseteq> set (eff_ps as n)\<close> \<open>rvars (eff_ve as n) = {}\<close>
  by (auto simp: tve_ok_def bfree_def tvars_def rvars_def dest!: set_zip_rightD)

text \<open>One step of \<^const>\<open>ops_stat\<close>:\<close>

lemma ops_stat_ConsE:
  assumes \<open>ops_stat B pre ps ve n ((opn, ty) # ops) = Some (es, n')\<close>
  obtains t\<^sub>1 rr t\<^sub>2 tvs rvs n\<^sub>1 es' where
    \<open>ty_stat B False ve n ty = Some (TFn t\<^sub>1 rr t\<^sub>2, (tvs, rvs), n\<^sub>1)\<close>
    \<open>ops_stat B pre ps ve n\<^sub>1 ops = Some (es', n')\<close>
    \<open>es = (n_txt opn, TEop (mangle pre (n_txt opn)) ps
      (close_ty (set ps) {} t\<^sub>1) (close_ty (set ps) {} t\<^sub>2)) # es'\<close>
proof -
  from assms obtain \<tau> tvs rvs n\<^sub>1 where \<open>ty_stat B False ve n ty = Some (\<tau>, (tvs, rvs), n\<^sub>1)\<close>
    by (auto simp: bind_eq_Some_conv)
  with assms that show ?thesis by (cases \<tau>) (auto simp: bind_eq_Some_conv)
qed

text \<open>An effect's operation entries: the parameters \<open>ps\<close> are closed into the
  entries, everything else is fresh or from the basis.\<close>

lemma ops_stat_wf:
  \<open>ops_stat B pre ps ve n ops = Some (es, n') \<Longrightarrow> cenv B \<Longrightarrow> tve_ok ve \<Longrightarrow>
     n \<le> n' \<and> ftv_env es \<subseteq> (tvars ve \<union> {n ..< n'}) - set ps \<and>
     frv_env es \<subseteq> rvars ve \<union> {n ..< n'} \<and> ktv_env es \<subseteq> ktv_env B \<and> bfree_env es\<close>
proof (induction ops arbitrary: n es n')
  case (Cons oty ops)
  obtain opn ty where oty: \<open>oty = (opn, ty)\<close> by (cases oty)
  from Cons.prems obtain t\<^sub>1 rr t\<^sub>2 tvs rvs n\<^sub>1 es' where
    ts: \<open>ty_stat B False ve n ty = Some (TFn t\<^sub>1 rr t\<^sub>2, (tvs, rvs), n\<^sub>1)\<close>
    and os: \<open>ops_stat B pre ps ve n\<^sub>1 ops = Some (es', n')\<close>
    and es: \<open>es = (n_txt opn, TEop (mangle pre (n_txt opn)) ps
      (close_ty (set ps) {} t\<^sub>1) (close_ty (set ps) {} t\<^sub>2)) # es'\<close>
    unfolding oty by (blast elim: ops_stat_ConsE)
  note w = ty_stat_wf[OF ts \<open>cenv B\<close> \<open>tve_ok ve\<close>]
  have le1: \<open>n \<le> n\<^sub>1\<close> using tve_step_le[OF w[THEN conjunct1]] .
  have b1: \<open>ftv t\<^sub>1 \<subseteq> tvars ve \<union> {n ..< n\<^sub>1}\<close> \<open>ftv t\<^sub>2 \<subseteq> tvars ve \<union> {n ..< n\<^sub>1}\<close>
    \<open>frv t\<^sub>1 \<subseteq> rvars ve \<union> {n ..< n\<^sub>1}\<close> \<open>frv t\<^sub>2 \<subseteq> rvars ve \<union> {n ..< n\<^sub>1}\<close>
    \<open>ktv t\<^sub>1 \<subseteq> ktv_env B\<close> \<open>ktv t\<^sub>2 \<subseteq> ktv_env B\<close> \<open>bfree t\<^sub>1\<close> \<open>bfree t\<^sub>2\<close>
    using w[THEN conjunct2] unfolding fresh_ty_def by auto
  note ih = Cons.IH[OF os \<open>cenv B\<close> \<open>tve_ok ve\<close>]
  have le2: \<open>n\<^sub>1 \<le> n'\<close> using ih by simp
  have subn1: \<open>{n ..< n\<^sub>1} \<subseteq> {n ..< n'}\<close> using le2 by simp
  have subn2: \<open>{n\<^sub>1 ..< n'} \<subseteq> {n ..< n'}\<close> using le1 by simp
  show ?case unfolding es using ih b1 subn1 subn2 le1 le2
    by (auto simp: bfree_def ftv_close_ty frv_close_ty btv_close_ty brv_close_ty ktv_close_ty)
qed simp

lemma ops_stat_closed:
  \<open>ops_stat B pre ps ve n ops = Some (es, n') \<Longrightarrow> cenv B \<Longrightarrow> tve_ok ve \<Longrightarrow>
     tvars ve \<subseteq> set ps \<Longrightarrow> rvars ve = {} \<Longrightarrow>
     ftv_env es = {} \<and> frv_env es = {} \<and> ktv_env es \<subseteq> ktv_env B \<and> bfree_env es\<close>
proof (induction ops arbitrary: n es n')
  case (Cons oty ops)
  obtain opn ty where oty: \<open>oty = (opn, ty)\<close> by (cases oty)
  from Cons.prems obtain t\<^sub>1 rr t\<^sub>2 tvs rvs n\<^sub>1 es' where
    ts: \<open>ty_stat B False ve n ty = Some (TFn t\<^sub>1 rr t\<^sub>2, (tvs, rvs), n\<^sub>1)\<close>
    and os: \<open>ops_stat B pre ps ve n\<^sub>1 ops = Some (es', n')\<close>
    and es: \<open>es = (n_txt opn, TEop (mangle pre (n_txt opn)) ps
      (close_ty (set ps) {} t\<^sub>1) (close_ty (set ps) {} t\<^sub>2)) # es'\<close>
    unfolding oty by (blast elim: ops_stat_ConsE)
  note wc = ty_stat_closed(1)[OF ts \<open>cenv B\<close>]
    and ww = ty_stat_wf[OF ts \<open>cenv B\<close> \<open>tve_ok ve\<close>]
  have cl: \<open>ftv t\<^sub>1 \<subseteq> set ps\<close> \<open>ftv t\<^sub>2 \<subseteq> set ps\<close> \<open>frv t\<^sub>1 = {}\<close> \<open>frv t\<^sub>2 = {}\<close>
    using wc Cons.prems by auto
  have kb: \<open>ktv t\<^sub>1 \<subseteq> ktv_env B\<close> \<open>ktv t\<^sub>2 \<subseteq> ktv_env B\<close> \<open>bfree t\<^sub>1\<close> \<open>bfree t\<^sub>2\<close>
    using ww[THEN conjunct2] unfolding fresh_ty_def by (auto simp: bfree_def)
  note ih = Cons.IH[OF os \<open>cenv B\<close> \<open>tve_ok ve\<close> \<open>tvars ve \<subseteq> set ps\<close>
    \<open>rvars ve = {}\<close>]
  show ?case unfolding es using ih cl kb
    by (auto simp: bfree_def ftv_close_ty frv_close_ty btv_close_ty brv_close_ty ktv_close_ty)
qed simp

lemma cons_stat_closed:
  \<open>cons_stat B ve ps c n alts = Some (es, n') \<Longrightarrow> cenv B \<Longrightarrow> tve_ok ve \<Longrightarrow>
     tvars ve \<subseteq> set ps \<Longrightarrow> rvars ve = {} \<Longrightarrow>
     ftv_env es = {} \<and> frv_env es = {} \<and> ktv_env es \<subseteq> ktv_env B \<and> bfree_env es\<close>
proof (induction alts arbitrary: n es n')
  case (Cons cna alts)
  obtain cn args where cna: \<open>cna = (cn, args)\<close> by (cases cna)
  obtain ts tvs\<^sub>2 rvs\<^sub>2 n\<^sub>1 where as: \<open>atoms_stat B False ve n args = Some (ts, (tvs\<^sub>2, rvs\<^sub>2), n\<^sub>1)\<close>
  proof (cases \<open>atoms_stat B False ve n args\<close>)
    case None then show ?thesis using Cons.prems cna by simp
  next
    case (Some r) then show ?thesis using that by (cases r) auto
  qed
  define rws where \<open>rws = [n\<^sub>1 ..< n\<^sub>1 + length ts]\<close>
  define \<tau> where \<open>\<tau> = foldr (\<lambda>(t, r) acc. TFn t (RV r) acc) (zip ts rws) (TC c (map TV ps))\<close>
  obtain es' n\<^sub>2 where rec: \<open>cons_stat B ve ps c (n\<^sub>1 + length ts) alts = Some (es', n\<^sub>2)\<close>
    and es: \<open>es = (n_txt cn,
      TEcon (close_sch (set ps) (set [n ..< n\<^sub>1 + length ts]) \<tau>) (length ts)) # es'\<close>
  proof (cases \<open>cons_stat B ve ps c (n\<^sub>1 + length ts) alts\<close>)
    case None then show ?thesis using Cons.prems cna as
      by (simp add: bind_eq_Some_conv Let_def rws_def \<tau>_def)
  next
    case (Some r) then show ?thesis using that Cons.prems cna as
      by (cases r) (auto simp: bind_eq_Some_conv Let_def rws_def \<tau>_def)
  qed
  have nF: \<open>\<not> False\<close> by simp
  note w = ty_stat_closed(2)[OF as \<open>cenv B\<close> nF]
  have le1: \<open>n \<le> n\<^sub>1\<close>
    using tve_step_le[OF atoms_stat_wf[OF as \<open>cenv B\<close> \<open>tve_ok ve\<close>, THEN conjunct1]] .
  have fts: \<open>\<forall>t\<in>set ts. ftv t \<subseteq> set ps \<and> frv t = {}\<close>
    using w[THEN conjunct1] Cons.prems by fastforce
  have zt: \<open>(t, r) \<in> set (zip ts rws) \<Longrightarrow> t \<in> set ts\<close> for t r by (auto dest: set_zip_leftD)
  have zr: \<open>(t, r) \<in> set (zip ts rws) \<Longrightarrow> r \<in> {n\<^sub>1 ..< n\<^sub>1 + length ts}\<close> for t r
    by (auto dest: set_zip_rightD simp: rws_def)
  have bt: \<open>ftv (TC c (map TV ps)) = set ps\<close> by (induction ps) auto
  have br: \<open>frv (TC c (map TV ps)) = {}\<close> by (induction ps) auto
  have z1: \<open>(\<Union>(t, r)\<in>set (zip ts rws). ftv t) \<subseteq> set ps\<close>
    by (rule UN_least) (use fts zt in auto)
  have z2: \<open>(\<Union>(t, r)\<in>set (zip ts rws). frv t \<union> {r}) \<subseteq> {n\<^sub>1 ..< n\<^sub>1 + length ts}\<close>
    by (rule UN_least) (use fts zt zr in auto)
  have ft\<tau>: \<open>ftv \<tau> \<subseteq> set ps\<close> unfolding \<tau>_def ftv_foldr_arrow bt using z1 by auto
  have fr\<tau>: \<open>frv \<tau> \<subseteq> {n\<^sub>1 ..< n\<^sub>1 + length ts}\<close>
    unfolding \<tau>_def frv_foldr_arrow br using z2 by auto
  have e1: \<open>ftv_sch (close_sch (set ps) (set [n ..< n\<^sub>1 + length ts]) \<tau>) = {}\<close>
    using ft\<tau> unfolding ftv_sch_close_eq by auto
  have e2: \<open>frv_sch (close_sch (set ps) (set [n ..< n\<^sub>1 + length ts]) \<tau>) = {}\<close>
    using fr\<tau> le1 unfolding frv_sch_close_eq by auto
  note kbw = cons_stat_wf[OF \<open>cons_stat B ve ps c n (cna # alts) = Some (es, n')\<close>
    \<open>cenv B\<close> \<open>tve_ok ve\<close>]
  note ih = Cons.IH[OF rec \<open>cenv B\<close> \<open>tve_ok ve\<close> \<open>tvars ve \<subseteq> set ps\<close>
    \<open>rvars ve = {}\<close>]
  have Cftv: \<open>ftv_env es = {}\<close>
  proof -
    have \<open>ftv_env es =
      ftv_sch (close_sch (set ps) (set [n ..< n\<^sub>1 + length ts]) \<tau>) \<union> ftv_env es'\<close>
      unfolding es by simp
    then show ?thesis using e1 ih by simp
  qed
  have Cfrv: \<open>frv_env es = {}\<close>
  proof -
    have \<open>frv_env es =
      frv_sch (close_sch (set ps) (set [n ..< n\<^sub>1 + length ts]) \<tau>) \<union> frv_env es'\<close>
      unfolding es by simp
    then show ?thesis using e2 ih by simp
  qed
  show ?case using Cftv Cfrv kbw by simp
qed simp

lemma resolve_inner_pend:
  \<open>resolve_inner K pd = Some pd' \<Longrightarrow>
    ftv_pend pd' = ftv_pend pd \<and> frv_pend pd' = frv_pend pd \<and> ktv_rows pd' = ktv_rows pd\<close>
  by (induction K pd arbitrary: pd' rule: resolve_inner_induct)
     (fastforce simp: bind_eq_Some_conv split: if_split_asm)+

lemma ftv_ksubst: \<open>ftv (ksubst \<theta> t) \<subseteq> ftv t \<union> (\<Union>k\<in>ktv t. ftv (\<theta> k))\<close>
  by (induction t arbitrary: \<theta>) (fastforce split: if_split_asm)+

lemma frv_ksubst: \<open>frv (ksubst \<theta> t) \<subseteq> frv t \<union> (\<Union>k\<in>ktv t. frv (\<theta> k))\<close>
  by (induction t arbitrary: \<theta>) (fastforce split: if_split_asm)+

text \<open>Opening a closed body at a realisation keeps it fresh (a covered
  position becomes one of the realisation's closed types, an uncovered one
  \<^const>\<open>unit_ty\<close>).\<close>

lemma fresh_ok_kopen_tsp:
  assumes ft: \<open>ftv \<tau>' \<subseteq> {..< n}\<close> and fr: \<open>frv \<tau>' \<subseteq> {..< n}\<close> and kt: \<open>ktv \<tau>' \<subseteq> FK\<close>
    and bt: \<open>btv \<tau>' = {}\<close> and br: \<open>brv \<tau>' = {}\<close>
    and phi: \<open>\<forall>(k, u) \<in> set \<phi>. ftv u \<subseteq> {..< m} \<and> frv u \<subseteq> {..< m} \<and> ktv u \<subseteq> FK \<and> bfree u\<close>
    and cov: \<open>set K \<subseteq> fst ` set \<phi>\<close> and le: \<open>n \<le> m\<close>
  shows \<open>fresh_ok (kopen (tsp K \<phi>) \<tau>') 0 m FK\<close>
proof -
  have F: \<open>ftv (tsp K \<phi> i) \<subseteq> {..< m} \<and> frv (tsp K \<phi> i) \<subseteq> {..< m} \<and> ktv (tsp K \<phi> i) \<subseteq> FK
           \<and> btv (tsp K \<phi> i) = {} \<and> brv (tsp K \<phi> i) = {}\<close> for i
  proof (cases \<open>i < length K\<close>)
    case True
    then have \<open>K ! i \<in> fst ` set \<phi>\<close> using cov by auto
    then obtain v where mv: \<open>map_of \<phi> (K ! i) = Some v\<close> by (auto dest!: weak_map_of_SomeI)
    have \<open>(K ! i, v) \<in> set \<phi>\<close> by (rule map_of_SomeD[OF mv])
    then show ?thesis using phi True mv by (fastforce simp: tsp_def tsl_def bfree_def)
  next
    case False
    then show ?thesis by (simp add: tsp_def)
  qed
  have F1: \<open>ftv (tsp K \<phi> i) \<subseteq> {..< m}\<close> and F2: \<open>frv (tsp K \<phi> i) \<subseteq> {..< m}\<close>
    and F3: \<open>ktv (tsp K \<phi> i) \<subseteq> FK\<close> and F4: \<open>btv (tsp K \<phi> i) = {}\<close>
    and F5: \<open>brv (tsp K \<phi> i) = {}\<close> for i using F[of i] by auto
  have sub: \<open>{..< n} \<subseteq> {..< m}\<close> using le by simp
  have fF: \<open>ftv (kopen (tsp K \<phi>) \<tau>') \<subseteq> {..< m}\<close>
    by (rule subset_trans[OF ftv_kopen]) (use ft sub F1 in auto)
  have rF: \<open>frv (kopen (tsp K \<phi>) \<tau>') \<subseteq> {..< m}\<close>
    by (rule subset_trans[OF frv_kopen]) (use fr sub F2 in auto)
  have kF: \<open>ktv (kopen (tsp K \<phi>) \<tau>') \<subseteq> FK\<close>
    by (rule subset_trans[OF ktv_kopen]) (use kt F3 in auto)
  have bF: \<open>bfree (kopen (tsp K \<phi>) \<tau>')\<close>
    using btv_kopen[of 0 \<open>tsp K \<phi>\<close> \<tau>'] brv_kopen[of 0 \<open>tsp K \<phi>\<close> \<tau>'] bt br F4 F5
    by (auto simp: bfree_def)
  show ?thesis using fF rF kF bF by (simp add: fresh_ok_def atLeast0LessThan)
qed

lemma ftv_env_rev[simp]: \<open>ftv_env (rev E) = ftv_env E\<close>
  by (induction E) (simp_all add: Un_ac split_paired_all)

lemma frv_env_rev[simp]: \<open>frv_env (rev E) = frv_env E\<close>
  by (induction E) (simp_all add: Un_ac split_paired_all)

lemma ktv_env_rev[simp]: \<open>ktv_env (rev E) = ktv_env E\<close>
  by (induction E) (simp_all add: Un_ac split_paired_all)

lemma bfree_env_rev[simp]: \<open>bfree_env (rev E) = bfree_env E\<close>
  by (induction E) auto

lemma cenv_acc: \<open>ftv_env acc = {} \<Longrightarrow> frv_env acc = {} \<Longrightarrow> cenv B \<Longrightarrow> cenv (acc @ B)\<close>
proof (induction acc)
  case (Cons xe acc)
  then show ?case by (cases xe) (auto simp: cenv_def)
qed (simp add: cenv_def)

lemma bfree_bsubstl:
  \<open>(\<And>a. a \<in> btv t \<Longrightarrow> bfree (\<theta> a)) \<Longrightarrow> (\<And>v. v \<in> brv t \<Longrightarrow> brv_row (\<rho> v) = {}) \<Longrightarrow>
    bfree (bsubstl \<theta> \<rho> t)\<close>
  by (auto simp: bfree_def btv_bsubstl brv_bsubstl)

lemma btv_treal: \<open>btv (treal \<phi> t) \<subseteq> btv t\<close>
proof (induction t)
  case (TC c ts)
  then show ?case
    by (auto simp: btv_bsubstl split: option.splits tydef.splits
        dest!: map_of_SomeD set_zip_rightD) blast
qed auto

lemma brv_treal: \<open>brv (treal \<phi> t) \<subseteq> brv t\<close>
proof (induction t)
  case (TC c ts)
  then show ?case
    by (auto simp: brv_bsubstl split: option.splits tydef.splits
        dest!: map_of_SomeD set_zip_rightD) blast
qed auto

lemma bfree_treal: \<open>bfree t \<Longrightarrow> bfree (treal \<phi> t)\<close>
proof (induction t)
  case (TC c ts)
  have bt: \<open>\<forall>u \<in> set ts. bfree (treal \<phi> u)\<close> using TC by (auto simp: bfree_def)
  show ?case
  proof (cases \<open>map_of \<phi> (stamp c)\<close>)
    case None then show ?thesis using bt by (auto simp: bfree_def btv_bsubstl brv_bsubstl)
  next
    case (Some d)
    show ?thesis
    proof (cases d)
      case (TyAbs c' k) then show ?thesis using Some bt by (auto simp: bfree_def)
    next
      case (TyFn ps b)
      have \<theta>b:
        \<open>bfree (case map_of (zip ps (map (treal \<phi>) ts)) a of Some u \<Rightarrow> u | None \<Rightarrow> unit_ty)\<close>
        for a
      proof (cases \<open>map_of (zip ps (map (treal \<phi>) ts)) a\<close>)
        case (Some u)
        have \<open>u \<in> set (map (treal \<phi>) ts)\<close>
          using map_of_SomeD[OF Some] by (auto dest: set_zip_rightD)
        then obtain w where \<open>w \<in> set ts\<close> \<open>u = treal \<phi> w\<close> by auto
        then show ?thesis using Some bt by simp
      qed (simp add: bfree_def)
      have \<open>bfree (bsubstl
          (\<lambda>a. case map_of (zip ps (map (treal \<phi>) ts)) a of Some u \<Rightarrow> u | None \<Rightarrow> unit_ty)
          (\<lambda>_. RNil) b)\<close>
        by (rule bfree_bsubstl) (use \<theta>b in auto)
      then show ?thesis using Some TyFn by simp
    qed
  qed
qed (auto simp: bfree_def)

lemma bfree_real_scheme: \<open>bfree_sch \<sigma> \<Longrightarrow> bfree_sch (real_scheme \<phi> \<sigma>)\<close>
  by (cases \<sigma>) (auto simp: bfree_treal)

lemma bfree_real:
  \<open>bfree_ent e \<Longrightarrow> bfree_ent (real_ent \<phi> e)\<close>
  \<open>bfree_env E \<Longrightarrow> bfree_env (real_env \<phi> E)\<close>
  by (induction \<phi> e and \<phi> E rule: real_ent_real_env.induct)
     (auto simp: bfree_real_scheme bfree_treal list_all_iff
        dest!: subsetD[OF btv_treal] subsetD[OF brv_treal])

lemma abs_present_append[simp]:
  \<open>abs_present t (E\<^sub>1 @ E\<^sub>2) \<longleftrightarrow> abs_present t E\<^sub>1 \<or> abs_present t E\<^sub>2\<close>
  by (induction E\<^sub>1) auto

lemma abs_present_rev[simp]: \<open>abs_present t (rev E) \<longleftrightarrow> abs_present t E\<close>
  by (induction E) auto

lemma abs_present_real:
  \<open>abs_present_ent t e \<Longrightarrow> t \<notin> fst ` set \<phi> \<Longrightarrow> abs_present_ent t (real_ent \<phi> e)\<close>
  \<open>abs_present t E \<Longrightarrow> t \<notin> fst ` set \<phi> \<Longrightarrow> abs_present t (real_env \<phi> E)\<close>
proof (induction \<phi> e and \<phi> E rule: real_ent_induct)
  case (real_ent_TEtyp \<phi> d)
  from \<open>abs_present_ent t (TEtyp d)\<close> obtain c k where d: \<open>d = TyAbs c k\<close>
    and st: \<open>stamp c = t\<close>
    by (cases d) auto
  have \<open>map_of \<phi> (stamp c) = None\<close>
    using \<open>t \<notin> fst ` set \<phi>\<close> st by (simp add: map_of_eq_None_iff)
  then show ?case using d st by simp
qed auto

lemma abs_present_dep_ktv:
  \<open>abs_present_ent t e \<Longrightarrow> map_of \<phi> t = Some (TyFn [] (TK k)) \<Longrightarrow>
    k \<in> ktv_ent (real_ent \<phi> e)\<close>
  \<open>abs_present t E \<Longrightarrow> map_of \<phi> t = Some (TyFn [] (TK k)) \<Longrightarrow>
    k \<in> ktv_env (real_env \<phi> E)\<close>
proof (induction \<phi> e and \<phi> E rule: real_ent_induct)
  case (real_ent_TEtyp \<phi> d)
  from real_ent_TEtyp.prems obtain c k' where d: \<open>d = TyAbs c k'\<close> and st: \<open>stamp c = t\<close>
    by (cases d) auto
  show ?case using d st real_ent_TEtyp.prems by simp
qed auto

text \<open>A signature member environment is a structure tree: only \<open>TEstr\<close>
  recurses, and no signature or instance member nests inside (the surface
  has no nested-signature spec). Every operation the elaboration performs on
  such environments keeps them pure, and purity implies \<open>sig_wf_env\<close>.\<close>

fun pure_ent :: \<open>tentry \<Rightarrow> bool\<close> and
  pure_env :: \<open>tenv \<Rightarrow> bool\<close>
where
  \<open>pure_ent (TEstr E) = pure_env E\<close>
| \<open>pure_ent (TEfun _ _) = False\<close>
| \<open>pure_ent (TEsig _) = False\<close>
| \<open>pure_ent (TEinst _) = False\<close>
| \<open>pure_ent e = True\<close>
| pure_env_Nil: \<open>pure_env [] = True\<close>
| pure_env_Cons: \<open>pure_env ((x, e) # r) \<longleftrightarrow> pure_ent e \<and> pure_env r\<close>

lemma pure_env_append[simp]: \<open>pure_env (E\<^sub>1 @ E\<^sub>2) \<longleftrightarrow> pure_env E\<^sub>1 \<and> pure_env E\<^sub>2\<close>
  by (induction E\<^sub>1) auto

lemma pure_env_rev[simp]: \<open>pure_env (rev E) \<longleftrightarrow> pure_env E\<close>
  by (induction E) auto

lemma pure_real:
  \<open>pure_ent (real_ent \<phi> e) = pure_ent e\<close> \<open>pure_env (real_env \<phi> E) = pure_env E\<close>
  by (induction \<phi> e and \<phi> E rule: real_ent_real_env.induct) auto

text \<open>Signature well-formedness: every abstract stamp a signature entry lists
  names an abstract type of its member environment (which is pure), at every
  depth.\<close>

fun sig_wf_ent :: \<open>tentry \<Rightarrow> bool\<close> and
  sig_wf_env :: \<open>tenv \<Rightarrow> bool\<close>
where
  \<open>sig_wf_ent (TEsig (T\<^sub>0, E\<^sub>0)) \<longleftrightarrow>
    (\<forall>t\<in>set T\<^sub>0. abs_present t E\<^sub>0) \<and> sig_wf_env E\<^sub>0 \<and> pure_env E\<^sub>0\<close>
| \<open>sig_wf_ent (TEstr E) = sig_wf_env E\<close>
| \<open>sig_wf_ent (TEinst E) = sig_wf_env E\<close>
| \<open>sig_wf_ent e = True\<close>
| sig_wf_env_Nil: \<open>sig_wf_env [] = True\<close>
| sig_wf_env_Cons: \<open>sig_wf_env ((x, e) # r) \<longleftrightarrow> sig_wf_ent e \<and> sig_wf_env r\<close>

lemma sig_wf_env_append[simp]:
  \<open>sig_wf_env (E\<^sub>1 @ E\<^sub>2) \<longleftrightarrow> sig_wf_env E\<^sub>1 \<and> sig_wf_env E\<^sub>2\<close>
  by (induction E\<^sub>1) auto

lemma pure_sig_wf: \<open>pure_ent e \<Longrightarrow> sig_wf_ent e\<close> \<open>pure_env E \<Longrightarrow> sig_wf_env E\<close>
  by (induction e and E rule: pure_ent_pure_env.induct) auto

lemma sig_wf_env_map_of: \<open>sig_wf_env B \<Longrightarrow> map_of B x = Some e \<Longrightarrow> sig_wf_ent e\<close>
  by (induction B) (auto split: if_split_asm)

lemma sig_wf_tlookup:
  \<open>sig_wf_env B \<Longrightarrow> tlookup B p = Some e \<Longrightarrow> sig_wf_ent e\<close>
proof (induction B p rule: tlookup_induct)
  case (Cons_Nil env x)
  then show ?case using sig_wf_env_map_of by fastforce
next
  case (Cons_Cons env x y ys)
  then obtain ex where \<open>map_of env x = Some (TEstr ex) \<and> tlookup ex (y # ys) = Some e
                        \<or> map_of env x = Some (TEinst ex) \<and> tlookup ex (y # ys) = Some e\<close>
    by (auto split: option.split_asm tentry.split_asm)
  then show ?case using Cons_Cons.IH Cons_Cons.prems by (auto dest: sig_wf_env_map_of)
qed simp

text \<open>Substitution touches only \<open>TEval\<close> entries, so it leaves
  \<open>sig_wf_env\<close> alone.\<close>

lemma sig_wf_ent_sub_ent[simp]: \<open>sig_wf_ent (sub_ent \<theta> \<rho> e) = sig_wf_ent e\<close>
  by (cases \<open>(\<theta>, \<rho>, e)\<close> rule: sub_ent.cases) auto

lemma sig_wf_env_sub_env[simp]: \<open>sig_wf_env (sub_env \<theta> \<rho> E) = sig_wf_env E\<close>
  by (induction E) (auto simp: sub_env_def)

lemma sig_wf_env_sappe[simp]: \<open>sig_wf_env (sappe s E) = sig_wf_env E\<close>
  by (cases s) simp

lemma match_sig_closed:
  \<open>match_sig E T sg = Some \<phi> \<Longrightarrow> cenv E \<Longrightarrow>
     real_ftv \<phi> = {} \<and> real_frv \<phi> = {} \<and> real_ktv \<phi> \<subseteq> ktv_env E\<close>
proof (induction E T sg arbitrary: \<phi> rule: match_sig_induct)
  case (Cons_TEtyp_TyAbs E T t c k r)
  show ?case
  proof (cases \<open>stamp c \<in> set T\<close>)
    case False
    then have m: \<open>match_sig E T r = Some \<phi>\<close> using Cons_TEtyp_TyAbs.prems by simp
    from False m \<open>cenv E\<close> show ?thesis by (rule Cons_TEtyp_TyAbs.IH)
  next
    case True
    then obtain d \<phi>' where md: \<open>map_of E t = Some (TEtyp d)\<close>
      and ar: \<open>tydef_arity d = k \<and> cons_match c d\<close>
      and rr: \<open>match_sig E T r = Some \<phi>'\<close> and pe: \<open>\<phi> = (stamp c, d) # \<phi>'\<close>
      using Cons_TEtyp_TyAbs.prems
      by (auto simp: bind_eq_Some_conv split: option.split_asm tentry.split_asm if_split_asm)
    have cl: \<open>ftv_tydef d = {}\<close> \<open>frv_tydef d = {}\<close>
      using \<open>cenv E\<close> map_of_SomeD[OF md] by (auto simp: cenv_def)
    have kd: \<open>ktv_tydef d \<subseteq> ktv_env E\<close> using ktv_env_map_of[OF md] by simp
    from True md refl ar rr \<open>cenv E\<close>
    have ih: \<open>real_ftv \<phi>' = {} \<and> real_frv \<phi>' = {} \<and> real_ktv \<phi>' \<subseteq> ktv_env E\<close>
      by (rule Cons_TEtyp_TyAbs.IH)
    show ?thesis using cl kd ih pe by (auto simp: real_ftv_def real_frv_def real_ktv_def)
  qed
next
  case (Cons_TEstr E T x E\<^sub>1 r)
  obtain E\<^sub>2 \<phi>\<^sub>1 \<phi>\<^sub>2 where mx: \<open>map_of E x = Some (TEstr E\<^sub>2)\<close>
    and m1: \<open>match_sig E\<^sub>2 T E\<^sub>1 = Some \<phi>\<^sub>1\<close> and m2: \<open>match_sig E T r = Some \<phi>\<^sub>2\<close>
    and pe: \<open>\<phi> = \<phi>\<^sub>1 @ \<phi>\<^sub>2\<close>
    using Cons_TEstr.prems
    by (auto simp: bind_eq_Some_conv split: option.split_asm tentry.split_asm)
  have clE2: \<open>ftv_env E\<^sub>2 = {}\<close> \<open>frv_env E\<^sub>2 = {}\<close>
    using \<open>cenv E\<close> map_of_SomeD[OF mx] by (auto simp: cenv_def)
  have cE2: \<open>cenv E\<^sub>2\<close> using cenv_acc[OF clE2 cenv_Nil] by simp
  have kE2: \<open>ktv_env E\<^sub>2 \<subseteq> ktv_env E\<close> using ktv_env_map_of[OF mx] by simp
  from mx refl m1 cE2
  have ih1: \<open>real_ftv \<phi>\<^sub>1 = {} \<and> real_frv \<phi>\<^sub>1 = {} \<and> real_ktv \<phi>\<^sub>1 \<subseteq> ktv_env E\<^sub>2\<close>
    by (rule Cons_TEstr.IH)
  from mx refl m1 m2 \<open>cenv E\<close>
  have ih2: \<open>real_ftv \<phi>\<^sub>2 = {} \<and> real_frv \<phi>\<^sub>2 = {} \<and> real_ktv \<phi>\<^sub>2 \<subseteq> ktv_env E\<close>
    by (rule Cons_TEstr.IH)
  show ?case using ih1 ih2 kE2 pe by (auto simp: real_ftv_def real_frv_def real_ktv_def)
qed (auto simp: real_ftv_def real_frv_def real_ktv_def)

lemma match_dep_closed:
  \<open>match_dep E K E' = Some \<phi> \<Longrightarrow> cenv E \<Longrightarrow>
     (\<Union>(k, u) \<in> set \<phi>. ftv u) = {} \<and> (\<Union>(k, u) \<in> set \<phi>. frv u) = {} \<and>
     (\<Union>(k, u) \<in> set \<phi>. ktv u) \<subseteq> ktv_env E \<and> (\<forall>(k, u) \<in> set \<phi>. bfree u) \<and>
     fst ` set \<phi> \<subseteq> set K\<close>
proof (induction E K E' arbitrary: \<phi> rule: match_dep_induct)
  case (Cons_TEtyp_TyFn_Nil_TK E K t k r)
  show ?case
  proof (cases \<open>k \<in> set K\<close>)
    case False
    then have m: \<open>match_dep E K r = Some \<phi>\<close> using Cons_TEtyp_TyFn_Nil_TK.prems by simp
    from False m \<open>cenv E\<close> show ?thesis by (rule Cons_TEtyp_TyFn_Nil_TK.IH)
  next
    case True
    then obtain d \<phi>' where md: \<open>map_of E t = Some (TEtyp d)\<close> and ar: \<open>tydef_arity d = 0\<close>
      and rr: \<open>match_dep E K r = Some \<phi>'\<close> and pe: \<open>\<phi> = (k, tydef_app d []) # \<phi>'\<close>
      using Cons_TEtyp_TyFn_Nil_TK.prems
      by (auto simp: bind_eq_Some_conv split: option.split_asm tentry.split_asm if_split_asm)
    have cl: \<open>ftv_tydef d = {}\<close> \<open>frv_tydef d = {}\<close>
      using \<open>cenv E\<close> map_of_SomeD[OF md] by (auto simp: cenv_def)
    have kd: \<open>ktv_tydef d \<subseteq> ktv_env E\<close> using ktv_env_map_of[OF md] by simp
    have fu: \<open>ftv (tydef_app d []) = {}\<close> using tydef_app_ftv[of d \<open>[]\<close>] cl by auto
    have ru: \<open>frv (tydef_app d []) = {}\<close> using tydef_app_frv[of d \<open>[]\<close>] cl by auto
    have ku: \<open>ktv (tydef_app d []) \<subseteq> ktv_env E\<close> using tydef_app_ktv[of d \<open>[]\<close>] kd by auto
    have bu: \<open>bfree (tydef_app d [])\<close> using tydef_app_bfree[of \<open>[]\<close> d] by simp
    from True md refl ar rr \<open>cenv E\<close>
    have ih: \<open>(\<Union>(k, u) \<in> set \<phi>'. ftv u) = {} \<and> (\<Union>(k, u) \<in> set \<phi>'. frv u) = {} \<and>
      (\<Union>(k, u) \<in> set \<phi>'. ktv u) \<subseteq> ktv_env E \<and> (\<forall>(k, u) \<in> set \<phi>'. bfree u) \<and>
      fst ` set \<phi>' \<subseteq> set K\<close>
      by (rule Cons_TEtyp_TyFn_Nil_TK.IH)
    show ?thesis unfolding pe using ih fu ru ku bu True by auto
  qed
next
  case (Cons_TEstr E K x E\<^sub>1 r)
  obtain E\<^sub>2 \<phi>\<^sub>1 \<phi>\<^sub>2 where mx: \<open>map_of E x = Some (TEstr E\<^sub>2)\<close>
    and m1: \<open>match_dep E\<^sub>2 K E\<^sub>1 = Some \<phi>\<^sub>1\<close> and m2: \<open>match_dep E K r = Some \<phi>\<^sub>2\<close>
    and pe: \<open>\<phi> = \<phi>\<^sub>1 @ \<phi>\<^sub>2\<close>
    using Cons_TEstr.prems
    by (auto simp: bind_eq_Some_conv split: option.split_asm tentry.split_asm)
  have clE2: \<open>ftv_env E\<^sub>2 = {}\<close> \<open>frv_env E\<^sub>2 = {}\<close>
    using \<open>cenv E\<close> map_of_SomeD[OF mx] by (auto simp: cenv_def)
  have cE2: \<open>cenv E\<^sub>2\<close> using cenv_acc[OF clE2 cenv_Nil] by simp
  have kE2: \<open>ktv_env E\<^sub>2 \<subseteq> ktv_env E\<close> using ktv_env_map_of[OF mx] by simp
  note ih = Cons_TEstr.IH[OF mx refl m1]
  show ?case unfolding pe using ih m2 cE2 \<open>cenv E\<close> kE2 by auto
qed auto

lemma match_dep_dom:
  \<open>match_dep E K E' = Some \<phi> \<Longrightarrow> (t, TEtyp (TyFn [] (TK k))) \<in> set E' \<Longrightarrow> k \<in> set K \<Longrightarrow>
     k \<in> fst ` set \<phi>\<close>
proof (induction E K E' arbitrary: \<phi> rule: match_dep_induct)
  case (Cons_TEtyp_TyFn_Nil_TK E K t' k' r)
  consider (hd) \<open>t = t' \<and> k = k'\<close> | (tl) \<open>(t, TEtyp (TyFn [] (TK k))) \<in> set r\<close>
    using Cons_TEtyp_TyFn_Nil_TK.prems by auto
  then show ?case
  proof cases
    case hd
    then have kK: \<open>k' \<in> set K\<close> using \<open>k \<in> set K\<close> by simp
    then obtain d \<phi>' where pe: \<open>\<phi> = (k', tydef_app d []) # \<phi>'\<close>
      using Cons_TEtyp_TyFn_Nil_TK.prems
      by (auto simp: bind_eq_Some_conv split: option.split_asm tentry.split_asm if_split_asm)
    show ?thesis using pe hd by simp
  next
    case tl
    show ?thesis
    proof (cases \<open>k' \<in> set K\<close>)
      case False
      then have m: \<open>match_dep E K r = Some \<phi>\<close> using Cons_TEtyp_TyFn_Nil_TK.prems by simp
      from False m tl \<open>k \<in> set K\<close> show ?thesis by (rule Cons_TEtyp_TyFn_Nil_TK.IH)
    next
      case True
      then obtain d \<phi>' where md: \<open>map_of E t' = Some (TEtyp d)\<close> and ar: \<open>tydef_arity d = 0\<close>
        and rr: \<open>match_dep E K r = Some \<phi>'\<close> and pe: \<open>\<phi> = (k', tydef_app d []) # \<phi>'\<close>
        using Cons_TEtyp_TyFn_Nil_TK.prems
        by (auto simp: bind_eq_Some_conv split: option.split_asm tentry.split_asm if_split_asm)
      from True md refl ar rr tl \<open>k \<in> set K\<close> have \<open>k \<in> fst ` set \<phi>'\<close>
        by (rule Cons_TEtyp_TyFn_Nil_TK.IH)
      then show ?thesis using pe by simp
    qed
  qed
next
  case (Cons_TEstr E K x E\<^sub>1 r)
  obtain E\<^sub>2 \<phi>\<^sub>1 \<phi>\<^sub>2 where mx: \<open>map_of E x = Some (TEstr E\<^sub>2)\<close>
    and m1: \<open>match_dep E\<^sub>2 K E\<^sub>1 = Some \<phi>\<^sub>1\<close> and m2: \<open>match_dep E K r = Some \<phi>\<^sub>2\<close>
    and pe: \<open>\<phi> = \<phi>\<^sub>1 @ \<phi>\<^sub>2\<close>
    using Cons_TEstr.prems
    by (auto simp: bind_eq_Some_conv split: option.split_asm tentry.split_asm)
  from Cons_TEstr.prems have \<open>(t, TEtyp (TyFn [] (TK k))) \<in> set r\<close> by auto
  with mx refl m1 m2 have \<open>k \<in> fst ` set \<phi>\<^sub>2\<close> using \<open>k \<in> set K\<close> by (rule Cons_TEstr.IH)
  then show ?case using pe by auto
qed auto

text \<open>Signature elaboration is confined: the environment that a signature, a
  refinement or a spec list elaborates to is closed and binder-free, its
  \<^const>\<open>ktv\<close> variables come from the basis, and the stamp counter only grows.\<close>


lemma sig_stat_wf:
  \<open>sig_stat B n sg = Some ((T, E), n') \<Longrightarrow> cenv B \<Longrightarrow> bfree_env B \<Longrightarrow>
     n \<le> n' \<and> ftv_env E = {} \<and> frv_env E = {} \<and> ktv_env E \<subseteq> ktv_env B \<and> bfree_env E\<close>
  \<open>refn_stat B n \<Sigma> refs = Some ((T, E), n') \<Longrightarrow> cenv B \<Longrightarrow>
     ftv_env (snd \<Sigma>) = {} \<Longrightarrow> frv_env (snd \<Sigma>) = {} \<Longrightarrow> ktv_env (snd \<Sigma>) \<subseteq> ktv_env B \<Longrightarrow>
     bfree_env (snd \<Sigma>) \<Longrightarrow> bfree_env B \<Longrightarrow>
     n \<le> n' \<and> ftv_env E = {} \<and> frv_env E = {} \<and> ktv_env E \<subseteq> ktv_env B \<and> bfree_env E\<close>
  \<open>spec_stat B n T\<^sub>0 acc ss = Some ((T, E), n') \<Longrightarrow> cenv B \<Longrightarrow>
     ftv_env acc = {} \<Longrightarrow> frv_env acc = {} \<Longrightarrow> ktv_env acc \<subseteq> ktv_env B \<Longrightarrow>
     bfree_env acc \<Longrightarrow> bfree_env B \<Longrightarrow>
     n \<le> n' \<and> ftv_env E = {} \<and> frv_env E = {} \<and> ktv_env E \<subseteq> ktv_env B \<and> bfree_env E\<close>
proof (induction B n sg and B n \<Sigma> refs and B n T\<^sub>0 acc ss
       arbitrary: T E n' and T E n' and T E n'
       rule: sig_stat_induct)
  case (sig_stat_SPath B n p refs)
  obtain T\<^sub>0 E\<^sub>0 where lk: \<open>tlookup B (path_nms p) = Some (TEsig (T\<^sub>0, E\<^sub>0))\<close>
    and rf: \<open>refn_stat B n (T\<^sub>0, E\<^sub>0) refs = Some ((T, E), n')\<close>
    using sig_stat_SPath.prems by (auto split: option.split_asm tentry.split_asm)
  have cl0: \<open>ftv_env E\<^sub>0 = {}\<close> \<open>frv_env E\<^sub>0 = {}\<close>
    using cenv_tlookup_nonval[OF \<open>cenv B\<close> lk] by auto
  have k0: \<open>ktv_env E\<^sub>0 \<subseteq> ktv_env B\<close> using ktv_env_tlookup[OF lk] by simp
  have b0: \<open>bfree_env E\<^sub>0\<close> using bfree_env_tlookup[OF \<open>bfree_env B\<close> lk] by simp
  show ?case
    by (rule sig_stat_SPath.IH) (use lk rf \<open>cenv B\<close> \<open>bfree_env B\<close> cl0 k0 b0 in auto)
next
  case (sig_stat_SLit B n specs)
  have rec: \<open>spec_stat B n [] [] specs = Some ((T, E), n')\<close> using sig_stat_SLit.prems by simp
  show ?case by (rule sig_stat_SLit.IH) (auto simp: rec \<open>cenv B\<close> \<open>bfree_env B\<close>)
next
  case (refn_stat_Nil B n \<Sigma>) show ?case using refn_stat_Nil.prems by (cases \<Sigma>) auto
next
  case (refn_stat_Cons_RType B n T\<^sub>0 E\<^sub>0 t ty refs)
  show ?case
  proof (cases \<open>map_of E\<^sub>0 (n_txt t)\<close>)
    case None then show ?thesis using refn_stat_Cons_RType.prems by simp
  next
    case (Some e)
    show ?thesis
    proof (cases e)
      case (TEtyp d)
      show ?thesis
      proof (cases d)
        case (TyAbs c k)
        show ?thesis
        proof (cases \<open>k = 0 \<and> stamp c \<in> set T\<^sub>0\<close>)
          case False
          then show ?thesis using refn_stat_Cons_RType.prems Some TEtyp TyAbs
            by (auto split: if_split_asm nat.split_asm)
        next
          case True
          then have k0: \<open>k = 0\<close> and st: \<open>stamp c \<in> set T\<^sub>0\<close> by auto
          have mo: \<open>map_of E\<^sub>0 (n_txt t) = Some (TEtyp (TyAbs c 0))\<close>
            using Some TEtyp TyAbs k0 by simp
          obtain \<tau> ve\<^sub>1 n\<^sub>1 Tr where
            ts: \<open>ty_stat B False ([], []) n ty = Some (\<tau>, ve\<^sub>1, n\<^sub>1)\<close> and
            rec: \<open>refn_stat B n\<^sub>1 (removeAll (stamp c) T\<^sub>0, real_env [(stamp c, TyFn [] \<tau>)] E\<^sub>0) refs
              = Some ((Tr, E), n')\<close>
            and rp: \<open>rep_ok T\<^sub>0 c \<tau>\<close>
            using refn_stat_Cons_RType.prems mo st
            by (auto simp: bind_eq_Some_conv split: prod.split_asm if_split_asm)
          have nF: \<open>\<not> False\<close> by simp
          have tok: \<open>tve_ok ([], [])\<close> by (simp add: tve_ok_def)
          have ft\<tau>: \<open>ftv \<tau> = {}\<close> \<open>frv \<tau> = {}\<close>
            using ty_stat_closed(1)[OF ts \<open>cenv B\<close> nF] by (auto simp: tvars_def rvars_def)
          have k\<tau>: \<open>ktv \<tau> \<subseteq> ktv_env B\<close> \<open>bfree \<tau>\<close>
            using ty_stat_wf[OF ts \<open>cenv B\<close> tok, THEN conjunct2] unfolding fresh_ty_def
            by auto
          have e0: \<open>ftv_env E\<^sub>0 = {}\<close> \<open>frv_env E\<^sub>0 = {}\<close> \<open>ktv_env E\<^sub>0 \<subseteq> ktv_env B\<close> \<open>bfree_env E\<^sub>0\<close>
            using refn_stat_Cons_RType.prems by auto
          let ?E = \<open>real_env [(stamp c, TyFn [] \<tau>)] E\<^sub>0\<close>
          have cf: \<open>ftv_env ?E = {}\<close>
            using real_env_ftv[of \<open>[(stamp c, TyFn [] \<tau>)]\<close> E\<^sub>0] ft\<tau>(1) e0(1)
            by (auto simp: real_ftv_def)
          have cr: \<open>frv_env ?E = {}\<close>
            using real_env_frv[of \<open>[(stamp c, TyFn [] \<tau>)]\<close> E\<^sub>0] ft\<tau>(2) e0(2)
            by (auto simp: real_frv_def)
          have ck: \<open>ktv_env ?E \<subseteq> ktv_env B\<close>
            using real_env_ktv[of \<open>[(stamp c, TyFn [] \<tau>)]\<close> E\<^sub>0] k\<tau>(1) e0(3)
            by (auto simp: real_ktv_def)
          have cb: \<open>bfree_env ?E\<close> using bfree_real(2)[OF e0(4)] .
          have le: \<open>n \<le> n\<^sub>1\<close>
            using tve_step_le[OF ty_stat_wf[OF ts \<open>cenv B\<close> tok, THEN conjunct1]] .
          have ih: \<open>n\<^sub>1 \<le> n' \<and> ftv_env E = {} \<and> frv_env E = {} \<and> ktv_env E \<subseteq> ktv_env B \<and>
            bfree_env E\<close>
            by (rule refn_stat_Cons_RType.IH)
              (use mo st ts rp refn_stat_Cons_RType.prems cf cr ck cb in auto)
          show ?thesis using ih le by (intro conjI) (auto elim: order_trans)
        qed
      next
        case (TyFn ps b)
        then show ?thesis using refn_stat_Cons_RType.prems Some TEtyp by simp
      qed
    qed (use refn_stat_Cons_RType.prems Some in \<open>auto\<close>)
  qed
next
  case (refn_stat_Cons_RMod B n T\<^sub>0 E\<^sub>0 M P refs)
  from refn_stat_Cons_RMod.prems obtain E\<^sub>M E_P \<phi> where
    mM: \<open>map_of E\<^sub>0 (n_txt M) = Some (TEstr E\<^sub>M)\<close>
    and br: \<open>tlookup B (path_nms P) = Some (TEstr E_P) \<or>
      tlookup B (path_nms P) = Some (TEinst E_P)\<close>
    and ms: \<open>match_sig E_P T\<^sub>0 E\<^sub>M = Some \<phi>\<close>
    and rec: \<open>refn_stat B n (filter (\<lambda>k. map_of \<phi> k = None) T\<^sub>0, real_env \<phi> E\<^sub>0) refs
      = Some ((T, E), n')\<close>
    by (auto simp: bind_eq_Some_conv split: option.split_asm tentry.split_asm prod.split_asm)
  have conf: \<open>ftv_env (real_env \<phi> E\<^sub>0) = {} \<and> frv_env (real_env \<phi> E\<^sub>0) = {} \<and>
              ktv_env (real_env \<phi> E\<^sub>0) \<subseteq> ktv_env B \<and> bfree_env (real_env \<phi> E\<^sub>0)\<close>
    if ce: \<open>cenv E_P\<close> and ke: \<open>ktv_env E_P \<subseteq> ktv_env B\<close>
  proof -
    note mc = match_sig_closed[OF ms ce]
    have cf: \<open>ftv_env (real_env \<phi> E\<^sub>0) = {}\<close>
      using real_env_ftv[of \<phi> E\<^sub>0] mc refn_stat_Cons_RMod.prems by (auto simp: real_ftv_def)
    have cr: \<open>frv_env (real_env \<phi> E\<^sub>0) = {}\<close>
      using real_env_frv[of \<phi> E\<^sub>0] mc refn_stat_Cons_RMod.prems by (auto simp: real_frv_def)
    have rk: \<open>real_ktv \<phi> \<subseteq> ktv_env B\<close> using mc ke by auto
    have ck: \<open>ktv_env (real_env \<phi> E\<^sub>0) \<subseteq> ktv_env B\<close>
      using real_env_ktv[of \<phi> E\<^sub>0] rk refn_stat_Cons_RMod.prems by auto
    have b0: \<open>bfree_env E\<^sub>0\<close> using refn_stat_Cons_RMod.prems by simp
    have cb: \<open>bfree_env (real_env \<phi> E\<^sub>0)\<close> using bfree_real(2)[OF b0] .
    show ?thesis using cf cr ck cb by blast
  qed
  from br show ?case
  proof (elim disjE)
    assume tP: \<open>tlookup B (path_nms P) = Some (TEstr E_P)\<close>
    have cl: \<open>ftv_env E_P = {}\<close> \<open>frv_env E_P = {}\<close>
      using cenv_tlookup_nonval[OF \<open>cenv B\<close> tP] by auto
    have ce: \<open>cenv E_P\<close> using cenv_acc[OF cl cenv_Nil] by simp
    have ke: \<open>ktv_env E_P \<subseteq> ktv_env B\<close> using ktv_env_tlookup[OF tP] by simp
    show ?case
      by (rule refn_stat_Cons_RMod.IH,
          use mM tP ms rec conf[OF ce ke] refn_stat_Cons_RMod.prems in auto)
  next
    assume tP: \<open>tlookup B (path_nms P) = Some (TEinst E_P)\<close>
    have cl: \<open>ftv_env E_P = {}\<close> \<open>frv_env E_P = {}\<close>
      using cenv_tlookup_nonval[OF \<open>cenv B\<close> tP] by auto
    have ce: \<open>cenv E_P\<close> using cenv_acc[OF cl cenv_Nil] by simp
    have ke: \<open>ktv_env E_P \<subseteq> ktv_env B\<close> using ktv_env_tlookup[OF tP] by simp
    show ?case
      by (rule refn_stat_Cons_RMod.IH,
          use mM tP ms rec conf[OF ce ke] refn_stat_Cons_RMod.prems in auto)
  qed
next
  case (spec_stat_Cons_SpType_None B n T acc t as ss)
  have cf: \<open>ftv_env ((n_txt t, TEtyp (TyAbs (n, n_txt t, []) (length as))) # acc) = {}\<close>
    using \<open>ftv_env acc = {}\<close> by simp
  have cr: \<open>frv_env ((n_txt t, TEtyp (TyAbs (n, n_txt t, []) (length as))) # acc) = {}\<close>
    using \<open>frv_env acc = {}\<close> by simp
  have ck: \<open>ktv_env ((n_txt t, TEtyp (TyAbs (n, n_txt t, []) (length as))) # acc) \<subseteq> ktv_env B\<close>
    using \<open>ktv_env acc \<subseteq> ktv_env B\<close> by simp
  have cb: \<open>bfree_env ((n_txt t, TEtyp (TyAbs (n, n_txt t, []) (length as))) # acc)\<close>
    using \<open>bfree_env acc\<close> by simp
  show ?case
    using spec_stat_Cons_SpType_None.IH[OF _ \<open>cenv B\<close> cf cr ck cb \<open>bfree_env B\<close>]
      spec_stat_Cons_SpType_None.prems
    by simp
next
  case (spec_stat_Cons_SpType_Some B n T acc t as ty ss)
  from spec_stat_Cons_SpType_Some.prems obtain \<tau> ve\<^sub>1 n\<^sub>1 where
    ts: \<open>ty_stat (acc @ B) False (zip (map n_txt as) (map TV [n ..< n + length as]), [])
      (n + length as) ty = Some (\<tau>, ve\<^sub>1, n\<^sub>1)\<close>
    by (auto simp: bind_eq_Some_conv Let_def)
  have cB': \<open>cenv (acc @ B)\<close> using cenv_acc[OF \<open>ftv_env acc = {}\<close> \<open>frv_env acc = {}\<close> \<open>cenv B\<close>] .
  have nF: \<open>\<not> False\<close> by simp
  have tvsub:
    \<open>tvars (zip (map n_txt as) (map TV [n ..< n + length as]), []) \<subseteq> set [n ..< n + length as]\<close>
  proof
    fix x assume \<open>x \<in> tvars (zip (map n_txt as) (map TV [n ..< n + length as]), [])\<close>
    then obtain a t where at: \<open>(a, t) \<in> set (zip (map n_txt as) (map TV [n ..< n + length as]))\<close>
      \<open>x \<in> ftv t\<close>
      by (auto simp: tvars_def)
    then have \<open>t \<in> set (map TV [n ..< n + length as])\<close> by (auto dest: set_zip_rightD)
    then show \<open>x \<in> set [n ..< n + length as]\<close> using at(2) by auto
  qed
  have ft\<tau>: \<open>ftv \<tau> \<subseteq> set [n ..< n + length as]\<close>
    using ty_stat_closed(1)[OF ts cB' nF] tvsub by auto
  have rvz: \<open>rvars (zip (map n_txt as) (map TV [n ..< n + length as]), []) = {}\<close>
  proof -
    have \<open>frv t = {}\<close>
      if \<open>(a, t) \<in> set (zip (map n_txt as) (map TV [n ..< n + length as]))\<close> for a t
    proof -
      from that have \<open>t \<in> set (map TV [n ..< n + length as])\<close> by (auto dest: set_zip_rightD)
      then show ?thesis by auto
    qed
    then show ?thesis by (auto simp: rvars_def)
  qed
  have fr\<tau>: \<open>frv \<tau> = {}\<close> using ty_stat_closed(1)[OF ts cB' nF] rvz by auto
  have tokz: \<open>tve_ok (zip (map n_txt as) (map TV [n ..< n + length as]), [])\<close>
  proof -
    have \<open>ktv t = {} \<and> bfree t\<close>
      if \<open>(a, t) \<in> set (zip (map n_txt as) (map TV [n ..< n + length as]))\<close> for a t
    proof -
      from that have \<open>t \<in> set (map TV [n ..< n + length as])\<close> by (auto dest: set_zip_rightD)
      then show ?thesis by (auto simp: bfree_def)
    qed
    then show ?thesis by (auto simp: tve_ok_def)
  qed
  have le: \<open>n \<le> n\<^sub>1\<close> using tve_step_le[OF ty_stat_wf[OF ts cB' tokz, THEN conjunct1]] by simp
  let ?e = \<open>(n_txt t,
    TEtyp (TyFn [n ..< n + length as] (close_ty (set [n ..< n + length as]) {} \<tau>))) # acc\<close>
  have cf: \<open>ftv_env ?e = {}\<close> using ft\<tau> \<open>ftv_env acc = {}\<close> by (simp add: ftv_close_ty)
  have cr: \<open>frv_env ?e = {}\<close> using fr\<tau> \<open>frv_env acc = {}\<close> by (simp add: frv_close_ty)
  have ck: \<open>ktv_env ?e \<subseteq> ktv_env B\<close>
    using ktv_close_ty_sub[of \<open>set [n ..< n + length as]\<close> \<open>{}\<close> \<tau>]
          ty_stat_wf[OF ts cB' tokz, THEN conjunct2] \<open>ktv_env acc \<subseteq> ktv_env B\<close>
    unfolding fresh_ty_def by auto
  have cb: \<open>bfree_env ?e\<close> using \<open>bfree_env acc\<close> by simp
  have ih:
    \<open>n\<^sub>1 \<le> n' \<and> ftv_env E = {} \<and> frv_env E = {} \<and> ktv_env E \<subseteq> ktv_env B \<and> bfree_env E\<close>
    by (rule spec_stat_Cons_SpType_Some.IH)
      (use ts spec_stat_Cons_SpType_Some.prems cf cr ck cb in auto)
  show ?case using ih le by (intro conjI) (auto elim: order_trans)
next
  case (spec_stat_Cons_SpData B n Ta acc t as alts ss)
  let ?ps = \<open>[Suc n ..< Suc n + length as]\<close>
  let ?c = \<open>(n, n_txt t, map (\<lambda>(cn, args). (n_txt cn, length args)) alts)\<close>
  let ?en = \<open>(n_txt t, TEtyp (TyAbs ?c (length as)))\<close>
  let ?B' = \<open>?en # acc @ B\<close>
  let ?ve = \<open>(zip (map n_txt as) (map TV ?ps), [])\<close>
  have dist: \<open>distinct (map (n_txt \<circ> fst) alts)\<close>
    and nm: \<open>list_all (\<lambda>(cn, _). nm_ok (n_txt cn)) alts\<close>
    using spec_stat_Cons_SpData.prems by (auto simp: Let_def split: if_split_asm)
  obtain cs n\<^sub>1 where
    cc: \<open>cons_stat ?B' ?ve ?ps ?c (Suc n + length as) alts = Some (cs, n\<^sub>1)\<close>
    using spec_stat_Cons_SpData.prems dist nm
    by (auto simp: Let_def bind_eq_Some_conv split: prod.split_asm)
  have step: \<open>spec_stat B n\<^sub>1 (Ta @ [n]) (rev cs @ ?en # acc) ss =
    spec_stat B n Ta acc (SpData t as alts # ss)\<close>
    using dist nm cc by (simp add: Let_def)
  note rec = \<open>spec_stat B n Ta acc (SpData t as alts # ss) = Some ((T, E), n')\<close>[folded step]
  have cB': \<open>cenv ?B'\<close>
    using cenv_acc[OF \<open>ftv_env acc = {}\<close> \<open>frv_env acc = {}\<close> \<open>cenv B\<close>] by simp
  have tvsub: \<open>tvars ?ve \<subseteq> set ?ps\<close>
  proof
    fix x assume \<open>x \<in> tvars ?ve\<close>
    then obtain a t where at: \<open>(a, t) \<in> set (zip (map n_txt as) (map TV ?ps))\<close> \<open>x \<in> ftv t\<close>
      by (auto simp: tvars_def)
    then have \<open>t \<in> set (map TV ?ps)\<close> by (auto dest: set_zip_rightD)
    then show \<open>x \<in> set ?ps\<close> using at(2) by auto
  qed
  have rvz: \<open>rvars ?ve = {}\<close>
  proof -
    have \<open>frv t = {}\<close> if \<open>(a, t) \<in> set (zip (map n_txt as) (map TV ?ps))\<close> for a t
    proof -
      from that have \<open>t \<in> set (map TV ?ps)\<close> by (auto dest: set_zip_rightD)
      then show ?thesis by auto
    qed
    then show ?thesis by (auto simp: rvars_def)
  qed
  have tokz: \<open>tve_ok ?ve\<close>
  proof -
    have \<open>ktv t = {} \<and> bfree t\<close> if \<open>(a, t) \<in> set (zip (map n_txt as) (map TV ?ps))\<close> for a t
    proof -
      from that have \<open>t \<in> set (map TV ?ps)\<close> by (auto dest: set_zip_rightD)
      then show ?thesis by (auto simp: bfree_def)
    qed
    then show ?thesis by (auto simp: tve_ok_def)
  qed
  note cw = cons_stat_closed[OF cc cB' tokz tvsub rvz]
  have kB': \<open>ktv_env ?B' \<subseteq> ktv_env B\<close>
    using \<open>ktv_env acc \<subseteq> ktv_env B\<close> by auto
  have cwk: \<open>ktv_env cs \<subseteq> ktv_env B\<close> using cw kB' by auto
  let ?e = \<open>rev cs @ ?en # acc\<close>
  have cf: \<open>ftv_env ?e = {}\<close> using cw \<open>ftv_env acc = {}\<close> by auto
  have cr: \<open>frv_env ?e = {}\<close> using cw \<open>frv_env acc = {}\<close> by auto
  have ck: \<open>ktv_env ?e \<subseteq> ktv_env B\<close>
    using cwk \<open>ktv_env acc \<subseteq> ktv_env B\<close> by auto
  have cb: \<open>bfree_env ?e\<close> using cw \<open>bfree_env acc\<close> by auto
  have le: \<open>n \<le> n\<^sub>1\<close> using cons_stat_wf[OF cc cB' tokz, THEN conjunct1] by linarith
  have ih:
    \<open>n\<^sub>1 \<le> n' \<and> ftv_env E = {} \<and> frv_env E = {} \<and> ktv_env E \<subseteq> ktv_env B \<and> bfree_env E\<close>
    using spec_stat_Cons_SpData.IH[OF refl refl refl conjI[OF dist nm] cc refl rec \<open>cenv B\<close>
      cf cr ck cb \<open>bfree_env B\<close>] .
  show ?case using ih le by (intro conjI) (auto elim: order_trans)
next
  case (spec_stat_Cons_SpVal B n T acc x ty ss)
  from spec_stat_Cons_SpVal.prems obtain \<tau> ve\<^sub>1 n\<^sub>1 where
    ts: \<open>ty_stat (acc @ B) True ([], []) n ty = Some (\<tau>, ve\<^sub>1, n\<^sub>1)\<close> and nm: \<open>nm_ok (n_txt x)\<close>
    by (auto simp: bind_eq_Some_conv simp del: set_upt split: if_split_asm)
  have cB': \<open>cenv (acc @ B)\<close> using cenv_acc[OF \<open>ftv_env acc = {}\<close> \<open>frv_env acc = {}\<close> \<open>cenv B\<close>] .
  have tok: \<open>tve_ok ([], [])\<close> by (simp add: tve_ok_def)
  have ft\<tau>: \<open>ftv \<tau> \<subseteq> {n ..< n\<^sub>1}\<close> \<open>frv \<tau> \<subseteq> {n ..< n\<^sub>1}\<close>
    using ty_stat_wf[OF ts cB' tok, THEN conjunct2] unfolding fresh_ty_def
    by (auto simp: tvars_def rvars_def)
  have le: \<open>n \<le> n\<^sub>1\<close> using tve_step_le[OF ty_stat_wf[OF ts cB' tok, THEN conjunct1]] .
  let ?e = \<open>(n_txt x, TEval (close_sch (set [n ..< n\<^sub>1]) (set [n ..< n\<^sub>1]) \<tau>)) # acc\<close>
  have cf: \<open>ftv_env ?e = {}\<close>
    using ft\<tau>(1) \<open>ftv_env acc = {}\<close> by (simp add: ftv_sch_close_eq)
  have cr: \<open>frv_env ?e = {}\<close>
    using ft\<tau>(2) \<open>frv_env acc = {}\<close> by (simp add: frv_sch_close_eq)
  have ck: \<open>ktv_env ?e \<subseteq> ktv_env B\<close>
    using ktv_sch_close[of \<open>set [n ..< n\<^sub>1]\<close> \<open>set [n ..< n\<^sub>1]\<close> \<tau>]
          ty_stat_wf[OF ts cB' tok, THEN conjunct2] \<open>ktv_env acc \<subseteq> ktv_env B\<close>
    unfolding fresh_ty_def by auto
  have cb: \<open>bfree_env ?e\<close> using \<open>bfree_env acc\<close> by simp
  have ih:
    \<open>n\<^sub>1 \<le> n' \<and> ftv_env E = {} \<and> frv_env E = {} \<and> ktv_env E \<subseteq> ktv_env B \<and> bfree_env E\<close>
    by (rule spec_stat_Cons_SpVal.IH)
      (use nm ts spec_stat_Cons_SpVal.prems cf cr ck cb in \<open>auto simp del: set_upt\<close>)
  show ?case using ih le by (intro conjI) (auto elim: order_trans)
next
  case (spec_stat_Cons_SpEff B n Ta acc x as ops ss)
  from spec_stat_Cons_SpEff.prems obtain es n\<^sub>1
    where wf: \<open>distinct (map n_txt as)\<close>
    and os: \<open>ops_stat (acc @ B) (mangle (str ''%spec'') (n_txt x)) (eff_ps as n) (eff_ve as n)
      (n + length as) ops = Some (es, n\<^sub>1)\<close>
    by (auto simp: bind_eq_Some_conv split: if_split_asm)
  let ?ee =
    \<open>(n_txt x, TEeff (mangle (str ''%spec'') (n_txt x)) (map fst es) (length as))\<close>
  obtain Tf where rec: \<open>spec_stat B n\<^sub>1 Ta (rev es @ ?ee # acc) ss = Some ((Tf, E), n')\<close>
    using spec_stat_Cons_SpEff.prems wf os by (auto simp: bind_eq_Some_conv split: if_split_asm)
  have cB': \<open>cenv (acc @ B)\<close>
    using cenv_acc[OF \<open>ftv_env acc = {}\<close> \<open>frv_env acc = {}\<close> \<open>cenv B\<close>] .
  note oc = ops_stat_closed[OF os cB' eff_ve_ok]
  have le: \<open>n \<le> n\<^sub>1\<close> using ops_stat_wf[OF os cB' eff_ve_ok(1)] by simp
  let ?e = \<open>rev es @ ?ee # acc\<close>
  have cf: \<open>ftv_env ?e = {}\<close> using oc \<open>ftv_env acc = {}\<close> by simp
  have cr: \<open>frv_env ?e = {}\<close> using oc \<open>frv_env acc = {}\<close> by simp
  have ck: \<open>ktv_env ?e \<subseteq> ktv_env B\<close>
    using oc \<open>ktv_env acc \<subseteq> ktv_env B\<close> by auto
  have cb: \<open>bfree_env ?e\<close> using oc \<open>bfree_env acc\<close> by simp
  have ih:
    \<open>n\<^sub>1 \<le> n' \<and> ftv_env E = {} \<and> frv_env E = {} \<and> ktv_env E \<subseteq> ktv_env B \<and> bfree_env E\<close>
    using spec_stat_Cons_SpEff.IH[OF wf os refl rec \<open>cenv B\<close> cf cr ck cb \<open>bfree_env B\<close>] .
  show ?case using ih le by (intro conjI) (auto elim: order_trans)
next
  case (spec_stat_Cons_SpFix B n T acc f pr opr ss)
  from spec_stat_Cons_SpFix.prems obtain prec where rn: \<open>read_nat (n_txt pr) = Some prec\<close>
    by (cases \<open>read_nat (n_txt pr)\<close>) (auto simp: bind_eq_Some_conv)
  let ?e = \<open>(fix_key (n_txt opr), TEfix f prec) # acc\<close>
  have cf: \<open>ftv_env ?e = {}\<close> using \<open>ftv_env acc = {}\<close> by simp
  have cr: \<open>frv_env ?e = {}\<close> using \<open>frv_env acc = {}\<close> by simp
  have ck: \<open>ktv_env ?e \<subseteq> ktv_env B\<close> using \<open>ktv_env acc \<subseteq> ktv_env B\<close> by simp
  have cb: \<open>bfree_env ?e\<close> using \<open>bfree_env acc\<close> by simp
  show ?case
    using spec_stat_Cons_SpFix.IH[OF rn _ \<open>cenv B\<close> cf cr ck cb \<open>bfree_env B\<close>]
      spec_stat_Cons_SpFix.prems rn
    by (simp add: bind_eq_Some_conv)
next
  case (spec_stat_Cons_SpMod B n Ta acc x sg ss)
  from spec_stat_Cons_SpMod.prems obtain T' E' n\<^sub>1
    where sig: \<open>sig_stat (acc @ B) n sg = Some ((T', E'), n\<^sub>1)\<close> and nm: \<open>nm_ok (n_txt x)\<close>
    by (auto simp: bind_eq_Some_conv split: prod.split_asm if_split_asm)
  obtain Tf
    where rec: \<open>spec_stat B n\<^sub>1 (Ta @ T') ((n_txt x, TEstr E') # acc) ss = Some ((Tf, E), n')\<close>
    using spec_stat_Cons_SpMod.prems sig nm by (auto simp: bind_eq_Some_conv split: prod.split_asm)
  have cB': \<open>cenv (acc @ B)\<close>
    using cenv_acc[OF \<open>ftv_env acc = {}\<close> \<open>frv_env acc = {}\<close> \<open>cenv B\<close>] .
  have bB': \<open>bfree_env (acc @ B)\<close> using \<open>bfree_env acc\<close> \<open>bfree_env B\<close> by simp
  have sw: \<open>n \<le> n\<^sub>1 \<and> ftv_env E' = {} \<and> frv_env E' = {} \<and> ktv_env E' \<subseteq> ktv_env (acc @ B) \<and>
    bfree_env E'\<close>
    by (rule spec_stat_Cons_SpMod.IH[OF nm], use sig cB' bB' in auto)
  have le: \<open>n \<le> n\<^sub>1\<close> using sw by simp
  let ?e = \<open>(n_txt x, TEstr E') # acc\<close>
  have cf: \<open>ftv_env ?e = {}\<close> using sw \<open>ftv_env acc = {}\<close> by simp
  have cr: \<open>frv_env ?e = {}\<close> using sw \<open>frv_env acc = {}\<close> by simp
  have ck: \<open>ktv_env ?e \<subseteq> ktv_env B\<close>
    using sw \<open>ktv_env acc \<subseteq> ktv_env B\<close> by auto
  have cb: \<open>bfree_env ?e\<close> using sw \<open>bfree_env acc\<close> by simp
  from nm sig refl refl rec \<open>cenv B\<close> cf cr ck cb \<open>bfree_env B\<close>
  have ih:
    \<open>n\<^sub>1 \<le> n' \<and> ftv_env E = {} \<and> frv_env E = {} \<and> ktv_env E \<subseteq> ktv_env B \<and> bfree_env E\<close>
    by (rule spec_stat_Cons_SpMod.IH)
  show ?case using ih le by (intro conjI) (auto elim: order_trans)
next
  case (spec_stat_Cons_SpInc B n Ta acc sg ss)
  from spec_stat_Cons_SpInc.prems obtain T' E' n\<^sub>1
    where sig: \<open>sig_stat (acc @ B) n sg = Some ((T', E'), n\<^sub>1)\<close>
    by (auto simp: bind_eq_Some_conv split: prod.split_asm)
  obtain Tf where rec: \<open>spec_stat B n\<^sub>1 (Ta @ T') (rev E' @ acc) ss = Some ((Tf, E), n')\<close>
    using spec_stat_Cons_SpInc.prems sig by (auto simp: bind_eq_Some_conv split: prod.split_asm)
  have cB': \<open>cenv (acc @ B)\<close>
    using cenv_acc[OF \<open>ftv_env acc = {}\<close> \<open>frv_env acc = {}\<close> \<open>cenv B\<close>] .
  have bB': \<open>bfree_env (acc @ B)\<close> using \<open>bfree_env acc\<close> \<open>bfree_env B\<close> by simp
  have sw: \<open>n \<le> n\<^sub>1 \<and> ftv_env E' = {} \<and> frv_env E' = {} \<and> ktv_env E' \<subseteq> ktv_env (acc @ B) \<and>
    bfree_env E'\<close>
    by (rule spec_stat_Cons_SpInc.IH, use sig cB' bB' in auto)
  have le: \<open>n \<le> n\<^sub>1\<close> using sw by simp
  let ?e = \<open>rev E' @ acc\<close>
  have cf: \<open>ftv_env ?e = {}\<close> using sw \<open>ftv_env acc = {}\<close> by simp
  have cr: \<open>frv_env ?e = {}\<close> using sw \<open>frv_env acc = {}\<close> by simp
  have ck: \<open>ktv_env ?e \<subseteq> ktv_env B\<close>
    using sw \<open>ktv_env acc \<subseteq> ktv_env B\<close> by auto
  have cb: \<open>bfree_env ?e\<close> using sw \<open>bfree_env acc\<close> by simp
  from sig refl refl rec \<open>cenv B\<close> cf cr ck cb \<open>bfree_env B\<close>
  have ih:
    \<open>n\<^sub>1 \<le> n' \<and> ftv_env E = {} \<and> frv_env E = {} \<and> ktv_env E \<subseteq> ktv_env B \<and> bfree_env E\<close>
    by (rule spec_stat_Cons_SpInc.IH)
  show ?case using ih le by (intro conjI) (auto elim: order_trans)
qed (auto split: if_split_asm)


lemma cons_stat_pure: \<open>cons_stat B ve ps c n alts = Some (cs, n\<^sub>1) \<Longrightarrow> pure_env cs\<close>
  by (induction B ve ps c n alts arbitrary: cs n\<^sub>1 rule: cons_stat.induct)
     (auto simp: bind_eq_Some_conv Let_def split: prod.split_asm)

lemma ops_stat_pure: \<open>ops_stat B pre ps ve n ops = Some (es, n') \<Longrightarrow> pure_env es\<close>
proof (induction ops arbitrary: n es n')
  case (Cons oty ops)
  obtain opn ty where oty: \<open>oty = (opn, ty)\<close> by (cases oty)
  from Cons.prems obtain t\<^sub>1 t\<^sub>2 n\<^sub>1 es' where
    ops: \<open>ops_stat B pre ps ve n\<^sub>1 ops = Some (es', n')\<close> and
    es: \<open>es = (n_txt opn, TEop (mangle pre (n_txt opn)) ps
      (close_ty (set ps) {} t\<^sub>1) (close_ty (set ps) {} t\<^sub>2)) # es'\<close>
    unfolding oty by (blast elim: ops_stat_ConsE)
  from Cons.IH[OF ops] show ?case by (simp add: es)
qed simp

text \<open>Coverage: every abstract stamp a signature reports is realised by a
  \<open>TyAbs\<close> member of the environment it reports (so \<open>dep_vars\<close> plants a hole for
  each and \<open>match_dep\<close> resolves them). Reported environments stay pure.\<close>

lemma sig_stat_covers:
  \<open>sig_stat B n sg = Some ((RT, E), n') \<Longrightarrow> sig_wf_env B \<Longrightarrow>
     (\<forall>t\<in>set RT. abs_present t E) \<and> pure_env E\<close>
  \<open>refn_stat B n \<Sigma> refs = Some ((RT, E), n') \<Longrightarrow> sig_wf_env B \<Longrightarrow>
     (\<forall>t\<in>set (fst \<Sigma>). abs_present t (snd \<Sigma>)) \<Longrightarrow> pure_env (snd \<Sigma>) \<Longrightarrow>
     (\<forall>t\<in>set RT. abs_present t E) \<and> pure_env E\<close>
  \<open>spec_stat B n T\<^sub>0 acc ss = Some ((RT, E), n') \<Longrightarrow> sig_wf_env B \<Longrightarrow>
     (\<forall>t\<in>set T\<^sub>0. abs_present t acc) \<Longrightarrow> pure_env acc \<Longrightarrow>
     (\<forall>t\<in>set RT. abs_present t E) \<and> pure_env E\<close>
proof (induction B n sg and B n \<Sigma> refs and B n T\<^sub>0 acc ss
       arbitrary: RT E n' and RT E n' and RT E n'
       rule: sig_stat_induct)
  case (sig_stat_SPath B n p refs)
  obtain T\<^sub>0 E\<^sub>0 where lk: \<open>tlookup B (path_nms p) = Some (TEsig (T\<^sub>0, E\<^sub>0))\<close>
    and rf: \<open>refn_stat B n (T\<^sub>0, E\<^sub>0) refs = Some ((RT, E), n')\<close>
    using sig_stat_SPath.prems by (auto split: option.split_asm tentry.split_asm)
  have wf0: \<open>(\<forall>t\<in>set T\<^sub>0. abs_present t E\<^sub>0) \<and> sig_wf_env E\<^sub>0 \<and> pure_env E\<^sub>0\<close>
    using sig_wf_tlookup[OF \<open>sig_wf_env B\<close> lk] by simp
  show ?case by (rule sig_stat_SPath.IH) (use lk rf \<open>sig_wf_env B\<close> wf0 in auto)
next
  case (sig_stat_SLit B n specs)
  have rec: \<open>spec_stat B n [] [] specs = Some ((RT, E), n')\<close> using sig_stat_SLit.prems by simp
  show ?case by (rule sig_stat_SLit.IH) (use rec \<open>sig_wf_env B\<close> in auto)
next
  case (refn_stat_Nil B n \<Sigma>) show ?case using refn_stat_Nil.prems by (cases \<Sigma>) auto
next
  case (refn_stat_Cons_RType B n T\<^sub>0 E\<^sub>0 t ty refs)
  show ?case
  proof (cases \<open>map_of E\<^sub>0 (n_txt t)\<close>)
    case None then show ?thesis using refn_stat_Cons_RType.prems by simp
  next
    case (Some e)
    show ?thesis
    proof (cases e)
      case (TEtyp d)
      show ?thesis
      proof (cases d)
        case (TyAbs c k)
        show ?thesis
        proof (cases \<open>k = 0 \<and> stamp c \<in> set T\<^sub>0\<close>)
          case False
          then show ?thesis using refn_stat_Cons_RType.prems Some TEtyp TyAbs
            by (auto split: if_split_asm nat.split_asm)
        next
          case True
          then have k0: \<open>k = 0\<close> and st: \<open>stamp c \<in> set T\<^sub>0\<close> by auto
          have mo: \<open>map_of E\<^sub>0 (n_txt t) = Some (TEtyp (TyAbs c 0))\<close>
            using Some TEtyp TyAbs k0 by simp
          obtain \<tau> ve\<^sub>1 n\<^sub>1 Tr where
            ts: \<open>ty_stat B False ([], []) n ty = Some (\<tau>, ve\<^sub>1, n\<^sub>1)\<close> and
            rec: \<open>refn_stat B n\<^sub>1 (removeAll (stamp c) T\<^sub>0, real_env [(stamp c, TyFn [] \<tau>)] E\<^sub>0) refs
              = Some ((Tr, E), n')\<close>
            and rp: \<open>rep_ok T\<^sub>0 c \<tau>\<close>
            using refn_stat_Cons_RType.prems mo st
            by (auto simp: bind_eq_Some_conv split: prod.split_asm if_split_asm)
          have cov': \<open>\<forall>t'\<in>set (removeAll (stamp c) T\<^sub>0).
            abs_present t' (real_env [(stamp c, TyFn [] \<tau>)] E\<^sub>0)\<close>
          proof
            fix t' assume \<open>t' \<in> set (removeAll (stamp c) T\<^sub>0)\<close>
            then have tin: \<open>t' \<in> set T\<^sub>0\<close> and tne: \<open>t' \<noteq> stamp c\<close> by auto
            have \<open>abs_present t' E\<^sub>0\<close> using refn_stat_Cons_RType.prems tin by simp
            then show \<open>abs_present t' (real_env [(stamp c, TyFn [] \<tau>)] E\<^sub>0)\<close>
              using abs_present_real(2)[of t' E\<^sub>0 \<open>[(stamp c, TyFn [] \<tau>)]\<close>] tne by simp
          qed
          have pur': \<open>pure_env (real_env [(stamp c, TyFn [] \<tau>)] E\<^sub>0)\<close>
            using refn_stat_Cons_RType.prems by (simp add: pure_real)
          show ?thesis by (rule refn_stat_Cons_RType.IH)
            (use mo st ts rp rec refn_stat_Cons_RType.prems cov' pur' in auto)
        qed
      next
        case (TyFn ps b) then show ?thesis using refn_stat_Cons_RType.prems Some TEtyp by simp
      qed
    qed (use refn_stat_Cons_RType.prems Some in \<open>auto\<close>)
  qed
next
  case (refn_stat_Cons_RMod B n T\<^sub>0 E\<^sub>0 M P refs)
  from refn_stat_Cons_RMod.prems obtain E\<^sub>M E_P \<phi> where
    mM: \<open>map_of E\<^sub>0 (n_txt M) = Some (TEstr E\<^sub>M)\<close>
    and br: \<open>tlookup B (path_nms P) = Some (TEstr E_P) \<or>
      tlookup B (path_nms P) = Some (TEinst E_P)\<close>
    and ms: \<open>match_sig E_P T\<^sub>0 E\<^sub>M = Some \<phi>\<close>
    and rec: \<open>refn_stat B n (filter (\<lambda>k. map_of \<phi> k = None) T\<^sub>0, real_env \<phi> E\<^sub>0) refs
      = Some ((RT, E), n')\<close>
    by (auto simp: bind_eq_Some_conv split: option.split_asm tentry.split_asm prod.split_asm)
  have cov':
    \<open>\<forall>t'\<in>set (filter (\<lambda>k. map_of \<phi> k = None) T\<^sub>0). abs_present t' (real_env \<phi> E\<^sub>0)\<close>
  proof
    fix t' assume \<open>t' \<in> set (filter (\<lambda>k. map_of \<phi> k = None) T\<^sub>0)\<close>
    then have tin: \<open>t' \<in> set T\<^sub>0\<close> and tnd: \<open>map_of \<phi> t' = None\<close> by auto
    have \<open>abs_present t' E\<^sub>0\<close> using refn_stat_Cons_RMod.prems tin by simp
    then show \<open>abs_present t' (real_env \<phi> E\<^sub>0)\<close>
      using abs_present_real(2)[of t' E\<^sub>0 \<phi>] tnd by (simp add: map_of_eq_None_iff)
  qed
  have pur': \<open>pure_env (real_env \<phi> E\<^sub>0)\<close>
    using refn_stat_Cons_RMod.prems by (simp add: pure_real)
  from br show ?case
  proof (elim disjE)
    assume tP: \<open>tlookup B (path_nms P) = Some (TEstr E_P)\<close>
    show ?case
      by (rule refn_stat_Cons_RMod.IH, use mM tP ms rec \<open>sig_wf_env B\<close> cov' pur' in auto)
  next
    assume tP: \<open>tlookup B (path_nms P) = Some (TEinst E_P)\<close>
    show ?case
      by (rule refn_stat_Cons_RMod.IH, use mM tP ms rec \<open>sig_wf_env B\<close> cov' pur' in auto)
  qed
next
  case (spec_stat_Cons_SpType_None B n T acc t as ss)
  let ?en = \<open>(n_txt t, TEtyp (TyAbs (n, n_txt t, []) (length as)))\<close>
  have cov': \<open>\<forall>t'\<in>set (T @ [n]). abs_present t' (?en # acc)\<close>
    using \<open>\<forall>t\<in>set T. abs_present t acc\<close> by auto
  have pur': \<open>pure_env (?en # acc)\<close> using \<open>pure_env acc\<close> by simp
  show ?case
    using spec_stat_Cons_SpType_None.IH[OF _ \<open>sig_wf_env B\<close> cov' pur']
      spec_stat_Cons_SpType_None.prems
    by simp
next
  case (spec_stat_Cons_SpType_Some B n T acc t as ty ss)
  from spec_stat_Cons_SpType_Some.prems obtain \<tau> ve\<^sub>1 n\<^sub>1 where
    ts: \<open>ty_stat (acc @ B) False (zip (map n_txt as) (map TV [n ..< n + length as]), [])
      (n + length as) ty = Some (\<tau>, ve\<^sub>1, n\<^sub>1)\<close>
    by (auto simp: bind_eq_Some_conv Let_def)
  let ?en = \<open>(n_txt t,
    TEtyp (TyFn [n ..< n + length as] (close_ty (set [n ..< n + length as]) {} \<tau>)))\<close>
  have cov': \<open>\<forall>t'\<in>set T. abs_present t' (?en # acc)\<close>
    using \<open>\<forall>t\<in>set T. abs_present t acc\<close> by simp
  have pur': \<open>pure_env (?en # acc)\<close> using \<open>pure_env acc\<close> by simp
  show ?case
    by (rule spec_stat_Cons_SpType_Some.IH)
      (use ts spec_stat_Cons_SpType_Some.prems cov' pur' in \<open>auto simp: Let_def\<close>)
next
  case (spec_stat_Cons_SpData B n Ta acc t as alts ss)
  let ?ps = \<open>[Suc n ..< Suc n + length as]\<close>
  let ?c = \<open>(n, n_txt t, map (\<lambda>(cn, args). (n_txt cn, length args)) alts)\<close>
  let ?en = \<open>(n_txt t, TEtyp (TyAbs ?c (length as)))\<close>
  let ?B' = \<open>?en # acc @ B\<close>
  let ?ve = \<open>(zip (map n_txt as) (map TV ?ps), [])\<close>
  have dist: \<open>distinct (map (n_txt \<circ> fst) alts)\<close>
    and nm: \<open>list_all (\<lambda>(cn, _). nm_ok (n_txt cn)) alts\<close>
    using spec_stat_Cons_SpData.prems by (auto simp: Let_def split: if_split_asm)
  obtain cs n\<^sub>1 where
    cc: \<open>cons_stat ?B' ?ve ?ps ?c (Suc n + length as) alts = Some (cs, n\<^sub>1)\<close>
    using spec_stat_Cons_SpData.prems dist nm
    by (auto simp: Let_def bind_eq_Some_conv split: prod.split_asm)
  have step: \<open>spec_stat B n\<^sub>1 (Ta @ [n]) (rev cs @ ?en # acc) ss =
    spec_stat B n Ta acc (SpData t as alts # ss)\<close>
    using dist nm cc by (simp add: Let_def)
  note rec = \<open>spec_stat B n Ta acc (SpData t as alts # ss) = Some ((RT, E), n')\<close>[folded step]
  have cwp: \<open>pure_env cs\<close> using cons_stat_pure[OF cc] .
  have cwc: \<open>\<forall>t'\<in>set (Ta @ [n]). abs_present t' (rev cs @ ?en # acc)\<close>
    using \<open>\<forall>t\<in>set Ta. abs_present t acc\<close> by auto
  have pur': \<open>pure_env (rev cs @ ?en # acc)\<close> using cwp \<open>pure_env acc\<close> by simp
  show ?case
    using spec_stat_Cons_SpData.IH[OF refl refl refl conjI[OF dist nm] cc refl rec \<open>sig_wf_env B\<close>
      cwc pur'] .
next
  case (spec_stat_Cons_SpVal B n T acc x ty ss)
  from spec_stat_Cons_SpVal.prems obtain \<tau> ve\<^sub>1 n\<^sub>1 where
    ts: \<open>ty_stat (acc @ B) True ([], []) n ty = Some (\<tau>, ve\<^sub>1, n\<^sub>1)\<close> and nm: \<open>nm_ok (n_txt x)\<close>
    by (auto simp: bind_eq_Some_conv simp del: set_upt split: if_split_asm)
  let ?en = \<open>(n_txt x, TEval (close_sch (set [n ..< n\<^sub>1]) (set [n ..< n\<^sub>1]) \<tau>))\<close>
  have cov': \<open>\<forall>t'\<in>set T. abs_present t' (?en # acc)\<close>
    using \<open>\<forall>t\<in>set T. abs_present t acc\<close> by simp
  have pur': \<open>pure_env (?en # acc)\<close> using \<open>pure_env acc\<close> by simp
  show ?case
    by (rule spec_stat_Cons_SpVal.IH)
      (use nm ts spec_stat_Cons_SpVal.prems cov' pur' in \<open>auto simp del: set_upt\<close>)
next
  case (spec_stat_Cons_SpEff B n Ta acc x as ops ss)
  from spec_stat_Cons_SpEff.prems obtain es n\<^sub>1
    where wf: \<open>distinct (map n_txt as)\<close>
    and os: \<open>ops_stat (acc @ B) (mangle (str ''%spec'') (n_txt x)) (eff_ps as n) (eff_ve as n)
      (n + length as) ops = Some (es, n\<^sub>1)\<close>
    by (auto simp: bind_eq_Some_conv split: if_split_asm)
  have esp: \<open>pure_env es\<close> using ops_stat_pure[OF os] .
  let ?e = \<open>rev es @
    (n_txt x, TEeff (mangle (str ''%spec'') (n_txt x)) (map fst es) (length as)) # acc\<close>
  have cov': \<open>\<forall>t'\<in>set Ta. abs_present t' ?e\<close> using \<open>\<forall>t\<in>set Ta. abs_present t acc\<close> by auto
  have pur': \<open>pure_env ?e\<close> using esp \<open>pure_env acc\<close> by simp
  from spec_stat_Cons_SpEff.prems os wf
  have rec: \<open>spec_stat B n\<^sub>1 Ta ?e ss = Some ((RT, E), n')\<close> by (auto simp: bind_eq_Some_conv)
  show ?case
    by (rule spec_stat_Cons_SpEff.IH) (use wf os rec \<open>sig_wf_env B\<close> cov' pur' in auto)
next
  case (spec_stat_Cons_SpFix B n T acc f pr opr ss)
  from spec_stat_Cons_SpFix.prems obtain prec where rn: \<open>read_nat (n_txt pr) = Some prec\<close>
    by (cases \<open>read_nat (n_txt pr)\<close>) (auto simp: bind_eq_Some_conv)
  let ?en = \<open>(fix_key (n_txt opr), TEfix f prec)\<close>
  have cov': \<open>\<forall>t'\<in>set T. abs_present t' (?en # acc)\<close>
    using \<open>\<forall>t\<in>set T. abs_present t acc\<close> by simp
  have pur': \<open>pure_env (?en # acc)\<close> using \<open>pure_env acc\<close> by simp
  show ?case
    using spec_stat_Cons_SpFix.IH[OF rn _ \<open>sig_wf_env B\<close> cov' pur'] spec_stat_Cons_SpFix.prems rn
    by (simp add: bind_eq_Some_conv)
next
  case (spec_stat_Cons_SpMod B n Ta acc x sg ss)
  from spec_stat_Cons_SpMod.prems obtain T' E' n\<^sub>1
    where sig: \<open>sig_stat (acc @ B) n sg = Some ((T', E'), n\<^sub>1)\<close> and nm: \<open>nm_ok (n_txt x)\<close>
    by (auto simp: bind_eq_Some_conv split: prod.split_asm if_split_asm)
  have rec: \<open>spec_stat B n\<^sub>1 (Ta @ T') ((n_txt x, TEstr E') # acc) ss = Some ((RT, E), n')\<close>
    using spec_stat_Cons_SpMod.prems sig nm by (auto simp: bind_eq_Some_conv split: prod.split_asm)
  have swB': \<open>sig_wf_env (acc @ B)\<close>
    using pure_sig_wf(2)[OF \<open>pure_env acc\<close>] \<open>sig_wf_env B\<close> by simp
  have sw: \<open>(\<forall>t\<in>set T'. abs_present t E') \<and> pure_env E'\<close>
    by (rule spec_stat_Cons_SpMod.IH[OF nm], use sig swB' in auto)
  let ?e = \<open>(n_txt x, TEstr E') # acc\<close>
  have cov': \<open>\<forall>t'\<in>set (Ta @ T'). abs_present t' ?e\<close>
    using \<open>\<forall>t\<in>set Ta. abs_present t acc\<close> sw by auto
  have pur': \<open>pure_env ?e\<close> using sw \<open>pure_env acc\<close> by simp
  from nm sig refl refl rec \<open>sig_wf_env B\<close> cov' pur' show ?case
    by (rule spec_stat_Cons_SpMod.IH)
next
  case (spec_stat_Cons_SpInc B n Ta acc sg ss)
  from spec_stat_Cons_SpInc.prems obtain T' E' n\<^sub>1
    where sig: \<open>sig_stat (acc @ B) n sg = Some ((T', E'), n\<^sub>1)\<close>
    by (auto simp: bind_eq_Some_conv split: prod.split_asm)
  have rec: \<open>spec_stat B n\<^sub>1 (Ta @ T') (rev E' @ acc) ss = Some ((RT, E), n')\<close>
    using spec_stat_Cons_SpInc.prems sig by (auto simp: bind_eq_Some_conv split: prod.split_asm)
  have swB': \<open>sig_wf_env (acc @ B)\<close>
    using pure_sig_wf(2)[OF \<open>pure_env acc\<close>] \<open>sig_wf_env B\<close> by simp
  have sw: \<open>(\<forall>t\<in>set T'. abs_present t E') \<and> pure_env E'\<close>
    by (rule spec_stat_Cons_SpInc.IH, use sig swB' in auto)
  let ?e = \<open>rev E' @ acc\<close>
  have cov': \<open>\<forall>t'\<in>set (Ta @ T'). abs_present t' ?e\<close>
    using \<open>\<forall>t\<in>set Ta. abs_present t acc\<close> sw by auto
  have pur': \<open>pure_env ?e\<close> using sw \<open>pure_env acc\<close> by simp
  from sig refl refl rec \<open>sig_wf_env B\<close> cov' pur' show ?case
    by (rule spec_stat_Cons_SpInc.IH)
qed (auto split: if_split_asm)

text \<open>The environment of a dependent functor parameter. \<^const>\<open>dep_env\<close> draws
  \<open>m\<close> fresh distinct stamps \<open>K\<close> for the signature's abstract types, so the
  environment is closed and its \<^const>\<open>ktv\<close> variables come from the basis or
  from \<open>K\<close>.\<close>

lemma dep_env_wf:
  \<open>dep_env B n sg m = Some (K, E, n') \<Longrightarrow> cenv B \<Longrightarrow> bfree_env B \<Longrightarrow>
     n \<le> n' \<and> length K = m \<and> distinct K \<and> set K \<subseteq> {n ..< n'} \<and>
     ftv_env E = {} \<and> frv_env E = {} \<and> ktv_env E \<subseteq> ktv_env B \<union> set K \<and> bfree_env E\<close>
proof -
  assume de: \<open>dep_env B n sg m = Some (K, E, n')\<close> and cB: \<open>cenv B\<close> and bB: \<open>bfree_env B\<close>
  from de obtain T E\<^sub>0 n\<^sub>0 where ss: \<open>sig_stat B n sg = Some ((T, E\<^sub>0), n\<^sub>0)\<close> and
    Keq: \<open>K = [n\<^sub>0 ..< n\<^sub>0 + m]\<close> and Eeq: \<open>E = real_env (dep_vars T K) E\<^sub>0\<close> and
    n'eq: \<open>n' = n\<^sub>0 + m\<close> and lenT: \<open>length T = m\<close>
    by (auto simp: dep_env_def bind_eq_Some_conv split: prod.split_asm if_split_asm)
  note w = sig_stat_wf(1)[OF ss cB bB]
  have le0: \<open>n \<le> n\<^sub>0\<close> using w by simp
  have le: \<open>n \<le> n'\<close> using le0 unfolding n'eq by simp
  have Kfacts: \<open>length K = m\<close> \<open>distinct K\<close> \<open>set K \<subseteq> {n ..< n'}\<close>
    using le0 unfolding Keq n'eq by auto
  have b0: \<open>bfree_env E\<^sub>0\<close> using w by simp
  have cf: \<open>ftv_env E = {}\<close> unfolding Eeq
    using real_env_ftv[of \<open>dep_vars T K\<close> E\<^sub>0] w dep_vars_ftv[of T K] by auto
  have cr: \<open>frv_env E = {}\<close> unfolding Eeq
    using real_env_frv[of \<open>dep_vars T K\<close> E\<^sub>0] w dep_vars_frv[of T K] by auto
  have ck: \<open>ktv_env E \<subseteq> ktv_env B \<union> set K\<close> unfolding Eeq
    using real_env_ktv[of \<open>dep_vars T K\<close> E\<^sub>0] w dep_vars_ktv[of T K] by auto
  have cb: \<open>bfree_env E\<close> unfolding Eeq using bfree_real(2)[OF b0] .
  show ?thesis using le Kfacts cf cr ck cb by blast
qed

lemma tsl_zipK_Some: \<open>map_of (zip K (map TK K')) k = Some u \<Longrightarrow> \<exists>k' \<in> set K'. u = TK k'\<close>
  by (auto simp: set_zip dest!: map_of_SomeD)

lemma tsl_zipK_vars:
  \<open>ftv (tsl (zip K (map TK K')) k) = {}\<close> \<open>frv (tsl (zip K (map TK K')) k) = {}\<close>
  \<open>btv (tsl (zip K (map TK K')) k) = {}\<close> \<open>brv (tsl (zip K (map TK K')) k) = {}\<close>
  \<open>ktv (tsl (zip K (map TK K')) k) \<subseteq> insert k (set K')\<close>
  by (auto simp: tsl_def split: option.split dest!: tsl_zipK_Some)

lemma fresh_ok_ksubst_rename:
  assumes f: \<open>fresh_ok (TAct lt K \<epsilon> \<tau>) 0 n FK\<close>
    and len: \<open>length K = length K'\<close> and dj: \<open>set K \<inter> ktv \<tau> = {}\<close>
  shows \<open>fresh_ok (TAct lt K' \<epsilon> (ksubst (tsl (zip K (map TK K'))) \<tau>)) 0 n FK\<close>
proof -
  have \<open>map_of (zip K (map TK K')) k = None\<close> if \<open>k \<in> ktv \<tau>\<close> for k
    using that len dj map_of_zip_is_None[of K \<open>map TK K'\<close> k] by auto
  then have \<open>ksubst (tsl (zip K (map TK K'))) \<tau> = \<tau>\<close> by (intro ksubst_id) (simp add: tsl_def)
  then show ?thesis using f by (simp add: fresh_ok_def bfree_def)
qed

text \<open>The renaming of an annotation's action binders keeps the type fresh.\<close>

lemma fresh_ok_act_rename:
  assumes \<open>fresh_ok \<tau>\<^sub>a 0 n FK\<close>
  shows \<open>fresh_ok (act_rename B \<tau> \<tau>\<^sub>a) 0 n FK\<close>
proof (cases \<tau>)
  case (TAct lt K \<epsilon>\<^sub>0 \<tau>\<^sub>0)
  show ?thesis
  proof (cases \<tau>\<^sub>a)
    case (TAct lt' K' \<epsilon>\<^sub>0' \<tau>\<^sub>0')
    then show ?thesis
      using assms \<open>\<tau> = TAct lt K \<epsilon>\<^sub>0 \<tau>\<^sub>0\<close> fresh_ok_ksubst_rename[of lt' K' \<epsilon>\<^sub>0' \<tau>\<^sub>0' n FK K]
      by (auto simp: act_rename_def)
  qed (use assms \<open>\<tau> = TAct lt K \<epsilon>\<^sub>0 \<tau>\<^sub>0\<close> in \<open>simp_all add: act_rename_def\<close>)
qed (use assms in \<open>simp_all add: act_rename_def\<close>)

lemma fresh_ok_ann_ty:
  assumes \<open>fresh_ok \<tau>\<^sub>a 0 n FK\<close>
  shows \<open>fresh_ok (ann_ty B \<tau> \<tau>\<^sub>a) 0 n FK\<close>
proof (cases \<tau>)
  case (TFn t\<^sub>1 \<epsilon> t\<^sub>2)
  show ?thesis
  proof (cases \<tau>\<^sub>a)
    case (TFn t\<^sub>1' \<epsilon>' t\<^sub>2')
    have f\<^sub>1: \<open>fresh_ok t\<^sub>1' 0 n FK\<close> and f\<^sub>2: \<open>fresh_ok t\<^sub>2' 0 n FK\<close>
      and r\<^sub>1: \<open>frv_row \<epsilon>' \<subseteq> {..< n}\<close> and r\<^sub>2: \<open>brv_row \<epsilon>' = {}\<close>
      using assms unfolding TFn by (auto simp: fresh_ok_def bfree_def)
    show ?thesis
      using fresh_ok_TFn[OF fresh_ok_act_rename[OF f\<^sub>1] f\<^sub>2 r\<^sub>1 r\<^sub>2]
      by (simp add: ann_ty_def \<open>\<tau> = TFn t\<^sub>1 \<epsilon> t\<^sub>2\<close> TFn)
  qed (use assms \<open>\<tau> = TFn t\<^sub>1 \<epsilon> t\<^sub>2\<close> in \<open>simp_all add: ann_ty_def fresh_ok_act_rename\<close>)
qed (use assms in \<open>simp_all add: ann_ty_def fresh_ok_act_rename\<close>)

text \<open>One application step: \<^const>\<open>app_arg\<close> unifies the head type with an
  arrow from the argument type to a fresh variable (after renaming the head's
  action binders to the argument's). The output is well formed and the result
  type fresh.\<close>

lemma app_arg_wf:
  assumes E: \<open>app_arg uf B A pd \<tau>\<^sub>h \<tau>\<^sub>a n = Some (s, \<tau>, pd', n')\<close>
    and I: \<open>inwf B A pd FK n\<close> and fh: \<open>fresh_ok \<tau>\<^sub>h 0 n FK\<close> and fa: \<open>fresh_ok \<tau>\<^sub>a 0 n FK\<close>
  shows \<open>Suc n \<le> n' \<and> outwf s pd' FK n' \<and> fresh_ok \<tau> 0 n' FK\<close>
proof -
  define \<tau>\<^sub>h' where \<open>\<tau>\<^sub>h' = (case (\<tau>\<^sub>h, \<tau>\<^sub>a) of
      (TFn (TAct lt K \<epsilon>\<^sub>0 \<tau>\<^sub>0) \<epsilon>\<^sub>l \<tau>\<^sub>2, TAct lt' K' \<epsilon>\<^sub>0' \<tau>\<^sub>0') \<Rightarrow>
        (if length K = length K' \<and> set K \<inter> ktv_env B = {} \<and> set K \<inter> ktv \<tau>\<^sub>0 = {}
         then TFn (TAct lt K' \<epsilon>\<^sub>0 (ksubst (tsl (zip K (map TK K'))) \<tau>\<^sub>0)) \<epsilon>\<^sub>l \<tau>\<^sub>2 else \<tau>\<^sub>h)
    | _ \<Rightarrow> \<tau>\<^sub>h)\<close>
  have fh': \<open>fresh_ok \<tau>\<^sub>h' 0 n FK\<close>
  proof (cases \<open>\<exists>lt K \<epsilon>\<^sub>0 \<tau>\<^sub>0 \<epsilon>\<^sub>l \<tau>\<^sub>2 lt' K' \<epsilon>\<^sub>0' \<tau>\<^sub>0'.
                  \<tau>\<^sub>h = TFn (TAct lt K \<epsilon>\<^sub>0 \<tau>\<^sub>0) \<epsilon>\<^sub>l \<tau>\<^sub>2 \<and> \<tau>\<^sub>a = TAct lt' K' \<epsilon>\<^sub>0' \<tau>\<^sub>0' \<and>
                  length K = length K' \<and> set K \<inter> ktv_env B = {} \<and> set K \<inter> ktv \<tau>\<^sub>0 = {}\<close>)
    case True
    then obtain lt K \<epsilon>\<^sub>0 \<tau>\<^sub>0 \<epsilon>\<^sub>l \<tau>\<^sub>2 lt' K' \<epsilon>\<^sub>0' \<tau>\<^sub>0' where
      h: \<open>\<tau>\<^sub>h = TFn (TAct lt K \<epsilon>\<^sub>0 \<tau>\<^sub>0) \<epsilon>\<^sub>l \<tau>\<^sub>2\<close> and a: \<open>\<tau>\<^sub>a = TAct lt' K' \<epsilon>\<^sub>0' \<tau>\<^sub>0'\<close>
      and len: \<open>length K = length K'\<close> and kd: \<open>set K \<inter> ktv_env B = {}\<close>
      and kd0: \<open>set K \<inter> ktv \<tau>\<^sub>0 = {}\<close> by blast
    have e: \<open>\<tau>\<^sub>h' = TFn (TAct lt K' \<epsilon>\<^sub>0 (ksubst (tsl (zip K (map TK K'))) \<tau>\<^sub>0)) \<epsilon>\<^sub>l \<tau>\<^sub>2\<close>
      by (simp add: \<tau>\<^sub>h'_def h a len kd kd0)
    have p: \<open>fresh_ok (TAct lt K \<epsilon>\<^sub>0 \<tau>\<^sub>0) 0 n FK\<close>
      and p2: \<open>fresh_ok \<tau>\<^sub>2 0 n FK\<close> \<open>frv_row \<epsilon>\<^sub>l \<subseteq> {..< n}\<close> \<open>brv_row \<epsilon>\<^sub>l = {}\<close>
      using fh unfolding h by (auto simp: fresh_ok_def bfree_def)
    show ?thesis
      unfolding e by (rule fresh_ok_TFn[OF fresh_ok_ksubst_rename[OF p len kd0] p2])
  next
    case False
    then have \<open>\<tau>\<^sub>h' = \<tau>\<^sub>h\<close> unfolding \<tau>\<^sub>h'_def by (auto split: kty.splits)
    then show ?thesis using fh by simp
  qed
  from E obtain n\<^sub>2 where un: \<open>uni uf \<tau>\<^sub>h' (TFn \<tau>\<^sub>a A (TV n)) (Suc n) = Some (s, n\<^sub>2)\<close>
    and n': \<open>n' = n\<^sub>2\<close>
    and \<tau>: \<open>\<tau> = sapp s (TV n)\<close> and pd': \<open>pd' = sub_pend s pd\<close>
    unfolding app_arg_def Let_def \<tau>\<^sub>h'_def[symmetric]
    by (auto simp: bind_eq_Some_conv)
  from I have frA: \<open>frv_row A \<subseteq> {..< n}\<close> and brA: \<open>brv_row A = {}\<close>
    and ftp: \<open>ftv_pend pd \<subseteq> {..< n}\<close> and frp: \<open>frv_pend pd \<subseteq> {..< n}\<close> and ktp: \<open>ktv_rows pd \<subseteq> FK\<close> by (auto simp: inwf_def)
  have f2: \<open>fresh_ok (TFn \<tau>\<^sub>a A (TV n)) 0 (Suc n) FK\<close>
    by (rule fresh_ok_TFn[OF fresh_ok_mono[OF fa le_refl le_SucI[OF le_refl]]
          fresh_ok_TV[OF lessI]])
       (use frA brA in auto)
  have f1: \<open>fresh_ok \<tau>\<^sub>h' 0 (Suc n) FK\<close> using fresh_ok_mono[OF fh' le_refl] by simp
  note unf = uni_fresh[OF un f1 f2 le0]
  have le: \<open>Suc n \<le> n\<^sub>2\<close> and sc: \<open>sconf s {..< n\<^sub>2} {..< n\<^sub>2}\<close>
    and kh: \<open>khyg s FK\<close> and bf: \<open>bfree_sub s\<close>
    using unf by (simp_all add: atLeast0LessThan)
  have o: \<open>outwf s (sub_pend s pd) FK n\<^sub>2\<close>
    by (rule outwf_of_uni[OF sc kh bf ftp frp _ ktp]) (use le in simp)
  have f: \<open>fresh_ok (sapp s (TV n)) 0 n\<^sub>2 FK\<close> by (rule fresh_ok_sapp0[OF fresh_ok_TV[OF lessI] o le])
  show ?thesis using le o f unfolding n' \<tau> pd' by simp
qed

text \<open>Instantiating an operation's parameters with fresh arguments gives a fresh type:\<close>

lemma op_inst_fresh:
  assumes bt: \<open>btv \<tau> \<subseteq> set ps\<close> and cl: \<open>brv \<tau> = {}\<close> \<open>ftv \<tau> = {}\<close> \<open>frv \<tau> = {}\<close> \<open>ktv \<tau> \<subseteq> FK\<close>
    and len: \<open>length args = length ps\<close> and fa: \<open>\<forall>t \<in> set args. fresh_ok t 0 m FK\<close>
  shows \<open>fresh_ok (op_inst ps args \<tau>) 0 m FK\<close>
proof -
  let ?\<theta> = \<open>\<lambda>a. case map_of (zip ps args) a of Some t \<Rightarrow> t | None \<Rightarrow> TB a\<close>
  have \<theta>: \<open>?\<theta> a \<in> set args\<close> if \<open>a \<in> btv \<tau>\<close> for a
  proof -
    have \<open>a \<in> set ps\<close> using that bt by blast
    then obtain t where t: \<open>map_of (zip ps args) a = Some t\<close>
      using len map_of_zip_is_Some[of ps args a] by auto
    then show ?thesis using map_of_SomeD[OF t] by (auto dest: set_zip_rightD)
  qed
  have f: \<open>ftv (?\<theta> a) \<subseteq> {0 ..< m}\<close> \<open>frv (?\<theta> a) \<subseteq> {0 ..< m}\<close> \<open>ktv (?\<theta> a) \<subseteq> FK\<close>
    \<open>btv (?\<theta> a) = {}\<close> \<open>brv (?\<theta> a) = {}\<close> if \<open>a \<in> btv \<tau>\<close> for a
    using \<theta>[OF that] fa by (auto simp: fresh_ok_def bfree_def)
  have \<open>ftv (op_inst ps args \<tau>) \<subseteq> {0 ..< m}\<close> \<open>frv (op_inst ps args \<tau>) \<subseteq> {0 ..< m}\<close>
    \<open>ktv (op_inst ps args \<tau>) \<subseteq> FK\<close> \<open>btv (op_inst ps args \<tau>) = {}\<close>
    \<open>brv (op_inst ps args \<tau>) = {}\<close>
    unfolding op_inst_def ftv_bsubstl frv_bsubstl btv_bsubstl brv_bsubstl
    using ktv_bsubstl[of ?\<theta> RB \<tau>] cl f by (auto simp: UN_subset_iff) blast
  then show ?thesis by (simp add: fresh_ok_def bfree_def)
qed

text \<open>A path that names no entry is an operation reference \<open>x.op\<close>
  (\<^const>\<open>infer_opn\<close>). It and a path atom in general (\<open>apath_wf\<close>) keep the
  output well formed and the type fresh.\<close>

lemma infer_opn_wf:
  assumes I: \<open>inwf B A pd FK n\<close> and E: \<open>infer_opn uf B pd p n = Some (s, a', \<tau>, pd', n')\<close>
  shows \<open>n \<le> n' \<and> outwf s pd' FK n' \<and> fresh_ok \<tau> 0 n' FK\<close>
proof -
  from E obtain x op \<sigma> lop ps \<tau>\<^sub>1 \<tau>\<^sub>2 l \<tau>\<^sub>x n\<^sub>1 n\<^sub>3 where
    lx: \<open>tlookup B [x] = Some (TEval \<sigma>)\<close> and
    lo: \<open>tlookup B [op] = Some (TEop lop ps \<tau>\<^sub>1 \<tau>\<^sub>2)\<close> and
    ins: \<open>inst_scheme n \<sigma> = (\<tau>\<^sub>x, n\<^sub>1)\<close> and
    un: \<open>uni uf \<tau>\<^sub>x (TEv (eff_ty l (map TV [n\<^sub>1 ..< n\<^sub>1 + length ps])) (TV (n\<^sub>1 + length ps))
      (tuple (map TV [n\<^sub>1 ..< n\<^sub>1 + length ps]))) (Suc (n\<^sub>1 + length ps)) = Some (s, n\<^sub>3)\<close> and
    \<tau>: \<open>\<tau> = TFn (sapp s (op_inst ps (map TV [n\<^sub>1 ..< n\<^sub>1 + length ps]) \<tau>\<^sub>1))
      (canon_row (RCons (nlbl lop) (RV n\<^sub>3)))
      (sapp s (op_inst ps (map TV [n\<^sub>1 ..< n\<^sub>1 + length ps]) \<tau>\<^sub>2))\<close> and
    pd': \<open>pd' = sub_pend s pd\<close> and n': \<open>n' = Suc n\<^sub>3\<close>
    by (auto simp: infer_opn_def Let_def bind_eq_Some_conv
        split: list.split_asm option.split_asm tentry.split_asm prod.split_asm)
  let ?n\<^sub>2 = \<open>n\<^sub>1 + length ps\<close> and ?args = \<open>map TV [n\<^sub>1 ..< n\<^sub>1 + length ps]\<close>
  have kb: \<open>ktv_env B \<subseteq> FK\<close> \<open>ftv_env B \<subseteq> {..< n}\<close> \<open>frv_env B \<subseteq> {..< n}\<close> \<open>bfree_env B\<close> \<open>cenv B\<close>
    and ftp: \<open>ftv_pend pd \<subseteq> {..< n}\<close> and frp: \<open>frv_pend pd \<subseteq> {..< n}\<close> and ktp: \<open>ktv_rows pd \<subseteq> FK\<close>
    using I by (auto simp: inwf_def)
  have b: \<open>ftv_sch \<sigma> \<subseteq> {..< n}\<close> \<open>frv_sch \<sigma> \<subseteq> {..< n}\<close> \<open>ktv_sch \<sigma> \<subseteq> FK\<close> \<open>bfree_sch \<sigma>\<close>
    using ftv_env_tlookup[OF lx] frv_env_tlookup[OF lx] ktv_env_tlookup[OF lx]
          bfree_env_tlookup[OF kb(4) lx] kb by auto
  note sx = sch_inst_fresh[OF b ins]
  have le1: \<open>n \<le> n\<^sub>1\<close> using sx by simp
  have cl: \<open>ftv \<tau>\<^sub>1 = {}\<close> \<open>frv \<tau>\<^sub>1 = {}\<close> \<open>ftv \<tau>\<^sub>2 = {}\<close> \<open>frv \<tau>\<^sub>2 = {}\<close>
    using cenv_tlookup_nonval[OF kb(5) lo] by auto
  have kb2: \<open>ktv \<tau>\<^sub>1 \<subseteq> FK\<close> \<open>ktv \<tau>\<^sub>2 \<subseteq> FK\<close> \<open>btv \<tau>\<^sub>1 \<subseteq> set ps\<close> \<open>btv \<tau>\<^sub>2 \<subseteq> set ps\<close>
    \<open>brv \<tau>\<^sub>1 = {}\<close> \<open>brv \<tau>\<^sub>2 = {}\<close>
    using ktv_env_tlookup[OF lo] kb(1) bfree_env_tlookup[OF kb(4) lo] by auto
  have fargs: \<open>\<forall>t \<in> set ?args. fresh_ok t 0 ?n\<^sub>2 FK\<close> by (auto simp: fresh_ok_def bfree_def)
  have fo: \<open>fresh_ok (op_inst ps ?args \<tau>\<^sub>1) 0 ?n\<^sub>2 FK\<close> \<open>fresh_ok (op_inst ps ?args \<tau>\<^sub>2) 0 ?n\<^sub>2 FK\<close>
    by (rule op_inst_fresh[OF _ _ _ _ _ _ fargs]; use cl kb2 in simp)+
  have f1: \<open>fresh_ok \<tau>\<^sub>x 0 (Suc ?n\<^sub>2) FK\<close> using fresh_ok_mono[OF sx[THEN conjunct2] le_refl] by simp
  have f2: \<open>fresh_ok (TEv (eff_ty l ?args) (TV ?n\<^sub>2) (tuple ?args)) 0 (Suc ?n\<^sub>2) FK\<close>
    by (auto simp: fresh_ok_def bfree_def eff_ty_def)
  note unf = uni_fresh[OF un f1 f2 le0]
  have le: \<open>Suc ?n\<^sub>2 \<le> n\<^sub>3\<close> and sc: \<open>sconf s {..< n\<^sub>3} {..< n\<^sub>3}\<close>
    and kh: \<open>khyg s FK\<close> and bf: \<open>bfree_sub s\<close>
    using unf by (simp_all add: atLeast0LessThan)
  have o: \<open>outwf s (sub_pend s pd) FK (Suc n\<^sub>3)\<close>
    by (rule outwf_of_uni[OF sconf_mono[OF sc] kh bf ftp frp _ ktp]) (use le le1 in auto)
  have fs: \<open>fresh_ok (sapp s (op_inst ps ?args \<tau>\<^sub>1)) 0 (Suc n\<^sub>3) FK\<close>
    \<open>fresh_ok (sapp s (op_inst ps ?args \<tau>\<^sub>2)) 0 (Suc n\<^sub>3) FK\<close>
    by (rule fresh_ok_sapp0[OF fo(1) o], use le in simp)
       (rule fresh_ok_sapp0[OF fo(2) o], use le in simp)
  have f\<tau>: \<open>fresh_ok \<tau> 0 (Suc n\<^sub>3) FK\<close> unfolding \<tau> by (rule fresh_ok_TFn[OF fs]) auto
  show ?thesis unfolding n' pd' using le le1 o f\<tau> by simp
qed

lemma apath_wf:
  assumes I: \<open>inwf B A pd FK n\<close>
    and E: \<open>infer_atom uf B A pd (APath p) n = Some (s, a', \<tau>, pd', n')\<close>
  shows \<open>n \<le> n' \<and> outwf s pd' FK n' \<and> fresh_ok \<tau> 0 n' FK\<close>
proof (cases \<open>tlookup B (path_nms p)\<close>)
  case None
  then have \<open>infer_opn uf B pd p n = Some (s, a', \<tau>, pd', n')\<close> using E by simp
  then show ?thesis by (rule infer_opn_wf[OF I])
next
  case (Some e)
  have kb: \<open>ktv_env B \<subseteq> FK\<close> \<open>ftv_env B \<subseteq> {..< n}\<close> \<open>frv_env B \<subseteq> {..< n}\<close> \<open>bfree_env B\<close>
    using I by (auto simp: inwf_def)
  show ?thesis
  proof (cases e)
    case (TEval \<sigma>)
    have b: \<open>ftv_sch \<sigma> \<subseteq> {..< n}\<close> \<open>frv_sch \<sigma> \<subseteq> {..< n}\<close> \<open>ktv_sch \<sigma> \<subseteq> FK\<close> \<open>bfree_sch \<sigma>\<close>
      using ftv_env_tlookup[OF Some] frv_env_tlookup[OF Some] ktv_env_tlookup[OF Some]
            bfree_env_tlookup[OF kb(4) Some] kb unfolding TEval by auto
    obtain \<tau>\<^sub>0 n\<^sub>1 evs pdo where i: \<open>inst_scheme n \<sigma> = (\<tau>\<^sub>0, n\<^sub>1)\<close>
      and o: \<open>off_evs n\<^sub>1 \<tau>\<^sub>0 = (evs, pdo, \<tau>, n')\<close> and se: \<open>s = sid\<close> \<open>pd' = pdo @ pd\<close>
      using E Some TEval by (auto split: prod.split_asm)
    have w: \<open>n \<le> n\<^sub>1\<close> \<open>fresh_ok \<tau>\<^sub>0 0 n\<^sub>1 FK\<close> using sch_inst_fresh[OF b i] by simp_all
    have le1: \<open>n\<^sub>1 \<le> n'\<close> by (rule off_evs_le[OF o])
    have le: \<open>n \<le> n'\<close> using w(1) le1 by simp
    have sub: \<open>{..< n\<^sub>1} \<subseteq> {..< n'}\<close> using le1 by simp
    have f: \<open>fresh_ok \<tau> 0 n' FK\<close>
      using w(2) off_evs_ftv[OF o] off_evs_frv[OF o] off_evs_ktv[OF o] off_evs_btv[OF o] sub
      by (auto simp: fresh_ok_def bfree_def)
    have po: \<open>ftv_pend pdo \<subseteq> {..< n'}\<close> \<open>frv_pend pdo \<subseteq> {..< n'}\<close> \<open>ktv_rows pdo \<subseteq> FK\<close>
      using w(2) off_evs_ftv[OF o] off_evs_frv[OF o] off_evs_ktv_rows[OF o] sub
      by (auto simp: fresh_ok_def)
    show ?thesis using le f po outwf_sid_mono[OF I le] se by (auto simp: outwf_def)
  next
    case (TEcon \<sigma> k)
    have b: \<open>ftv_sch \<sigma> \<subseteq> {..< n}\<close> \<open>frv_sch \<sigma> \<subseteq> {..< n}\<close> \<open>ktv_sch \<sigma> \<subseteq> FK\<close> \<open>bfree_sch \<sigma>\<close>
      using ftv_env_tlookup[OF Some] frv_env_tlookup[OF Some] ktv_env_tlookup[OF Some]
            bfree_env_tlookup[OF kb(4) Some] kb unfolding TEcon by auto
    obtain m where i: \<open>inst_scheme n \<sigma> = (\<tau>, m)\<close> \<open>n' = m\<close> \<open>s = sid\<close> \<open>pd' = pd\<close>
      using E Some TEcon by (auto split: prod.split_asm)
    show ?thesis using sch_inst_fresh[OF b i(1)] outwf_sid_mono[OF I] i by auto
  next
    case (TEffi sy \<sigma>)
    have b: \<open>ftv_sch \<sigma> \<subseteq> {..< n}\<close> \<open>frv_sch \<sigma> \<subseteq> {..< n}\<close> \<open>ktv_sch \<sigma> \<subseteq> FK\<close> \<open>bfree_sch \<sigma>\<close>
      using ftv_env_tlookup[OF Some] frv_env_tlookup[OF Some] ktv_env_tlookup[OF Some]
            bfree_env_tlookup[OF kb(4) Some] kb unfolding TEffi by auto
    obtain m where i: \<open>inst_scheme n \<sigma> = (\<tau>, m)\<close> \<open>n' = m\<close> \<open>s = sid\<close> \<open>pd' = pd\<close>
      using E Some TEffi by (auto split: prod.split_asm)
    show ?thesis using sch_inst_fresh[OF b i(1)] outwf_sid_mono[OF I] i by auto
  next
    case (TEop l ps \<tau>\<^sub>1 \<tau>\<^sub>2)
    have cenvB: \<open>cenv B\<close> using I by (simp add: inwf_def)
    have cl: \<open>ftv_ent e = {}\<close> \<open>frv_ent e = {}\<close>
      using cenv_tlookup_nonval[OF cenvB Some[unfolded TEop]] by (simp_all add: TEop)
    have kb2: \<open>ktv_ent e \<subseteq> FK\<close> \<open>bfree_ent e\<close>
      using ktv_env_tlookup[OF Some] kb bfree_env_tlookup[OF kb(4) Some] by auto
    have vals: \<open>s = sid\<close> \<open>a' = APath p\<close> \<open>\<tau> = TFn \<tau>\<^sub>1 (canon_row (RCons l (RV n))) \<tau>\<^sub>2\<close>
      \<open>pd' = pd\<close> \<open>n' = Suc n\<close>
      and pnil: \<open>ps = []\<close>
      using E Some TEop by (auto split: if_split_asm)
    have \<open>fresh_ok \<tau> 0 n' FK\<close>
      using cl kb2 vals unfolding TEop pnil by (auto simp: fresh_ok_def bfree_def)
    then show ?thesis using outwf_sid_mono[OF I, of n'] vals by auto
  qed (use E Some in auto)
qed

text \<open>In head position a path is instantiated but gets no evidence (the application
  supplies it), so the pending list is unchanged.\<close>

lemma hpath_wf:
  assumes I: \<open>inwf B A pd FK n\<close>
    and E: \<open>infer_head uf B A pd (APath p) n = Some (s, a', \<tau>, pd', n')\<close>
  shows \<open>n \<le> n' \<and> outwf s pd' FK n' \<and> fresh_ok \<tau> 0 n' FK\<close>
proof (cases \<open>tlookup B (path_nms p)\<close>)
  case None
  then have \<open>infer_opn uf B pd p n = Some (s, a', \<tau>, pd', n')\<close> using E by simp
  then show ?thesis by (rule infer_opn_wf[OF I])
next
  case (Some e)
  have kb: \<open>ktv_env B \<subseteq> FK\<close> \<open>ftv_env B \<subseteq> {..< n}\<close> \<open>frv_env B \<subseteq> {..< n}\<close> \<open>bfree_env B\<close>
    using I by (auto simp: inwf_def)
  show ?thesis
  proof (cases e)
    case (TEval \<sigma>)
    have b: \<open>ftv_sch \<sigma> \<subseteq> {..< n}\<close> \<open>frv_sch \<sigma> \<subseteq> {..< n}\<close> \<open>ktv_sch \<sigma> \<subseteq> FK\<close> \<open>bfree_sch \<sigma>\<close>
      using ftv_env_tlookup[OF Some] frv_env_tlookup[OF Some] ktv_env_tlookup[OF Some]
            bfree_env_tlookup[OF kb(4) Some] kb unfolding TEval by auto
    obtain m where i: \<open>inst_scheme n \<sigma> = (\<tau>, m)\<close> \<open>n' = m\<close> \<open>s = sid\<close> \<open>pd' = pd\<close>
      using E Some TEval by (auto split: prod.split_asm)
    show ?thesis using sch_inst_fresh[OF b i(1)] outwf_sid_mono[OF I] i by auto
  next
    case (TEcon \<sigma> k)
    have b: \<open>ftv_sch \<sigma> \<subseteq> {..< n}\<close> \<open>frv_sch \<sigma> \<subseteq> {..< n}\<close> \<open>ktv_sch \<sigma> \<subseteq> FK\<close> \<open>bfree_sch \<sigma>\<close>
      using ftv_env_tlookup[OF Some] frv_env_tlookup[OF Some] ktv_env_tlookup[OF Some]
            bfree_env_tlookup[OF kb(4) Some] kb unfolding TEcon by auto
    obtain m where i: \<open>inst_scheme n \<sigma> = (\<tau>, m)\<close> \<open>n' = m\<close> \<open>s = sid\<close> \<open>pd' = pd\<close>
      using E Some TEcon by (auto split: prod.split_asm)
    show ?thesis using sch_inst_fresh[OF b i(1)] outwf_sid_mono[OF I] i by auto
  next
    case (TEffi sy \<sigma>)
    have b: \<open>ftv_sch \<sigma> \<subseteq> {..< n}\<close> \<open>frv_sch \<sigma> \<subseteq> {..< n}\<close> \<open>ktv_sch \<sigma> \<subseteq> FK\<close> \<open>bfree_sch \<sigma>\<close>
      using ftv_env_tlookup[OF Some] frv_env_tlookup[OF Some] ktv_env_tlookup[OF Some]
            bfree_env_tlookup[OF kb(4) Some] kb unfolding TEffi by auto
    obtain m where i: \<open>inst_scheme n \<sigma> = (\<tau>, m)\<close> \<open>n' = m\<close> \<open>s = sid\<close> \<open>pd' = pd\<close>
      using E Some TEffi by (auto split: prod.split_asm)
    show ?thesis using sch_inst_fresh[OF b i(1)] outwf_sid_mono[OF I] i by auto
  next
    case (TEop l ps \<tau>\<^sub>1 \<tau>\<^sub>2)
    have cenvB: \<open>cenv B\<close> using I by (simp add: inwf_def)
    have cl: \<open>ftv_ent e = {}\<close> \<open>frv_ent e = {}\<close>
      using cenv_tlookup_nonval[OF cenvB Some[unfolded TEop]] by (simp_all add: TEop)
    have kb2: \<open>ktv_ent e \<subseteq> FK\<close> \<open>bfree_ent e\<close>
      using ktv_env_tlookup[OF Some] kb bfree_env_tlookup[OF kb(4) Some] by auto
    have vals: \<open>s = sid\<close> \<open>a' = APath p\<close> \<open>\<tau> = TFn \<tau>\<^sub>1 (canon_row (RCons l (RV n))) \<tau>\<^sub>2\<close>
      \<open>pd' = pd\<close> \<open>n' = Suc n\<close>
      and pnil: \<open>ps = []\<close>
      using E Some TEop by (auto split: if_split_asm)
    have \<open>fresh_ok \<tau> 0 n' FK\<close>
      using cl kb2 vals unfolding TEop pnil by (auto simp: fresh_ok_def bfree_def)
    then show ?thesis using outwf_sid_mono[OF I, of n'] vals by auto
  qed (use E Some in auto)
qed

lemma infer_args_step:
  assumes E: \<open>infer_args uf B A pd d \<tau>\<^sub>0 as n = Some (s, as', \<tau>, pd', n')\<close>
    and I: \<open>inwf B A pd FK n\<close> and F: \<open>fresh_ok \<tau>\<^sub>0 0 n FK\<close>
    and nd: \<open>(\<forall>i sg K e t. \<tau>\<^sub>0 \<noteq> TDep i sg K e t) \<and> (\<forall>x r t. \<tau>\<^sub>0 \<noteq> TOff x r t)\<close>
    and IH\<^sub>1: \<open>\<And>a rest s\<^sub>1 a'' \<tau>\<^sub>a pd\<^sub>1 n\<^sub>1. as = a # rest \<Longrightarrow>
        infer_atom uf B A pd a n = Some (s\<^sub>1, a'', \<tau>\<^sub>a, pd\<^sub>1, n\<^sub>1) \<Longrightarrow> inwf B A pd FK n \<Longrightarrow>
        n \<le> n\<^sub>1 \<and> outwf s\<^sub>1 pd\<^sub>1 FK n\<^sub>1 \<and> fresh_ok \<tau>\<^sub>a 0 n\<^sub>1 FK\<close>
    and IH\<^sub>2: \<open>\<And>a rest s\<^sub>1 a'' \<tau>\<^sub>a pd\<^sub>1 n\<^sub>1 s\<^sub>2 \<tau>\<^sub>r pd\<^sub>2 n\<^sub>2 s\<^sub>3 rest'' \<tau>' pd\<^sub>3 n\<^sub>3. as = a # rest \<Longrightarrow>
        infer_atom uf B A pd a n = Some (s\<^sub>1, a'', \<tau>\<^sub>a, pd\<^sub>1, n\<^sub>1) \<Longrightarrow>
        app_arg uf (sappe s\<^sub>1 B) (sappr s\<^sub>1 A) pd\<^sub>1 (sapp s\<^sub>1 \<tau>\<^sub>0) \<tau>\<^sub>a n\<^sub>1 = Some (s\<^sub>2, \<tau>\<^sub>r, pd\<^sub>2, n\<^sub>2) \<Longrightarrow>
        infer_args uf (sappe (s\<^sub>2 \<odot> s\<^sub>1) B) (sappr (s\<^sub>2 \<odot> s\<^sub>1) A) pd\<^sub>2 d \<tau>\<^sub>r rest n\<^sub>2 =
          Some (s\<^sub>3, rest'', \<tau>', pd\<^sub>3, n\<^sub>3) \<Longrightarrow>
        inwf (sappe (s\<^sub>2 \<odot> s\<^sub>1) B) (sappr (s\<^sub>2 \<odot> s\<^sub>1) A) pd\<^sub>2 FK n\<^sub>2 \<Longrightarrow> fresh_ok \<tau>\<^sub>r 0 n\<^sub>2 FK \<Longrightarrow>
        n\<^sub>2 \<le> n\<^sub>3 \<and> outwf s\<^sub>3 pd\<^sub>3 FK n\<^sub>3 \<and> fresh_ok \<tau>' 0 n\<^sub>3 FK\<close>
  shows \<open>n \<le> n' \<and> outwf s pd' FK n' \<and> fresh_ok \<tau> 0 n' FK\<close>
proof (cases as)
  case Nil
  then show ?thesis using E F nd outwf_sid[OF I] by (cases \<tau>\<^sub>0) (auto simp: outwf_def)
next
  case (Cons a rest)
  obtain s\<^sub>1 a'' \<tau>\<^sub>a pd\<^sub>1 n\<^sub>1 s\<^sub>2 \<tau>\<^sub>r pd\<^sub>2 n\<^sub>2 s\<^sub>3 rest'' where
    d1: \<open>infer_atom uf B A pd a n = Some (s\<^sub>1, a'', \<tau>\<^sub>a, pd\<^sub>1, n\<^sub>1)\<close> and
    ap: \<open>app_arg uf (sappe s\<^sub>1 B) (sappr s\<^sub>1 A) pd\<^sub>1 (sapp s\<^sub>1 \<tau>\<^sub>0) \<tau>\<^sub>a n\<^sub>1 = Some (s\<^sub>2, \<tau>\<^sub>r, pd\<^sub>2, n\<^sub>2)\<close> and
    d2: \<open>infer_args uf (sappe (s\<^sub>2 \<odot> s\<^sub>1) B) (sappr (s\<^sub>2 \<odot> s\<^sub>1) A) pd\<^sub>2 d \<tau>\<^sub>r rest n\<^sub>2
           = Some (s\<^sub>3, rest'', \<tau>, pd', n')\<close> and
    se: \<open>s = s\<^sub>3 \<odot> (s\<^sub>2 \<odot> s\<^sub>1)\<close>
    using E[unfolded Cons infer_args_Cons_plain[OF conjunct1[OF nd] conjunct2[OF nd]]]
    by (auto simp: bind_eq_Some_conv simp del: infer_args.simps)
  note w1 = IH\<^sub>1[OF Cons d1 I]
  have le1: \<open>n \<le> n\<^sub>1\<close> and o1: \<open>outwf s\<^sub>1 pd\<^sub>1 FK n\<^sub>1\<close> and fa: \<open>fresh_ok \<tau>\<^sub>a 0 n\<^sub>1 FK\<close>
    using w1 by simp_all
  note w2 = app_arg_wf[OF ap inwf_step[OF I o1 le1] fresh_ok_sapp0[OF F o1 le1] fa]
  have le12: \<open>n\<^sub>1 \<le> n\<^sub>2\<close> and o2: \<open>outwf s\<^sub>2 pd\<^sub>2 FK n\<^sub>2\<close> and fr: \<open>fresh_ok \<tau>\<^sub>r 0 n\<^sub>2 FK\<close>
    using w2 by simp_all
  have os: \<open>outwf (s\<^sub>2 \<odot> s\<^sub>1) pd\<^sub>2 FK n\<^sub>2\<close> by (rule outwf_scomp[OF o1 o2 le12])
  have le2: \<open>n \<le> n\<^sub>2\<close> using le1 le12 by simp
  note w3 = IH\<^sub>2[OF Cons d1 ap d2 inwf_step[OF I os le2] fr]
  have le3: \<open>n\<^sub>2 \<le> n'\<close> and o3: \<open>outwf s\<^sub>3 pd' FK n'\<close> and f\<tau>: \<open>fresh_ok \<tau> 0 n' FK\<close>
    using w3 by simp_all
  show ?thesis using se le2 le3 f\<tau> outwf_scomp[OF os o3 le3] by simp
qed

text \<open>The two named-handler forms. A named handler runs the clauses under fresh
  row and answer variables. \<open>with x = h in e\<close> infers the handler, then the
  body as an action under the name \<open>x\<close> (hiding its scope variable by
  \<open>sproj\<close>, like \<open>EFnMod\<close>), and applies the one to the other through
  \<open>app_arg\<close>.\<close>

lemma infer_handlern_wf:
  assumes E: \<open>infer uf B A pd (EHandlerN cls) n = Some (s, e', \<tau>, pd', n')\<close>
    and I: \<open>inwf B A pd FK n\<close>
    and IH: \<open>\<And>lbl rest l ls ar s\<^sub>c cls'' \<tau>\<^sub>c pd\<^sub>c n\<^sub>c. hlabels B cls = lbl # rest \<Longrightarrow>
        eff_of_op B lbl = Some (l, ls, ar) \<Longrightarrow>
        set (hlabels B cls) = set (map (mangle l) ls) \<Longrightarrow>
        n + ar \<notin> ktv_env B \<Longrightarrow>
        infer_cls uf B (RV (Suc (n + ar))) pd True (TV (Suc (Suc (n + ar))))
          (tuple (map TV [n ..< n + ar])) cls (Suc (Suc (Suc (n + ar)))) =
          Some (s\<^sub>c, cls'', \<tau>\<^sub>c, pd\<^sub>c, n\<^sub>c) \<Longrightarrow>
        inwf B (RV (Suc (n + ar))) pd FK (Suc (Suc (Suc (n + ar)))) \<Longrightarrow>
        fresh_ok (TV (Suc (Suc (n + ar)))) 0 (Suc (Suc (Suc (n + ar)))) FK \<Longrightarrow>
        fresh_ok (tuple (map TV [n ..< n + ar])) 0 (Suc (Suc (Suc (n + ar)))) FK \<Longrightarrow>
        Suc (Suc (Suc (n + ar))) \<le> n\<^sub>c \<and> outwf s\<^sub>c pd\<^sub>c FK n\<^sub>c \<and> fresh_ok \<tau>\<^sub>c 0 n\<^sub>c FK\<close>
  shows \<open>n \<le> n' \<and> outwf s pd' FK n' \<and> fresh_ok \<tau> 0 n' FK\<close>
proof -
  let ?k = \<open>n + ar\<close> and ?n\<^sub>2 = \<open>Suc (Suc (Suc (n + ar)))\<close>
  from E obtain lbl rest l ls ar cls'' \<tau>\<^sub>c where
    hl: \<open>hlabels B cls = lbl # rest\<close> and eo: \<open>eff_of_op B lbl = Some (l, ls, ar)\<close> and
    ok: \<open>set (hlabels B cls) = set (map (mangle l) ls)\<close> and
    kn: \<open>n + ar \<notin> ktv_env B\<close> and
    ic: \<open>infer_cls uf B (RV (Suc (n + ar))) pd True (TV (Suc (Suc (n + ar))))
      (tuple (map TV [n ..< n + ar])) cls (Suc (Suc (Suc (n + ar)))) = Some (s, cls'', \<tau>\<^sub>c, pd', n')\<close>
    and rs: \<open>\<tau> = TFn (TAct (eff_ty l (map (sapp s) (map TV [n ..< n + ar]))) [n + ar]
        (canon_row (rext (map (nlbl \<circ> mangle l) ls) (sappr s (RV (Suc (n + ar))))))
        (sapp s (TV (Suc (Suc (n + ar)))))) (sappr s (RV (Suc (n + ar)))) \<tau>\<^sub>c\<close>
    by (auto simp: Let_def bind_eq_Some_conv
        split: list.splits option.splits prod.split_asm if_split_asm)
  have I': \<open>inwf B (RV (Suc (n + ar))) pd FK (Suc (Suc (Suc (n + ar))))\<close>
    using inwf_step[OF I outwf_sid_mono[OF I, of \<open>Suc (Suc (Suc (n + ar)))\<close>]]
    by (simp add: inwf_def)
  have f0: \<open>fresh_ok (TV (Suc (Suc (n + ar)))) 0 (Suc (Suc (Suc (n + ar)))) FK\<close>
    by (rule fresh_ok_TV) simp
  have fa: \<open>fresh_ok (tuple (map TV [n ..< n + ar])) 0 (Suc (Suc (Suc (n + ar)))) FK\<close>
    by (rule fresh_ok_tuple) (auto simp: fresh_ok_def bfree_def)
  note wc = IH[OF hl eo ok kn ic I' f0 fa]
  have le: \<open>Suc (Suc (Suc (n + ar))) \<le> n'\<close> and o: \<open>outwf s pd' FK n'\<close> and fc: \<open>fresh_ok \<tau>\<^sub>c 0 n' FK\<close>
    using wc by simp_all
  from o have sc: \<open>sconf s {..< n'} {..< n'}\<close> and bf: \<open>bfree_sub s\<close> by (auto simp: outwf_def)
  have f0': \<open>fresh_ok (sapp s (TV (Suc (Suc (n + ar))))) 0 n' FK\<close>
    by (rule fresh_ok_sapp0[OF f0 o le])
  have fr: \<open>frv_row (sappr s (RV (Suc (n + ar)))) \<subseteq> {..< n'}\<close>
    by (rule frv_sappr_sconf[OF sc]) (use le in auto)
  have br: \<open>brv_row (sappr s (RV (Suc (n + ar)))) = {}\<close> by (rule bfree_sappr[OF bf]) simp
  have fa': \<open>fresh_ok (sapp s (tuple (map TV [n ..< n + ar]))) 0 n' FK\<close>
    by (rule fresh_ok_sapp0[OF fa o le])
  have fresh: \<open>fresh_ok \<tau> 0 n' FK\<close>
    unfolding rs using f0' fc fr br fa' by (auto simp: fresh_ok_def bfree_def rext_def eff_ty_def)
  have \<open>n \<le> n'\<close> using le by linarith
  then show ?thesis using o fresh by simp
qed

lemma infer_with_wf:
  assumes E: \<open>infer uf B A pd (EWith x h e) n = Some (s, e', \<tau>, pd', n')\<close>
    and I: \<open>inwf B A pd FK n\<close>
    and IH\<^sub>1: \<open>\<And>s\<^sub>1 h' \<tau>\<^sub>h pd\<^sub>1 n\<^sub>1. infer uf B A pd h n = Some (s\<^sub>1, h', \<tau>\<^sub>h, pd\<^sub>1, n\<^sub>1) \<Longrightarrow>
        inwf B A pd FK n \<Longrightarrow> n \<le> n\<^sub>1 \<and> outwf s\<^sub>1 pd\<^sub>1 FK n\<^sub>1 \<and> fresh_ok \<tau>\<^sub>h 0 n\<^sub>1 FK\<close>
    and IH\<^sub>2: \<open>\<And>s\<^sub>1 h' \<tau>\<^sub>h pd\<^sub>1 n\<^sub>1 s\<^sub>2 \<tau>\<^sub>a pd\<^sub>2 n\<^sub>3 s\<^sub>b e'' \<tau>\<^sub>b pd\<^sub>b n\<^sub>b FK'.
        infer uf B A pd h n = Some (s\<^sub>1, h', \<tau>\<^sub>h, pd\<^sub>1, n\<^sub>1) \<Longrightarrow>
        n\<^sub>1 \<notin> ktv_env (sappe s\<^sub>1 B) \<Longrightarrow> nm_ok (n_txt x) \<Longrightarrow>
        app_arg uf (sappe s\<^sub>1 B) (sappr s\<^sub>1 A) pd\<^sub>1 \<tau>\<^sub>h
          (TAct (TV (Suc n\<^sub>1)) [n\<^sub>1] (RV (Suc (Suc (Suc n\<^sub>1)))) (TV (Suc (Suc (Suc (Suc n\<^sub>1))))))
          (Suc (Suc (Suc (Suc (Suc n\<^sub>1))))) = Some (s\<^sub>2, \<tau>\<^sub>a, pd\<^sub>2, n\<^sub>3) \<Longrightarrow>
        infer uf (name_env (sappe s\<^sub>2 (sappe s\<^sub>1 B)) (n_txt x) (sapp s\<^sub>2 (TV (Suc n\<^sub>1))) @
            (n_txt x, TEval (kmono (TEv (sapp s\<^sub>2 (TV (Suc n\<^sub>1))) (TK n\<^sub>1)
                                        (sapp s\<^sub>2 (TV (Suc (Suc n\<^sub>1))))))) #
            sappe s\<^sub>2 (sappe s\<^sub>1 B))
          (sappr s\<^sub>2 (RV (Suc (Suc (Suc n\<^sub>1))))) pd\<^sub>2 e n\<^sub>3 = Some (s\<^sub>b, e'', \<tau>\<^sub>b, pd\<^sub>b, n\<^sub>b) \<Longrightarrow>
        inwf (name_env (sappe s\<^sub>2 (sappe s\<^sub>1 B)) (n_txt x) (sapp s\<^sub>2 (TV (Suc n\<^sub>1))) @
            (n_txt x, TEval (kmono (TEv (sapp s\<^sub>2 (TV (Suc n\<^sub>1))) (TK n\<^sub>1)
                                        (sapp s\<^sub>2 (TV (Suc (Suc n\<^sub>1))))))) #
            sappe s\<^sub>2 (sappe s\<^sub>1 B))
          (sappr s\<^sub>2 (RV (Suc (Suc (Suc n\<^sub>1))))) pd\<^sub>2 FK' n\<^sub>3 \<Longrightarrow>
        n\<^sub>3 \<le> n\<^sub>b \<and> outwf s\<^sub>b pd\<^sub>b FK' n\<^sub>b \<and> fresh_ok \<tau>\<^sub>b 0 n\<^sub>b FK'\<close>
  shows \<open>n \<le> n' \<and> outwf s pd' FK n' \<and> fresh_ok \<tau> 0 n' FK\<close>
proof -
  from E obtain s\<^sub>1 h' \<tau>\<^sub>h pd\<^sub>1 n\<^sub>1 where
    d1: \<open>infer uf B A pd h n = Some (s\<^sub>1, h', \<tau>\<^sub>h, pd\<^sub>1, n\<^sub>1)\<close>
    by (auto simp: bind_eq_Some_conv)
  let ?B\<^sub>1 = \<open>sappe s\<^sub>1 B\<close> and ?n\<^sub>2 = \<open>Suc (Suc (Suc (Suc (Suc n\<^sub>1))))\<close>
  from E d1 obtain s\<^sub>2 \<tau>\<^sub>a pd\<^sub>2 n\<^sub>3 s\<^sub>b e'' \<tau>\<^sub>b pd\<^sub>b n\<^sub>b s\<^sub>4 n\<^sub>5 where
    kn: \<open>n\<^sub>1 \<notin> ktv_env ?B\<^sub>1\<close> and nm: \<open>nm_ok (n_txt x)\<close> and
    ap: \<open>app_arg uf ?B\<^sub>1 (sappr s\<^sub>1 A) pd\<^sub>1 \<tau>\<^sub>h
      (TAct (TV (Suc n\<^sub>1)) [n\<^sub>1] (RV (Suc (Suc (Suc n\<^sub>1)))) (TV (Suc (Suc (Suc (Suc n\<^sub>1))))))
      ?n\<^sub>2 = Some (s\<^sub>2, \<tau>\<^sub>a, pd\<^sub>2, n\<^sub>3)\<close> and
    ib: \<open>infer uf (name_env (sappe s\<^sub>2 ?B\<^sub>1) (n_txt x) (sapp s\<^sub>2 (TV (Suc n\<^sub>1))) @
          (n_txt x, TEval (kmono (TEv (sapp s\<^sub>2 (TV (Suc n\<^sub>1))) (TK n\<^sub>1)
                                      (sapp s\<^sub>2 (TV (Suc (Suc n\<^sub>1))))))) # sappe s\<^sub>2 ?B\<^sub>1)
        (sappr s\<^sub>2 (RV (Suc (Suc (Suc n\<^sub>1))))) pd\<^sub>2 e n\<^sub>3 = Some (s\<^sub>b, e'', \<tau>\<^sub>b, pd\<^sub>b, n\<^sub>b)\<close> and
    un: \<open>uni uf (sapp (s\<^sub>b \<odot> s\<^sub>2) (TV (Suc (Suc (Suc (Suc n\<^sub>1)))))) \<tau>\<^sub>b n\<^sub>b = Some (s\<^sub>4, n\<^sub>5)\<close> and
    esc: \<open>list_all (\<lambda>a. n\<^sub>1 \<notin> ktv (fst (s\<^sub>4 \<odot> s\<^sub>b) a)) [0 ..< n\<^sub>3]\<close> and
    escp: \<open>n\<^sub>1 \<notin> ktv_rows (sub_pend s\<^sub>4 pd\<^sub>b)\<close> and
    se: \<open>s = sproj n\<^sub>3 (s\<^sub>4 \<odot> s\<^sub>b) \<odot> s\<^sub>2 \<odot> s\<^sub>1\<close> \<open>\<tau> = sapp (sproj n\<^sub>3 (s\<^sub>4 \<odot> s\<^sub>b)) \<tau>\<^sub>a\<close>
      \<open>pd' = sub_pend s\<^sub>4 pd\<^sub>b\<close> \<open>n' = n\<^sub>5\<close>
    by (auto simp: Let_def bind_eq_Some_conv split: prod.split_asm if_split_asm)
  note w1 = IH\<^sub>1[OF d1 I]
  have le1: \<open>n \<le> n\<^sub>1\<close> and o1: \<open>outwf s\<^sub>1 pd\<^sub>1 FK n\<^sub>1\<close> and fh: \<open>fresh_ok \<tau>\<^sub>h 0 n\<^sub>1 FK\<close>
    using w1 by simp_all
  have I1: \<open>inwf ?B\<^sub>1 (sappr s\<^sub>1 A) pd\<^sub>1 FK n\<^sub>1\<close> by (rule inwf_step[OF I o1 le1])
  have le12: \<open>n\<^sub>1 \<le> ?n\<^sub>2\<close> by simp
  have I1': \<open>inwf ?B\<^sub>1 (sappr s\<^sub>1 A) pd\<^sub>1 FK ?n\<^sub>2\<close>
    using inwf_step[OF I1 outwf_sid_mono[OF I1 le12] le12] by simp
  have fh': \<open>fresh_ok \<tau>\<^sub>h 0 ?n\<^sub>2 FK\<close> by (rule fresh_ok_mono[OF fh le_refl le12])
  have fa: \<open>fresh_ok (TAct (TV (Suc n\<^sub>1)) [n\<^sub>1] (RV (Suc (Suc (Suc n\<^sub>1))))
      (TV (Suc (Suc (Suc (Suc n\<^sub>1)))))) 0 ?n\<^sub>2 FK\<close>
    by (auto simp: fresh_ok_def bfree_def)
  note w2 = app_arg_wf[OF ap I1' fh' fa]
  have le23: \<open>Suc ?n\<^sub>2 \<le> n\<^sub>3\<close> and o2: \<open>outwf s\<^sub>2 pd\<^sub>2 FK n\<^sub>3\<close> and fta: \<open>fresh_ok \<tau>\<^sub>a 0 n\<^sub>3 FK\<close>
    using w2 by simp_all
  have I2: \<open>inwf (sappe s\<^sub>2 ?B\<^sub>1) (sappr s\<^sub>2 (sappr s\<^sub>1 A)) pd\<^sub>2 FK n\<^sub>3\<close>
    by (rule inwf_step[OF I1' o2]) (use le23 in simp)
  from I2 have cenvB: \<open>cenv (sappe s\<^sub>2 ?B\<^sub>1)\<close> and bfB: \<open>bfree_env (sappe s\<^sub>2 ?B\<^sub>1)\<close>
    and ktvB: \<open>ktv_env (sappe s\<^sub>2 ?B\<^sub>1) \<subseteq> FK\<close>
    and ftvB: \<open>ftv_env (sappe s\<^sub>2 ?B\<^sub>1) \<subseteq> {..< n\<^sub>3}\<close>
    and frvB: \<open>frv_env (sappe s\<^sub>2 ?B\<^sub>1) \<subseteq> {..< n\<^sub>3}\<close>
    and ftp: \<open>ftv_pend pd\<^sub>2 \<subseteq> {..< n\<^sub>3}\<close> and frp: \<open>frv_pend pd\<^sub>2 \<subseteq> {..< n\<^sub>3}\<close> and ktp: \<open>ktv_rows pd\<^sub>2 \<subseteq> FK\<close>
    by (auto simp: inwf_def)
  from o2 have sc2: \<open>sconf s\<^sub>2 {..< n\<^sub>3} {..< n\<^sub>3}\<close> and kh2: \<open>khyg s\<^sub>2 FK\<close>
    and bf2: \<open>bfree_sub s\<^sub>2\<close> by (auto simp: outwf_def)
  let ?lt = \<open>sapp s\<^sub>2 (TV (Suc n\<^sub>1))\<close> and ?ta = \<open>sapp s\<^sub>2 (TV (Suc (Suc n\<^sub>1)))\<close>
  have klt: \<open>ktv ?lt \<subseteq> FK\<close> and kta: \<open>ktv ?ta \<subseteq> FK\<close>
    by (rule khyg_sapp[OF kh2], simp)+
  have flt: \<open>ftv ?lt \<subseteq> {..< n\<^sub>3}\<close> and fta': \<open>ftv ?ta \<subseteq> {..< n\<^sub>3}\<close>
    by (rule ftv_sapp_sconf[OF sc2], use le23 in simp)+
  have rlt: \<open>frv ?lt \<subseteq> {..< n\<^sub>3}\<close> and rta: \<open>frv ?ta \<subseteq> {..< n\<^sub>3}\<close>
    by (rule frv_sapp_sconf[OF sc2]; use le23 in simp)+
  have blt: \<open>bfree ?lt\<close> and bta: \<open>bfree ?ta\<close> by (rule bfree_sapp[OF bf2], simp)+
  have ne: \<open>cenv (name_env (sappe s\<^sub>2 ?B\<^sub>1) (n_txt x) ?lt) \<and>
      bfree_env (name_env (sappe s\<^sub>2 ?B\<^sub>1) (n_txt x) ?lt) \<and>
      ktv_env (name_env (sappe s\<^sub>2 ?B\<^sub>1) (n_txt x) ?lt) = {} \<and>
      ftv_env (name_env (sappe s\<^sub>2 ?B\<^sub>1) (n_txt x) ?lt) = {} \<and>
      frv_env (name_env (sappe s\<^sub>2 ?B\<^sub>1) (n_txt x) ?lt) = {}\<close>
    by (cases rule: name_env_cases[of \<open>sappe s\<^sub>2 ?B\<^sub>1\<close> \<open>n_txt x\<close> ?lt]) simp_all
  have fr0: \<open>frv_row (sappr s\<^sub>2 (RV (Suc (Suc (Suc n\<^sub>1))))) \<subseteq> {..< n\<^sub>3}\<close>
    by (rule frv_sappr_sconf[OF sc2]) (use le23 in auto)
  have br0: \<open>brv_row (sappr s\<^sub>2 (RV (Suc (Suc (Suc n\<^sub>1))))) = {}\<close>
    by (rule bfree_sappr[OF bf2]) simp
  have iB': \<open>inwf (name_env (sappe s\<^sub>2 ?B\<^sub>1) (n_txt x) ?lt @
        (n_txt x, TEval (kmono (TEv ?lt (TK n\<^sub>1) ?ta))) # sappe s\<^sub>2 ?B\<^sub>1)
      (sappr s\<^sub>2 (RV (Suc (Suc (Suc n\<^sub>1))))) pd\<^sub>2 (insert n\<^sub>1 FK) n\<^sub>3\<close>
    using ne cenvB bfB ktvB ftvB frvB ftp frp subset_insertI2[OF ktp] klt kta flt fta' rlt rta blt bta
          fr0 br0
    by (auto simp: inwf_def bfree_def)
  note wb = IH\<^sub>2[OF d1 kn nm ap ib iB']
  have le3: \<open>n\<^sub>3 \<le> n\<^sub>b\<close> and ob: \<open>outwf s\<^sub>b pd\<^sub>b (insert n\<^sub>1 FK) n\<^sub>b\<close>
    and ftb: \<open>fresh_ok \<tau>\<^sub>b 0 n\<^sub>b (insert n\<^sub>1 FK)\<close> using wb by simp_all
  have o2': \<open>outwf s\<^sub>2 pd\<^sub>2 (insert n\<^sub>1 FK) n\<^sub>3\<close>
    using o2 khyg_mono[OF kh2, of \<open>insert n\<^sub>1 FK\<close>] by (auto simp: outwf_def)
  have f0: \<open>fresh_ok (TV (Suc (Suc (Suc (Suc n\<^sub>1))))) 0 n\<^sub>3 (insert n\<^sub>1 FK)\<close>
    by (rule fresh_ok_mono[OF fresh_ok_TV]) (use le23 in simp_all)
  have f1: \<open>fresh_ok (sapp (s\<^sub>b \<odot> s\<^sub>2) (TV (Suc (Suc (Suc (Suc n\<^sub>1)))))) 0 n\<^sub>b (insert n\<^sub>1 FK)\<close>
    unfolding sapp_scomp by (rule fresh_ok_sapp0[OF fresh_ok_sapp0[OF f0 o2' order_refl] ob le3])
  note wu = uni_fresh[OF un f1 ftb zero_le]
  have le4: \<open>n\<^sub>b \<le> n\<^sub>5\<close> and sc4: \<open>sconf s\<^sub>4 {..< n\<^sub>5} {..< n\<^sub>5}\<close> and kh4: \<open>khyg s\<^sub>4 (insert n\<^sub>1 FK)\<close>
    and bf4: \<open>bfree_sub s\<^sub>4\<close> using wu by (simp_all add: atLeast0LessThan)
  from ob have opd: \<open>ftv_pend pd\<^sub>b \<subseteq> {..< n\<^sub>b}\<close> \<open>frv_pend pd\<^sub>b \<subseteq> {..< n\<^sub>b}\<close>
    \<open>ktv_rows pd\<^sub>b \<subseteq> insert n\<^sub>1 FK\<close>
    by (auto simp: outwf_def)
  have o4: \<open>outwf s\<^sub>4 (sub_pend s\<^sub>4 pd\<^sub>b) (insert n\<^sub>1 FK) n\<^sub>5\<close>
    by (rule outwf_of_uni[OF sc4 kh4 bf4 opd(1) opd(2) le4 opd(3)])
  have o': \<open>outwf (s\<^sub>4 \<odot> s\<^sub>b) (sub_pend s\<^sub>4 pd\<^sub>b) (insert n\<^sub>1 FK) n\<^sub>5\<close>
    by (rule outwf_scomp[OF ob o4 le4])
  then have sc': \<open>sconf (s\<^sub>4 \<odot> s\<^sub>b) {..< n\<^sub>5} {..< n\<^sub>5}\<close> and kh': \<open>khyg (s\<^sub>4 \<odot> s\<^sub>b) (insert n\<^sub>1 FK)\<close>
    and bf': \<open>bfree_sub (s\<^sub>4 \<odot> s\<^sub>b)\<close> and pd': \<open>ftv_pend (sub_pend s\<^sub>4 pd\<^sub>b) \<subseteq> {..< n\<^sub>5}\<close>
      \<open>frv_pend (sub_pend s\<^sub>4 pd\<^sub>b) \<subseteq> {..< n\<^sub>5}\<close> by (auto simp: outwf_def)
  have kall: \<open>\<forall>a < n\<^sub>3. ktv (fst (s\<^sub>4 \<odot> s\<^sub>b) a) \<subseteq> FK\<close>
  proof (intro allI impI)
    fix a assume \<open>a < n\<^sub>3\<close>
    then have \<open>n\<^sub>1 \<notin> ktv (fst (s\<^sub>4 \<odot> s\<^sub>b) a)\<close> using esc by (auto simp: list_all_iff)
    then show \<open>ktv (fst (s\<^sub>4 \<odot> s\<^sub>b) a) \<subseteq> FK\<close> using kh' unfolding khyg_def by blast
  qed
  have opk: \<open>ktv_rows (sub_pend s\<^sub>4 pd\<^sub>b) \<subseteq> FK\<close> using o' escp by (auto simp: outwf_def)
  have op: \<open>outwf (sproj n\<^sub>3 (s\<^sub>4 \<odot> s\<^sub>b)) (sub_pend s\<^sub>4 pd\<^sub>b) FK n\<^sub>5\<close>
    unfolding outwf_def
    using sconf_sproj[OF sc'] khyg_sproj[OF kall] bfree_sub_sproj[OF bf'] pd' opk by simp
  have le35: \<open>n\<^sub>3 \<le> n\<^sub>5\<close> using le3 le4 by simp
  have os2: \<open>outwf (sproj n\<^sub>3 (s\<^sub>4 \<odot> s\<^sub>b) \<odot> s\<^sub>2) (sub_pend s\<^sub>4 pd\<^sub>b) FK n\<^sub>5\<close>
    by (rule outwf_scomp[OF o2 op le35])
  have le15: \<open>n\<^sub>1 \<le> n\<^sub>5\<close> using le12 le23 le35 by simp
  have os: \<open>outwf s (sub_pend s\<^sub>4 pd\<^sub>b) FK n\<^sub>5\<close>
    unfolding se(1) by (rule outwf_scomp[OF o1 os2 le15])
  have f\<tau>: \<open>fresh_ok \<tau> 0 n\<^sub>5 FK\<close> unfolding se(2) by (rule fresh_ok_sapp0[OF fta op le35])
  have \<open>n \<le> n\<^sub>5\<close> using le1 le15 by simp
  then show ?thesis using os f\<tau> se by simp
qed

text \<open>A \<open>let\<close>: the bound pattern's generalised frame (\<^const>\<open>gen_env\<close>) is
  well formed at the new counter.\<close>

lemma infer_let_wf:
  assumes E: \<open>infer uf B A pd (ELet p e b) n = Some (s, e\<^sub>x, \<tau>, pd', n')\<close>
    and I: \<open>inwf B A pd FK n\<close>
    and IH\<^sub>e: \<open>\<And>s e' \<tau> pd' n' FK. infer uf B A pd e n = Some (s, e', \<tau>, pd', n') \<Longrightarrow>
        inwf B A pd FK n \<Longrightarrow> n \<le> n' \<and> outwf s pd' FK n' \<and> fresh_ok \<tau> 0 n' FK\<close>
    and IH\<^sub>b: \<open>\<And>s\<^sub>1 e'' \<tau>\<^sub>e pd\<^sub>1 n\<^sub>1 sp p\<^sub>x \<tau>\<^sub>p \<Gamma> n\<^sub>2 s\<^sub>2 n\<^sub>3 asx rsx reqs pdr s\<^sub>3 b'' \<tau>\<^sub>b pd\<^sub>3 n\<^sub>4 FK.
        infer uf B A pd e n = Some (s\<^sub>1, e'', \<tau>\<^sub>e, pd\<^sub>1, n\<^sub>1) \<Longrightarrow>
        infer_pat uf (sappe s\<^sub>1 B) p n\<^sub>1 = Some (sp, p\<^sub>x, \<tau>\<^sub>p, \<Gamma>, n\<^sub>2) \<Longrightarrow>
        uni uf (sapp sp \<tau>\<^sub>e) \<tau>\<^sub>p n\<^sub>2 = Some (s\<^sub>2, n\<^sub>3) \<Longrightarrow>
        (asx, rsx, reqs, pdr) =
          (if val_exp B e''
           then (if var_pat p \<and> length \<Gamma> = 1
                 then gen_off (sappe (s\<^sub>2 \<odot> sp \<odot> s\<^sub>1) B) (sappr (s\<^sub>2 \<odot> sp \<odot> s\<^sub>1) A)
                        (sub_pend (s\<^sub>2 \<odot> sp) pd\<^sub>1) n (sapp s\<^sub>2 \<tau>\<^sub>p)
                 else (case gen_p (sappe (s\<^sub>2 \<odot> sp \<odot> s\<^sub>1) B) (sappr (s\<^sub>2 \<odot> sp \<odot> s\<^sub>1) A)
                              (sub_pend (s\<^sub>2 \<odot> sp) pd\<^sub>1) n (sapp s\<^sub>2 \<tau>\<^sub>p)
                       of (as, rs) \<Rightarrow> (as, rs, [], sub_pend (s\<^sub>2 \<odot> sp) pd\<^sub>1)))
           else ({}, {}, [], sub_pend (s\<^sub>2 \<odot> sp) pd\<^sub>1)) \<Longrightarrow>
        covers (sappe (s\<^sub>2 \<odot> sp \<odot> s\<^sub>1) B) (sapp s\<^sub>2 \<tau>\<^sub>p) [p] \<and>
          btv_list (sapp s\<^sub>2 \<tau>\<^sub>p) = [] \<and> brv_list (sapp s\<^sub>2 \<tau>\<^sub>p) = [] \<Longrightarrow>
        infer uf (gen_env s\<^sub>2 asx rsx reqs \<Gamma> @ sappe (s\<^sub>2 \<odot> sp \<odot> s\<^sub>1) B) (sappr (s\<^sub>2 \<odot> sp \<odot> s\<^sub>1) A)
          pdr b n\<^sub>3 = Some (s\<^sub>3, b'', \<tau>\<^sub>b, pd\<^sub>3, n\<^sub>4) \<Longrightarrow>
        inwf (gen_env s\<^sub>2 asx rsx reqs \<Gamma> @ sappe (s\<^sub>2 \<odot> sp \<odot> s\<^sub>1) B) (sappr (s\<^sub>2 \<odot> sp \<odot> s\<^sub>1) A)
          pdr FK n\<^sub>3 \<Longrightarrow>
        n\<^sub>3 \<le> n\<^sub>4 \<and> outwf s\<^sub>3 pd\<^sub>3 FK n\<^sub>4 \<and> fresh_ok \<tau>\<^sub>b 0 n\<^sub>4 FK\<close>
  shows \<open>n \<le> n' \<and> outwf s pd' FK n' \<and> fresh_ok \<tau> 0 n' FK\<close>
proof -
  obtain s\<^sub>1 e'' \<tau>\<^sub>e pd\<^sub>1 n\<^sub>1 where d1: \<open>infer uf B A pd e n = Some (s\<^sub>1, e'', \<tau>\<^sub>e, pd\<^sub>1, n\<^sub>1)\<close>
  proof (cases \<open>infer uf B A pd e n\<close>)
    case None then show ?thesis using E by simp
  next
    case (Some r) then show ?thesis using that by (cases r) auto
  qed
  obtain sp p\<^sub>x \<tau>\<^sub>p \<Gamma> n\<^sub>2 where dp: \<open>infer_pat uf (sappe s\<^sub>1 B) p n\<^sub>1 = Some (sp, p\<^sub>x, \<tau>\<^sub>p, \<Gamma>, n\<^sub>2)\<close>
  proof (cases \<open>infer_pat uf (sappe s\<^sub>1 B) p n\<^sub>1\<close>)
    case None then show ?thesis using E
      by (simp add: d1 del: sapp.simps sappe.simps sappr.simps sapps.simps)
  next
    case (Some r) then show ?thesis using that by (cases r) auto
  qed
  obtain s\<^sub>2 n\<^sub>3 where u1: \<open>uni uf (sapp sp \<tau>\<^sub>e) \<tau>\<^sub>p n\<^sub>2 = Some (s\<^sub>2, n\<^sub>3)\<close>
  proof (cases \<open>uni uf (sapp sp \<tau>\<^sub>e) \<tau>\<^sub>p n\<^sub>2\<close>)
    case None then show ?thesis using E
      by (simp add: d1 dp del: sapp.simps sappe.simps sappr.simps sapps.simps)
  next
    case (Some r) then show ?thesis using that by (cases r) auto
  qed
  let ?s = \<open>s\<^sub>2 \<odot> sp \<odot> s\<^sub>1\<close> and ?pd = \<open>sub_pend (s\<^sub>2 \<odot> sp) pd\<^sub>1\<close>
  obtain asx rsx reqs pdr where asrs: \<open>(asx, rsx, reqs, pdr) =
    (if val_exp B e''
     then (if var_pat p \<and> length \<Gamma> = 1
           then gen_off (sappe ?s B) (sappr ?s A) ?pd n (sapp s\<^sub>2 \<tau>\<^sub>p)
           else (case gen_p (sappe ?s B) (sappr ?s A) ?pd n (sapp s\<^sub>2 \<tau>\<^sub>p)
                 of (as, rs) \<Rightarrow> (as, rs, [], ?pd)))
     else ({}, {}, [], ?pd))\<close>
    by (metis prod_cases4)
  have covb: \<open>covers (sappe ?s B) (sapp s\<^sub>2 \<tau>\<^sub>p) [p] \<and>
      btv_list (sapp s\<^sub>2 \<tau>\<^sub>p) = [] \<and> brv_list (sapp s\<^sub>2 \<tau>\<^sub>p) = []\<close>
    using E by (simp add: d1 dp u1 asrs[symmetric] Let_def
        split: if_split_asm del: sapp.simps sappe.simps sappr.simps sapps.simps)
  obtain s\<^sub>3 b'' pd\<^sub>3
    where d3: \<open>infer uf (gen_env s\<^sub>2 asx rsx reqs \<Gamma> @ sappe ?s B) (sappr ?s A) pdr b n\<^sub>3
        = Some (s\<^sub>3, b'', \<tau>, pd\<^sub>3, n')\<close>
      and se: \<open>s = s\<^sub>3 \<odot> ?s\<close> \<open>pd' = pd\<^sub>3\<close>
  proof (cases \<open>infer uf (gen_env s\<^sub>2 asx rsx reqs \<Gamma> @ sappe ?s B) (sappr ?s A) pdr b n\<^sub>3\<close>)
    case None then show ?thesis using E
      by (simp add: d1 dp u1 asrs[symmetric] covb gen_env_def Let_def
          del: sapp.simps sappe.simps sappr.simps sapps.simps)
  next
    case (Some r) then show ?thesis using that E
      by (cases r) (auto simp: d1 dp u1 asrs[symmetric] covb gen_env_def Let_def
          simp del: sapp.simps sappe.simps sappr.simps sapps.simps)
  qed
  from I have cenvB: \<open>cenv B\<close> and bfB: \<open>bfree_env B\<close> and ktvB: \<open>ktv_env B \<subseteq> FK\<close>
    and frA: \<open>frv_row A \<subseteq> {..< n}\<close> and brA: \<open>brv_row A = {}\<close>
    and ftp: \<open>ftv_pend pd \<subseteq> {..< n}\<close> and frp: \<open>frv_pend pd \<subseteq> {..< n}\<close> and ktp: \<open>ktv_rows pd \<subseteq> FK\<close>
    by (auto simp: inwf_def)
  from d1 I have \<open>n \<le> n\<^sub>1 \<and> outwf s\<^sub>1 pd\<^sub>1 FK n\<^sub>1 \<and> fresh_ok \<tau>\<^sub>e 0 n\<^sub>1 FK\<close>
    by (rule IH\<^sub>e)
  then have le1: \<open>n \<le> n\<^sub>1\<close> and o1: \<open>outwf s\<^sub>1 pd\<^sub>1 FK n\<^sub>1\<close>
    and fte: \<open>fresh_ok \<tau>\<^sub>e 0 n\<^sub>1 FK\<close> by simp_all
  from o1 have sc1: \<open>sconf s\<^sub>1 {..< n\<^sub>1} {..< n\<^sub>1}\<close> and kh1: \<open>khyg s\<^sub>1 FK\<close>
    and bf1: \<open>bfree_sub s\<^sub>1\<close> and ftp1: \<open>ftv_pend pd\<^sub>1 \<subseteq> {..< n\<^sub>1}\<close>
    and frp1: \<open>frv_pend pd\<^sub>1 \<subseteq> {..< n\<^sub>1}\<close> and pk1: \<open>ktv_rows pd\<^sub>1 \<subseteq> FK\<close>
    by (auto simp: outwf_def)
  note wp = infer_pat_wf(1)[OF dp cenv_sappe[OF cenvB] bfree_env_sappe[OF bf1 bfB]
              ktv_env_sappe[OF kh1 ktvB]]
  have le2: \<open>n\<^sub>1 \<le> n\<^sub>2\<close> using wp by simp
  have scp0: \<open>sconf sp {n\<^sub>1 ..< n\<^sub>2} {n\<^sub>1 ..< n\<^sub>2}\<close> and khp: \<open>khyg sp FK\<close>
    and bfp: \<open>bfree_sub sp\<close> and boG: \<open>binds_ok \<Gamma> n\<^sub>1 n\<^sub>2 FK\<close>
    and fp: \<open>fresh_ok \<tau>\<^sub>p n\<^sub>1 n\<^sub>2 FK\<close> using wp by simp_all
  have scp: \<open>sconf sp {..< n\<^sub>2} {..< n\<^sub>2}\<close> by (rule sconf_mono[OF scp0]) auto
  have fse: \<open>fresh_ok (sapp sp \<tau>\<^sub>e) 0 n\<^sub>2 FK\<close>
    by (rule fresh_ok_sapp0[OF fte outwf_of_uni[OF scp khp bfp ftp1 frp1 le2 pk1] le2])
  note uf1 = uni_fresh[OF u1 fse fresh_ok_weaken0[OF fp] le0]
  have le3: \<open>n\<^sub>2 \<le> n\<^sub>3\<close> using uf1 by simp
  have sc2: \<open>sconf s\<^sub>2 {..< n\<^sub>3} {..< n\<^sub>3}\<close> using uf1 by (simp add: atLeast0LessThan)
  have kh2: \<open>khyg s\<^sub>2 FK\<close> and bf2: \<open>bfree_sub s\<^sub>2\<close> using uf1 by simp_all
  have le13: \<open>n \<le> n\<^sub>3\<close> using le1 le2 le3 by simp
  have subn12: \<open>{..< n\<^sub>1} \<subseteq> {..< n\<^sub>2}\<close> using le2 by simp
  have subn23: \<open>{..< n\<^sub>2} \<subseteq> {..< n\<^sub>3}\<close> using le3 by simp
  have scps1: \<open>sconf (sp \<odot> s\<^sub>1) {..< n\<^sub>2} {..< n\<^sub>2}\<close>
    by (rule sconf_scomp_mono[OF sc1 scp subn12 subn12])
  have scs: \<open>sconf ?s {..< n\<^sub>3} {..< n\<^sub>3}\<close>
    using sconf_scomp_mono[OF scps1 sc2 subn23 subn23] by (simp add: scomp_assoc)
  have khs: \<open>khyg ?s FK\<close>
    using khyg_scomp[OF khyg_scomp[OF kh1 khp] kh2] by (simp add: scomp_assoc)
  have bfs: \<open>bfree_sub ?s\<close>
    using bfree_sub_scomp[OF bfree_sub_scomp[OF bf1 bfp] bf2] by (simp add: scomp_assoc)
  have sc2p: \<open>sconf (s\<^sub>2 \<odot> sp) {..< n\<^sub>3} {..< n\<^sub>3}\<close>
    by (rule sconf_scomp_mono[OF scp sc2 subn23 subn23])
  have kh2p: \<open>khyg (s\<^sub>2 \<odot> sp) FK\<close> by (rule khyg_scomp[OF khp kh2])
  have boG0: \<open>binds_ok \<Gamma> 0 n\<^sub>3 FK\<close> by (rule binds_ok_mono[OF boG le0 le3])
  have sub13x: \<open>{..< n} \<subseteq> {..< n\<^sub>3}\<close> using le13 by simp
  have af: \<open>frv_row (sappr ?s A) \<subseteq> {..< n\<^sub>3}\<close>
    by (rule frv_sappr_sconf[OF scs subset_trans[OF frA sub13x]])
  have ab: \<open>brv_row (sappr ?s A) = {}\<close> by (rule bfree_sappr[OF bfs brA])
  have sub123: \<open>{..< n\<^sub>1} \<subseteq> {..< n\<^sub>3}\<close> using subn12 subn23 by simp
  have pf: \<open>ftv_pend ?pd \<subseteq> {..< n\<^sub>3}\<close>
    by (rule ftv_pend_sub_pend[OF sc2p subset_trans[OF ftp1 sub123]])
  have pr: \<open>frv_pend ?pd \<subseteq> {..< n\<^sub>3}\<close>
    by (rule frv_pend_sub_pend[OF sc2p subset_trans[OF ftp1 sub123] subset_trans[OF frp1 sub123]])
  have pk: \<open>ktv_rows ?pd \<subseteq> FK\<close> by (rule ktv_rows_sub_pend[OF kh2p pk1])
  note gc = gen_choice_pend[OF asrs]
  have pf': \<open>ftv_pend pdr \<subseteq> {..< n\<^sub>3}\<close> using ftv_pend_mono[OF gc(1)] pf by blast
  have pr': \<open>frv_pend pdr \<subseteq> {..< n\<^sub>3}\<close> using frv_pend_mono[OF gc(1)] pr by blast
  have pk': \<open>ktv_rows pdr \<subseteq> FK\<close> using ktv_rows_mono[OF gc(1)] pk by blast
  note rk = reqs_bounds[OF gc(2) pf pr pk]
  have i3: \<open>inwf (gen_env s\<^sub>2 asx rsx reqs \<Gamma> @ sappe ?s B) (sappr ?s A) pdr FK n\<^sub>3\<close>
    by (rule inwf_let[OF I scs khs bfs sc2 kh2 boG0 af ab pf' pr' pk' rk le13])
  have \<open>n\<^sub>3 \<le> n' \<and> outwf s\<^sub>3 pd\<^sub>3 FK n' \<and> fresh_ok \<tau> 0 n' FK\<close>
    by (rule IH\<^sub>b[OF d1 dp u1 asrs covb d3 i3])
  then have le4: \<open>n\<^sub>3 \<le> n'\<close> and o3: \<open>outwf s\<^sub>3 pd\<^sub>3 FK n'\<close>
    and fresh: \<open>fresh_ok \<tau> 0 n' FK\<close> by simp_all
  have os: \<open>outwf ?s ?pd FK n\<^sub>3\<close> unfolding outwf_def using scs khs bfs pf pr pk by simp
  show ?thesis using se le13 le4 fresh outwf_scomp[OF os o3 le4] by simp
qed


lemma infer_letfun_wf:
  assumes E: \<open>infer uf B A pd (ELetFun f mbs cls b) n = Some (s, e\<^sub>x, \<tau>, pd', n')\<close>
    and I: \<open>inwf B A pd FK n\<close>
    and IH\<^sub>r: \<open>\<And>s\<^sub>1 r' \<tau>' pd\<^sub>1 n\<^sub>1 FK'.
        infer uf ((n_txt f, TEval (kmono (TV n))) # B) A pd (foldr EFnMod mbs (dfun_rhs cls)) (Suc n)
          = Some (s\<^sub>1, r', \<tau>', pd\<^sub>1, n\<^sub>1) \<Longrightarrow>
        inwf ((n_txt f, TEval (kmono (TV n))) # B) A pd FK' (Suc n) \<Longrightarrow>
        Suc n \<le> n\<^sub>1 \<and> outwf s\<^sub>1 pd\<^sub>1 FK' n\<^sub>1 \<and> fresh_ok \<tau>' 0 n\<^sub>1 FK'\<close>
    and IH\<^sub>b: \<open>\<And>s\<^sub>1 r' \<tau>' pd\<^sub>1 n\<^sub>1 s\<^sub>2 n\<^sub>2 as rs reqs pdr s\<^sub>3 b' \<tau>\<^sub>b pd\<^sub>3 n\<^sub>3 FK'.
        infer uf ((n_txt f, TEval (kmono (TV n))) # B) A pd (foldr EFnMod mbs (dfun_rhs cls)) (Suc n)
          = Some (s\<^sub>1, r', \<tau>', pd\<^sub>1, n\<^sub>1) \<Longrightarrow>
        uni uf (sapp s\<^sub>1 (TV n)) \<tau>' n\<^sub>1 = Some (s\<^sub>2, n\<^sub>2) \<Longrightarrow>
        (as, rs, reqs, pdr) = gen_off (sappe (s\<^sub>2 \<odot> s\<^sub>1) B) (sappr (s\<^sub>2 \<odot> s\<^sub>1) A) (sub_pend s\<^sub>2 pd\<^sub>1) n
          (sapp s\<^sub>2 \<tau>') \<Longrightarrow>
        btv_list (sapp s\<^sub>2 \<tau>') = [] \<and> brv_list (sapp s\<^sub>2 \<tau>') = [] \<Longrightarrow>
        infer uf ((n_txt f, TEval (close_sch as rs (offs reqs (sapp s\<^sub>2 \<tau>')))) # sappe (s\<^sub>2 \<odot> s\<^sub>1) B)
          (sappr (s\<^sub>2 \<odot> s\<^sub>1) A) pdr b n\<^sub>2 = Some (s\<^sub>3, b', \<tau>\<^sub>b, pd\<^sub>3, n\<^sub>3) \<Longrightarrow>
        inwf ((n_txt f, TEval (close_sch as rs (offs reqs (sapp s\<^sub>2 \<tau>')))) # sappe (s\<^sub>2 \<odot> s\<^sub>1) B)
          (sappr (s\<^sub>2 \<odot> s\<^sub>1) A) pdr FK' n\<^sub>2 \<Longrightarrow>
        n\<^sub>2 \<le> n\<^sub>3 \<and> outwf s\<^sub>3 pd\<^sub>3 FK' n\<^sub>3 \<and> fresh_ok \<tau>\<^sub>b 0 n\<^sub>3 FK'\<close>
  shows \<open>n \<le> n' \<and> outwf s pd' FK n' \<and> fresh_ok \<tau> 0 n' FK\<close>
proof -
  obtain s\<^sub>1 r' \<tau>' pd\<^sub>1 n\<^sub>1 where d1:
    \<open>infer uf ((n_txt f, TEval (kmono (TV n))) # B) A pd (foldr EFnMod mbs (dfun_rhs cls)) (Suc n)
       = Some (s\<^sub>1, r', \<tau>', pd\<^sub>1, n\<^sub>1)\<close>
    using E by (auto simp: Let_def bind_eq_Some_conv split: prod.split_asm if_split_asm
      simp del: sapp.simps sappe.simps sappr.simps sapps.simps)
  obtain s\<^sub>2 n\<^sub>2 where u1: \<open>uni uf (sapp s\<^sub>1 (TV n)) \<tau>' n\<^sub>1 = Some (s\<^sub>2, n\<^sub>2)\<close>
  proof (cases \<open>uni uf (sapp s\<^sub>1 (TV n)) \<tau>' n\<^sub>1\<close>)
    case None then show ?thesis using E
      by (simp add: d1 Let_def split: if_split_asm del: sapp.simps sappe.simps sappr.simps sapps.simps)
  next
    case (Some r) then show ?thesis using that by (cases r) auto
  qed
  obtain as rs reqs pdr where asrs: \<open>(as, rs, reqs, pdr) = gen_off (sappe (s\<^sub>2 \<odot> s\<^sub>1) B)
      (sappr (s\<^sub>2 \<odot> s\<^sub>1) A) (sub_pend s\<^sub>2 pd\<^sub>1) n (sapp s\<^sub>2 \<tau>')\<close>
    by (metis prod_cases4)
  have bt: \<open>btv_list (sapp s\<^sub>2 \<tau>') = [] \<and> brv_list (sapp s\<^sub>2 \<tau>') = []\<close>
    using E by (simp add: d1 u1[simplified] asrs[symmetric] Let_def
        split: if_split_asm del: sapp.simps sappe.simps sappr.simps sapps.simps)
  obtain s\<^sub>3 b' pd\<^sub>3 where d3:
    \<open>infer uf ((n_txt f, TEval (close_sch as rs (offs reqs (sapp s\<^sub>2 \<tau>')))) # sappe (s\<^sub>2 \<odot> s\<^sub>1) B)
       (sappr (s\<^sub>2 \<odot> s\<^sub>1) A) pdr b n\<^sub>2 = Some (s\<^sub>3, b', \<tau>, pd\<^sub>3, n')\<close>
    and se: \<open>s = s\<^sub>3 \<odot> (s\<^sub>2 \<odot> s\<^sub>1)\<close> \<open>pd' = pd\<^sub>3\<close>
  proof (cases \<open>infer uf ((n_txt f, TEval (close_sch as rs (offs reqs (sapp s\<^sub>2 \<tau>')))) # sappe (s\<^sub>2 \<odot> s\<^sub>1) B)
       (sappr (s\<^sub>2 \<odot> s\<^sub>1) A) pdr b n\<^sub>2\<close>)
    case None then show ?thesis using E
      by (simp add: d1 u1[simplified] asrs[symmetric] bt Let_def split: if_split_asm
          del: sapp.simps sappe.simps sappr.simps sapps.simps)
  next
    case (Some r) then show ?thesis using that E
      by (cases r) (auto simp: d1 u1[simplified] asrs[symmetric] bt Let_def split: if_split_asm
          simp del: sapp.simps sappe.simps sappr.simps sapps.simps)
  qed
  from I have cenvB: \<open>cenv B\<close> and bfB: \<open>bfree_env B\<close> and ktvB: \<open>ktv_env B \<subseteq> FK\<close>
    and ftvB: \<open>ftv_env B \<subseteq> {..< n}\<close> and frvB: \<open>frv_env B \<subseteq> {..< n}\<close>
    and frA: \<open>frv_row A \<subseteq> {..< n}\<close> and brA: \<open>brv_row A = {}\<close>
    and ftp: \<open>ftv_pend pd \<subseteq> {..< n}\<close> and frp: \<open>frv_pend pd \<subseteq> {..< n}\<close> and ktp: \<open>ktv_rows pd \<subseteq> FK\<close>
    and pk0: \<open>ktv_rows pd \<subseteq> FK\<close>
    by (auto simp: inwf_def)
  have subn: \<open>{..< n} \<subseteq> {..< Suc n}\<close> by simp
  have i0: \<open>inwf ((n_txt f, TEval (kmono (TV n))) # B) A pd FK (Suc n)\<close>
    using cenvB bfB ktvB frA brA subset_trans[OF ftvB subn] subset_trans[OF frvB subn]
      subset_trans[OF ftp subn] subset_trans[OF frp subn] pk0
    by (auto simp: inwf_def bfree_def)
  have w1: \<open>Suc n \<le> n\<^sub>1 \<and> outwf s\<^sub>1 pd\<^sub>1 FK n\<^sub>1 \<and> fresh_ok \<tau>' 0 n\<^sub>1 FK\<close> by (rule IH\<^sub>r[OF d1 i0])
  then have le1: \<open>Suc n \<le> n\<^sub>1\<close> and o1: \<open>outwf s\<^sub>1 pd\<^sub>1 FK n\<^sub>1\<close> and ft': \<open>fresh_ok \<tau>' 0 n\<^sub>1 FK\<close>
    by simp_all
  have ftv0: \<open>fresh_ok (TV n) 0 n\<^sub>1 FK\<close> using le1 by (auto simp: fresh_ok_def bfree_def)
  have fs0: \<open>fresh_ok (sapp s\<^sub>1 (TV n)) 0 n\<^sub>1 FK\<close>
    by (rule fresh_ok_sapp0[OF ftv0 o1 le_refl])
  note uf1 = uni_fresh[OF u1 fs0 ft' le0]
  then have le2: \<open>n\<^sub>1 \<le> n\<^sub>2\<close> and sc2: \<open>sconf s\<^sub>2 {..< n\<^sub>2} {..< n\<^sub>2}\<close>
    and kh2: \<open>khyg s\<^sub>2 FK\<close> and bf2: \<open>bfree_sub s\<^sub>2\<close> by (simp_all add: atLeast0LessThan)
  from o1 have sc1: \<open>sconf s\<^sub>1 {..< n\<^sub>1} {..< n\<^sub>1}\<close> and kh1: \<open>khyg s\<^sub>1 FK\<close>
    and bf1: \<open>bfree_sub s\<^sub>1\<close> and ftp1: \<open>ftv_pend pd\<^sub>1 \<subseteq> {..< n\<^sub>1}\<close>
    and frp1: \<open>frv_pend pd\<^sub>1 \<subseteq> {..< n\<^sub>1}\<close> and pk1: \<open>ktv_rows pd\<^sub>1 \<subseteq> FK\<close>
    by (auto simp: outwf_def)
  have le12: \<open>n \<le> n\<^sub>2\<close> using le1 le2 by simp
  have subn12: \<open>{..< n\<^sub>1} \<subseteq> {..< n\<^sub>2}\<close> using le2 by simp
  have scs: \<open>sconf (s\<^sub>2 \<odot> s\<^sub>1) {..< n\<^sub>2} {..< n\<^sub>2}\<close>
    by (rule sconf_scomp_mono[OF sc1 sc2 subn12 subn12])
  have khs: \<open>khyg (s\<^sub>2 \<odot> s\<^sub>1) FK\<close> by (rule khyg_scomp[OF kh1 kh2])
  have bfs: \<open>bfree_sub (s\<^sub>2 \<odot> s\<^sub>1)\<close> by (rule bfree_sub_scomp[OF bf1 bf2])
  have boG: \<open>binds_ok [(n_txt f, \<tau>')] 0 n\<^sub>2 FK\<close>
    using fresh_ok_mono[OF ft' le_refl le2] by (auto simp: binds_ok_def)
  have sub1n: \<open>{..< n} \<subseteq> {..< n\<^sub>2}\<close> using le12 by simp
  have af: \<open>frv_row (sappr (s\<^sub>2 \<odot> s\<^sub>1) A) \<subseteq> {..< n\<^sub>2}\<close>
    by (rule frv_sappr_sconf[OF scs subset_trans[OF frA sub1n]])
  have ab: \<open>brv_row (sappr (s\<^sub>2 \<odot> s\<^sub>1) A) = {}\<close> by (rule bfree_sappr[OF bfs brA])
  have pf: \<open>ftv_pend (sub_pend s\<^sub>2 pd\<^sub>1) \<subseteq> {..< n\<^sub>2}\<close>
    by (rule ftv_pend_sub_pend[OF sc2 subset_trans[OF ftp1 subn12]])
  have pr: \<open>frv_pend (sub_pend s\<^sub>2 pd\<^sub>1) \<subseteq> {..< n\<^sub>2}\<close>
    by (rule frv_pend_sub_pend[OF sc2 subset_trans[OF ftp1 subn12] subset_trans[OF frp1 subn12]])
  have pk: \<open>ktv_rows (sub_pend s\<^sub>2 pd\<^sub>1) \<subseteq> FK\<close> by (rule ktv_rows_sub_pend[OF kh2 pk1])
  from gen_off_pend[OF asrs[symmetric]]
  have sub: \<open>set pdr \<subseteq> set (sub_pend s\<^sub>2 pd\<^sub>1)\<close>
    and rq: \<open>\<And>v x r. (v, x, r) \<in> set reqs \<Longrightarrow> (v, POff x r) \<in> set (sub_pend s\<^sub>2 pd\<^sub>1)\<close>
    by blast+
  have pf': \<open>ftv_pend pdr \<subseteq> {..< n\<^sub>2}\<close> using ftv_pend_mono[OF sub] pf by blast
  have pr': \<open>frv_pend pdr \<subseteq> {..< n\<^sub>2}\<close> using frv_pend_mono[OF sub] pr by blast
  have pk': \<open>ktv_rows pdr \<subseteq> FK\<close> using ktv_rows_mono[OF sub] pk by blast
  note rk = reqs_bounds[OF rq pf pr pk]
  have i3: \<open>inwf (gen_env s\<^sub>2 as rs reqs [(n_txt f, \<tau>')] @ sappe (s\<^sub>2 \<odot> s\<^sub>1) B)
      (sappr (s\<^sub>2 \<odot> s\<^sub>1) A) pdr FK n\<^sub>2\<close>
    by (rule inwf_let[OF I scs khs bfs sc2 kh2 boG af ab pf' pr' pk' rk le12])
  then have i3': \<open>inwf ((n_txt f, TEval (close_sch as rs (offs reqs (sapp s\<^sub>2 \<tau>')))) # sappe (s\<^sub>2 \<odot> s\<^sub>1) B)
      (sappr (s\<^sub>2 \<odot> s\<^sub>1) A) pdr FK n\<^sub>2\<close>
    by (simp add: gen_env_def)
  have w3: \<open>n\<^sub>2 \<le> n' \<and> outwf s\<^sub>3 pd\<^sub>3 FK n' \<and> fresh_ok \<tau> 0 n' FK\<close>
    by (rule IH\<^sub>b[OF d1 u1 asrs bt d3 i3'])
  then have le3: \<open>n\<^sub>2 \<le> n'\<close> and o3: \<open>outwf s\<^sub>3 pd\<^sub>3 FK n'\<close> and fresh: \<open>fresh_ok \<tau> 0 n' FK\<close>
    by simp_all
  have os: \<open>outwf (s\<^sub>2 \<odot> s\<^sub>1) (sub_pend s\<^sub>2 pd\<^sub>1) FK n\<^sub>2\<close>
    unfolding outwf_def using scs khs bfs pf pr pk by simp
  show ?thesis using se le12 le3 fresh outwf_scomp[OF os o3 le3] by simp
qed
text \<open>Confinement of the expression algorithm, one part per function of the
  mutual definition. From a well-formed input (\<^const>\<open>inwf\<close>) every run moves the
  counter forward and returns a well-formed output (\<^const>\<open>outwf\<close>) and a result
  type fresh below the final counter (\<^const>\<open>fresh_ok\<close>). The parts that consume
  a given type (e.g. \<open>infer_args\<close>) assume it fresh as well.\<close>

lemma infer_wf:
  \<open>infer uf B A pd e n = Some (s, e', \<tau>, pd', n') \<Longrightarrow> inwf B A pd FK n \<Longrightarrow>
     n \<le> n' \<and> outwf s pd' FK n' \<and> fresh_ok \<tau> 0 n' FK\<close>
  \<open>infer_head uf B A pd a n = Some (s, a', \<tau>, pd', n') \<Longrightarrow> inwf B A pd FK n \<Longrightarrow>
     n \<le> n' \<and> outwf s pd' FK n' \<and> fresh_ok \<tau> 0 n' FK\<close>
  \<open>infer_atom uf B A pd a n = Some (s, a', \<tau>, pd', n') \<Longrightarrow> inwf B A pd FK n \<Longrightarrow>
     n \<le> n' \<and> outwf s pd' FK n' \<and> fresh_ok \<tau> 0 n' FK\<close>
  \<open>infer_args uf B A pd rg \<tau>\<^sub>0 as n = Some (s, as', \<tau>, pd', n') \<Longrightarrow> inwf B A pd FK n \<Longrightarrow>
     fresh_ok \<tau>\<^sub>0 0 n FK \<Longrightarrow>
     n \<le> n' \<and> outwf s pd' FK n' \<and> fresh_ok \<tau> 0 n' FK\<close>
  \<open>infer_exps uf B A pd es n = Some (s, es', \<tau>s, pd', n') \<Longrightarrow> inwf B A pd FK n \<Longrightarrow>
     n \<le> n' \<and> outwf s pd' FK n' \<and> (\<forall>\<tau> \<in> set \<tau>s. fresh_ok \<tau> 0 n' FK)\<close>
  \<open>infer_chain uf B A pd e n = Some (s, e', oprs, \<tau>s, pd', n') \<Longrightarrow> inwf B A pd FK n \<Longrightarrow>
     n \<le> n' \<and> outwf s pd' FK n' \<and> (\<forall>\<tau> \<in> set \<tau>s. fresh_ok \<tau> 0 n' FK)\<close>
  \<open>infer_arms uf B A pd \<tau>\<^sub>0 \<tau>\<^sub>r arms n = Some (s, arms', pd', n') \<Longrightarrow> inwf B A pd FK n \<Longrightarrow>
     fresh_ok \<tau>\<^sub>0 0 n FK \<Longrightarrow> fresh_ok \<tau>\<^sub>r 0 n FK \<Longrightarrow>
     n \<le> n' \<and> outwf s pd' FK n' \<and> fresh_ok (sapp s \<tau>\<^sub>r) 0 n' FK\<close>
  \<open>infer_cls uf B A pd nm \<tau>\<^sub>0 targs cls n = Some (s, cls', \<tau>, pd', n') \<Longrightarrow> inwf B A pd FK n \<Longrightarrow>
     fresh_ok \<tau>\<^sub>0 0 n FK \<Longrightarrow> fresh_ok targs 0 n FK \<Longrightarrow>
     n \<le> n' \<and> outwf s pd' FK n' \<and> fresh_ok \<tau> 0 n' FK\<close>
  proof (induction uf B A pd e n and uf B A pd a n and uf B A pd a n
           and uf B A pd rg \<tau>\<^sub>0 as n and uf B A pd es n and uf B A pd e n
           and uf B A pd \<tau>\<^sub>0 \<tau>\<^sub>r arms n and uf B A pd nm \<tau>\<^sub>0 targs cls n
         arbitrary: s e' \<tau> pd' n' FK and s a' \<tau> pd' n' FK and s a' \<tau> pd' n' FK
           and s as' \<tau> pd' n' FK and s es' \<tau>s pd' n' FK and s e' oprs \<tau>s pd' n' FK
           and s arms' pd' n' FK and s cls' \<tau> pd' n' FK
         rule: infer_induct)
    case (infer_ESpine_Cons uf B A pd a as n s e' \<tau> pd' n' FK)
    have E: \<open>infer uf B A pd (ESpine (a # as)) n = Some (s, e', \<tau>, pd', n')\<close>
      and I: \<open>inwf B A pd FK n\<close> by (fact infer_ESpine_Cons.prems)+
    from E obtain s\<^sub>1 a'' \<tau>\<^sub>0 pd\<^sub>1 n\<^sub>1 s\<^sub>2 as'' where
      d1: \<open>infer_head uf B A pd a n = Some (s\<^sub>1, a'', \<tau>\<^sub>0, pd\<^sub>1, n\<^sub>1)\<close> and
      d2: \<open>infer_args uf (sappe s\<^sub>1 B) (sappr s\<^sub>1 A) pd\<^sub>1 uf \<tau>\<^sub>0 as n\<^sub>1
        = Some (s\<^sub>2, as'', \<tau>, pd', n')\<close> and
      se: \<open>s = s\<^sub>2 \<odot> s\<^sub>1\<close>
      by (auto simp del: infer_args.simps split: Option.bind_split_asm prod.split_asm)
    from d1 I have \<open>n \<le> n\<^sub>1 \<and> outwf s\<^sub>1 pd\<^sub>1 FK n\<^sub>1 \<and> fresh_ok \<tau>\<^sub>0 0 n\<^sub>1 FK\<close>
      by (rule infer_ESpine_Cons.IH)
    then have le1: \<open>n \<le> n\<^sub>1\<close> and o1: \<open>outwf s\<^sub>1 pd\<^sub>1 FK n\<^sub>1\<close>
      and f0: \<open>fresh_ok \<tau>\<^sub>0 0 n\<^sub>1 FK\<close> by simp_all
    from d1 refl refl refl refl d2 inwf_step[OF I o1 le1] f0
    have \<open>n\<^sub>1 \<le> n' \<and> outwf s\<^sub>2 pd' FK n' \<and> fresh_ok \<tau> 0 n' FK\<close>
      by (rule infer_ESpine_Cons.IH)
    then have le2: \<open>n\<^sub>1 \<le> n'\<close> and o2: \<open>outwf s\<^sub>2 pd' FK n'\<close>
      and f2: \<open>fresh_ok \<tau> 0 n' FK\<close> by simp_all
    show ?case using se le1 le2 f2 outwf_scomp[OF o1 o2 le2] by simp
  next
    case (infer_EOp uf B A pd as opr e n s e' \<tau> pd' n' FK)
    have E: \<open>infer uf B A pd (EOp as opr e) n = Some (s, e', \<tau>, pd', n')\<close>
      and I: \<open>inwf B A pd FK n\<close> by (fact infer_EOp.prems)+
    obtain s\<^sub>1 e'x oprs \<tau>s pd\<^sub>1 n\<^sub>1
      where dc: \<open>infer_chain uf B A pd (EOp as opr e) n = Some (s\<^sub>1, e'x, oprs, \<tau>s, pd\<^sub>1, n\<^sub>1)\<close>
    proof (cases \<open>infer_chain uf B A pd (EOp as opr e) n\<close>)
      case None then show ?thesis using E by simp
    next
      case (Some r) then show ?thesis using that by (cases r) auto
    qed
    obtain tree where ct: \<open>chain_tree B oprs = Some tree\<close>
    proof (cases \<open>chain_tree B oprs\<close>)
      case None then show ?thesis using E
        by (simp add: dc del: sapp.simps sappe.simps sappr.simps)
    next
      case (Some t) then show ?thesis using that by simp
    qed
    obtain s\<^sub>2 n\<^sub>2
      where dt: \<open>infer_tree uf (sappe s\<^sub>1 B) (sappr s\<^sub>1 A) \<tau>s tree n\<^sub>1 = Some (s\<^sub>2, \<tau>, n\<^sub>2)\<close>
      and se: \<open>s = s\<^sub>2 \<odot> s\<^sub>1\<close> \<open>pd' = sub_pend s\<^sub>2 pd\<^sub>1\<close> \<open>n' = n\<^sub>2\<close>
    proof (cases \<open>infer_tree uf (sappe s\<^sub>1 B) (sappr s\<^sub>1 A) \<tau>s tree n\<^sub>1\<close>)
      case None then show ?thesis using E
        by (simp add: dc ct del: sapp.simps sappe.simps sappr.simps)
    next
      case (Some r) then show ?thesis using that E
        by (cases r) (auto simp: dc ct simp del: sapp.simps sappe.simps sappr.simps)
    qed
    from I have cenvB: \<open>cenv B\<close> and bfB: \<open>bfree_env B\<close> and ktvB: \<open>ktv_env B \<subseteq> FK\<close>
      and ftvB: \<open>ftv_env B \<subseteq> {..< n}\<close> and frvB: \<open>frv_env B \<subseteq> {..< n}\<close>
      and frA: \<open>frv_row A \<subseteq> {..< n}\<close> and brA: \<open>brv_row A = {}\<close>
      and ftp: \<open>ftv_pend pd \<subseteq> {..< n}\<close> and frp: \<open>frv_pend pd \<subseteq> {..< n}\<close> and ktp: \<open>ktv_rows pd \<subseteq> FK\<close>
      by (auto simp: inwf_def)
    note wc = infer_EOp.IH[OF dc I]
    have le1: \<open>n \<le> n\<^sub>1\<close> using wc by simp
    have o1: \<open>outwf s\<^sub>1 pd\<^sub>1 FK n\<^sub>1\<close> using wc by simp
    have fts: \<open>\<forall>\<tau> \<in> set \<tau>s. fresh_ok \<tau> 0 n\<^sub>1 FK\<close> using wc by simp
    from o1 have sc1: \<open>sconf s\<^sub>1 {..< n\<^sub>1} {..< n\<^sub>1}\<close> and kh1: \<open>khyg s\<^sub>1 FK\<close>
      and bf1: \<open>bfree_sub s\<^sub>1\<close> and ftp1: \<open>ftv_pend pd\<^sub>1 \<subseteq> {..< n\<^sub>1}\<close>
      and frp1: \<open>frv_pend pd\<^sub>1 \<subseteq> {..< n\<^sub>1}\<close> and ktp1: \<open>ktv_rows pd\<^sub>1 \<subseteq> FK\<close> by (auto simp: outwf_def)
    have subn: \<open>{..< n} \<subseteq> {..< n\<^sub>1}\<close> using le1 by simp
    note wt = infer_tree_wf[OF dt cenv_sappe[OF cenvB] bfree_env_sappe[OF bf1 bfB]
                ktv_env_sappe[OF kh1 ktvB] ftv_sappe_sconf[OF sc1 subset_trans[OF ftvB subn]]
                frv_sappe_sconf[OF sc1 subset_trans[OF ftvB subn] subset_trans[OF frvB subn]]
                frv_sappr_sconf[OF sc1 subset_trans[OF frA subn]] bfree_sappr[OF bf1 brA] fts]
    have le2: \<open>n\<^sub>1 \<le> n\<^sub>2\<close> using wt by simp
    have sc2: \<open>sconf s\<^sub>2 {..< n\<^sub>2} {..< n\<^sub>2}\<close> and kh2: \<open>khyg s\<^sub>2 FK\<close>
      and bf2: \<open>bfree_sub s\<^sub>2\<close> and f\<tau>: \<open>fresh_ok \<tau> 0 n\<^sub>2 FK\<close> using wt by simp_all
    have subn12: \<open>{..< n\<^sub>1} \<subseteq> {..< n\<^sub>2}\<close> using le2 by simp
    have scs: \<open>sconf (s\<^sub>2 \<odot> s\<^sub>1) {..< n\<^sub>2} {..< n\<^sub>2}\<close>
      by (rule sconf_scomp_mono[OF sc1 sc2 subn12 subn12])
    have khs: \<open>khyg (s\<^sub>2 \<odot> s\<^sub>1) FK\<close> by (rule khyg_scomp[OF kh1 kh2])
    have bfs: \<open>bfree_sub (s\<^sub>2 \<odot> s\<^sub>1)\<close> by (rule bfree_sub_scomp[OF bf1 bf2])
    have pf: \<open>ftv_pend (sub_pend s\<^sub>2 pd\<^sub>1) \<subseteq> {..< n\<^sub>2}\<close>
      by (rule ftv_pend_sub_pend[OF sc2 subset_trans[OF ftp1 subn12]])
    have pr: \<open>frv_pend (sub_pend s\<^sub>2 pd\<^sub>1) \<subseteq> {..< n\<^sub>2}\<close>
      by (rule frv_pend_sub_pend[OF sc2 subset_trans[OF ftp1 subn12]
            subset_trans[OF frp1 subn12]])
    have le: \<open>n \<le> n'\<close> using le1 le2 se by simp
    have os: \<open>outwf (s\<^sub>2 \<odot> s\<^sub>1) (sub_pend s\<^sub>2 pd\<^sub>1) FK n\<^sub>2\<close>
      unfolding outwf_def using scs khs bfs pf pr ktv_rows_sub_pend[OF kh2 ktp1] by simp
    show ?case using se le f\<tau> os by simp
  next
    case (infer_EAnn uf B A pd e ty n s e' \<tau> pd' n' FK)
    have E: \<open>infer uf B A pd (EAnn e ty) n = Some (s, e', \<tau>, pd', n')\<close>
      and I: \<open>inwf B A pd FK n\<close> by (fact infer_EAnn.prems)+
    from E obtain s\<^sub>1 e'' \<tau>\<^sub>1 pd\<^sub>1 n\<^sub>1 \<tau>\<^sub>a ve n\<^sub>2 s\<^sub>2 n\<^sub>3 where
      d1: \<open>infer uf B A pd e n = Some (s\<^sub>1, e'', \<tau>\<^sub>1, pd\<^sub>1, n\<^sub>1)\<close> and
      ts: \<open>ty_stat (sappe s\<^sub>1 B) True ([], []) n\<^sub>1 ty = Some (\<tau>\<^sub>a, ve, n\<^sub>2)\<close> and
      un: \<open>uni uf \<tau>\<^sub>1 (ann_ty (sappe s\<^sub>1 B) \<tau>\<^sub>1 \<tau>\<^sub>a) n\<^sub>2 = Some (s\<^sub>2, n\<^sub>3)\<close> and
      se: \<open>s = s\<^sub>2 \<odot> s\<^sub>1\<close> \<open>\<tau> = sapp s\<^sub>2 \<tau>\<^sub>1\<close> \<open>pd' = sub_pend s\<^sub>2 pd\<^sub>1\<close> \<open>n' = n\<^sub>3\<close>
      by (auto split: Option.bind_split_asm prod.split_asm)
    note w1 = infer_EAnn.IH[OF d1 I]
    have o1: \<open>outwf s\<^sub>1 pd\<^sub>1 FK n\<^sub>1\<close> and le1: \<open>n \<le> n\<^sub>1\<close>
      and f1: \<open>fresh_ok \<tau>\<^sub>1 0 n\<^sub>1 FK\<close> using w1 by simp_all
    have cenvB: \<open>cenv B\<close> and ktvB: \<open>ktv_env B \<subseteq> FK\<close> using I by (auto simp: inwf_def)
    from o1 have kh1: \<open>khyg s\<^sub>1 FK\<close> and sc1: \<open>sconf s\<^sub>1 {..< n\<^sub>1} {..< n\<^sub>1}\<close>
      and ftp1: \<open>ftv_pend pd\<^sub>1 \<subseteq> {..< n\<^sub>1}\<close> and frp1: \<open>frv_pend pd\<^sub>1 \<subseteq> {..< n\<^sub>1}\<close> and ktp1: \<open>ktv_rows pd\<^sub>1 \<subseteq> FK\<close>
      by (auto simp: outwf_def)
    have kv1: \<open>ktv_env (sappe s\<^sub>1 B) \<subseteq> FK\<close> by (rule ktv_env_sappe[OF kh1 ktvB])
    note tw = ty_stat_wf[OF ts cenv_sappe[OF cenvB], simplified tve_ok_def, simplified]
    have le2: \<open>n\<^sub>1 \<le> n\<^sub>2\<close> using tve_step_le[OF conjunct1[OF tw]] .
    have fa: \<open>fresh_ok \<tau>\<^sub>a n\<^sub>1 n\<^sub>2 FK\<close>
      by (rule fresh_ty_fresh_ok[OF conjunct2[OF tw] kv1])
    note unf = uni_fresh[OF un fresh_ok_mono[OF f1 le_refl le2]
        fresh_ok_ann_ty[OF fresh_ok_weaken0[OF fa]] le0]
    have le3: \<open>n\<^sub>2 \<le> n\<^sub>3\<close> using unf by simp
    have sc2: \<open>sconf s\<^sub>2 {..< n\<^sub>3} {..< n\<^sub>3}\<close> using unf by (simp add: atLeast0LessThan)
    have kh2: \<open>khyg s\<^sub>2 FK\<close> and bf2: \<open>bfree_sub s\<^sub>2\<close> using unf by simp_all
    have le13: \<open>n\<^sub>1 \<le> n\<^sub>3\<close> using le2 le3 by simp
    have o2: \<open>outwf s\<^sub>2 (sub_pend s\<^sub>2 pd\<^sub>1) FK n\<^sub>3\<close>
      by (rule outwf_of_uni[OF sc2 kh2 bf2 ftp1 frp1 le13 ktp1])
    show ?case using se le1 le13 outwf_scomp[OF o1 o2 le13] fresh_ok_sapp0[OF f1 o2 le13]
      by auto
  next
    case (infer_EFn uf B A pd ps b n s e' \<tau> pd' n' FK)
    have E: \<open>infer uf B A pd (EFn ps b) n = Some (s, e', \<tau>, pd', n')\<close>
      and I: \<open>inwf B A pd FK n\<close> by (fact infer_EFn.prems)+
    from E obtain sp \<tau>s \<Gamma> n\<^sub>1 s\<^sub>2 b'' \<tau>\<^sub>b ps\<^sub>x where
      d1: \<open>infer_pats uf B ps n = Some (sp, ps\<^sub>x, \<tau>s, \<Gamma>, n\<^sub>1)\<close> and
      d2: \<open>infer uf (mono_env sid \<Gamma> @ sappe sp B) (RV n\<^sub>1) (sub_pend sp pd) b (Suc n\<^sub>1)
             = Some (s\<^sub>2, b'', \<tau>\<^sub>b, pd', n')\<close> and
      se: \<open>s = s\<^sub>2 \<odot> sp\<close>
      and te: \<open>\<tau> = TFn (sapp s\<^sub>2 (fn_ty \<tau>s)) (sappr s\<^sub>2 (RV n\<^sub>1)) \<tau>\<^sub>b\<close>
      by (auto split: Option.bind_split_asm prod.split_asm if_split_asm simp: Let_def)
    from I have cenvB: \<open>cenv B\<close> and bfB: \<open>bfree_env B\<close> and ktvB: \<open>ktv_env B \<subseteq> FK\<close>
      and ftp: \<open>ftv_pend pd \<subseteq> {..< n}\<close> and frp: \<open>frv_pend pd \<subseteq> {..< n}\<close> and ktp: \<open>ktv_rows pd \<subseteq> FK\<close>
      by (auto simp: inwf_def)
    note wp = infer_pat_wf(4)[OF d1 cenvB bfB ktvB]
    have le1: \<open>n \<le> n\<^sub>1\<close> using wp by simp
    have scp0: \<open>sconf sp {n ..< n\<^sub>1} {n ..< n\<^sub>1}\<close> and khp: \<open>khyg sp FK\<close> and bfp: \<open>bfree_sub sp\<close>
      and boG: \<open>binds_ok \<Gamma> n n\<^sub>1 FK\<close> using wp by simp_all
    have \<tau>sf: \<open>\<forall>\<tau> \<in> set \<tau>s. fresh_ok \<tau> n n\<^sub>1 FK\<close> using wp by simp
    have scp: \<open>sconf sp {..< n\<^sub>1} {..< n\<^sub>1}\<close>
      by (rule sconf_mono[OF scp0]) auto
    have bo0: \<open>binds_ok \<Gamma> 0 n\<^sub>1 FK\<close> by (rule binds_ok_mono[OF boG le0 order_refl])
    have lsuc: \<open>{..< n\<^sub>1} \<subseteq> {..< Suc n\<^sub>1}\<close> by simp
    have ln1: \<open>{..< n} \<subseteq> {..< n\<^sub>1}\<close> using le1 by simp
    have o_sp: \<open>outwf sp (sub_pend sp pd) FK n\<^sub>1\<close>
      by (rule outwf_of_uni[OF scp khp bfp ftp frp le1 ktp])
    have af: \<open>frv_row (RV n\<^sub>1) \<subseteq> {..< Suc n\<^sub>1}\<close> by simp
    have pf: \<open>ftv_pend (sub_pend sp pd) \<subseteq> {..< Suc n\<^sub>1}\<close>
      by (rule subset_trans[OF ftv_pend_sub_pend[OF scp subset_trans[OF ftp ln1]] lsuc])
    have pr: \<open>frv_pend (sub_pend sp pd) \<subseteq> {..< Suc n\<^sub>1}\<close>
      by (rule subset_trans[OF frv_pend_sub_pend[OF scp subset_trans[OF ftp ln1]
            subset_trans[OF frp ln1]] lsuc])
    have pk: \<open>ktv_rows (sub_pend sp pd) \<subseteq> FK\<close> by (rule ktv_rows_sub_pend[OF khp ktp])
    have i2: \<open>inwf (mono_env sid \<Gamma> @ sappe sp B) (RV n\<^sub>1) (sub_pend sp pd) FK (Suc n\<^sub>1)\<close>
      using inwf_binders[OF I scp khp bfp bo0 af _ pf pr pk le1 le_SucI[OF le_refl]] by simp
    note w2 = infer_EFn.IH[OF d1 refl refl refl refl d2 i2]
    have le2: \<open>Suc n\<^sub>1 \<le> n'\<close> using w2 by simp
    have le3: \<open>n\<^sub>1 \<le> n'\<close> using le2 by simp
    have o2: \<open>outwf s\<^sub>2 pd' FK n'\<close> using w2 by simp
    have \<tau>sf0: \<open>\<forall>\<tau> \<in> set \<tau>s. fresh_ok \<tau> 0 n\<^sub>1 FK\<close>
      using \<tau>sf by (blast intro: fresh_ok_weaken0)
    have fa: \<open>fresh_ok (sapp s\<^sub>2 (fn_ty \<tau>s)) 0 n' FK\<close>
      by (rule fresh_ok_sapp0[OF fresh_ok_fn_ty[OF \<tau>sf0] o2 le3])
    have fe: \<open>frv_row (sappr s\<^sub>2 (RV n\<^sub>1)) \<subseteq> {..< n'}\<close>
      using frv_sappr_sconf[of s\<^sub>2 \<open>{..< n'}\<close> \<open>{..< n'}\<close> \<open>RV n\<^sub>1\<close>] o2 le2
      by (auto simp: outwf_def)
    have fb: \<open>brv_row (sappr s\<^sub>2 (RV n\<^sub>1)) = {}\<close>
      using bfree_sappr[of s\<^sub>2 \<open>RV n\<^sub>1\<close>] o2 by (auto simp: outwf_def)
    have fresh: \<open>fresh_ok \<tau> 0 n' FK\<close>
      unfolding te by (rule fresh_ok_TFn[OF fa w2[THEN conjunct2, THEN conjunct2] fe fb])
    show ?case using se le1 le3 fresh
      outwf_scomp[OF o_sp o2 le3] by auto
  next
    case (infer_EFnMod uf B A pd b e n s e' \<tau> pd' n' FK)
    have E: \<open>infer uf B A pd (EFnMod b e) n = Some (s, e', \<tau>, pd', n')\<close>
      and I: \<open>inwf B A pd FK n\<close> by (fact infer_EFnMod.prems)+
    from E obtain T E\<^sub>0 n\<^sub>1 K E\<^sub>K n\<^sub>2 s\<^sub>b e'' \<tau>\<^sub>b pd\<^sub>1 n\<^sub>3 pd'' where
      ss: \<open>sig_stat B n (mbind_sig b) = Some ((T, E\<^sub>0), n\<^sub>1)\<close> and
      de: \<open>dep_env B n (mbind_sig b) (length T) = Some (K, E\<^sub>K, n\<^sub>2)\<close> and
      ib: \<open>infer uf
          ((mbind_nm b, if is_imp b then TEinst (param_env E\<^sub>K) else TEstr (param_env E\<^sub>K)) # B)
          (RV (n\<^sub>2)) pd e (Suc (n\<^sub>2)) = Some (s\<^sub>b, e'', \<tau>\<^sub>b, pd\<^sub>1, n\<^sub>3)\<close> and
      ri: \<open>resolve_inner K pd\<^sub>1 = Some pd''\<close> and
      esc: \<open>list_all (\<lambda>a. set K \<inter> ktv (fst s\<^sub>b a) = {}) [0 ..< Suc (n\<^sub>2)]\<close> and
      escp: \<open>set K \<inter> ktv_rows pd'' = {}\<close> and
      rs: \<open>s = sproj (Suc (n\<^sub>2)) s\<^sub>b\<close>
        \<open>\<tau> = TDep (is_imp b) (mbind_sig b) (length T) (sappr s\<^sub>b (RV n\<^sub>2))
               (kclose K \<tau>\<^sub>b)\<close>
        \<open>pd' = pd''\<close> \<open>n' = n\<^sub>3\<close>
      by (auto simp: Let_def bind_eq_Some_conv split: prod.split_asm if_split_asm)
    let ?P = \<open>if is_imp b then TEinst (param_env E\<^sub>K) else TEstr (param_env E\<^sub>K)\<close>
    let ?B' = \<open>(mbind_nm b, ?P) # B\<close>
    from I have cenvB: \<open>cenv B\<close> and bfB: \<open>bfree_env B\<close> and ktvB: \<open>ktv_env B \<subseteq> FK\<close>
      and ftvB: \<open>ftv_env B \<subseteq> {..< n}\<close> and frvB: \<open>frv_env B \<subseteq> {..< n}\<close>
      and ftp: \<open>ftv_pend pd \<subseteq> {..< n}\<close> and frp: \<open>frv_pend pd \<subseteq> {..< n}\<close> and ktp: \<open>ktv_rows pd \<subseteq> FK\<close>
      by (auto simp: inwf_def)
    note dw = dep_env_wf[OF de cenvB bfB]
    have le1: \<open>n \<le> n\<^sub>2\<close> using dw by simp
    have pf: \<open>ftv_ent ?P = {}\<close> using param_env_ftv[of E\<^sub>K] dw by (auto split: if_split)
    have pr: \<open>frv_ent ?P = {}\<close> using param_env_frv[of E\<^sub>K] dw by (auto split: if_split)
    have pk: \<open>ktv_ent ?P \<subseteq> FK \<union> set K\<close>
      using param_env_ktv[of E\<^sub>K] dw ktvB by (auto split: if_split)
    have pb: \<open>bfree_ent ?P\<close> using bfree_env_param_env dw by (auto split: if_split)
    have iB': \<open>inwf ?B' (RV (n\<^sub>2)) pd (FK \<union> set K) (Suc (n\<^sub>2))\<close>
      unfolding inwf_def
    proof (intro conjI)
      show \<open>cenv ?B'\<close> using pf pr cenvB by (auto simp: cenv_def)
      show \<open>bfree_env ?B'\<close> using pb bfB by simp
      show \<open>ktv_env ?B' \<subseteq> FK \<union> set K\<close> using pk ktvB by auto
      show \<open>ftv_env ?B' \<subseteq> {..< Suc (n\<^sub>2)}\<close> using pf ftvB le1 by auto
      show \<open>frv_env ?B' \<subseteq> {..< Suc (n\<^sub>2)}\<close> using pr frvB le1 by auto
      show \<open>frv_row (RV (n\<^sub>2)) \<subseteq> {..< Suc (n\<^sub>2)}\<close> by auto
      show \<open>brv_row (RV (n\<^sub>2)) = {}\<close> by simp
      show \<open>frv_pend pd \<subseteq> {..< Suc (n\<^sub>2)}\<close> using frp le1 by auto
      show \<open>ktv_rows pd \<subseteq> FK \<union> set K\<close> using ktp by auto
      show \<open>ftv_pend pd \<subseteq> {..< Suc (n\<^sub>2)}\<close> using ftp le1 by auto
    qed
    have wbody: \<open>Suc (n\<^sub>2) \<le> n\<^sub>3 \<and> outwf s\<^sub>b pd\<^sub>1 (FK \<union> set K) n\<^sub>3 \<and>
                fresh_ok \<tau>\<^sub>b 0 n\<^sub>3 (FK \<union> set K)\<close>
      using infer_EFnMod.IH[OF ss refl refl de refl refl ib iB'] .
    have le3: \<open>Suc (n\<^sub>2) \<le> n\<^sub>3\<close> using wbody by simp
    have scb: \<open>sconf s\<^sub>b {..< n\<^sub>3} {..< n\<^sub>3}\<close> and khb: \<open>khyg s\<^sub>b (FK \<union> set K)\<close>
      and bfb: \<open>bfree_sub s\<^sub>b\<close> using wbody by (auto simp: outwf_def)
    have ftb: \<open>fresh_ok \<tau>\<^sub>b 0 n\<^sub>3 (FK \<union> set K)\<close> using wbody by simp
    have nle: \<open>n \<le> n\<^sub>3\<close> using le1 le3 by simp
    have escb: \<open>\<forall>a \<in> set [0 ..< Suc (n\<^sub>2)]. set K \<inter> ktv (fst s\<^sub>b a) = {}\<close>
      using esc by (simp only: list_all_iff)
    have kall: \<open>\<forall>a < Suc (n\<^sub>2). ktv (fst s\<^sub>b a) \<subseteq> FK\<close>
    proof (intro allI impI)
      fix a assume aL: \<open>a < Suc (n\<^sub>2)\<close>
      hence \<open>a \<in> set [0 ..< Suc (n\<^sub>2)]\<close> by (auto simp: less_Suc_eq)
      hence \<open>set K \<inter> ktv (fst s\<^sub>b a) = {}\<close> using escb by blast
      moreover have \<open>ktv (fst s\<^sub>b a) \<subseteq> FK \<union> set K\<close>
        using khb by (simp add: khyg_def)
      ultimately show \<open>ktv (fst s\<^sub>b a) \<subseteq> FK\<close> by auto
    qed
    have opd: \<open>ftv_pend pd'' \<subseteq> {..< n\<^sub>3}\<close> \<open>frv_pend pd'' \<subseteq> {..< n\<^sub>3}\<close>
      \<open>ktv_rows pd'' \<subseteq> FK \<union> set K\<close>
      using resolve_inner_pend[OF ri] scb wbody by (auto simp: outwf_def)
    have opk: \<open>ktv_rows pd'' \<subseteq> FK\<close> using opd(3) escp by auto
    have out': \<open>outwf (sproj (Suc (n\<^sub>2)) s\<^sub>b) pd'' FK n\<^sub>3\<close>
      unfolding outwf_def
      using sconf_sproj[OF scb] khyg_sproj[OF kall] bfree_sub_sproj[OF bfb] opd opk by simp
    have ftt: \<open>ftv \<tau>\<^sub>b \<subseteq> {0 ..< n\<^sub>3}\<close> and frt: \<open>frv \<tau>\<^sub>b \<subseteq> {0 ..< n\<^sub>3}\<close>
      and ktt: \<open>ktv \<tau>\<^sub>b \<subseteq> FK \<union> set K\<close> and btt: \<open>bfree \<tau>\<^sub>b\<close>
      using ftb by (auto simp: fresh_ok_def)
    have frsr: \<open>frv_row (sappr s\<^sub>b (RV (n\<^sub>2))) \<subseteq> {..< n\<^sub>3}\<close>
      by (rule frv_sappr_sconf[OF scb]) (use le3 in auto)
    have brsr: \<open>brv_row (sappr s\<^sub>b (RV (n\<^sub>2))) = {}\<close> by (rule bfree_sappr[OF bfb]) simp
    have fresh': \<open>fresh_ok (TDep (is_imp b) (mbind_sig b) (length T)
                    (sappr s\<^sub>b (RV (n\<^sub>2))) (kclose K \<tau>\<^sub>b)) 0 n\<^sub>3 FK\<close>
      using ftt frt ktt btt frsr brsr by (auto simp: fresh_ok_def bfree_def)
    show ?case using nle out' fresh' rs by simp
  next
    case (infer_ELet uf B A pd p e b n s e\<^sub>x \<tau> pd' n' FK)
    from infer_ELet.prems show ?case
      by (rule infer_let_wf) (rule infer_ELet.IH; (assumption | rule gen_env_def refl)+)+
  next
    case (infer_ELetFun uf B A pd f mbs cls b n s e' \<tau> pd' n' FK)
    have G: \<open>\<not> (cls = [] \<or> \<not> is_fn (foldr EFnMod mbs (dfun_rhs cls)) \<or> \<not> nm_ok (n_txt f))\<close>
      using infer_ELetFun.prems(1) by (auto simp: Let_def split: if_split_asm)
    from infer_ELetFun.prems show ?case
    proof (rule infer_letfun_wf)
      fix s\<^sub>1 r' \<tau>' pd\<^sub>1 n\<^sub>1 FK'
      assume \<open>infer uf ((n_txt f, TEval (kmono (TV n))) # B) A pd (foldr EFnMod mbs (dfun_rhs cls)) (Suc n)
          = Some (s\<^sub>1, r', \<tau>', pd\<^sub>1, n\<^sub>1)\<close>
        \<open>inwf ((n_txt f, TEval (kmono (TV n))) # B) A pd FK' (Suc n)\<close>
      then show \<open>Suc n \<le> n\<^sub>1 \<and> outwf s\<^sub>1 pd\<^sub>1 FK' n\<^sub>1 \<and> fresh_ok \<tau>' 0 n\<^sub>1 FK'\<close>
        by (rule infer_ELetFun.IH(1)[OF refl G])
    next
      fix s\<^sub>1 r' \<tau>' pd\<^sub>1 n\<^sub>1 s\<^sub>2 n\<^sub>2 as rs reqs pdr s\<^sub>3 b' \<tau>\<^sub>b pd\<^sub>3 n\<^sub>3 FK'
      assume h: \<open>infer uf ((n_txt f, TEval (kmono (TV n))) # B) A pd (foldr EFnMod mbs (dfun_rhs cls)) (Suc n)
          = Some (s\<^sub>1, r', \<tau>', pd\<^sub>1, n\<^sub>1)\<close>
        \<open>uni uf (sapp s\<^sub>1 (TV n)) \<tau>' n\<^sub>1 = Some (s\<^sub>2, n\<^sub>2)\<close>
        \<open>(as, rs, reqs, pdr) = gen_off (sappe (s\<^sub>2 \<odot> s\<^sub>1) B) (sappr (s\<^sub>2 \<odot> s\<^sub>1) A) (sub_pend s\<^sub>2 pd\<^sub>1) n
          (sapp s\<^sub>2 \<tau>')\<close>
        \<open>btv_list (sapp s\<^sub>2 \<tau>') = [] \<and> brv_list (sapp s\<^sub>2 \<tau>') = []\<close>
        \<open>infer uf ((n_txt f, TEval (close_sch as rs (offs reqs (sapp s\<^sub>2 \<tau>')))) # sappe (s\<^sub>2 \<odot> s\<^sub>1) B)
          (sappr (s\<^sub>2 \<odot> s\<^sub>1) A) pdr b n\<^sub>2 = Some (s\<^sub>3, b', \<tau>\<^sub>b, pd\<^sub>3, n\<^sub>3)\<close>
        \<open>inwf ((n_txt f, TEval (close_sch as rs (offs reqs (sapp s\<^sub>2 \<tau>')))) # sappe (s\<^sub>2 \<odot> s\<^sub>1) B)
          (sappr (s\<^sub>2 \<odot> s\<^sub>1) A) pdr FK' n\<^sub>2\<close>
      show \<open>n\<^sub>2 \<le> n\<^sub>3 \<and> outwf s\<^sub>3 pd\<^sub>3 FK' n\<^sub>3 \<and> fresh_ok \<tau>\<^sub>b 0 n\<^sub>3 FK'\<close>
        by (rule infer_ELetFun.IH(2)[OF refl G]; (rule h | rule refl)+)
    qed
  next
    case (infer_EGuards_Cons uf B A pd gs e alts n s ex \<tau> pd' n' FK)
    note IH = infer_EGuards_Cons.IH
    have E: \<open>infer uf B A pd (EGuards ((gs, e) # alts)) n = Some (s, ex, \<tau>, pd', n')\<close>
      and I: \<open>inwf B A pd FK n\<close> by (fact infer_EGuards_Cons.prems)+
    obtain s\<^sub>1 gs' \<tau>s pd\<^sub>1 n\<^sub>1 where d1: \<open>infer_exps uf B A pd gs n = Some (s\<^sub>1, gs', \<tau>s, pd\<^sub>1, n\<^sub>1)\<close>
      using E by (auto simp: bind_eq_Some_conv)
    obtain s\<^sub>2 n\<^sub>2 where u1: \<open>unis uf (map (\<lambda>\<tau>. (\<tau>, TC bool_ty [])) \<tau>s) n\<^sub>1 = Some (s\<^sub>2, n\<^sub>2)\<close>
      using E d1 by (auto simp: bind_eq_Some_conv)
    obtain s\<^sub>3 e'' \<tau>\<^sub>e pd\<^sub>3 n\<^sub>3 where d2: \<open>infer uf (sappe (s\<^sub>2 \<odot> s\<^sub>1) B) (sappr (s\<^sub>2 \<odot> s\<^sub>1) A)
        (sub_pend s\<^sub>2 pd\<^sub>1) e n\<^sub>2 = Some (s\<^sub>3, e'', \<tau>\<^sub>e, pd\<^sub>3, n\<^sub>3)\<close>
      using E d1 u1 by (auto simp: Let_def bind_eq_Some_conv)
    from d1 I have \<open>n \<le> n\<^sub>1 \<and> outwf s\<^sub>1 pd\<^sub>1 FK n\<^sub>1 \<and> (\<forall>\<tau> \<in> set \<tau>s. fresh_ok \<tau> 0 n\<^sub>1 FK)\<close>
      by (rule IH(1))
    then have le1: \<open>n \<le> n\<^sub>1\<close> and o1: \<open>outwf s\<^sub>1 pd\<^sub>1 FK n\<^sub>1\<close>
      and \<tau>sf: \<open>\<forall>\<tau> \<in> set \<tau>s. fresh_ok \<tau> 0 n\<^sub>1 FK\<close> by simp_all
    from o1 have ftp1: \<open>ftv_pend pd\<^sub>1 \<subseteq> {..< n\<^sub>1}\<close> and frp1: \<open>frv_pend pd\<^sub>1 \<subseteq> {..< n\<^sub>1}\<close> and ktp1: \<open>ktv_rows pd\<^sub>1 \<subseteq> FK\<close>
      by (auto simp: outwf_def)
    have cb: \<open>ftv_cs (map (\<lambda>\<tau>. (\<tau>, TC bool_ty [])) \<tau>s) \<subseteq> {0 ..< n\<^sub>1}\<close>
      \<open>frv_cs (map (\<lambda>\<tau>. (\<tau>, TC bool_ty [])) \<tau>s) \<subseteq> {0 ..< n\<^sub>1}\<close>
      \<open>ktv_cs (map (\<lambda>\<tau>. (\<tau>, TC bool_ty [])) \<tau>s) \<subseteq> FK\<close>
      \<open>bfree_cs (map (\<lambda>\<tau>. (\<tau>, TC bool_ty [])) \<tau>s)\<close>
      using \<tau>sf by (auto simp: ftv_cs_def frv_cs_def ktv_cs_def bfree_cs_def fresh_ok_def bfree_def)
    note uf1 = unis_fresh[OF u1 cb le0]
    have le2: \<open>n\<^sub>1 \<le> n\<^sub>2\<close> using uf1 by simp
    have sc2: \<open>sconf s\<^sub>2 {..< n\<^sub>2} {..< n\<^sub>2}\<close> using uf1 by (simp add: atLeast0LessThan)
    have kh2: \<open>khyg s\<^sub>2 FK\<close> and bf2: \<open>bfree_sub s\<^sub>2\<close> using uf1 by simp_all
    have o2': \<open>outwf s\<^sub>2 (sub_pend s\<^sub>2 pd\<^sub>1) FK n\<^sub>2\<close>
      by (rule outwf_of_uni[OF sc2 kh2 bf2 ftp1 frp1 le2 ktp1])
    have os: \<open>outwf (s\<^sub>2 \<odot> s\<^sub>1) (sub_pend s\<^sub>2 pd\<^sub>1) FK n\<^sub>2\<close> by (rule outwf_scomp[OF o1 o2' le2])
    have i3: \<open>inwf (sappe (s\<^sub>2 \<odot> s\<^sub>1) B) (sappr (s\<^sub>2 \<odot> s\<^sub>1) A) (sub_pend s\<^sub>2 pd\<^sub>1) FK n\<^sub>2\<close>
      by (rule inwf_step[OF I os le_trans[OF le1 le2]])
    have r2: \<open>n\<^sub>2 \<le> n\<^sub>3 \<and> outwf s\<^sub>3 pd\<^sub>3 FK n\<^sub>3 \<and> fresh_ok \<tau>\<^sub>e 0 n\<^sub>3 FK\<close>
      using d1 refl refl refl refl u1 refl refl d2 i3 by (rule IH(2))
    then have le3: \<open>n\<^sub>2 \<le> n\<^sub>3\<close> and o3: \<open>outwf s\<^sub>3 pd\<^sub>3 FK n\<^sub>3\<close>
      and fte: \<open>fresh_ok \<tau>\<^sub>e 0 n\<^sub>3 FK\<close> by simp_all
    have ost: \<open>outwf (s\<^sub>3 \<odot> (s\<^sub>2 \<odot> s\<^sub>1)) pd\<^sub>3 FK n\<^sub>3\<close> by (rule outwf_scomp[OF os o3 le3])
    have le13: \<open>n \<le> n\<^sub>3\<close> using le1 le2 le3 by simp
    show ?case
    proof (cases \<open>alts = []\<close>)
      case True
      then show ?thesis
        using E d1 u1 d2 le13 ost fte by (auto simp: Let_def bind_eq_Some_conv)
    next
      case False
      obtain s\<^sub>4 g' \<tau>\<^sub>g pd\<^sub>4 n\<^sub>4 where d3: \<open>infer uf (sappe (s\<^sub>3 \<odot> (s\<^sub>2 \<odot> s\<^sub>1)) B)
          (sappr (s\<^sub>3 \<odot> (s\<^sub>2 \<odot> s\<^sub>1)) A) pd\<^sub>3 (EGuards alts) n\<^sub>3 = Some (s\<^sub>4, g', \<tau>\<^sub>g, pd\<^sub>4, n\<^sub>4)\<close>
        using E d1 u1 d2 False by (auto simp: Let_def bind_eq_Some_conv)
      obtain s\<^sub>5 where u2: \<open>uni uf \<tau>\<^sub>g (sapp s\<^sub>4 \<tau>\<^sub>e) n\<^sub>4 = Some (s\<^sub>5, n')\<close>
        and se: \<open>s = s\<^sub>5 \<odot> s\<^sub>4 \<odot> (s\<^sub>3 \<odot> (s\<^sub>2 \<odot> s\<^sub>1))\<close> and te: \<open>\<tau> = sapp s\<^sub>5 \<tau>\<^sub>g\<close>
        and pe: \<open>pd' = sub_pend s\<^sub>5 pd\<^sub>4\<close>
        using E d1 u1 d2 d3 False by (auto simp: Let_def bind_eq_Some_conv)
      have i4: \<open>inwf (sappe (s\<^sub>3 \<odot> (s\<^sub>2 \<odot> s\<^sub>1)) B) (sappr (s\<^sub>3 \<odot> (s\<^sub>2 \<odot> s\<^sub>1)) A) pd\<^sub>3 FK n\<^sub>3\<close>
        by (rule inwf_step[OF I ost le13])
      have r3: \<open>n\<^sub>3 \<le> n\<^sub>4 \<and> outwf s\<^sub>4 pd\<^sub>4 FK n\<^sub>4 \<and> fresh_ok \<tau>\<^sub>g 0 n\<^sub>4 FK\<close>
        using d1 refl refl refl refl u1 refl refl d2 refl refl refl refl False refl d3 i4
        by (rule IH(3))
      then have le4: \<open>n\<^sub>3 \<le> n\<^sub>4\<close> and o4: \<open>outwf s\<^sub>4 pd\<^sub>4 FK n\<^sub>4\<close>
        and fg: \<open>fresh_ok \<tau>\<^sub>g 0 n\<^sub>4 FK\<close> by simp_all
      have fst4: \<open>fresh_ok (sapp s\<^sub>4 \<tau>\<^sub>e) 0 n\<^sub>4 FK\<close> by (rule fresh_ok_sapp0[OF fte o4 le4])
      note uf2 = uni_fresh[OF u2 fg fst4 le0]
      have le5: \<open>n\<^sub>4 \<le> n'\<close> using uf2 by simp
      have sc5: \<open>sconf s\<^sub>5 {..< n'} {..< n'}\<close> using uf2 by (simp add: atLeast0LessThan)
      from o4 have ftp4: \<open>ftv_pend pd\<^sub>4 \<subseteq> {..< n\<^sub>4}\<close> and frp4: \<open>frv_pend pd\<^sub>4 \<subseteq> {..< n\<^sub>4}\<close> and ktp4: \<open>ktv_rows pd\<^sub>4 \<subseteq> FK\<close>
        by (auto simp: outwf_def)
      have o5': \<open>outwf s\<^sub>5 (sub_pend s\<^sub>5 pd\<^sub>4) FK n'\<close>
        using uf2 by (intro outwf_of_uni[OF sc5 _ _ ftp4 frp4 le5 ktp4]) simp_all
      have ost2: \<open>outwf (s\<^sub>4 \<odot> (s\<^sub>3 \<odot> (s\<^sub>2 \<odot> s\<^sub>1))) pd\<^sub>4 FK n\<^sub>4\<close>
        by (rule outwf_scomp[OF ost o4 le4])
      have ofin: \<open>outwf (s\<^sub>5 \<odot> (s\<^sub>4 \<odot> (s\<^sub>3 \<odot> (s\<^sub>2 \<odot> s\<^sub>1)))) (sub_pend s\<^sub>5 pd\<^sub>4) FK n'\<close>
        by (rule outwf_scomp[OF ost2 o5' le5])
      have le: \<open>n \<le> n'\<close> using le13 le4 le5 by simp
      have fresh: \<open>fresh_ok \<tau> 0 n' FK\<close>
        unfolding te by (rule fresh_ok_sapp0[OF fg o5' le5])
      have ofin': \<open>outwf s (sub_pend s\<^sub>5 pd\<^sub>4) FK n'\<close>
        using ofin unfolding se by (simp only: scomp_assoc)
      show ?thesis using pe le fresh ofin' by simp
    qed
  next
    case (infer_ESeq uf B A pd e\<^sub>1 e\<^sub>2 n s e' \<tau> pd' n' FK)
    have E: \<open>infer uf B A pd (ESeq e\<^sub>1 e\<^sub>2) n = Some (s, e', \<tau>, pd', n')\<close>
      and I: \<open>inwf B A pd FK n\<close> by (fact infer_ESeq.prems)+
    from E obtain s\<^sub>1 e\<^sub>1' \<tau>\<^sub>1 pd\<^sub>1 n\<^sub>1 s\<^sub>2 e\<^sub>2' pd\<^sub>2 where
      d1: \<open>infer uf B A pd e\<^sub>1 n = Some (s\<^sub>1, e\<^sub>1', \<tau>\<^sub>1, pd\<^sub>1, n\<^sub>1)\<close> and
      d2: \<open>infer uf (sappe s\<^sub>1 B) (sappr s\<^sub>1 A) pd\<^sub>1 e\<^sub>2 n\<^sub>1 = Some (s\<^sub>2, e\<^sub>2', \<tau>, pd\<^sub>2, n')\<close> and
      se: \<open>s = s\<^sub>2 \<odot> s\<^sub>1\<close> \<open>pd' = pd\<^sub>2\<close>
      by (auto split: Option.bind_split_asm prod.split_asm)
    from d1 I have \<open>n \<le> n\<^sub>1 \<and> outwf s\<^sub>1 pd\<^sub>1 FK n\<^sub>1 \<and> fresh_ok \<tau>\<^sub>1 0 n\<^sub>1 FK\<close>
      by (rule infer_ESeq.IH)
    then have le1: \<open>n \<le> n\<^sub>1\<close> and o1: \<open>outwf s\<^sub>1 pd\<^sub>1 FK n\<^sub>1\<close> by simp_all
    from d1 refl refl refl refl d2 inwf_step[OF I o1 le1]
    have \<open>n\<^sub>1 \<le> n' \<and> outwf s\<^sub>2 pd\<^sub>2 FK n' \<and> fresh_ok \<tau> 0 n' FK\<close>
      by (rule infer_ESeq.IH)
    then have le2: \<open>n\<^sub>1 \<le> n'\<close> and o2: \<open>outwf s\<^sub>2 pd\<^sub>2 FK n'\<close>
      and f2: \<open>fresh_ok \<tau> 0 n' FK\<close> by simp_all
    show ?case using se le1 le2 f2 outwf_scomp[OF o1 o2 le2] by simp
  next
    case (infer_EIf_Some uf B A pd c t e n s ex \<tau> pd' n' FK)
    have E: \<open>infer uf B A pd (EIf c t (Some e)) n = Some (s, ex, \<tau>, pd', n')\<close>
      and I: \<open>inwf B A pd FK n\<close> by (fact infer_EIf_Some.prems)+
    from E obtain s\<^sub>1 c'' \<tau>c pd\<^sub>1 n\<^sub>1 s\<^sub>2 n\<^sub>2 s\<^sub>3 t'' \<tau>t pd\<^sub>3 n\<^sub>3 s\<^sub>4 e'' \<tau>e pd\<^sub>4 n\<^sub>4 s\<^sub>5 where
      d1: \<open>infer uf B A pd c n = Some (s\<^sub>1, c'', \<tau>c, pd\<^sub>1, n\<^sub>1)\<close> and
      u1: \<open>uni uf \<tau>c (TC bool_ty []) n\<^sub>1 = Some (s\<^sub>2, n\<^sub>2)\<close> and
      d3: \<open>infer uf (sappe (s\<^sub>2 \<odot> s\<^sub>1) B) (sappr (s\<^sub>2 \<odot> s\<^sub>1) A) (sub_pend s\<^sub>2 pd\<^sub>1) t n\<^sub>2
             = Some (s\<^sub>3, t'', \<tau>t, pd\<^sub>3, n\<^sub>3)\<close> and
      d4: \<open>infer uf (sappe (s\<^sub>3 \<odot> (s\<^sub>2 \<odot> s\<^sub>1)) B) (sappr (s\<^sub>3 \<odot> (s\<^sub>2 \<odot> s\<^sub>1)) A) pd\<^sub>3 e n\<^sub>3
             = Some (s\<^sub>4, e'', \<tau>e, pd\<^sub>4, n\<^sub>4)\<close> and
      u2: \<open>uni uf \<tau>e (sapp s\<^sub>4 \<tau>t) n\<^sub>4 = Some (s\<^sub>5, n')\<close> and
      se: \<open>s = s\<^sub>5 \<odot> s\<^sub>4 \<odot> (s\<^sub>3 \<odot> (s\<^sub>2 \<odot> s\<^sub>1))\<close>
      and te: \<open>\<tau> = sapp s\<^sub>5 (sapp s\<^sub>4 \<tau>t)\<close> and pe: \<open>pd' = sub_pend s\<^sub>5 pd\<^sub>4\<close>
      by (auto simp: Let_def bind_eq_Some_conv)
    from d1 I have \<open>n \<le> n\<^sub>1 \<and> outwf s\<^sub>1 pd\<^sub>1 FK n\<^sub>1 \<and> fresh_ok \<tau>c 0 n\<^sub>1 FK\<close>
      by (rule infer_EIf_Some.IH)
    then have le1: \<open>n \<le> n\<^sub>1\<close> and o1: \<open>outwf s\<^sub>1 pd\<^sub>1 FK n\<^sub>1\<close>
      and f1: \<open>fresh_ok \<tau>c 0 n\<^sub>1 FK\<close> by simp_all
    from o1 have ftp1: \<open>ftv_pend pd\<^sub>1 \<subseteq> {..< n\<^sub>1}\<close> and frp1: \<open>frv_pend pd\<^sub>1 \<subseteq> {..< n\<^sub>1}\<close> and ktp1: \<open>ktv_rows pd\<^sub>1 \<subseteq> FK\<close>
      by (auto simp: outwf_def)
    note uf1 = uni_fresh[OF u1 fresh_ok_mono[OF f1 le_refl le_refl] fresh_ok_TC_nil le0]
    have le2: \<open>n\<^sub>1 \<le> n\<^sub>2\<close> using uf1 by simp
    have sc2: \<open>sconf s\<^sub>2 {..< n\<^sub>2} {..< n\<^sub>2}\<close> using uf1 by (simp add: atLeast0LessThan)
    have o2': \<open>outwf s\<^sub>2 (sub_pend s\<^sub>2 pd\<^sub>1) FK n\<^sub>2\<close>
      using uf1 by (intro outwf_of_uni[OF sc2 _ _ ftp1 frp1 le2 ktp1]) simp_all
    have os: \<open>outwf (s\<^sub>2 \<odot> s\<^sub>1) (sub_pend s\<^sub>2 pd\<^sub>1) FK n\<^sub>2\<close> by (rule outwf_scomp[OF o1 o2' le2])
    have i3: \<open>inwf (sappe (s\<^sub>2 \<odot> s\<^sub>1) B) (sappr (s\<^sub>2 \<odot> s\<^sub>1) A) (sub_pend s\<^sub>2 pd\<^sub>1) FK n\<^sub>2\<close>
      by (rule inwf_step[OF I os le_trans[OF le1 le2]])
    from d1 refl refl refl refl u1 refl refl d3 i3
    have \<open>n\<^sub>2 \<le> n\<^sub>3 \<and> outwf s\<^sub>3 pd\<^sub>3 FK n\<^sub>3 \<and> fresh_ok \<tau>t 0 n\<^sub>3 FK\<close>
      by (rule infer_EIf_Some.IH)
    then have le3: \<open>n\<^sub>2 \<le> n\<^sub>3\<close> and o3: \<open>outwf s\<^sub>3 pd\<^sub>3 FK n\<^sub>3\<close>
      and ftt: \<open>fresh_ok \<tau>t 0 n\<^sub>3 FK\<close> by simp_all
    have ost: \<open>outwf (s\<^sub>3 \<odot> (s\<^sub>2 \<odot> s\<^sub>1)) pd\<^sub>3 FK n\<^sub>3\<close> by (rule outwf_scomp[OF os o3 le3])
    have i4: \<open>inwf (sappe (s\<^sub>3 \<odot> (s\<^sub>2 \<odot> s\<^sub>1)) B) (sappr (s\<^sub>3 \<odot> (s\<^sub>2 \<odot> s\<^sub>1)) A) pd\<^sub>3 FK n\<^sub>3\<close>
      by (rule inwf_step[OF I ost le_trans[OF le_trans[OF le1 le2] le3]])
    from d1 refl refl refl refl u1 refl refl d3 refl refl refl refl refl d4 i4
    have \<open>n\<^sub>3 \<le> n\<^sub>4 \<and> outwf s\<^sub>4 pd\<^sub>4 FK n\<^sub>4 \<and> fresh_ok \<tau>e 0 n\<^sub>4 FK\<close>
      by (rule infer_EIf_Some.IH)
    then have le4: \<open>n\<^sub>3 \<le> n\<^sub>4\<close> and o4: \<open>outwf s\<^sub>4 pd\<^sub>4 FK n\<^sub>4\<close>
      and fte: \<open>fresh_ok \<tau>e 0 n\<^sub>4 FK\<close> by simp_all
    have fst4: \<open>fresh_ok (sapp s\<^sub>4 \<tau>t) 0 n\<^sub>4 FK\<close> by (rule fresh_ok_sapp0[OF ftt o4 le4])
    note uf2 = uni_fresh[OF u2 fresh_ok_mono[OF fte le_refl le_refl] fst4 le0]
    have le5: \<open>n\<^sub>4 \<le> n'\<close> using uf2 by simp
    have sc5: \<open>sconf s\<^sub>5 {..< n'} {..< n'}\<close> using uf2 by (simp add: atLeast0LessThan)
    from o4 have ftp4: \<open>ftv_pend pd\<^sub>4 \<subseteq> {..< n\<^sub>4}\<close> and frp4: \<open>frv_pend pd\<^sub>4 \<subseteq> {..< n\<^sub>4}\<close> and ktp4: \<open>ktv_rows pd\<^sub>4 \<subseteq> FK\<close>
      by (auto simp: outwf_def)
    have o5': \<open>outwf s\<^sub>5 (sub_pend s\<^sub>5 pd\<^sub>4) FK n'\<close>
      using uf2 by (intro outwf_of_uni[OF sc5 _ _ ftp4 frp4 le5 ktp4]) simp_all
    have ost2: \<open>outwf (s\<^sub>4 \<odot> (s\<^sub>3 \<odot> (s\<^sub>2 \<odot> s\<^sub>1))) pd\<^sub>4 FK n\<^sub>4\<close>
      by (rule outwf_scomp[OF ost o4 le4])
    have ofin: \<open>outwf (s\<^sub>5 \<odot> (s\<^sub>4 \<odot> (s\<^sub>3 \<odot> (s\<^sub>2 \<odot> s\<^sub>1)))) (sub_pend s\<^sub>5 pd\<^sub>4) FK n'\<close>
      by (rule outwf_scomp[OF ost2 o5' le5])
    have le: \<open>n \<le> n'\<close> using le1 le2 le3 le4 le5 by simp
    have fresh: \<open>fresh_ok \<tau> 0 n' FK\<close>
      unfolding te by (rule fresh_ok_sapp0[OF fst4 o5' le5])
    have ofin': \<open>outwf s (sub_pend s\<^sub>5 pd\<^sub>4) FK n'\<close>
      using ofin unfolding se by (simp only: scomp_assoc)
    show ?case using pe le fresh ofin' by simp
  next
    case (infer_EIf_None uf B A pd c t n s e' \<tau> pd' n' FK)
    have E: \<open>infer uf B A pd (EIf c t None) n = Some (s, e', \<tau>, pd', n')\<close>
      and I: \<open>inwf B A pd FK n\<close> by (fact infer_EIf_None.prems)+
    from E obtain s\<^sub>1 c'' \<tau>c pd\<^sub>1 n\<^sub>1 s\<^sub>2 n\<^sub>2 s\<^sub>3 t'' \<tau>t pd\<^sub>3 n\<^sub>3 s\<^sub>4 where
      d1: \<open>infer uf B A pd c n = Some (s\<^sub>1, c'', \<tau>c, pd\<^sub>1, n\<^sub>1)\<close> and
      u1: \<open>uni uf \<tau>c (TC bool_ty []) n\<^sub>1 = Some (s\<^sub>2, n\<^sub>2)\<close> and
      d3: \<open>infer uf (sappe (s\<^sub>2 \<odot> s\<^sub>1) B) (sappr (s\<^sub>2 \<odot> s\<^sub>1) A) (sub_pend s\<^sub>2 pd\<^sub>1) t n\<^sub>2
             = Some (s\<^sub>3, t'', \<tau>t, pd\<^sub>3, n\<^sub>3)\<close> and
      u2: \<open>uni uf \<tau>t unit_ty n\<^sub>3 = Some (s\<^sub>4, n')\<close> and
      se: \<open>s = s\<^sub>4 \<odot> s\<^sub>3 \<odot> (s\<^sub>2 \<odot> s\<^sub>1)\<close> \<open>\<tau> = unit_ty\<close> \<open>pd' = sub_pend s\<^sub>4 pd\<^sub>3\<close>
      by (auto simp: Let_def bind_eq_Some_conv)
    from d1 I have \<open>n \<le> n\<^sub>1 \<and> outwf s\<^sub>1 pd\<^sub>1 FK n\<^sub>1 \<and> fresh_ok \<tau>c 0 n\<^sub>1 FK\<close>
      by (rule infer_EIf_None.IH)
    then have le1: \<open>n \<le> n\<^sub>1\<close> and o1: \<open>outwf s\<^sub>1 pd\<^sub>1 FK n\<^sub>1\<close>
      and f1: \<open>fresh_ok \<tau>c 0 n\<^sub>1 FK\<close> by simp_all
    from o1 have ftp1: \<open>ftv_pend pd\<^sub>1 \<subseteq> {..< n\<^sub>1}\<close> and frp1: \<open>frv_pend pd\<^sub>1 \<subseteq> {..< n\<^sub>1}\<close> and ktp1: \<open>ktv_rows pd\<^sub>1 \<subseteq> FK\<close>
      by (auto simp: outwf_def)
    note uf1 = uni_fresh[OF u1 fresh_ok_mono[OF f1 le_refl le_refl] fresh_ok_TC_nil le0]
    have le2: \<open>n\<^sub>1 \<le> n\<^sub>2\<close> using uf1 by simp
    have sc2: \<open>sconf s\<^sub>2 {..< n\<^sub>2} {..< n\<^sub>2}\<close> using uf1 by (simp add: atLeast0LessThan)
    have kh2: \<open>khyg s\<^sub>2 FK\<close> and bf2: \<open>bfree_sub s\<^sub>2\<close> using uf1 by simp_all
    have o2': \<open>outwf s\<^sub>2 (sub_pend s\<^sub>2 pd\<^sub>1) FK n\<^sub>2\<close>
      by (rule outwf_of_uni[OF sc2 kh2 bf2 ftp1 frp1 le2 ktp1])
    have os: \<open>outwf (s\<^sub>2 \<odot> s\<^sub>1) (sub_pend s\<^sub>2 pd\<^sub>1) FK n\<^sub>2\<close>
      by (rule outwf_scomp[OF o1 o2' le2])
    have i3: \<open>inwf (sappe (s\<^sub>2 \<odot> s\<^sub>1) B) (sappr (s\<^sub>2 \<odot> s\<^sub>1) A) (sub_pend s\<^sub>2 pd\<^sub>1) FK n\<^sub>2\<close>
      by (rule inwf_step[OF I os le_trans[OF le1 le2]])
    from d1 refl refl refl refl u1 refl refl d3 i3
    have \<open>n\<^sub>2 \<le> n\<^sub>3 \<and> outwf s\<^sub>3 pd\<^sub>3 FK n\<^sub>3 \<and> fresh_ok \<tau>t 0 n\<^sub>3 FK\<close>
      by (rule infer_EIf_None.IH)
    then have le3: \<open>n\<^sub>2 \<le> n\<^sub>3\<close> and o3: \<open>outwf s\<^sub>3 pd\<^sub>3 FK n\<^sub>3\<close>
      and f3: \<open>fresh_ok \<tau>t 0 n\<^sub>3 FK\<close> by simp_all
    from o3 have ftp3: \<open>ftv_pend pd\<^sub>3 \<subseteq> {..< n\<^sub>3}\<close> and frp3: \<open>frv_pend pd\<^sub>3 \<subseteq> {..< n\<^sub>3}\<close> and ktp3: \<open>ktv_rows pd\<^sub>3 \<subseteq> FK\<close>
      by (auto simp: outwf_def)
    note uf2 = uni_fresh[OF u2 fresh_ok_mono[OF f3 le_refl le_refl] fresh_ok_unit le0]
    have le4: \<open>n\<^sub>3 \<le> n'\<close> using uf2 by simp
    have sc4: \<open>sconf s\<^sub>4 {..< n'} {..< n'}\<close> using uf2 by (simp add: atLeast0LessThan)
    have kh4: \<open>khyg s\<^sub>4 FK\<close> and bf4: \<open>bfree_sub s\<^sub>4\<close> using uf2 by simp_all
    have o4': \<open>outwf s\<^sub>4 (sub_pend s\<^sub>4 pd\<^sub>3) FK n'\<close>
      by (rule outwf_of_uni[OF sc4 kh4 bf4 ftp3 frp3 le4 ktp3])
    have ost: \<open>outwf (s\<^sub>3 \<odot> (s\<^sub>2 \<odot> s\<^sub>1)) pd\<^sub>3 FK n\<^sub>3\<close>
      by (rule outwf_scomp[OF os o3 le3])
    have ofin: \<open>outwf (s\<^sub>4 \<odot> (s\<^sub>3 \<odot> (s\<^sub>2 \<odot> s\<^sub>1))) (sub_pend s\<^sub>4 pd\<^sub>3) FK n'\<close>
      by (rule outwf_scomp[OF ost o4' le4])
    have le: \<open>n \<le> n'\<close> using le1 le2 le3 le4 by simp
    show ?case using se le ofin by (simp add: scomp_assoc)
  next
    case (infer_EMatch uf B A pd e arms n s e' \<tau> pd' n' FK)
    have E: \<open>infer uf B A pd (EMatch e arms) n = Some (s, e', \<tau>, pd', n')\<close>
      and I: \<open>inwf B A pd FK n\<close> by (fact infer_EMatch.prems)+
    from E obtain s\<^sub>1 e'' \<tau>\<^sub>0 pd\<^sub>1 n\<^sub>1 s\<^sub>2 arms'' where
      d1: \<open>infer uf B A pd e n = Some (s\<^sub>1, e'', \<tau>\<^sub>0, pd\<^sub>1, n\<^sub>1)\<close> and
      d2: \<open>infer_arms uf (sappe s\<^sub>1 B) (sappr s\<^sub>1 A) pd\<^sub>1 \<tau>\<^sub>0 (TV n\<^sub>1) arms (Suc n\<^sub>1)
             = Some (s\<^sub>2, arms'', pd', n')\<close> and
      se: \<open>s = s\<^sub>2 \<odot> s\<^sub>1\<close> \<open>\<tau> = sapp s\<^sub>2 (TV n\<^sub>1)\<close>
      by (auto split: Option.bind_split_asm prod.split_asm if_split_asm)
    from d1 I have \<open>n \<le> n\<^sub>1 \<and> outwf s\<^sub>1 pd\<^sub>1 FK n\<^sub>1 \<and> fresh_ok \<tau>\<^sub>0 0 n\<^sub>1 FK\<close>
      by (rule infer_EMatch.IH)
    then have le1: \<open>n \<le> n\<^sub>1\<close> and o1: \<open>outwf s\<^sub>1 pd\<^sub>1 FK n\<^sub>1\<close>
      and f1: \<open>fresh_ok \<tau>\<^sub>0 0 n\<^sub>1 FK\<close> by simp_all
    have i2: \<open>inwf (sappe s\<^sub>1 B) (sappr s\<^sub>1 A) pd\<^sub>1 FK (Suc n\<^sub>1)\<close>
      by (rule inwf_bump[OF inwf_step[OF I o1 le1] le_SucI[OF le_refl]])
    have f0: \<open>fresh_ok \<tau>\<^sub>0 0 (Suc n\<^sub>1) FK\<close> using fresh_ok_mono[OF f1 le_refl] by simp
    have fr: \<open>fresh_ok (TV n\<^sub>1) 0 (Suc n\<^sub>1) FK\<close> by (simp add: fresh_ok_def bfree_def)
    from d1 refl refl refl refl d2 i2 f0 fr
    have \<open>Suc n\<^sub>1 \<le> n' \<and> outwf s\<^sub>2 pd' FK n' \<and> fresh_ok (sapp s\<^sub>2 (TV n\<^sub>1)) 0 n' FK\<close>
      by (rule infer_EMatch.IH)
    then have le2: \<open>n\<^sub>1 \<le> n'\<close> and o2: \<open>outwf s\<^sub>2 pd' FK n'\<close>
      and f2: \<open>fresh_ok (sapp s\<^sub>2 (TV n\<^sub>1)) 0 n' FK\<close> by simp_all
    show ?case using se le1 le2 f2 outwf_scomp[OF o1 o2 le2] by simp
  next
    case (infer_EHandle uf B A pd e cls n s e' \<tau> pd' n' FK)
    have E: \<open>infer uf B A pd (EHandle e cls) n = Some (s, e', \<tau>, pd', n')\<close>
      and I: \<open>inwf B A pd FK n\<close> by (fact infer_EHandle.prems)+
    from E obtain s\<^sub>1 e'' \<tau>\<^sub>0 pd\<^sub>1 n\<^sub>1 s\<^sub>2 cls'' where
      pe: \<open>list_all (plain_eff B) (hlabels B cls)\<close> and
      d1: \<open>infer uf B (canon_row (rext (hlabels B cls) A)) pd e n
        = Some (s\<^sub>1, e'', \<tau>\<^sub>0, pd\<^sub>1, n\<^sub>1)\<close> and
      d2: \<open>infer_cls uf (sappe s\<^sub>1 B) (sappr s\<^sub>1 A) pd\<^sub>1 False \<tau>\<^sub>0 (tuple []) cls n\<^sub>1
        = Some (s\<^sub>2, cls'', \<tau>, pd', n')\<close> and
      se: \<open>s = s\<^sub>2 \<odot> s\<^sub>1\<close>
      by (auto split: Option.bind_split_asm prod.split_asm if_split_asm)
    have frA: \<open>frv_row A \<subseteq> {..< n}\<close> and brA: \<open>brv_row A = {}\<close>
      using I by (auto simp: inwf_def)
    have amb: \<open>inwf B (canon_row (rext (hlabels B cls) A)) pd FK n\<close>
      by (rule inwf_amb[OF I]) (simp_all add: rext_def frA brA)
    from pe d1 amb have \<open>n \<le> n\<^sub>1 \<and> outwf s\<^sub>1 pd\<^sub>1 FK n\<^sub>1 \<and> fresh_ok \<tau>\<^sub>0 0 n\<^sub>1 FK\<close>
      by (rule infer_EHandle.IH)
    then have le1: \<open>n \<le> n\<^sub>1\<close> and o1: \<open>outwf s\<^sub>1 pd\<^sub>1 FK n\<^sub>1\<close>
      and f0: \<open>fresh_ok \<tau>\<^sub>0 0 n\<^sub>1 FK\<close> by simp_all
    have fu: \<open>fresh_ok (tuple []) 0 n\<^sub>1 FK\<close> by (simp add: fresh_ok_def bfree_def)
    from pe d1 refl refl refl refl d2 inwf_step[OF I o1 le1] f0 fu
    have \<open>n\<^sub>1 \<le> n' \<and> outwf s\<^sub>2 pd' FK n' \<and> fresh_ok \<tau> 0 n' FK\<close>
      by (rule infer_EHandle.IH)
    then have le2: \<open>n\<^sub>1 \<le> n'\<close> and o2: \<open>outwf s\<^sub>2 pd' FK n'\<close>
      and f2: \<open>fresh_ok \<tau> 0 n' FK\<close> by simp_all
    show ?case using se le1 le2 f2 outwf_scomp[OF o1 o2 le2] by simp
  next
    case (infer_EHandler uf B A pd cls n s e' \<tau> pd' n' FK)
    have E: \<open>infer uf B A pd (EHandler cls) n = Some (s, e', \<tau>, pd', n')\<close>
      and I: \<open>inwf B A pd FK n\<close> by (fact infer_EHandler.prems)+
    from E obtain cls'' \<tau>c where
      pe: \<open>list_all (plain_eff B) (hlabels B cls)\<close> and
      d: \<open>infer_cls uf B (RV n) pd False (TV (Suc n)) (tuple []) cls (Suc (Suc n))
        = Some (s, cls'', \<tau>c, pd', n')\<close> and
      te: \<open>\<tau> = TFn (TFn unit_ty (sappr s (canon_row (rext (hlabels B cls) (RV n))))
                       (sapp s (TV (Suc n)))) (sappr s (RV n)) \<tau>c\<close>
      by (auto simp: bind_eq_Some_conv split: if_split_asm)
    have frA: \<open>frv_row A \<subseteq> {..< n}\<close> and brA: \<open>brv_row A = {}\<close>
      using I by (auto simp: inwf_def)
    have i: \<open>inwf B (RV n) pd FK (Suc (Suc n))\<close>
      by (rule inwf_amb[OF inwf_bump[OF I]]) auto
    have ft0: \<open>fresh_ok (TV (Suc n)) 0 (Suc (Suc n)) FK\<close> by (simp add: fresh_ok_def bfree_def)
    have fu: \<open>fresh_ok (tuple []) 0 (Suc (Suc n)) FK\<close> by (simp add: fresh_ok_def bfree_def)
    have w: \<open>Suc (Suc n) \<le> n' \<and> outwf s pd' FK n' \<and> fresh_ok \<tau>c 0 n' FK\<close>
      by (rule infer_EHandler.IH) (use pe d i ft0 fu in auto)
    have le: \<open>Suc (Suc n) \<le> n'\<close> using w by simp
    have o: \<open>outwf s pd' FK n'\<close> using w by simp
    from o have sc: \<open>sconf s {..< n'} {..< n'}\<close> and bfs: \<open>bfree_sub s\<close> by (auto simp: outwf_def)
    have le2: \<open>n \<le> n'\<close> using le by simp
    have ltn: \<open>n < n'\<close> using le by simp
    have ft1: \<open>fresh_ok (sapp s (TV (Suc n))) 0 n' FK\<close>
      by (rule fresh_ok_sapp0[OF ft0 o le])
    have fe1: \<open>frv_row (sappr s (canon_row (rext (hlabels B cls) (RV n)))) \<subseteq> {..< n'}\<close>
      by (rule frv_sappr_sconf[OF sc]) (use ltn in \<open>simp add: rext_def\<close>)
    have be1: \<open>brv_row (sappr s (canon_row (rext (hlabels B cls) (RV n)))) = {}\<close>
      by (rule bfree_sappr[OF bfs]) (simp add: rext_def)
    have fe2: \<open>frv_row (sappr s (RV n)) \<subseteq> {..< n'}\<close>
      by (rule frv_sappr_sconf[OF sc]) (use ltn in simp)
    have be2: \<open>brv_row (sappr s (RV n)) = {}\<close> by (rule bfree_sappr[OF bfs]) simp
    have finner: \<open>fresh_ok (TFn unit_ty (sappr s (canon_row (rext (hlabels B cls) (RV n))))
                            (sapp s (TV (Suc n)))) 0 n' FK\<close>
      by (rule fresh_ok_TFn[OF fresh_ok_unit ft1 fe1 be1])
    have fresh: \<open>fresh_ok \<tau> 0 n' FK\<close>
      unfolding te by (rule fresh_ok_TFn[OF finner w[THEN conjunct2, THEN conjunct2] fe2 be2])
    show ?case using o le2 fresh by simp
  next
    case (infer_EMask uf B A pd l e n s e' \<tau> pd' n' FK)
    have E: \<open>infer uf B A pd (EMask l e) n = Some (s, e', \<tau>, pd', n')\<close>
      and I: \<open>inwf B A pd FK n\<close> by (fact infer_EMask.prems)+
    from E obtain lbl ps \<tau>\<^sub>1 \<tau>\<^sub>2 s\<^sub>1 n\<^sub>1 s\<^sub>2 e'' where
      lk: \<open>tlookup B [n_txt l] = Some (TEop lbl ps \<tau>\<^sub>1 \<tau>\<^sub>2)\<close> and
      ur: \<open>uni_row A (canon_row (RCons lbl (RV n))) (Suc n) = Some (s\<^sub>1, n\<^sub>1)\<close> and
      d2: \<open>infer uf (sappe s\<^sub>1 B) (sappr s\<^sub>1 (RV n)) (sub_pend s\<^sub>1 pd) e n\<^sub>1
             = Some (s\<^sub>2, e'', \<tau>, pd', n')\<close> and
      se: \<open>s = s\<^sub>2 \<odot> s\<^sub>1\<close>
      by (auto split: option.split_asm tentry.split_asm Option.bind_split_asm prod.split_asm)
    from I have frA: \<open>frv_row A \<subseteq> {..< n}\<close> and brA: \<open>brv_row A = {}\<close>
      and ftp: \<open>ftv_pend pd \<subseteq> {..< n}\<close> and frp: \<open>frv_pend pd \<subseteq> {..< n}\<close> and ktp: \<open>ktv_rows pd \<subseteq> FK\<close>
      by (auto simp: inwf_def)
    have s0: \<open>{..< n} \<subseteq> {0 ..< Suc n}\<close> by (simp add: atLeast0LessThan)
    have r2f: \<open>frv_row (canon_row (RCons lbl (RV n))) \<subseteq> {0 ..< Suc n}\<close> by simp
    have ur_f: \<open>Suc n \<le> n\<^sub>1 \<and> sconf s\<^sub>1 {0 ..< n\<^sub>1} {0 ..< n\<^sub>1} \<and> khyg s\<^sub>1 FK \<and> bfree_sub s\<^sub>1\<close>
      by (rule uni_row_fresh[OF ur subset_trans[OF frA s0] r2f brA _ le0]) simp
    have le1: \<open>n \<le> n\<^sub>1\<close> using ur_f by simp
    have sc1: \<open>sconf s\<^sub>1 {..< n\<^sub>1} {..< n\<^sub>1}\<close> using ur_f by (simp add: atLeast0LessThan)
    have kh1: \<open>khyg s\<^sub>1 FK\<close> and bf1: \<open>bfree_sub s\<^sub>1\<close> using ur_f by simp_all
    have o1: \<open>outwf s\<^sub>1 (sub_pend s\<^sub>1 pd) FK n\<^sub>1\<close>
      by (rule outwf_of_uni[OF sc1 kh1 bf1 ftp frp le1 ktp])
    have le1': \<open>Suc n \<le> n\<^sub>1\<close> using ur_f by simp
    have lsub: \<open>{..< n} \<subseteq> {..< n\<^sub>1}\<close> using le1 by simp
    have afr: \<open>frv_row (RV n) \<subseteq> {..< n\<^sub>1}\<close> using le1'[unfolded Suc_le_eq] by simp
    have pf: \<open>ftv_pend (sub_pend s\<^sub>1 pd) \<subseteq> {..< n\<^sub>1}\<close>
      by (rule ftv_pend_sub_pend[OF sc1 subset_trans[OF ftp lsub]])
    have pr: \<open>frv_pend (sub_pend s\<^sub>1 pd) \<subseteq> {..< n\<^sub>1}\<close>
      by (rule frv_pend_sub_pend[OF sc1 subset_trans[OF ftp lsub] subset_trans[OF frp lsub]])
    have pk: \<open>ktv_rows (sub_pend s\<^sub>1 pd) \<subseteq> FK\<close> by (rule ktv_rows_sub_pend[OF kh1 ktp])
    have i2: \<open>inwf (sappe s\<^sub>1 B) (sappr s\<^sub>1 (RV n)) (sub_pend s\<^sub>1 pd) FK n\<^sub>1\<close>
      by (rule inwf_mk[OF I sc1 kh1 bf1 afr _ pf pr pk le1]) simp
    note w = infer_EMask.IH[OF lk refl ur refl d2 i2]
    show ?case using w se le1
      outwf_scomp[OF o1 conjunct1[OF conjunct2[OF w]] conjunct1[OF w]]
      by auto
  next
    case infer_head_APath
    from infer_head_APath.prems show ?case by (rule hpath_wf[rotated])
  next
    case infer_atom_APath
    from infer_atom_APath.prems show ?case by (rule apath_wf[rotated])
  next
    case (infer_atom_AParen_Cons_Nil uf B A pd e n s a' \<tau> pd' n' FK)
    have E: \<open>infer_atom uf B A pd (AParen [e]) n = Some (s, a', \<tau>, pd', n')\<close>
      and I: \<open>inwf B A pd FK n\<close> by (fact infer_atom_AParen_Cons_Nil.prems)+
    from E obtain e'' where d: \<open>infer uf B A pd e n = Some (s, e'', \<tau>, pd', n')\<close>
      by (auto split: Option.bind_split_asm prod.split_asm)
    from d I show ?case by (rule infer_atom_AParen_Cons_Nil.IH)
  next
    case infer_atom_AParen_Nil
    then show ?case
      by (auto simp: inwf_def outwf_def fresh_ok_def bfree_def
          split: Option.bind_split_asm prod.split_asm)
  next
    case (infer_atom_AParen_Cons_Cons uf B A pd v w va n s a' \<tau> pd' n' FK)
    have E: \<open>infer_atom uf B A pd (AParen (v # w # va)) n = Some (s, a', \<tau>, pd', n')\<close>
      and I: \<open>inwf B A pd FK n\<close> by (fact infer_atom_AParen_Cons_Cons.prems)+
    from E obtain es'' \<tau>s where
      d: \<open>infer_exps uf B A pd (v # w # va) n = Some (s, es'', \<tau>s, pd', n')\<close>
      and te: \<open>\<tau> = tuple \<tau>s\<close>
      by (auto split: Option.bind_split_asm prod.split_asm)
    from d I have \<open>n \<le> n' \<and> outwf s pd' FK n' \<and> (\<forall>\<tau> \<in> set \<tau>s. fresh_ok \<tau> 0 n' FK)\<close>
      by (rule infer_atom_AParen_Cons_Cons.IH)
    then show ?case using te fresh_ok_tuple by auto
  next
    case (infer_atom_AList uf B A pd es n s a' \<tau> pd' n' FK)
    have E: \<open>infer_atom uf B A pd (AList es) n = Some (s, a', \<tau>, pd', n')\<close>
      and I: \<open>inwf B A pd FK n\<close> by (fact infer_atom_AList.prems)+
    from E obtain s\<^sub>1 es'' \<tau>s pd\<^sub>1 n\<^sub>1 s\<^sub>2 where
      d1: \<open>infer_exps uf B A pd es n = Some (s\<^sub>1, es'', \<tau>s, pd\<^sub>1, n\<^sub>1)\<close> and
      un: \<open>unis uf (map (\<lambda>\<tau>. (\<tau>, TV n\<^sub>1)) \<tau>s) (Suc n\<^sub>1) = Some (s\<^sub>2, n')\<close> and
      se: \<open>s = s\<^sub>2 \<odot> s\<^sub>1\<close> and te: \<open>\<tau> = TC list_ty [sapp s\<^sub>2 (TV n\<^sub>1)]\<close>
      and pe: \<open>pd' = sub_pend s\<^sub>2 pd\<^sub>1\<close>
      by (auto simp: bind_eq_Some_conv)
    from d1 I
    have \<open>n \<le> n\<^sub>1 \<and> outwf s\<^sub>1 pd\<^sub>1 FK n\<^sub>1 \<and> (\<forall>\<tau> \<in> set \<tau>s. fresh_ok \<tau> 0 n\<^sub>1 FK)\<close>
      by (rule infer_atom_AList.IH)
    then have le1: \<open>n \<le> n\<^sub>1\<close> and o1: \<open>outwf s\<^sub>1 pd\<^sub>1 FK n\<^sub>1\<close>
      and \<tau>sf: \<open>\<forall>\<tau> \<in> set \<tau>s. fresh_ok \<tau> 0 n\<^sub>1 FK\<close> by simp_all
    from o1 have ftp1: \<open>ftv_pend pd\<^sub>1 \<subseteq> {..< n\<^sub>1}\<close> and frp1: \<open>frv_pend pd\<^sub>1 \<subseteq> {..< n\<^sub>1}\<close> and ktp1: \<open>ktv_rows pd\<^sub>1 \<subseteq> FK\<close>
      by (auto simp: outwf_def)
    note uf1 = unis_fresh[OF un cs_map_bounds[OF \<tau>sf] le0]
    have le2: \<open>Suc n\<^sub>1 \<le> n'\<close> using uf1 by simp
    have le12: \<open>n\<^sub>1 \<le> n'\<close> using le2 by simp
    have sc2: \<open>sconf s\<^sub>2 {..< n'} {..< n'}\<close> using uf1 by (simp add: atLeast0LessThan)
    have kh2: \<open>khyg s\<^sub>2 FK\<close> and bf2: \<open>bfree_sub s\<^sub>2\<close> using uf1 by simp_all
    have o2: \<open>outwf s\<^sub>2 (sub_pend s\<^sub>2 pd\<^sub>1) FK n'\<close>
      by (rule outwf_of_uni[OF sc2 kh2 bf2 ftp1 frp1 le12 ktp1])
    have ftv: \<open>fresh_ok (TV n\<^sub>1) 0 (Suc n\<^sub>1) FK\<close> by (simp add: fresh_ok_def bfree_def)
    have fsl: \<open>fresh_ok (sapp s\<^sub>2 (TV n\<^sub>1)) 0 n' FK\<close>
      by (rule fresh_ok_sapp0[OF ftv o2 le2])
    have fresh: \<open>fresh_ok \<tau> 0 n' FK\<close>
      unfolding te using fsl by (auto simp: fresh_ok_def bfree_def)
    have le: \<open>n \<le> n'\<close> using le1 le12 by simp
    show ?case using se pe le fresh outwf_scomp[OF o1 o2 le12] by simp
  next
    case (infer_args uf B A pd d \<tau>\<^sub>0 as n s as' \<tau> pd' n' FK)
    have E: \<open>infer_args uf B A pd d \<tau>\<^sub>0 as n = Some (s, as', \<tau>, pd', n')\<close>
      and I: \<open>inwf B A pd FK n\<close> and F: \<open>fresh_ok \<tau>\<^sub>0 0 n FK\<close> by (fact infer_args.prems)+
    show ?case
    proof (cases \<tau>\<^sub>0)
      case (TV x)
      show ?thesis
      proof (rule infer_args_step[OF E I F])
        show \<open>(\<forall>i sg K e t. \<tau>\<^sub>0 \<noteq> TDep i sg K e t) \<and> (\<forall>x r t. \<tau>\<^sub>0 \<noteq> TOff x r t)\<close>
          by (simp add: TV)
      qed (rule infer_args.IH, rule TV, (assumption | rule refl)+)+
    next
      case (TB x)
      show ?thesis
      proof (rule infer_args_step[OF E I F])
        show \<open>(\<forall>i sg K e t. \<tau>\<^sub>0 \<noteq> TDep i sg K e t) \<and> (\<forall>x r t. \<tau>\<^sub>0 \<noteq> TOff x r t)\<close>
          by (simp add: TB)
      qed (rule infer_args.IH, rule TB, (assumption | rule refl)+)+
    next
      case (TK x)
      show ?thesis
      proof (rule infer_args_step[OF E I F])
        show \<open>(\<forall>i sg K e t. \<tau>\<^sub>0 \<noteq> TDep i sg K e t) \<and> (\<forall>x r t. \<tau>\<^sub>0 \<noteq> TOff x r t)\<close>
          by (simp add: TK)
      qed (rule infer_args.IH, rule TK, (assumption | rule refl)+)+
    next
      case (TA d j)
      show ?thesis
      proof (rule infer_args_step[OF E I F])
        show \<open>(\<forall>i sg K e t. \<tau>\<^sub>0 \<noteq> TDep i sg K e t) \<and> (\<forall>x r t. \<tau>\<^sub>0 \<noteq> TOff x r t)\<close>
          by (simp add: TA)
      qed (rule infer_args.IH, rule TA, (assumption | rule refl)+)+
    next
      case (TC c ts)
      show ?thesis
      proof (rule infer_args_step[OF E I F])
        show \<open>(\<forall>i sg K e t. \<tau>\<^sub>0 \<noteq> TDep i sg K e t) \<and> (\<forall>x r t. \<tau>\<^sub>0 \<noteq> TOff x r t)\<close>
          by (simp add: TC)
      qed (rule infer_args.IH, rule TC, (assumption | rule refl)+)+
    next
      case (TApp t\<^sub>1 t\<^sub>2)
      show ?thesis
      proof (rule infer_args_step[OF E I F])
        show \<open>(\<forall>i sg K e t. \<tau>\<^sub>0 \<noteq> TDep i sg K e t) \<and> (\<forall>x r t. \<tau>\<^sub>0 \<noteq> TOff x r t)\<close>
          by (simp add: TApp)
      qed (rule infer_args.IH, rule TApp, (assumption | rule refl)+)+
    next
      case (TFn t\<^sub>1 e t\<^sub>2)
      show ?thesis
      proof (rule infer_args_step[OF E I F])
        show \<open>(\<forall>i sg K e t. \<tau>\<^sub>0 \<noteq> TDep i sg K e t) \<and> (\<forall>x r t. \<tau>\<^sub>0 \<noteq> TOff x r t)\<close>
          by (simp add: TFn)
      qed (rule infer_args.IH, rule TFn, (assumption | rule refl)+)+
    next
      case (TDep i sg m e t')
      show ?thesis
      proof (cases i)
        case True
        from E TDep True obtain K E\<^sub>K n\<^sub>1 s\<^sub>1 n\<^sub>3 s\<^sub>2 as'' where
          d0: \<open>d \<noteq> 0\<close> and kd: \<open>set K \<inter> ktv_env B = {}\<close> and
          de: \<open>dep_env B n sg m = Some (K, E\<^sub>K, n\<^sub>1)\<close> and
          ur: \<open>uni_row e A (n\<^sub>1 + m) = Some (s\<^sub>1, n\<^sub>3)\<close> and
          rec: \<open>infer_args uf (sappe s\<^sub>1 B) (sappr s\<^sub>1 A)
                  ((imp_name n\<^sub>3, PImp K (map (apsnd (sapp s\<^sub>1)) (zip K (map TV [n\<^sub>1 ..< n\<^sub>1 + m])))
                    E\<^sub>K (cands B) None) # sub_pend s\<^sub>1 pd)
                  (d - 1) (sapp s\<^sub>1 (kopen (tsp K (zip K (map TV [n\<^sub>1 ..< n\<^sub>1 + m]))) t')) as (Suc n\<^sub>3)
                = Some (s\<^sub>2, as'', \<tau>, pd', n')\<close> and
          se: \<open>s = s\<^sub>2 \<odot> s\<^sub>1\<close>
          by (auto simp del: infer_args.simps simp: infer_args_TDep_True Let_def bind_eq_Some_conv
            split: prod.split_asm if_split_asm)
        let ?\<alpha>s = \<open>[n\<^sub>1 ..< n\<^sub>1 + m]\<close>
        let ?\<phi> = \<open>zip K (map TV ?\<alpha>s)\<close>
        from I have cenvB: \<open>cenv B\<close> and bfB: \<open>bfree_env B\<close> and ktvB: \<open>ktv_env B \<subseteq> FK\<close>
          and ftvB: \<open>ftv_env B \<subseteq> {..< n}\<close> and frvB: \<open>frv_env B \<subseteq> {..< n}\<close>
          and frA: \<open>frv_row A \<subseteq> {..< n}\<close> and brA: \<open>brv_row A = {}\<close>
          and ftp: \<open>ftv_pend pd \<subseteq> {..< n}\<close> and frp: \<open>frv_pend pd \<subseteq> {..< n}\<close>
          and ktp: \<open>ktv_rows pd \<subseteq> FK\<close> by (auto simp: inwf_def)
        have fT: \<open>fresh_ok (TDep True sg m e t') 0 n FK\<close> using F TDep True by simp
        have ftt: \<open>ftv t' \<subseteq> {..< n}\<close> and frt: \<open>frv t' \<subseteq> {..< n}\<close> and fre: \<open>frv_row e \<subseteq> {..< n}\<close>
          and ktt: \<open>ktv t' \<subseteq> FK\<close> and btt: \<open>btv t' = {}\<close> and bre: \<open>brv_row e = {}\<close>
          and brt: \<open>brv t' = {}\<close> using fT by (auto simp: fresh_ok_def bfree_def)
        note dw = dep_env_wf[OF de cenvB bfB]
        have le01: \<open>n \<le> n\<^sub>1\<close> using dw by simp
        have le12: \<open>n\<^sub>1 \<le> n\<^sub>1 + m\<close> by simp
        have le02: \<open>n \<le> n\<^sub>1 + m\<close> using le01 le12 by simp
        have lenas: \<open>length ?\<alpha>s = length K\<close> using dw by simp
        have mfz: \<open>map fst ?\<phi> = K\<close> using lenas by simp
        have cov: \<open>set K \<subseteq> fst ` set ?\<phi>\<close> using mfz[THEN arg_cong[where f = set]] by simp
        have fre2: \<open>frv_row e \<subseteq> {0 ..< n\<^sub>1 + m}\<close>
          using fre le02 by (auto simp: atLeast0LessThan)
        have frA2: \<open>frv_row A \<subseteq> {0 ..< n\<^sub>1 + m}\<close>
          using frA le02 by (auto simp: atLeast0LessThan)
        note urf = uni_row_fresh[OF ur fre2 frA2 bre brA le0, of FK]
        have le23: \<open>n\<^sub>1 + m \<le> n\<^sub>3\<close> using urf by simp
        have sc1: \<open>sconf s\<^sub>1 {..< n\<^sub>3} {..< n\<^sub>3}\<close> using urf by (simp add: atLeast0LessThan)
        have kh1: \<open>khyg s\<^sub>1 FK\<close> and bf1: \<open>bfree_sub s\<^sub>1\<close> using urf by simp_all
        have le03: \<open>n \<le> n\<^sub>3\<close> using le02 le23 by simp
        have o1: \<open>outwf s\<^sub>1 (sub_pend s\<^sub>1 pd) FK n\<^sub>3\<close>
          by (rule outwf_of_uni[OF sc1 kh1 bf1 ftp frp le03 ktp])
        have fk: \<open>fresh_ok (kopen (tsp K ?\<phi>) t') 0 (n\<^sub>1 + m) FK\<close>
          by (rule fresh_ok_kopen_tsp[OF ftt frt ktt btt brt _ cov le02])
             (fastforce dest!: set_zip_rightD)
        have frec: \<open>fresh_ok (sapp s\<^sub>1 (kopen (tsp K ?\<phi>) t')) 0 (Suc n\<^sub>3) FK\<close>
          using fresh_ok_mono[OF fresh_ok_sapp0[OF fk o1 le23] le_refl le_SucI[OF le_refl]] .
        \<comment> \<open>the extended pending confinement\<close>
        have palt: \<open>ftv t \<subseteq> {..< n\<^sub>3} \<and> frv t \<subseteq> {..< n\<^sub>3}\<close>
          if \<open>(k, t) \<in> set (map (apsnd (sapp s\<^sub>1)) ?\<phi>)\<close> for k t
        proof -
          from that obtain u where mu: \<open>(k, u) \<in> set ?\<phi>\<close> and tu: \<open>t = sapp s\<^sub>1 u\<close>
            by (auto simp: apsnd_def)
          from mu obtain \<alpha> where al: \<open>\<alpha> \<in> set ?\<alpha>s\<close> and ua: \<open>u = TV \<alpha>\<close> by (auto simp: set_zip)
          have altn: \<open>\<alpha> < n\<^sub>3\<close> using al le23 by auto
          have \<open>ftv t \<subseteq> {..< n\<^sub>3}\<close> using tu ua altn ftv_sapp_sconf[OF sc1, of \<open>TV \<alpha>\<close>] by auto
          moreover have \<open>frv t \<subseteq> {..< n\<^sub>3}\<close>
            using tu ua altn frv_sapp_sconf[OF sc1, of \<open>TV \<alpha>\<close>] by auto
          ultimately show ?thesis by blast
        qed
        have part1: \<open>(\<Union>(k, t)\<in>set (map (apsnd (sapp s\<^sub>1)) ?\<phi>). ftv t) \<subseteq> {..< n\<^sub>3}\<close>
          using palt by fastforce
        have part1r: \<open>(\<Union>(k, t)\<in>set (map (apsnd (sapp s\<^sub>1)) ?\<phi>). frv t) \<subseteq> {..< n\<^sub>3}\<close>
          using palt by fastforce
        have subn3: \<open>{..< n} \<subseteq> {..< n\<^sub>3}\<close> using le03 by simp
        have ftpp: \<open>ftv_pend ((imp_name n\<^sub>3, PImp K (map (apsnd (sapp s\<^sub>1)) ?\<phi>)
          E\<^sub>K (cands B) None)
                     # sub_pend s\<^sub>1 pd)
                     \<subseteq> {..< Suc n\<^sub>3}\<close>
          using part1 ftv_pend_sub_pend[OF sc1 subset_trans[OF ftp subn3]]
          by (fastforce simp: ftv_pend_def)
        have frpp: \<open>frv_pend ((imp_name n\<^sub>3, PImp K (map (apsnd (sapp s\<^sub>1)) ?\<phi>)
          E\<^sub>K (cands B) None)
                     # sub_pend s\<^sub>1 pd)
                     \<subseteq> {..< Suc n\<^sub>3}\<close>
          using part1r frv_pend_sub_pend[OF sc1 subset_trans[OF ftp subn3]
                  subset_trans[OF frp subn3]]
          by (fastforce simp: frv_pend_def)
        have irec: \<open>inwf (sappe s\<^sub>1 B) (sappr s\<^sub>1 A)
              ((imp_name n\<^sub>3, PImp K (map (apsnd (sapp s\<^sub>1)) ?\<phi>)
                E\<^sub>K (cands B) None)
                # sub_pend s\<^sub>1 pd) FK (Suc n\<^sub>3)\<close>
          unfolding inwf_def
          using cenv_sappe[OF cenvB] bfree_env_sappe[OF bf1 bfB] ktv_env_sappe[OF kh1 ktvB]
            ftv_sappe_sconf[OF sc1 subset_trans[OF ftvB subn3]]
            frv_sappe_sconf[OF sc1 subset_trans[OF ftvB subn3]
              subset_trans[OF frvB subn3]]
            frv_sappr_sconf[OF sc1 subset_trans[OF frA subn3]]
            bfree_sappr[OF bf1 brA] ftpp frpp ktv_rows_sub_pend[OF kh1 ktp]
          by auto
        from TDep True[THEN eqTrueI] d0 de refl refl not_not[THEN iffD2, OF kd] refl refl refl
          ur refl refl refl rec irec frec
        have w2: \<open>Suc n\<^sub>3 \<le> n' \<and> outwf s\<^sub>2 pd' FK n' \<and> fresh_ok \<tau> 0 n' FK\<close>
          by (rule infer_args.IH)
        have le3n: \<open>n\<^sub>3 \<le> n'\<close> using w2 by simp
        show ?thesis using se le03 le3n w2
          outwf_scomp[OF o1 conjunct1[OF conjunct2[OF w2]] le3n] by simp
      next
        case False
        show ?thesis
        proof (cases as)
          case Nil then show ?thesis using E TDep False by simp
        next
          case (Cons a rest)
          show ?thesis
          proof (cases a)
            case (APath P)
            obtain ent E_P K E\<^sub>K n\<^sub>1 \<phi> s\<^sub>1 n\<^sub>2 s\<^sub>2 rest'' where
              nr: \<open>\<not> list_ex reserved (path_nms P)\<close> and kd: \<open>set K \<inter> ktv_env B = {}\<close> and
              tle: \<open>tlookup B (path_nms P) = Some ent\<close> and
              ec: \<open>(case ent of TEstr E \<Rightarrow> Some E | TEinst E \<Rightarrow> Some E | _ \<Rightarrow> None) = Some E_P\<close> and
              de: \<open>dep_env B n sg m = Some (K, E\<^sub>K, n\<^sub>1)\<close> and
              md: \<open>match_dep E_P K E\<^sub>K = Some \<phi>\<close> and
              enr: \<open>enrich E_P (kenv (tsl \<phi>) E\<^sub>K)\<close> and
              ur: \<open>uni_row e A n\<^sub>1 = Some (s\<^sub>1, n\<^sub>2)\<close> and
              rec: \<open>infer_args uf (sappe s\<^sub>1 B) (sappr s\<^sub>1 A) (sub_pend s\<^sub>1 pd) d
                      (sapp s\<^sub>1 (kopen (tsp K \<phi>) t')) rest n\<^sub>2 = Some (s\<^sub>2, rest'', \<tau>, pd', n')\<close> and
              se: \<open>s = s\<^sub>2 \<odot> s\<^sub>1\<close>
              using E TDep False Cons APath
              by (auto simp del: infer_args.simps
                       simp: infer_args_TDep_APath bind_eq_Some_conv
                       split: option.split_asm tentry.split_asm if_split_asm prod.split_asm)
            have tl: \<open>tlookup B (path_nms P) = Some (TEstr E_P)
                \<or> tlookup B (path_nms P) = Some (TEinst E_P)\<close>
              using tle ec by (auto split: tentry.split_asm)
            from I have cenvB: \<open>cenv B\<close> and bfB: \<open>bfree_env B\<close> and ktvB: \<open>ktv_env B \<subseteq> FK\<close>
              and frA: \<open>frv_row A \<subseteq> {..< n}\<close> and brA: \<open>brv_row A = {}\<close>
              and ftp: \<open>ftv_pend pd \<subseteq> {..< n}\<close> and frp: \<open>frv_pend pd \<subseteq> {..< n}\<close> and ktp: \<open>ktv_rows pd \<subseteq> FK\<close>
              by (auto simp: inwf_def)
            have fT: \<open>fresh_ok (TDep False sg m e t') 0 n FK\<close> using F TDep False by simp
            have ftt: \<open>ftv t' \<subseteq> {..< n}\<close> and frt: \<open>frv t' \<subseteq> {..< n}\<close>
              and ktt: \<open>ktv t' \<subseteq> FK\<close> and btt: \<open>btv t' = {}\<close>
              and bre: \<open>brv_row e = {}\<close> and brt: \<open>brv t' = {}\<close> and fre: \<open>frv_row e \<subseteq> {..< n}\<close>
              using fT by (auto simp: fresh_ok_def bfree_def)
            have cl: \<open>ftv_env E_P = {}\<close> \<open>frv_env E_P = {}\<close> and ke: \<open>ktv_env E_P \<subseteq> ktv_env B\<close>
              using tl cenv_tlookup_nonval[OF cenvB] ktv_env_tlookup by fastforce+
            have cP: \<open>cenv E_P\<close> using cenv_acc[OF cl cenv_Nil] by simp
            have le01: \<open>n \<le> n\<^sub>1\<close> using dep_env_wf[OF de cenvB bfB] by simp
            note mc = match_dep_closed[OF md cP]
            have phi: \<open>\<forall>(k, u) \<in> set \<phi>. ftv u = {} \<and> frv u = {} \<and> ktv u \<subseteq> FK \<and> bfree u\<close>
              using mc ke ktvB by fastforce
            have domsub: \<open>fst ` set \<phi> \<subseteq> set K\<close> using mc by simp
            have lenK: \<open>length K = m\<close> using dep_env_wf[OF de cenvB bfB] by simp
            obtain T\<^sub>d E\<^sub>d where Lc: \<open>length T\<^sub>d = m\<close> and dT: \<open>distinct T\<^sub>d\<close>
              and covT: \<open>\<forall>t\<in>set T\<^sub>d. abs_present t E\<^sub>d\<close> and ek: \<open>E\<^sub>K = real_env (dep_vars T\<^sub>d K) E\<^sub>d\<close>
              using de
              by (auto simp: dep_env_def bind_eq_Some_conv split: prod.split_asm if_split_asm)
            have cov: \<open>set K \<subseteq> fst ` set \<phi>\<close>
              using match_dep_covers[OF md[unfolded ek] covT _ dT] Lc lenK by simp
            have fk: \<open>fresh_ok (kopen (tsp K \<phi>) t') 0 n\<^sub>1 FK\<close>
              by (rule fresh_ok_kopen_tsp[OF _ _ ktt btt brt _ cov le01])
                 (use ftt frt phi in auto)
            have fre2: \<open>frv_row e \<subseteq> {0 ..< n\<^sub>1}\<close>
              using fre le01 by (auto simp: atLeast0LessThan)
            have frA2: \<open>frv_row A \<subseteq> {0 ..< n\<^sub>1}\<close>
              using frA le01 by (auto simp: atLeast0LessThan)
            note urf = uni_row_fresh[OF ur fre2 frA2 bre brA le0, of FK]
            have le12: \<open>n\<^sub>1 \<le> n\<^sub>2\<close> using urf by simp
            have le02: \<open>n \<le> n\<^sub>2\<close> using le01 le12 by simp
            have sc1: \<open>sconf s\<^sub>1 {..< n\<^sub>2} {..< n\<^sub>2}\<close> using urf by (simp add: atLeast0LessThan)
            have kh1: \<open>khyg s\<^sub>1 FK\<close> and bf1: \<open>bfree_sub s\<^sub>1\<close> using urf by simp_all
            have o1: \<open>outwf s\<^sub>1 (sub_pend s\<^sub>1 pd) FK n\<^sub>2\<close>
              by (rule outwf_of_uni[OF sc1 kh1 bf1 ftp frp le02 ktp])
            have frec: \<open>fresh_ok (sapp s\<^sub>1 (kopen (tsp K \<phi>) t')) 0 n\<^sub>2 FK\<close>
              by (rule fresh_ok_sapp0[OF fk o1 le12])
            have irec: \<open>inwf (sappe s\<^sub>1 B) (sappr s\<^sub>1 A) (sub_pend s\<^sub>1 pd) FK n\<^sub>2\<close>
              by (rule inwf_step[OF I o1 le02])
            from TDep eq_False[THEN iffD2, OF False] Cons APath nr tle ec de refl refl
              not_not[THEN iffD2, OF kd] md enr ur refl rec irec frec
            have w2: \<open>n\<^sub>2 \<le> n' \<and> outwf s\<^sub>2 pd' FK n' \<and> fresh_ok \<tau> 0 n' FK\<close>
              by (rule infer_args.IH)
            have le2n: \<open>n\<^sub>2 \<le> n'\<close> using w2 by simp
            show ?thesis using se le02 le2n w2
              outwf_scomp[OF o1 conjunct1[OF conjunct2[OF w2]] le2n] by simp
          next
            case (ANum l v sfx) then show ?thesis using E TDep False Cons by simp
          next
            case (AFloat x) then show ?thesis using E TDep False Cons by simp
          next
            case (AStr l cs) then show ?thesis using E TDep False Cons by simp
          next
            case (AChar l c) then show ?thesis using E TDep False Cons by simp
          next
            case (AParen es) then show ?thesis using E TDep False Cons by simp
          next
            case (AList es) then show ?thesis using E TDep False Cons by simp
          next
            case (AMod P sig') then show ?thesis using E TDep False Cons by simp
          next
            case (ARec fs) then show ?thesis using E TDep False Cons by simp
          next
            case (ADot b y) then show ?thesis using E TDep False Cons by simp
          next
            case (ABind y sg) then show ?thesis using E TDep False Cons by simp
          qed
        qed
      qed
    next
      case (TEv l w ts)
      show ?thesis
      proof (rule infer_args_step[OF E I F])
        show \<open>(\<forall>i sg K e t. \<tau>\<^sub>0 \<noteq> TDep i sg K e t) \<and> (\<forall>x r t. \<tau>\<^sub>0 \<noteq> TOff x r t)\<close>
          by (simp add: TEv)
      qed (rule infer_args.IH, rule TEv, (assumption | rule refl)+)+
    next
      case (TAct lt K e t)
      show ?thesis
      proof (rule infer_args_step[OF E I F])
        show \<open>(\<forall>i sg K e t. \<tau>\<^sub>0 \<noteq> TDep i sg K e t) \<and> (\<forall>x r t. \<tau>\<^sub>0 \<noteq> TOff x r t)\<close>
          by (simp add: TAct)
      qed (rule infer_args.IH, rule TAct, (assumption | rule refl)+)+
    next
      case TRNil
      show ?thesis
      proof (rule infer_args_step[OF E I F])
        show \<open>(\<forall>i sg K e t. \<tau>\<^sub>0 \<noteq> TDep i sg K e t) \<and> (\<forall>x r t. \<tau>\<^sub>0 \<noteq> TOff x r t)\<close>
          by (simp add: TRNil)
      qed (rule infer_args.IH, rule TRNil, (assumption | rule refl)+)+
    next
      case (TRCons lb t r)
      show ?thesis
      proof (rule infer_args_step[OF E I F])
        show \<open>(\<forall>i sg K e t. \<tau>\<^sub>0 \<noteq> TDep i sg K e t) \<and> (\<forall>x r t. \<tau>\<^sub>0 \<noteq> TOff x r t)\<close>
          by (simp add: TRCons)
      qed (rule infer_args.IH, rule TRCons, (assumption | rule refl)+)+
    next
      case (TOff x r t')
      from E TOff obtain as'' where
        rec: \<open>infer_args uf B A ((imp_name n, POff x r) # pd) d t' as (Suc n)
                = Some (s, as'', \<tau>, pd', n')\<close>
        by (auto simp del: infer_args.simps simp: infer_args_TOff Let_def bind_eq_Some_conv)
      have fr: \<open>ftv r \<subseteq> {..< n}\<close> \<open>frv r \<subseteq> {..< n}\<close> \<open>ktv r \<subseteq> FK\<close>
        and ft: \<open>fresh_ok t' 0 (Suc n) FK\<close>
        using F TOff by (auto simp: fresh_ok_def bfree_def subset_iff)
      have I': \<open>inwf B A ((imp_name n, POff x r) # pd) FK (Suc n)\<close>
        using I fr by (auto simp: inwf_def subset_iff)
      have \<open>Suc n \<le> n' \<and> outwf s pd' FK n' \<and> fresh_ok \<tau> 0 n' FK\<close>
        using TOff refl rec I' ft by (rule infer_args.IH)
      then show ?thesis by simp
    qed
  next
    case (infer_exps_Cons uf B A pd e es n s es' \<tau>s pd' n' FK)
    have E: \<open>infer_exps uf B A pd (e # es) n = Some (s, es', \<tau>s, pd', n')\<close>
      and I: \<open>inwf B A pd FK n\<close> by (fact infer_exps_Cons.prems)+
    from E obtain s\<^sub>1 e'' \<tau> pd\<^sub>1 n\<^sub>1 s\<^sub>2 es'' \<tau>s' where
      d1: \<open>infer uf B A pd e n = Some (s\<^sub>1, e'', \<tau>, pd\<^sub>1, n\<^sub>1)\<close> and
      d2: \<open>infer_exps uf (sappe s\<^sub>1 B) (sappr s\<^sub>1 A) pd\<^sub>1 es n\<^sub>1
        = Some (s\<^sub>2, es'', \<tau>s', pd', n')\<close> and
      se: \<open>s = s\<^sub>2 \<odot> s\<^sub>1\<close> \<open>\<tau>s = sapp s\<^sub>2 \<tau> # \<tau>s'\<close>
      by (auto split: Option.bind_split_asm prod.split_asm)
    from d1 I have \<open>n \<le> n\<^sub>1 \<and> outwf s\<^sub>1 pd\<^sub>1 FK n\<^sub>1 \<and> fresh_ok \<tau> 0 n\<^sub>1 FK\<close>
      by (rule infer_exps_Cons.IH)
    then have le1: \<open>n \<le> n\<^sub>1\<close> and o1: \<open>outwf s\<^sub>1 pd\<^sub>1 FK n\<^sub>1\<close>
      and f1: \<open>fresh_ok \<tau> 0 n\<^sub>1 FK\<close> by simp_all
    from d1 refl refl refl refl d2 inwf_step[OF I o1 le1]
    have \<open>n\<^sub>1 \<le> n' \<and> outwf s\<^sub>2 pd' FK n' \<and> (\<forall>\<tau> \<in> set \<tau>s'. fresh_ok \<tau> 0 n' FK)\<close>
      by (rule infer_exps_Cons.IH)
    then have le2: \<open>n\<^sub>1 \<le> n'\<close> and o2: \<open>outwf s\<^sub>2 pd' FK n'\<close>
      and f2: \<open>\<forall>\<tau> \<in> set \<tau>s'. fresh_ok \<tau> 0 n' FK\<close> by simp_all
    show ?case using se le1 le2 f2 fresh_ok_sapp0[OF f1 o2 le2] outwf_scomp[OF o1 o2 le2] by auto
  next
    case (infer_chain_EOp_Cons uf B A pd a as opr e n s e'x oprs \<tau>s pd' n' FK)
    have E: \<open>infer_chain uf B A pd (EOp (a # as) opr e) n = Some (s, e'x, oprs, \<tau>s, pd', n')\<close>
      and I: \<open>inwf B A pd FK n\<close> by (fact infer_chain_EOp_Cons.prems)+
    from E obtain s\<^sub>1 a'' \<tau>\<^sub>0 pd\<^sub>1 n\<^sub>1 s\<^sub>2 as'' \<tau> pd\<^sub>2 n\<^sub>2 where
      d1: \<open>infer_head uf B A pd a n = Some (s\<^sub>1, a'', \<tau>\<^sub>0, pd\<^sub>1, n\<^sub>1)\<close> and
      d2: \<open>infer_args uf (sappe s\<^sub>1 B) (sappr s\<^sub>1 A) pd\<^sub>1 uf \<tau>\<^sub>0 as n\<^sub>1
        = Some (s\<^sub>2, as'', \<tau>, pd\<^sub>2, n\<^sub>2)\<close> and
      R: \<open>(if is_eop e
            then infer_chain uf (sappe (s\<^sub>2 \<odot> s\<^sub>1) B) (sappr (s\<^sub>2 \<odot> s\<^sub>1) A) pd\<^sub>2 e n\<^sub>2 \<bind>
                   (\<lambda>(s\<^sub>3, e', oprs', \<tau>s', pd\<^sub>3, n\<^sub>3).
                     Some (s\<^sub>3 \<odot> (s\<^sub>2 \<odot> s\<^sub>1), EOp (a'' # as'') opr e', opr # oprs',
                           sapp s\<^sub>3 \<tau> # \<tau>s', pd\<^sub>3, n\<^sub>3))
            else infer uf (sappe (s\<^sub>2 \<odot> s\<^sub>1) B) (sappr (s\<^sub>2 \<odot> s\<^sub>1) A) pd\<^sub>2 e n\<^sub>2 \<bind>
                   (\<lambda>(s\<^sub>3, e', \<tau>\<^sub>l, pd\<^sub>3, n\<^sub>3).
                     Some (s\<^sub>3 \<odot> (s\<^sub>2 \<odot> s\<^sub>1), EOp (a'' # as'') opr e', [opr],
                           [sapp s\<^sub>3 \<tau>, \<tau>\<^sub>l], pd\<^sub>3, n\<^sub>3)))
           = Some (s, e'x, oprs, \<tau>s, pd', n')\<close>
      by (simp add: Let_def cong: if_cong) (auto simp: bind_eq_Some_conv)
    from d1 I have \<open>n \<le> n\<^sub>1 \<and> outwf s\<^sub>1 pd\<^sub>1 FK n\<^sub>1 \<and> fresh_ok \<tau>\<^sub>0 0 n\<^sub>1 FK\<close>
      by (rule infer_chain_EOp_Cons.IH)
    then have le1: \<open>n \<le> n\<^sub>1\<close> and o1: \<open>outwf s\<^sub>1 pd\<^sub>1 FK n\<^sub>1\<close>
      and f0: \<open>fresh_ok \<tau>\<^sub>0 0 n\<^sub>1 FK\<close> by simp_all
    from d1 refl refl refl refl d2 inwf_step[OF I o1 le1] f0
    have \<open>n\<^sub>1 \<le> n\<^sub>2 \<and> outwf s\<^sub>2 pd\<^sub>2 FK n\<^sub>2 \<and> fresh_ok \<tau> 0 n\<^sub>2 FK\<close>
      by (rule infer_chain_EOp_Cons.IH)
    then have le2: \<open>n\<^sub>1 \<le> n\<^sub>2\<close> and o2: \<open>outwf s\<^sub>2 pd\<^sub>2 FK n\<^sub>2\<close>
      and ft: \<open>fresh_ok \<tau> 0 n\<^sub>2 FK\<close> by simp_all
    have le12: \<open>n \<le> n\<^sub>2\<close> using le1 le2 by simp
    have os: \<open>outwf (s\<^sub>2 \<odot> s\<^sub>1) pd\<^sub>2 FK n\<^sub>2\<close> by (rule outwf_scomp[OF o1 o2 le2])
    have i3: \<open>inwf (sappe (s\<^sub>2 \<odot> s\<^sub>1) B) (sappr (s\<^sub>2 \<odot> s\<^sub>1) A) pd\<^sub>2 FK n\<^sub>2\<close>
      by (rule inwf_step[OF I os le12])
    show ?case
    proof (cases \<open>is_eop e\<close>)
      case True
      from R True obtain s\<^sub>3 e' oprs' \<tau>s' pd\<^sub>3 n\<^sub>3 where
        d3: \<open>infer_chain uf (sappe (s\<^sub>2 \<odot> s\<^sub>1) B) (sappr (s\<^sub>2 \<odot> s\<^sub>1) A) pd\<^sub>2 e n\<^sub>2
               = Some (s\<^sub>3, e', oprs', \<tau>s', pd\<^sub>3, n\<^sub>3)\<close> and
        se: \<open>s = s\<^sub>3 \<odot> (s\<^sub>2 \<odot> s\<^sub>1)\<close> \<open>\<tau>s = sapp s\<^sub>3 \<tau> # \<tau>s'\<close> \<open>pd' = pd\<^sub>3\<close> \<open>n' = n\<^sub>3\<close>
        by (auto simp: bind_eq_Some_conv)
      from d1 refl refl refl refl d2 refl refl refl refl refl True d3 i3
      have w3: \<open>n\<^sub>2 \<le> n\<^sub>3 \<and> outwf s\<^sub>3 pd\<^sub>3 FK n\<^sub>3 \<and> (\<forall>\<tau> \<in> set \<tau>s'. fresh_ok \<tau> 0 n\<^sub>3 FK)\<close>
        by (rule infer_chain_EOp_Cons.IH)
      have le3: \<open>n\<^sub>2 \<le> n\<^sub>3\<close> using w3 by simp
      have o3: \<open>outwf s\<^sub>3 pd\<^sub>3 FK n\<^sub>3\<close> using w3 by simp
      have hd: \<open>fresh_ok (sapp s\<^sub>3 \<tau>) 0 n\<^sub>3 FK\<close> by (rule fresh_ok_sapp0[OF ft o3 le3])
      have tl: \<open>\<forall>\<tau>'' \<in> set \<tau>s'. fresh_ok \<tau>'' 0 n\<^sub>3 FK\<close> using w3 by simp
      show ?thesis using se le12 le3 hd tl outwf_scomp[OF os o3 le3] by auto
    next
      case False
      from R False obtain s\<^sub>3 e' \<tau>\<^sub>l pd\<^sub>3 n\<^sub>3 where
        d3: \<open>infer uf (sappe (s\<^sub>2 \<odot> s\<^sub>1) B) (sappr (s\<^sub>2 \<odot> s\<^sub>1) A) pd\<^sub>2 e n\<^sub>2
               = Some (s\<^sub>3, e', \<tau>\<^sub>l, pd\<^sub>3, n\<^sub>3)\<close> and
        se: \<open>s = s\<^sub>3 \<odot> (s\<^sub>2 \<odot> s\<^sub>1)\<close> \<open>\<tau>s = [sapp s\<^sub>3 \<tau>, \<tau>\<^sub>l]\<close> \<open>pd' = pd\<^sub>3\<close> \<open>n' = n\<^sub>3\<close>
        by (auto simp: bind_eq_Some_conv)
      from d1 refl refl refl refl d2 refl refl refl refl refl False d3 i3
      have w3: \<open>n\<^sub>2 \<le> n\<^sub>3 \<and> outwf s\<^sub>3 pd\<^sub>3 FK n\<^sub>3 \<and> fresh_ok \<tau>\<^sub>l 0 n\<^sub>3 FK\<close>
        by (rule infer_chain_EOp_Cons.IH)
      have le3: \<open>n\<^sub>2 \<le> n\<^sub>3\<close> using w3 by simp
      have o3: \<open>outwf s\<^sub>3 pd\<^sub>3 FK n\<^sub>3\<close> using w3 by simp
      have ftl: \<open>fresh_ok \<tau>\<^sub>l 0 n\<^sub>3 FK\<close> using w3 by simp
      have hd: \<open>fresh_ok (sapp s\<^sub>3 \<tau>) 0 n\<^sub>3 FK\<close> by (rule fresh_ok_sapp0[OF ft o3 le3])
      show ?thesis using se le12 le3 hd ftl outwf_scomp[OF os o3 le3] by auto
    qed
  next
    case (infer_arms_Cons uf B A pd \<tau>\<^sub>0 \<tau>\<^sub>r p b arms n s arms'x pd' n' FK)
    have E: \<open>infer_arms uf B A pd \<tau>\<^sub>0 \<tau>\<^sub>r ((p, b) # arms) n = Some (s, arms'x, pd', n')\<close>
      and I: \<open>inwf B A pd FK n\<close> and F\<^sub>0: \<open>fresh_ok \<tau>\<^sub>0 0 n FK\<close>
      and F\<^sub>r: \<open>fresh_ok \<tau>\<^sub>r 0 n FK\<close> by (fact infer_arms_Cons.prems)+
    from E obtain sp \<tau>\<^sub>p \<Gamma> n\<^sub>1 s\<^sub>1 n\<^sub>2 s\<^sub>2 b'' \<tau>\<^sub>b pd\<^sub>2 n\<^sub>3 s\<^sub>3 n\<^sub>4 s\<^sub>4 arms'' p\<^sub>x where
      dp: \<open>infer_pat uf B p n = Some (sp, p\<^sub>x, \<tau>\<^sub>p, \<Gamma>, n\<^sub>1)\<close> and
      u1: \<open>uni uf (sapp sp \<tau>\<^sub>0) \<tau>\<^sub>p n\<^sub>1 = Some (s\<^sub>1, n\<^sub>2)\<close> and
      db: \<open>infer uf (mono_env s\<^sub>1 \<Gamma> @ sappe (s\<^sub>1 \<odot> sp) B) (sappr (s\<^sub>1 \<odot> sp) A)
             (sub_pend (s\<^sub>1 \<odot> sp) pd) b n\<^sub>2 = Some (s\<^sub>2, b'', \<tau>\<^sub>b, pd\<^sub>2, n\<^sub>3)\<close> and
      u2: \<open>uni uf \<tau>\<^sub>b (sapp (s\<^sub>2 \<odot> (s\<^sub>1 \<odot> sp)) \<tau>\<^sub>r) n\<^sub>3 = Some (s\<^sub>3, n\<^sub>4)\<close> and
      da: \<open>infer_arms uf (sappe (s\<^sub>3 \<odot> s\<^sub>2 \<odot> (s\<^sub>1 \<odot> sp)) B)
             (sappr (s\<^sub>3 \<odot> s\<^sub>2 \<odot> (s\<^sub>1 \<odot> sp)) A) (sub_pend s\<^sub>3 pd\<^sub>2)
             (sapp (s\<^sub>3 \<odot> s\<^sub>2 \<odot> (s\<^sub>1 \<odot> sp)) \<tau>\<^sub>0) (sapp (s\<^sub>3 \<odot> s\<^sub>2 \<odot> (s\<^sub>1 \<odot> sp)) \<tau>\<^sub>r)
             arms n\<^sub>4 = Some (s\<^sub>4, arms'', pd', n')\<close> and
      se: \<open>s = s\<^sub>4 \<odot> (s\<^sub>3 \<odot> s\<^sub>2 \<odot> (s\<^sub>1 \<odot> sp))\<close>
      by (auto simp: Let_def bind_eq_Some_conv)
    from I have cenvB: \<open>cenv B\<close> and bfB: \<open>bfree_env B\<close> and ktvB: \<open>ktv_env B \<subseteq> FK\<close>
      and ftp: \<open>ftv_pend pd \<subseteq> {..< n}\<close> and frp: \<open>frv_pend pd \<subseteq> {..< n}\<close> and ktp: \<open>ktv_rows pd \<subseteq> FK\<close>
      by (auto simp: inwf_def)
    note wp = infer_pat_wf(1)[OF dp cenvB bfB ktvB]
    have le1: \<open>n \<le> n\<^sub>1\<close> using wp by simp
    have scp0: \<open>sconf sp {n ..< n\<^sub>1} {n ..< n\<^sub>1}\<close> and khp: \<open>khyg sp FK\<close>
      and bfp: \<open>bfree_sub sp\<close> and boG: \<open>binds_ok \<Gamma> n n\<^sub>1 FK\<close>
      and fpp: \<open>fresh_ok \<tau>\<^sub>p n n\<^sub>1 FK\<close> using wp by simp_all
    have scp: \<open>sconf sp {..< n\<^sub>1} {..< n\<^sub>1}\<close> by (rule sconf_mono[OF scp0]) auto
    have o_sp: \<open>outwf sp (sub_pend sp pd) FK n\<^sub>1\<close>
      by (rule outwf_of_uni[OF scp khp bfp ftp frp le1 ktp])
    have fst0: \<open>fresh_ok (sapp sp \<tau>\<^sub>0) 0 n\<^sub>1 FK\<close>
      by (rule fresh_ok_sapp0[OF F\<^sub>0 o_sp le1])
    note uf1 = uni_fresh[OF u1 fst0 fresh_ok_weaken0[OF fpp] le0]
    have le2: \<open>n\<^sub>1 \<le> n\<^sub>2\<close> using uf1 by simp
    have sc1: \<open>sconf s\<^sub>1 {..< n\<^sub>2} {..< n\<^sub>2}\<close> using uf1 by (simp add: atLeast0LessThan)
    have kh1: \<open>khyg s\<^sub>1 FK\<close> and bf1: \<open>bfree_sub s\<^sub>1\<close> using uf1 by simp_all
    have subn12: \<open>{..< n\<^sub>1} \<subseteq> {..< n\<^sub>2}\<close> using le2 by simp
    have scs: \<open>sconf (s\<^sub>1 \<odot> sp) {..< n\<^sub>2} {..< n\<^sub>2}\<close>
      by (rule sconf_scomp_mono[OF scp sc1 subn12 subn12])
    have khs: \<open>khyg (s\<^sub>1 \<odot> sp) FK\<close> by (simp add: khyg_scomp khp kh1)
    have bfs: \<open>bfree_sub (s\<^sub>1 \<odot> sp)\<close> by (simp add: bfree_sub_scomp bfp bf1)
    have le12: \<open>n \<le> n\<^sub>2\<close> using le1 le2 by simp
    have subn1: \<open>{..< n} \<subseteq> {..< n\<^sub>2}\<close> using le12 by simp
    have bo1: \<open>binds_ok (map (apsnd (sapp s\<^sub>1)) \<Gamma>) 0 n\<^sub>2 FK\<close>
      by (rule binds_ok_sapp0[OF boG sc1 kh1 bf1 le2])
    have af: \<open>frv_row (sappr (s\<^sub>1 \<odot> sp) A) \<subseteq> {..< n\<^sub>2}\<close>
      by (rule frv_sappr_sconf[OF scs]) (use I subn1 in \<open>auto simp: inwf_def\<close>)
    have ab: \<open>brv_row (sappr (s\<^sub>1 \<odot> sp) A) = {}\<close>
      by (rule bfree_sappr[OF bfs]) (use I in \<open>simp add: inwf_def\<close>)
    have pf: \<open>ftv_pend (sub_pend (s\<^sub>1 \<odot> sp) pd) \<subseteq> {..< n\<^sub>2}\<close>
      by (rule ftv_pend_sub_pend[OF scs subset_trans[OF ftp subn1]])
    have pr: \<open>frv_pend (sub_pend (s\<^sub>1 \<odot> sp) pd) \<subseteq> {..< n\<^sub>2}\<close>
      by (rule frv_pend_sub_pend[OF scs subset_trans[OF ftp subn1] subset_trans[OF frp subn1]])
    have pk: \<open>ktv_rows (sub_pend (s\<^sub>1 \<odot> sp) pd) \<subseteq> FK\<close> by (rule ktv_rows_sub_pend[OF khs ktp])
    have ib: \<open>inwf (mono_env s\<^sub>1 \<Gamma> @ sappe (s\<^sub>1 \<odot> sp) B) (sappr (s\<^sub>1 \<odot> sp) A)
               (sub_pend (s\<^sub>1 \<odot> sp) pd) FK n\<^sub>2\<close>
      unfolding mono_env_binders
      by (rule inwf_binders[OF I scs khs bfs bo1 af ab pf pr pk le12 order_refl])
    from dp refl refl refl refl u1 refl refl db ib
    have wb: \<open>n\<^sub>2 \<le> n\<^sub>3 \<and> outwf s\<^sub>2 pd\<^sub>2 FK n\<^sub>3 \<and> fresh_ok \<tau>\<^sub>b 0 n\<^sub>3 FK\<close>
      by (rule infer_arms_Cons.IH)
    have le3: \<open>n\<^sub>2 \<le> n\<^sub>3\<close> using wb by simp
    have o_b: \<open>outwf s\<^sub>2 pd\<^sub>2 FK n\<^sub>3\<close> using wb by simp
    have ftb: \<open>fresh_ok \<tau>\<^sub>b 0 n\<^sub>3 FK\<close> using wb by simp
    from o_b have sc2: \<open>sconf s\<^sub>2 {..< n\<^sub>3} {..< n\<^sub>3}\<close> and kh2: \<open>khyg s\<^sub>2 FK\<close>
      and bf2: \<open>bfree_sub s\<^sub>2\<close> and ftp2: \<open>ftv_pend pd\<^sub>2 \<subseteq> {..< n\<^sub>3}\<close>
      and frp2: \<open>frv_pend pd\<^sub>2 \<subseteq> {..< n\<^sub>3}\<close> and ktp2: \<open>ktv_rows pd\<^sub>2 \<subseteq> FK\<close> by (auto simp: outwf_def)
    have subn23: \<open>{..< n\<^sub>2} \<subseteq> {..< n\<^sub>3}\<close> using le3 by simp
    have scs2: \<open>sconf (s\<^sub>2 \<odot> (s\<^sub>1 \<odot> sp)) {..< n\<^sub>3} {..< n\<^sub>3}\<close>
      by (rule sconf_scomp_mono[OF scs sc2 subn23 subn23])
    have le13x: \<open>n \<le> n\<^sub>3\<close> using le12 le3 by simp
    have fstr: \<open>fresh_ok (sapp (s\<^sub>2 \<odot> (s\<^sub>1 \<odot> sp)) \<tau>\<^sub>r) 0 n\<^sub>3 FK\<close>
      by (rule fresh_ok_sapp0[OF F\<^sub>r
            outwf_of_uni[OF scs2 khyg_scomp[OF khs kh2] bfree_sub_scomp[OF bfs bf2] ftp frp le13x ktp]
            le13x])
    note uf2 = uni_fresh[OF u2 ftb fstr le0]
    have le4: \<open>n\<^sub>3 \<le> n\<^sub>4\<close> using uf2 by simp
    have sc3: \<open>sconf s\<^sub>3 {..< n\<^sub>4} {..< n\<^sub>4}\<close> using uf2 by (simp add: atLeast0LessThan)
    have kh3: \<open>khyg s\<^sub>3 FK\<close> and bf3: \<open>bfree_sub s\<^sub>3\<close> using uf2 by simp_all
    have subn34: \<open>{..< n\<^sub>3} \<subseteq> {..< n\<^sub>4}\<close> using le4 by simp
    have scs3: \<open>sconf (s\<^sub>3 \<odot> s\<^sub>2 \<odot> (s\<^sub>1 \<odot> sp)) {..< n\<^sub>4} {..< n\<^sub>4}\<close>
      using sconf_scomp_mono[OF scs2 sc3 subn34 subn34] by (simp add: scomp_assoc)
    have khs3: \<open>khyg (s\<^sub>3 \<odot> s\<^sub>2 \<odot> (s\<^sub>1 \<odot> sp)) FK\<close>
      by (simp add: khyg_scomp khs kh2 kh3 scomp_assoc)
    have bfs3: \<open>bfree_sub (s\<^sub>3 \<odot> s\<^sub>2 \<odot> (s\<^sub>1 \<odot> sp))\<close>
      by (simp add: bfree_sub_scomp bfs bf2 bf3 scomp_assoc)
    have le13: \<open>n \<le> n\<^sub>4\<close> using le12 le3 le4 by simp
    have subn4: \<open>{..< n} \<subseteq> {..< n\<^sub>4}\<close> using le13 by simp
    have os3: \<open>outwf (s\<^sub>3 \<odot> s\<^sub>2 \<odot> (s\<^sub>1 \<odot> sp)) (sub_pend s\<^sub>3 pd\<^sub>2) FK n\<^sub>4\<close>
      unfolding outwf_def using scs3 khs3 bfs3
        ftv_pend_sub_pend[OF sc3 subset_trans[OF ftp2 subn34]]
        frv_pend_sub_pend[OF sc3 subset_trans[OF ftp2 subn34] subset_trans[OF frp2 subn34]]
        ktv_rows_sub_pend[OF kh3 ktp2]
      by simp
    have iarms: \<open>inwf (sappe (s\<^sub>3 \<odot> s\<^sub>2 \<odot> (s\<^sub>1 \<odot> sp)) B)
                  (sappr (s\<^sub>3 \<odot> s\<^sub>2 \<odot> (s\<^sub>1 \<odot> sp)) A) (sub_pend s\<^sub>3 pd\<^sub>2) FK n\<^sub>4\<close>
      by (rule inwf_step[OF I os3 le13])
    have f0a: \<open>fresh_ok (sapp (s\<^sub>3 \<odot> s\<^sub>2 \<odot> (s\<^sub>1 \<odot> sp)) \<tau>\<^sub>0) 0 n\<^sub>4 FK\<close>
      by (rule fresh_ok_sapp0[OF F\<^sub>0 os3 le13])
    have fra: \<open>fresh_ok (sapp (s\<^sub>3 \<odot> s\<^sub>2 \<odot> (s\<^sub>1 \<odot> sp)) \<tau>\<^sub>r) 0 n\<^sub>4 FK\<close>
      by (rule fresh_ok_sapp0[OF F\<^sub>r os3 le13])
    from dp refl refl refl refl u1 refl refl db refl refl refl refl u2 refl refl da iarms f0a fra
    have wa: \<open>n\<^sub>4 \<le> n' \<and> outwf s\<^sub>4 pd' FK n'
        \<and> fresh_ok (sapp s\<^sub>4 (sapp (s\<^sub>3 \<odot> s\<^sub>2 \<odot> (s\<^sub>1 \<odot> sp)) \<tau>\<^sub>r)) 0 n' FK\<close>
      by (rule infer_arms_Cons.IH)
    have le5: \<open>n\<^sub>4 \<le> n'\<close> using wa by simp
    have o_a: \<open>outwf s\<^sub>4 pd' FK n'\<close> using wa by simp
    have fresh: \<open>fresh_ok (sapp s \<tau>\<^sub>r) 0 n' FK\<close>
      using wa[THEN conjunct2, THEN conjunct2] unfolding se by (simp add: sapp_scomp)
    have le: \<open>n \<le> n'\<close> using le13 le5 by simp
    show ?case using se le fresh outwf_scomp[OF os3 o_a le5] by simp
  next
    case (infer_cls_Cons_HOp uf B A pd nm \<tau>\<^sub>0 targs opn ps k b cls n s cls'x \<tau> pd' n' FK)
    have E: \<open>infer_cls uf B A pd nm \<tau>\<^sub>0 targs (HOp opn ps k b # cls) n
        = Some (s, cls'x, \<tau>, pd', n')\<close>
      and I: \<open>inwf B A pd FK n\<close> and F\<^sub>0: \<open>fresh_ok \<tau>\<^sub>0 0 n FK\<close>
      and F\<^sub>t: \<open>fresh_ok targs 0 n FK\<close> by (fact infer_cls_Cons_HOp.prems)+
    define eps
      where \<open>eps sq = (if nm then sappr sq A else canon_row (rext (hlabels B cls) (sappr sq A)))\<close>
      for sq
    have \<open>\<exists>l ps\<^sub>e \<tau>\<^sub>1\<^sub>0 \<tau>\<^sub>2\<^sub>0 args.
            tlookup B [n_txt opn] = Some (TEop l ps\<^sub>e \<tau>\<^sub>1\<^sub>0 \<tau>\<^sub>2\<^sub>0) \<and> untuple targs = Some args \<and>
            length args = length ps\<^sub>e\<close>
      using E
      by (cases \<open>tlookup B [n_txt opn]\<close>; cases \<open>untuple targs\<close>;
          simp split: tentry.split_asm if_split_asm)
    then obtain l ps\<^sub>e \<tau>\<^sub>1\<^sub>0 \<tau>\<^sub>2\<^sub>0 args
      where lk: \<open>tlookup B [n_txt opn] = Some (TEop l ps\<^sub>e \<tau>\<^sub>1\<^sub>0 \<tau>\<^sub>2\<^sub>0)\<close>
      and ta: \<open>untuple targs = Some args\<close>
      and lc: \<open>length args = length ps\<^sub>e\<close> by blast
    have ta': \<open>targs = tuple args\<close> using ta by simp
    define \<tau>\<^sub>1 where \<open>\<tau>\<^sub>1 = op_inst ps\<^sub>e args \<tau>\<^sub>1\<^sub>0\<close>
    define \<tau>\<^sub>2 where \<open>\<tau>\<^sub>2 = op_inst ps\<^sub>e args \<tau>\<^sub>2\<^sub>0\<close>
    have lkm: \<open>map_of B (n_txt opn) = Some (TEop l ps\<^sub>e \<tau>\<^sub>1\<^sub>0 \<tau>\<^sub>2\<^sub>0)\<close> using lk by simp
    from E obtain sp \<tau>s \<Gamma> n\<^sub>1 s\<^sub>1 n\<^sub>2 s\<^sub>2 b'' \<tau>\<^sub>b pd\<^sub>2 n\<^sub>3 s\<^sub>3 n\<^sub>4 s\<^sub>4 cls'' ps\<^sub>x where
      dps: \<open>infer_pats uf B ps n = Some (sp, ps\<^sub>x, \<tau>s, \<Gamma>, n\<^sub>1)\<close> and
      u1: \<open>uni uf (fn_ty \<tau>s) (sapp sp \<tau>\<^sub>1) n\<^sub>1 = Some (s\<^sub>1, n\<^sub>2)\<close> and
      db: \<open>infer uf ((case k of None \<Rightarrow> mono_env s\<^sub>1 \<Gamma>
              | Some kn \<Rightarrow> (n_txt kn, TEval (kmono (TFn (sapp (s\<^sub>1 \<odot> sp) \<tau>\<^sub>2) (eps (s\<^sub>1 \<odot> sp))
                              (sapp (s\<^sub>1 \<odot> sp) \<tau>\<^sub>0)))) # mono_env s\<^sub>1 \<Gamma>) @ sappe (s\<^sub>1 \<odot> sp) B)
              (eps (s\<^sub>1 \<odot> sp)) (sub_pend (s\<^sub>1 \<odot> sp) pd) b n\<^sub>2 = Some (s\<^sub>2, b'', \<tau>\<^sub>b, pd\<^sub>2, n\<^sub>3)\<close> and
      u2: \<open>uni uf \<tau>\<^sub>b (case k of None \<Rightarrow> sapp (s\<^sub>2 \<odot> (s\<^sub>1 \<odot> sp)) \<tau>\<^sub>2
              | Some _ \<Rightarrow> sapp s\<^sub>2 (sapp (s\<^sub>1 \<odot> sp) \<tau>\<^sub>0)) n\<^sub>3 = Some (s\<^sub>3, n\<^sub>4)\<close> and
      dc: \<open>infer_cls uf (sappe (s\<^sub>3 \<odot> s\<^sub>2 \<odot> (s\<^sub>1 \<odot> sp)) B) (sappr (s\<^sub>3 \<odot> s\<^sub>2 \<odot> (s\<^sub>1 \<odot> sp)) A)
              (sub_pend s\<^sub>3 pd\<^sub>2) nm (sapp (s\<^sub>3 \<odot> s\<^sub>2 \<odot> (s\<^sub>1 \<odot> sp)) \<tau>\<^sub>0)
              (sapp (s\<^sub>3 \<odot> s\<^sub>2 \<odot> (s\<^sub>1 \<odot> sp)) targs) cls n\<^sub>4
              = Some (s\<^sub>4, cls'', \<tau>, pd', n')\<close> and
      se: \<open>s = s\<^sub>4 \<odot> (s\<^sub>3 \<odot> s\<^sub>2 \<odot> (s\<^sub>1 \<odot> sp))\<close>
      by (auto simp: lkm ta ta' lc eps_def[symmetric] \<tau>\<^sub>1_def[symmetric] \<tau>\<^sub>2_def[symmetric] Let_def
                     bind_eq_Some_conv split: if_split_asm)
    have covk: \<open>covers (sappe (s\<^sub>1 \<odot> sp) B) (sapp s\<^sub>1 (fn_ty \<tau>s)) [fn_pat ps]
        \<and> (case k of None \<Rightarrow> True
             | Some kn \<Rightarrow> n_txt kn \<notin> set (map fst \<Gamma>) \<and> nm_ok (n_txt kn))\<close>
      using E
      by (simp add: lkm ta ta' lc dps u1 \<tau>\<^sub>1_def[symmetric] \<tau>\<^sub>2_def[symmetric] Let_def
          split: if_split_asm)
    note cov = covk[THEN conjunct1]
    from I have cenvB: \<open>cenv B\<close> and bfB: \<open>bfree_env B\<close> and ktvB: \<open>ktv_env B \<subseteq> FK\<close>
      and frA: \<open>frv_row A \<subseteq> {..< n}\<close> and brA: \<open>brv_row A = {}\<close>
      and ftp: \<open>ftv_pend pd \<subseteq> {..< n}\<close> and frp: \<open>frv_pend pd \<subseteq> {..< n}\<close> and ktp: \<open>ktv_rows pd \<subseteq> FK\<close> by (auto simp: inwf_def)
    note wp = infer_pat_wf(4)[OF dps cenvB bfB ktvB]
    have le1: \<open>n \<le> n\<^sub>1\<close> using wp by simp
    have scp0: \<open>sconf sp {n ..< n\<^sub>1} {n ..< n\<^sub>1}\<close> and khp: \<open>khyg sp FK\<close> and bfp: \<open>bfree_sub sp\<close>
      and boG: \<open>binds_ok \<Gamma> n n\<^sub>1 FK\<close> and \<tau>sf: \<open>\<forall>\<tau>' \<in> set \<tau>s. fresh_ok \<tau>' n n\<^sub>1 FK\<close>
      using wp by simp_all
    have scp: \<open>sconf sp {..< n\<^sub>1} {..< n\<^sub>1}\<close> by (rule sconf_mono[OF scp0]) auto
    have o_sp: \<open>outwf sp (sub_pend sp pd) FK n\<^sub>1\<close> by (rule outwf_of_uni[OF scp khp bfp ftp frp le1 ktp])
    have \<tau>sf0: \<open>\<forall>\<tau>' \<in> set \<tau>s. fresh_ok \<tau>' 0 n\<^sub>1 FK\<close> using \<tau>sf by (blast intro: fresh_ok_weaken0)
    have ffn: \<open>fresh_ok (fn_ty \<tau>s) 0 n\<^sub>1 FK\<close> by (rule fresh_ok_fn_ty[OF \<tau>sf0])
    have ct0: \<open>ftv \<tau>\<^sub>1\<^sub>0 = {}\<close> \<open>frv \<tau>\<^sub>1\<^sub>0 = {}\<close> \<open>ftv \<tau>\<^sub>2\<^sub>0 = {}\<close> \<open>frv \<tau>\<^sub>2\<^sub>0 = {}\<close>
      using cenv_tlookup_nonval[OF cenvB lk] by auto
    have kt0: \<open>ktv \<tau>\<^sub>1\<^sub>0 \<subseteq> FK\<close> \<open>ktv \<tau>\<^sub>2\<^sub>0 \<subseteq> FK\<close> \<open>btv \<tau>\<^sub>1\<^sub>0 \<subseteq> set ps\<^sub>e\<close> \<open>btv \<tau>\<^sub>2\<^sub>0 \<subseteq> set ps\<^sub>e\<close>
      \<open>brv \<tau>\<^sub>1\<^sub>0 = {}\<close> \<open>brv \<tau>\<^sub>2\<^sub>0 = {}\<close>
      using ktv_env_tlookup[OF lk] ktvB bfree_env_tlookup[OF bfB lk] by auto
    have fargs: \<open>\<forall>t \<in> set args. fresh_ok t 0 n FK\<close>
      using F\<^sub>t unfolding ta' by (auto simp: fresh_ok_def bfree_def)
    have fo1: \<open>fresh_ok \<tau>\<^sub>1 0 n FK\<close> and fo2: \<open>fresh_ok \<tau>\<^sub>2 0 n FK\<close> unfolding \<tau>\<^sub>1_def \<tau>\<^sub>2_def
      by (rule op_inst_fresh[OF _ _ _ _ _ lc fargs]; use ct0 kt0 in simp)+
    have f\<tau>1: \<open>fresh_ok (sapp sp \<tau>\<^sub>1) 0 n\<^sub>1 FK\<close> by (rule fresh_ok_sapp0[OF fo1 o_sp le1])
    note uf1 = uni_fresh[OF u1 ffn f\<tau>1 le0]
    have le2: \<open>n\<^sub>1 \<le> n\<^sub>2\<close> using uf1 by simp
    have sc1: \<open>sconf s\<^sub>1 {..< n\<^sub>2} {..< n\<^sub>2}\<close> using uf1 by (simp add: atLeast0LessThan)
    have kh1: \<open>khyg s\<^sub>1 FK\<close> and bf1: \<open>bfree_sub s\<^sub>1\<close> using uf1 by simp_all
    have subn12: \<open>{..< n\<^sub>1} \<subseteq> {..< n\<^sub>2}\<close> using le2 by simp
    have scs: \<open>sconf (s\<^sub>1 \<odot> sp) {..< n\<^sub>2} {..< n\<^sub>2}\<close>
      by (rule sconf_scomp_mono[OF scp sc1 subn12 subn12])
    have khs: \<open>khyg (s\<^sub>1 \<odot> sp) FK\<close> by (rule khyg_scomp[OF khp kh1])
    have bfs: \<open>bfree_sub (s\<^sub>1 \<odot> sp)\<close> by (rule bfree_sub_scomp[OF bfp bf1])
    have le12: \<open>n \<le> n\<^sub>2\<close> using le1 le2 by simp
    have subn1: \<open>{..< n} \<subseteq> {..< n\<^sub>2}\<close> using le12 by simp
    have bo1: \<open>binds_ok (map (apsnd (sapp s\<^sub>1)) \<Gamma>) 0 n\<^sub>2 FK\<close>
      by (rule binds_ok_sapp0[OF boG sc1 kh1 bf1 le2])
    have afe: \<open>frv_row (eps (s\<^sub>1 \<odot> sp)) \<subseteq> {..< n\<^sub>2}\<close>
      unfolding eps_def
      by (cases nm) (simp add: rext_def, rule frv_sappr_sconf[OF scs subset_trans[OF frA subn1]])+
    have abe: \<open>brv_row (eps (s\<^sub>1 \<odot> sp)) = {}\<close>
      unfolding eps_def by (cases nm) (simp_all add: rext_def bfree_sappr[OF bfs brA])
    have pf: \<open>ftv_pend (sub_pend (s\<^sub>1 \<odot> sp) pd) \<subseteq> {..< n\<^sub>2}\<close>
      by (rule ftv_pend_sub_pend[OF scs subset_trans[OF ftp subn1]])
    have pr: \<open>frv_pend (sub_pend (s\<^sub>1 \<odot> sp) pd) \<subseteq> {..< n\<^sub>2}\<close>
      by (rule frv_pend_sub_pend[OF scs subset_trans[OF ftp subn1] subset_trans[OF frp subn1]])
    have pk: \<open>ktv_rows (sub_pend (s\<^sub>1 \<odot> sp) pd) \<subseteq> FK\<close> by (rule ktv_rows_sub_pend[OF khs ktp])
    have o_s: \<open>outwf (s\<^sub>1 \<odot> sp) (sub_pend (s\<^sub>1 \<odot> sp) pd) FK n\<^sub>2\<close>
      by (rule outwf_of_uni[OF scs khs bfs ftp frp le12 ktp])
    have f\<tau>0: \<open>fresh_ok (sapp (s\<^sub>1 \<odot> sp) \<tau>\<^sub>0) 0 n\<^sub>2 FK\<close>
      by (rule fresh_ok_sapp0[OF F\<^sub>0 o_s le12])
    have f\<tau>2s: \<open>fresh_ok (sapp (s\<^sub>1 \<odot> sp) \<tau>\<^sub>2) 0 n\<^sub>2 FK\<close> by (rule fresh_ok_sapp0[OF fo2 o_s le12])
    have f\<tau>2: \<open>fresh_ok \<tau>\<^sub>2 0 n\<^sub>2 FK\<close> by (rule fresh_ok_mono[OF fo2 le_refl le12])
    have ib: \<open>inwf ((case k of None \<Rightarrow> mono_env s\<^sub>1 \<Gamma>
              | Some kn \<Rightarrow> (n_txt kn, TEval (kmono (TFn (sapp (s\<^sub>1 \<odot> sp) \<tau>\<^sub>2) (eps (s\<^sub>1 \<odot> sp))
                              (sapp (s\<^sub>1 \<odot> sp) \<tau>\<^sub>0)))) # mono_env s\<^sub>1 \<Gamma>) @ sappe (s\<^sub>1 \<odot> sp) B)
              (eps (s\<^sub>1 \<odot> sp)) (sub_pend (s\<^sub>1 \<odot> sp) pd) FK n\<^sub>2\<close>
    proof (cases k)
      case None
      show ?thesis unfolding None option.case mono_env_binders
        by (rule inwf_binders[OF I scs khs bfs bo1 afe abe pf pr pk le12 order_refl])
    next
      case (Some kn)
      define G' where \<open>G' = (n_txt kn, TFn (sapp (s\<^sub>1 \<odot> sp) \<tau>\<^sub>2) (eps (s\<^sub>1 \<odot> sp))
                        (sapp (s\<^sub>1 \<odot> sp) \<tau>\<^sub>0)) # map (apsnd (sapp s\<^sub>1)) \<Gamma>\<close>
      have beq: \<open>(n_txt kn, TEval (kmono (TFn (sapp (s\<^sub>1 \<odot> sp) \<tau>\<^sub>2) (eps (s\<^sub>1 \<odot> sp))
                    (sapp (s\<^sub>1 \<odot> sp) \<tau>\<^sub>0)))) # mono_env s\<^sub>1 \<Gamma> = binders G'\<close>
        by (simp add: G'_def mono_env_binders)
      have bok: \<open>binds_ok G' 0 n\<^sub>2 FK\<close>
        unfolding G'_def by (simp add: fresh_ok_TFn[OF f\<tau>2s f\<tau>0 afe abe] bo1)
      show ?thesis unfolding Some option.case beq
        by (rule inwf_binders[OF I scs khs bfs bok afe abe pf pr pk le12 order_refl])
    qed
    have wb: \<open>n\<^sub>2 \<le> n\<^sub>3 \<and> outwf s\<^sub>2 pd\<^sub>2 FK n\<^sub>3 \<and> fresh_ok \<tau>\<^sub>b 0 n\<^sub>3 FK\<close>
      by (rule infer_cls_Cons_HOp.IH)
        (rule lk ta dps u1 covk db ib refl eps_def \<tau>\<^sub>1_def \<tau>\<^sub>2_def lc)+
    have le3: \<open>n\<^sub>2 \<le> n\<^sub>3\<close> using wb by simp
    have o_b: \<open>outwf s\<^sub>2 pd\<^sub>2 FK n\<^sub>3\<close> using wb by simp
    have ftb: \<open>fresh_ok \<tau>\<^sub>b 0 n\<^sub>3 FK\<close> using wb by simp
    from o_b have sc2: \<open>sconf s\<^sub>2 {..< n\<^sub>3} {..< n\<^sub>3}\<close> and kh2: \<open>khyg s\<^sub>2 FK\<close>
      and bf2: \<open>bfree_sub s\<^sub>2\<close> and ftp2: \<open>ftv_pend pd\<^sub>2 \<subseteq> {..< n\<^sub>3}\<close>
      and frp2: \<open>frv_pend pd\<^sub>2 \<subseteq> {..< n\<^sub>3}\<close> and ktp2: \<open>ktv_rows pd\<^sub>2 \<subseteq> FK\<close> by (auto simp: outwf_def)
    have subn23: \<open>{..< n\<^sub>2} \<subseteq> {..< n\<^sub>3}\<close> using le3 by simp
    have scs2: \<open>sconf (s\<^sub>2 \<odot> (s\<^sub>1 \<odot> sp)) {..< n\<^sub>3} {..< n\<^sub>3}\<close>
      by (rule sconf_scomp_mono[OF scs sc2 subn23 subn23])
    have le13: \<open>n \<le> n\<^sub>3\<close> using le12 le3 by simp
    have os: \<open>outwf (s\<^sub>2 \<odot> (s\<^sub>1 \<odot> sp)) pd\<^sub>2 FK n\<^sub>3\<close> by (rule outwf_scomp[OF o_s o_b le3])
    have fasc: \<open>fresh_ok (case k of None \<Rightarrow> sapp (s\<^sub>2 \<odot> (s\<^sub>1 \<odot> sp)) \<tau>\<^sub>2
                | Some _ \<Rightarrow> sapp s\<^sub>2 (sapp (s\<^sub>1 \<odot> sp) \<tau>\<^sub>0)) 0 n\<^sub>3 FK\<close>
    proof (cases k)
      case None
      show ?thesis unfolding None option.case by (rule fresh_ok_sapp0[OF f\<tau>2 os le3])
    next
      case (Some kn)
      show ?thesis unfolding Some option.case by (rule fresh_ok_sapp0[OF f\<tau>0 o_b le3])
    qed
    note uf2 = uni_fresh[OF u2 ftb fasc le0]
    have le4: \<open>n\<^sub>3 \<le> n\<^sub>4\<close> using uf2 by simp
    have sc3: \<open>sconf s\<^sub>3 {..< n\<^sub>4} {..< n\<^sub>4}\<close> using uf2 by (simp add: atLeast0LessThan)
    have kh3: \<open>khyg s\<^sub>3 FK\<close> and bf3: \<open>bfree_sub s\<^sub>3\<close> using uf2 by simp_all
    have subn34: \<open>{..< n\<^sub>3} \<subseteq> {..< n\<^sub>4}\<close> using le4 by simp
    have scs3: \<open>sconf (s\<^sub>3 \<odot> s\<^sub>2 \<odot> (s\<^sub>1 \<odot> sp)) {..< n\<^sub>4} {..< n\<^sub>4}\<close>
      using sconf_scomp_mono[OF scs2 sc3 subn34 subn34] by (simp add: scomp_assoc)
    have khs3: \<open>khyg (s\<^sub>3 \<odot> s\<^sub>2 \<odot> (s\<^sub>1 \<odot> sp)) FK\<close>
      using khyg_scomp[OF khyg_scomp[OF khs kh2] kh3] by (simp add: scomp_assoc)
    have bfs3: \<open>bfree_sub (s\<^sub>3 \<odot> s\<^sub>2 \<odot> (s\<^sub>1 \<odot> sp))\<close>
      using bfree_sub_scomp[OF bfree_sub_scomp[OF bfs bf2] bf3] by (simp add: scomp_assoc)
    have le14: \<open>n \<le> n\<^sub>4\<close> using le13 le4 by simp
    have os': \<open>outwf (s\<^sub>3 \<odot> s\<^sub>2 \<odot> (s\<^sub>1 \<odot> sp)) (sub_pend s\<^sub>3 pd\<^sub>2) FK n\<^sub>4\<close>
      unfolding outwf_def using scs3 khs3 bfs3
        ftv_pend_sub_pend[OF sc3 subset_trans[OF ftp2 subn34]]
        frv_pend_sub_pend[OF sc3 subset_trans[OF ftp2 subn34] subset_trans[OF frp2 subn34]]
        ktv_rows_sub_pend[OF kh3 ktp2] by simp
    have ic: \<open>inwf (sappe (s\<^sub>3 \<odot> s\<^sub>2 \<odot> (s\<^sub>1 \<odot> sp)) B) (sappr (s\<^sub>3 \<odot> s\<^sub>2 \<odot> (s\<^sub>1 \<odot> sp)) A)
                (sub_pend s\<^sub>3 pd\<^sub>2) FK n\<^sub>4\<close>
      by (rule inwf_step[OF I os' le14])
    have f\<tau>0b: \<open>fresh_ok (sapp (s\<^sub>3 \<odot> s\<^sub>2 \<odot> (s\<^sub>1 \<odot> sp)) \<tau>\<^sub>0) 0 n\<^sub>4 FK\<close>
      by (rule fresh_ok_sapp0[OF F\<^sub>0 os' le14])
    have ftb': \<open>fresh_ok (sapp (s\<^sub>3 \<odot> s\<^sub>2 \<odot> (s\<^sub>1 \<odot> sp)) targs) 0 n\<^sub>4 FK\<close>
      by (rule fresh_ok_sapp0[OF F\<^sub>t os' le14])
    have wc: \<open>n\<^sub>4 \<le> n' \<and> outwf s\<^sub>4 pd' FK n' \<and> fresh_ok \<tau> 0 n' FK\<close>
      by (rule infer_cls_Cons_HOp.IH)
        (rule lk ta dps u1 covk db u2 dc ic f\<tau>0b ftb' refl eps_def \<tau>\<^sub>1_def \<tau>\<^sub>2_def lc)+
    have le5: \<open>n\<^sub>4 \<le> n'\<close> using wc by simp
    have o_c: \<open>outwf s\<^sub>4 pd' FK n'\<close> using wc by simp
    have fresh: \<open>fresh_ok \<tau> 0 n' FK\<close> using wc by simp
    have le: \<open>n \<le> n'\<close> using le14 le5 by simp
    show ?case using se le fresh outwf_scomp[OF os' o_c le5] by simp
  next
    case (infer_cls_Cons_HFin uf B A pd nm \<tau>\<^sub>0 targs b cls n s cls'x \<tau> pd' n' FK)
    have E: \<open>infer_cls uf B A pd nm \<tau>\<^sub>0 targs (HFin b # cls) n = Some (s, cls'x, \<tau>, pd', n')\<close>
      and I: \<open>inwf B A pd FK n\<close> and F\<^sub>0: \<open>fresh_ok \<tau>\<^sub>0 0 n FK\<close>
      and F\<^sub>t: \<open>fresh_ok targs 0 n FK\<close> by (fact infer_cls_Cons_HFin.prems)+
    from E obtain s\<^sub>1 b'' \<tau>\<^sub>f pd\<^sub>1 n\<^sub>1 s\<^sub>2 n\<^sub>2 s\<^sub>3 cls'' where
      d1: \<open>infer uf B A pd b n = Some (s\<^sub>1, b'', \<tau>\<^sub>f, pd\<^sub>1, n\<^sub>1)\<close> and
      u1: \<open>uni uf \<tau>\<^sub>f unit_ty n\<^sub>1 = Some (s\<^sub>2, n\<^sub>2)\<close> and
      dc: \<open>infer_cls uf (sappe (s\<^sub>2 \<odot> s\<^sub>1) B) (sappr (s\<^sub>2 \<odot> s\<^sub>1) A) (sub_pend s\<^sub>2 pd\<^sub>1) nm
             (sapp (s\<^sub>2 \<odot> s\<^sub>1) \<tau>\<^sub>0) (sapp (s\<^sub>2 \<odot> s\<^sub>1) targs) cls n\<^sub>2
             = Some (s\<^sub>3, cls'', \<tau>, pd', n')\<close> and
      se: \<open>s = s\<^sub>3 \<odot> (s\<^sub>2 \<odot> s\<^sub>1)\<close>
      by (auto simp: Let_def bind_eq_Some_conv)
    from d1 I have \<open>n \<le> n\<^sub>1 \<and> outwf s\<^sub>1 pd\<^sub>1 FK n\<^sub>1 \<and> fresh_ok \<tau>\<^sub>f 0 n\<^sub>1 FK\<close>
      by (rule infer_cls_Cons_HFin.IH)
    then have le1: \<open>n \<le> n\<^sub>1\<close> and o1: \<open>outwf s\<^sub>1 pd\<^sub>1 FK n\<^sub>1\<close>
      and f1: \<open>fresh_ok \<tau>\<^sub>f 0 n\<^sub>1 FK\<close> by simp_all
    from o1 have ftp1: \<open>ftv_pend pd\<^sub>1 \<subseteq> {..< n\<^sub>1}\<close> and frp1: \<open>frv_pend pd\<^sub>1 \<subseteq> {..< n\<^sub>1}\<close> and ktp1: \<open>ktv_rows pd\<^sub>1 \<subseteq> FK\<close>
      by (auto simp: outwf_def)
    note uf1 = uni_fresh[OF u1 fresh_ok_mono[OF f1 le_refl le_refl] fresh_ok_unit le0]
    have le2: \<open>n\<^sub>1 \<le> n\<^sub>2\<close> using uf1 by simp
    have sc2: \<open>sconf s\<^sub>2 {..< n\<^sub>2} {..< n\<^sub>2}\<close> using uf1 by (simp add: atLeast0LessThan)
    have kh2: \<open>khyg s\<^sub>2 FK\<close> and bf2: \<open>bfree_sub s\<^sub>2\<close> using uf1 by simp_all
    have o2': \<open>outwf s\<^sub>2 (sub_pend s\<^sub>2 pd\<^sub>1) FK n\<^sub>2\<close>
      by (rule outwf_of_uni[OF sc2 kh2 bf2 ftp1 frp1 le2 ktp1])
    have os: \<open>outwf (s\<^sub>2 \<odot> s\<^sub>1) (sub_pend s\<^sub>2 pd\<^sub>1) FK n\<^sub>2\<close>
      by (rule outwf_scomp[OF o1 o2' le2])
    have le12: \<open>n \<le> n\<^sub>2\<close> using le1 le2 by simp
    have ic: \<open>inwf (sappe (s\<^sub>2 \<odot> s\<^sub>1) B) (sappr (s\<^sub>2 \<odot> s\<^sub>1) A) (sub_pend s\<^sub>2 pd\<^sub>1) FK n\<^sub>2\<close>
      by (rule inwf_step[OF I os le12])
    have f0: \<open>fresh_ok (sapp (s\<^sub>2 \<odot> s\<^sub>1) \<tau>\<^sub>0) 0 n\<^sub>2 FK\<close>
      by (rule fresh_ok_sapp0[OF F\<^sub>0 os le12])
    have ft: \<open>fresh_ok (sapp (s\<^sub>2 \<odot> s\<^sub>1) targs) 0 n\<^sub>2 FK\<close>
      by (rule fresh_ok_sapp0[OF F\<^sub>t os le12])
    from d1 refl refl refl refl u1 refl refl dc ic f0 ft
    have wc: \<open>n\<^sub>2 \<le> n' \<and> outwf s\<^sub>3 pd' FK n' \<and> fresh_ok \<tau> 0 n' FK\<close>
      by (rule infer_cls_Cons_HFin.IH)
    have le3: \<open>n\<^sub>2 \<le> n'\<close> and o_c: \<open>outwf s\<^sub>3 pd' FK n'\<close> and fresh: \<open>fresh_ok \<tau> 0 n' FK\<close>
      using wc by simp_all
    have le: \<open>n \<le> n'\<close> using le12 le3 by simp
    show ?case using se le fresh outwf_scomp[OF os o_c le3] by simp
  next
    case (infer_cls_Cons_HRet uf B A pd nm \<tau>\<^sub>0 targs p b cls n s cls'x \<tau> pd' n' FK)
    have E: \<open>infer_cls uf B A pd nm \<tau>\<^sub>0 targs (HRet p b # cls) n = Some (s, cls'x, \<tau>, pd', n')\<close>
      and I: \<open>inwf B A pd FK n\<close> and F\<^sub>0: \<open>fresh_ok \<tau>\<^sub>0 0 n FK\<close>
      and F\<^sub>t: \<open>fresh_ok targs 0 n FK\<close> by (fact infer_cls_Cons_HRet.prems)+
    define eps
      where \<open>eps sq = (if nm then sappr sq A else canon_row (rext (hlabels B cls) (sappr sq A)))\<close>
      for sq
    from E obtain sp \<tau>\<^sub>p \<Gamma> n\<^sub>1 s\<^sub>1 n\<^sub>2 s\<^sub>2 b'' \<tau>' pd\<^sub>2 n\<^sub>3 s\<^sub>3 cls'' p\<^sub>x where
      dp: \<open>infer_pat uf B p n = Some (sp, p\<^sub>x, \<tau>\<^sub>p, \<Gamma>, n\<^sub>1)\<close> and
      u1: \<open>uni uf (sapp sp \<tau>\<^sub>0) \<tau>\<^sub>p n\<^sub>1 = Some (s\<^sub>1, n\<^sub>2)\<close> and
      db: \<open>infer uf (mono_env s\<^sub>1 \<Gamma> @ sappe (s\<^sub>1 \<odot> sp) B)
             (eps (s\<^sub>1 \<odot> sp)) (sub_pend (s\<^sub>1 \<odot> sp) pd) b n\<^sub>2
             = Some (s\<^sub>2, b'', \<tau>', pd\<^sub>2, n\<^sub>3)\<close> and
      dc: \<open>infer_cls uf (sappe (s\<^sub>2 \<odot> (s\<^sub>1 \<odot> sp)) B) (sappr (s\<^sub>2 \<odot> (s\<^sub>1 \<odot> sp)) A) pd\<^sub>2 nm \<tau>'
             (sapp (s\<^sub>2 \<odot> (s\<^sub>1 \<odot> sp)) targs) cls n\<^sub>3 = Some (s\<^sub>3, cls'', \<tau>, pd', n')\<close> and
      se: \<open>s = s\<^sub>3 \<odot> (s\<^sub>2 \<odot> (s\<^sub>1 \<odot> sp))\<close>
      by (auto simp: eps_def[symmetric] Let_def bind_eq_Some_conv split: if_split_asm)
    have covn: \<open>covers (sappe (s\<^sub>1 \<odot> sp) B) (sapp s\<^sub>1 \<tau>\<^sub>p) [p] \<and> (nm \<longrightarrow> hlabels B cls = [])\<close>
      using E
      by (simp add: dp u1 Let_def split: if_split_asm
          del: sapp.simps sappe.simps sappr.simps sapps.simps)
    note cov = covn[THEN conjunct1]
    from I have cenvB: \<open>cenv B\<close> and bfB: \<open>bfree_env B\<close> and ktvB: \<open>ktv_env B \<subseteq> FK\<close>
      and frA: \<open>frv_row A \<subseteq> {..< n}\<close> and brA: \<open>brv_row A = {}\<close>
      and ftp: \<open>ftv_pend pd \<subseteq> {..< n}\<close> and frp: \<open>frv_pend pd \<subseteq> {..< n}\<close> and ktp: \<open>ktv_rows pd \<subseteq> FK\<close> by (auto simp: inwf_def)
    note wp = infer_pat_wf(1)[OF dp cenvB bfB ktvB]
    have le1: \<open>n \<le> n\<^sub>1\<close> using wp by simp
    have scp0: \<open>sconf sp {n ..< n\<^sub>1} {n ..< n\<^sub>1}\<close> and khp: \<open>khyg sp FK\<close> and bfp: \<open>bfree_sub sp\<close>
      and boG: \<open>binds_ok \<Gamma> n n\<^sub>1 FK\<close> and fpp: \<open>fresh_ok \<tau>\<^sub>p n n\<^sub>1 FK\<close> using wp by simp_all
    have scp: \<open>sconf sp {..< n\<^sub>1} {..< n\<^sub>1}\<close> by (rule sconf_mono[OF scp0]) auto
    have o_sp: \<open>outwf sp (sub_pend sp pd) FK n\<^sub>1\<close> by (rule outwf_of_uni[OF scp khp bfp ftp frp le1 ktp])
    have fst0: \<open>fresh_ok (sapp sp \<tau>\<^sub>0) 0 n\<^sub>1 FK\<close> by (rule fresh_ok_sapp0[OF F\<^sub>0 o_sp le1])
    note uf1 = uni_fresh[OF u1 fst0 fresh_ok_weaken0[OF fpp] le0]
    have le2: \<open>n\<^sub>1 \<le> n\<^sub>2\<close> using uf1 by simp
    have sc1: \<open>sconf s\<^sub>1 {..< n\<^sub>2} {..< n\<^sub>2}\<close> using uf1 by (simp add: atLeast0LessThan)
    have kh1: \<open>khyg s\<^sub>1 FK\<close> and bf1: \<open>bfree_sub s\<^sub>1\<close> using uf1 by simp_all
    have subn12: \<open>{..< n\<^sub>1} \<subseteq> {..< n\<^sub>2}\<close> using le2 by simp
    have scs: \<open>sconf (s\<^sub>1 \<odot> sp) {..< n\<^sub>2} {..< n\<^sub>2}\<close>
      by (rule sconf_scomp_mono[OF scp sc1 subn12 subn12])
    have khs: \<open>khyg (s\<^sub>1 \<odot> sp) FK\<close> by (simp add: khyg_scomp khp kh1)
    have bfs: \<open>bfree_sub (s\<^sub>1 \<odot> sp)\<close> by (simp add: bfree_sub_scomp bfp bf1)
    have le12: \<open>n \<le> n\<^sub>2\<close> using le1 le2 by simp
    have subn1: \<open>{..< n} \<subseteq> {..< n\<^sub>2}\<close> using le12 by simp
    have bo1: \<open>binds_ok (map (apsnd (sapp s\<^sub>1)) \<Gamma>) 0 n\<^sub>2 FK\<close>
      by (rule binds_ok_sapp0[OF boG sc1 kh1 bf1 le2])
    have af: \<open>frv_row (eps (s\<^sub>1 \<odot> sp)) \<subseteq> {..< n\<^sub>2}\<close>
      unfolding eps_def
      by (cases nm) (simp add: rext_def, rule frv_sappr_sconf[OF scs subset_trans[OF frA subn1]])+
    have ab: \<open>brv_row (eps (s\<^sub>1 \<odot> sp)) = {}\<close>
      unfolding eps_def by (cases nm) (simp_all add: rext_def bfree_sappr[OF bfs brA])
    have pf: \<open>ftv_pend (sub_pend (s\<^sub>1 \<odot> sp) pd) \<subseteq> {..< n\<^sub>2}\<close>
      by (rule ftv_pend_sub_pend[OF scs subset_trans[OF ftp subn1]])
    have pr: \<open>frv_pend (sub_pend (s\<^sub>1 \<odot> sp) pd) \<subseteq> {..< n\<^sub>2}\<close>
      by (rule frv_pend_sub_pend[OF scs subset_trans[OF ftp subn1] subset_trans[OF frp subn1]])
    have pk: \<open>ktv_rows (sub_pend (s\<^sub>1 \<odot> sp) pd) \<subseteq> FK\<close> by (rule ktv_rows_sub_pend[OF khs ktp])
    have ib: \<open>inwf (mono_env s\<^sub>1 \<Gamma> @ sappe (s\<^sub>1 \<odot> sp) B)
               (eps (s\<^sub>1 \<odot> sp)) (sub_pend (s\<^sub>1 \<odot> sp) pd) FK n\<^sub>2\<close>
      unfolding mono_env_binders
      by (rule inwf_binders[OF I scs khs bfs bo1 af ab pf pr pk le12 order_refl])
    from dp refl refl refl refl u1 refl refl refl eps_def covn db ib
    have wb: \<open>n\<^sub>2 \<le> n\<^sub>3 \<and> outwf s\<^sub>2 pd\<^sub>2 FK n\<^sub>3 \<and> fresh_ok \<tau>' 0 n\<^sub>3 FK\<close>
      by (rule infer_cls_Cons_HRet.IH)
    have le3: \<open>n\<^sub>2 \<le> n\<^sub>3\<close> using wb by simp
    have o_b: \<open>outwf s\<^sub>2 pd\<^sub>2 FK n\<^sub>3\<close> using wb by simp
    have ftpr: \<open>fresh_ok \<tau>' 0 n\<^sub>3 FK\<close> using wb by simp
    from o_b have sc2: \<open>sconf s\<^sub>2 {..< n\<^sub>3} {..< n\<^sub>3}\<close> by (auto simp: outwf_def)
    have subn23: \<open>{..< n\<^sub>2} \<subseteq> {..< n\<^sub>3}\<close> using le3 by simp
    have scs2: \<open>sconf (s\<^sub>2 \<odot> (s\<^sub>1 \<odot> sp)) {..< n\<^sub>3} {..< n\<^sub>3}\<close>
      by (rule sconf_scomp_mono[OF scs sc2 subn23 subn23])
    have le13: \<open>n \<le> n\<^sub>3\<close> using le12 le3 by simp
    have o_s: \<open>outwf (s\<^sub>1 \<odot> sp) (sub_pend (s\<^sub>1 \<odot> sp) pd) FK n\<^sub>2\<close>
      by (rule outwf_of_uni[OF scs khs bfs ftp frp le12 ktp])
    have os: \<open>outwf (s\<^sub>2 \<odot> (s\<^sub>1 \<odot> sp)) pd\<^sub>2 FK n\<^sub>3\<close> by (rule outwf_scomp[OF o_s o_b le3])
    have ic: \<open>inwf (sappe (s\<^sub>2 \<odot> (s\<^sub>1 \<odot> sp)) B) (sappr (s\<^sub>2 \<odot> (s\<^sub>1 \<odot> sp)) A) pd\<^sub>2 FK n\<^sub>3\<close>
      by (rule inwf_step[OF I os le13])
    have ftg: \<open>fresh_ok (sapp (s\<^sub>2 \<odot> (s\<^sub>1 \<odot> sp)) targs) 0 n\<^sub>3 FK\<close>
      by (rule fresh_ok_sapp0[OF F\<^sub>t os le13])
    from dp refl refl refl refl u1 refl refl refl eps_def covn db refl refl refl refl refl dc ic
      ftpr ftg
    have wc: \<open>n\<^sub>3 \<le> n' \<and> outwf s\<^sub>3 pd' FK n' \<and> fresh_ok \<tau> 0 n' FK\<close>
      by (rule infer_cls_Cons_HRet.IH)
    have le4: \<open>n\<^sub>3 \<le> n'\<close> using wc by simp
    have o_c: \<open>outwf s\<^sub>3 pd' FK n'\<close> using wc by simp
    have fresh: \<open>fresh_ok \<tau> 0 n' FK\<close> using wc by simp
    have le: \<open>n \<le> n'\<close> using le13 le4 by simp
    show ?case using se le fresh outwf_scomp[OF os o_c le4] by simp
  next
    case (infer_EWith uf B A pd x h e n s e' \<tau> pd' n' FK)
    show ?case
      by (rule infer_with_wf[OF infer_EWith.prems])
         (rule infer_EWith.IH; (simp only: sappe.simps)?; auto)+
  next
    case (infer_EHandlerN uf B A pd cls n s e' \<tau> pd' n' FK)
    show ?case
      by (rule infer_handlern_wf[OF infer_EHandlerN.prems]) (rule infer_EHandlerN.IH, auto)
  next
    case infer_head_AParen
    then show ?case using infer_head_AParen.IH by simp
  next
    case infer_head_ANum
    then show ?case using infer_head_ANum.IH by simp
  next
    case (infer_atom_ARec uf B A pd fs n s a' \<tau> pd' n' FK)
    have E: \<open>infer_atom uf B A pd (ARec fs) n = Some (s, a', \<tau>, pd', n')\<close>
      and I: \<open>inwf B A pd FK n\<close> by (fact infer_atom_ARec.prems)+
    from E obtain es'' \<tau>s where
      dist: \<open>distinct (map (n_txt \<circ> fst) fs)\<close> and
      d: \<open>infer_exps uf B A pd (map snd fs) n = Some (s, es'', \<tau>s, pd', n')\<close> and
      te: \<open>\<tau> = rec_of (zip (map (n_txt \<circ> fst) fs) \<tau>s) TRNil\<close>
      by (auto split: Option.bind_split_asm prod.split_asm if_split_asm)
    from dist d I have \<open>n \<le> n' \<and> outwf s pd' FK n' \<and> (\<forall>\<tau> \<in> set \<tau>s. fresh_ok \<tau> 0 n' FK)\<close>
      by (rule infer_atom_ARec.IH)
    then show ?case using te fresh_ok_rec_of by auto
  next
    case (infer_atom_ADot uf B A pd a x n s r \<tau> pd' n' FK)
    have E: \<open>infer_atom uf B A pd (ADot a x) n = Some (s, r, \<tau>, pd', n')\<close>
      and I: \<open>inwf B A pd FK n\<close> by (fact infer_atom_ADot.prems)+
    from E obtain s\<^sub>1 a' \<tau>\<^sub>a pd\<^sub>1 n\<^sub>1 s\<^sub>2 n\<^sub>2 where
      d1: \<open>infer_atom uf B A pd a n = Some (s\<^sub>1, a', \<tau>\<^sub>a, pd\<^sub>1, n\<^sub>1)\<close> and
      un: \<open>uni uf \<tau>\<^sub>a (TRCons (n_txt x) (TV n\<^sub>1) (TV (Suc n\<^sub>1))) (n\<^sub>1 + 2) = Some (s\<^sub>2, n\<^sub>2)\<close> and
      se: \<open>s = s\<^sub>2 \<odot> s\<^sub>1\<close> and te: \<open>\<tau> = sapp s\<^sub>2 (TV n\<^sub>1)\<close> and
      pe: \<open>pd' = (imp_name n\<^sub>2,
                   POff (n_txt x) (sapp s\<^sub>2 (TRCons (n_txt x) (TV n\<^sub>1) (TV (Suc n\<^sub>1)))))
                  # sub_pend s\<^sub>2 pd\<^sub>1\<close> and
      ne: \<open>n' = Suc n\<^sub>2\<close>
      by (auto simp: bind_eq_Some_conv Let_def)
    from d1 I have \<open>n \<le> n\<^sub>1 \<and> outwf s\<^sub>1 pd\<^sub>1 FK n\<^sub>1 \<and> fresh_ok \<tau>\<^sub>a 0 n\<^sub>1 FK\<close>
      by (rule infer_atom_ADot.IH)
    then have le1: \<open>n \<le> n\<^sub>1\<close> and o1: \<open>outwf s\<^sub>1 pd\<^sub>1 FK n\<^sub>1\<close> and fa: \<open>fresh_ok \<tau>\<^sub>a 0 n\<^sub>1 FK\<close>
      by simp_all
    from o1 have ftp1: \<open>ftv_pend pd\<^sub>1 \<subseteq> {..< n\<^sub>1}\<close> and frp1: \<open>frv_pend pd\<^sub>1 \<subseteq> {..< n\<^sub>1}\<close> and ktp1: \<open>ktv_rows pd\<^sub>1 \<subseteq> FK\<close>
      by (auto simp: outwf_def)
    have fa2: \<open>fresh_ok \<tau>\<^sub>a 0 (n\<^sub>1 + 2) FK\<close> by (rule fresh_ok_mono[OF fa order_refl]) simp
    have ft2: \<open>fresh_ok (TRCons (n_txt x) (TV n\<^sub>1) (TV (Suc n\<^sub>1))) 0 (n\<^sub>1 + 2) FK\<close>
      by (auto simp: fresh_ok_def bfree_def)
    note uf1 = uni_fresh[OF un fa2 ft2 le0]
    have le2: \<open>n\<^sub>1 + 2 \<le> n\<^sub>2\<close> using uf1 by simp
    have le12: \<open>n\<^sub>1 \<le> n\<^sub>2\<close> using le2 by simp
    have sc2: \<open>sconf s\<^sub>2 {..< n\<^sub>2} {..< n\<^sub>2}\<close> using uf1 by (simp add: atLeast0LessThan)
    have kh2: \<open>khyg s\<^sub>2 FK\<close> and bf2: \<open>bfree_sub s\<^sub>2\<close> using uf1 by simp_all
    have o2: \<open>outwf s\<^sub>2 (sub_pend s\<^sub>2 pd\<^sub>1) FK n\<^sub>2\<close>
      by (rule outwf_of_uni[OF sc2 kh2 bf2 ftp1 frp1 le12 ktp1])
    have os: \<open>outwf (s\<^sub>2 \<odot> s\<^sub>1) (sub_pend s\<^sub>2 pd\<^sub>1) FK n\<^sub>2\<close> by (rule outwf_scomp[OF o1 o2 le12])
    have fpo: \<open>fresh_ok (sapp s\<^sub>2 (TRCons (n_txt x) (TV n\<^sub>1) (TV (Suc n\<^sub>1)))) 0 n\<^sub>2 FK\<close>
      by (rule fresh_ok_sapp0[OF ft2 o2 le2])
    have ftv1: \<open>fresh_ok (TV n\<^sub>1) 0 (n\<^sub>1 + 2) FK\<close> by (simp add: fresh_ok_def bfree_def)
    have fsl: \<open>fresh_ok (sapp s\<^sub>2 (TV n\<^sub>1)) 0 n\<^sub>2 FK\<close> by (rule fresh_ok_sapp0[OF ftv1 o2 le2])
    have fresh: \<open>fresh_ok \<tau> 0 n' FK\<close>
      unfolding te ne by (rule fresh_ok_mono[OF fsl order_refl]) simp
    have sub: \<open>{..< n\<^sub>2} \<subseteq> {..< n'}\<close> unfolding ne by auto
    have out: \<open>outwf s pd' FK n'\<close>
      using os fpo sub unfolding se pe outwf_def fresh_ok_def
      by (auto 4 3 intro: sconf_mono[OF _ sub sub])
    have le: \<open>n \<le> n'\<close> using le1 le12 unfolding ne by simp
    show ?case using out fresh le by simp
  qed (auto simp: inwf_def outwf_def fresh_ok_def bfree_def split: Option.bind_split_asm if_split_asm)

end
