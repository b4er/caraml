theory Infer_Invariants
  imports Infer
begin

section \<open>Invariants of the inference algorithm\<close>

text \<open>The invariants of \<^const>\<open>infer\<close> and the unifiers that the soundness
  proofs use. \<^text>\<open>Infer_Confinement\<close> builds on them the substitution stability
  of the declarative judgement and the confinement of the algorithm's
  substitutions.

    \<^item> Substitution congruence and identity on closed types, and closed
      entries (\<^text>\<open>cenv\<close>): a lookup through a structure is invariant
      under substitution.

    \<^item> A confinement calculus (\<^text>\<open>sconf\<close>, \<^text>\<open>sub_avoids\<close>): a
      substitution the algorithm returns is the identity outside the
      variables of its input and the fresh ones it allocated (and moves
      nothing outside them).

    \<^item> Hygiene (\<^text>\<open>khyg\<close>, \<^text>\<open>bfree_sub\<close>): the abstract types a
      module binder binds never occur free outside it, so a substitution
      commutes with instantiating a binder. No bound variable of a scheme
      occurs in a live type, so a substitution commutes with instantiating
      a scheme.

    \<^item> The unifiers keep these invariants: monotone counters, confinement,
      hygiene.

    \<^item> Static elaboration is invariant under substitution.

    \<^item> Freshness and pattern inference is well formed.\<close>

subsection \<open>Substitution: congruence and identity\<close>

text \<open>A substitution leaves a closed type, row, scheme or basis alone, and
  composition is associative with \<^const>\<open>sid\<close> as unit.\<close>

lemma frv_tsubst:
  \<open>frv (tsubst \<theta> \<rho> t) = (\<Union>a\<in>ftv t. frv (\<theta> a)) \<union> (\<Union>v\<in>frv t. frv_row (\<rho> v))\<close>
  by (induction t) (auto simp: frv_rsubst)

lemma sapp_closed: \<open>ftv t = {} \<Longrightarrow> frv t = {} \<Longrightarrow> sapp s t = t\<close>
  by (cases s) (auto intro!: tsubst_id_on)

lemma sub_scheme_closed: \<open>ftv_sch \<sigma> = {} \<Longrightarrow> frv_sch \<sigma> = {} \<Longrightarrow> sub_scheme \<theta> \<rho> \<sigma> = \<sigma>\<close>
  by (cases \<sigma>) (auto intro!: tsubst_id_on)

lemma sapps_closed: \<open>ftv_sch \<sigma> = {} \<Longrightarrow> frv_sch \<sigma> = {} \<Longrightarrow> sapps s \<sigma> = \<sigma>\<close>
  by (cases s) (simp add: sub_scheme_closed)

lemma scomp_assoc: \<open>(s\<^sub>3 \<odot> s\<^sub>2) \<odot> s\<^sub>1 = s\<^sub>3 \<odot> (s\<^sub>2 \<odot> s\<^sub>1)\<close>
  by (cases s\<^sub>1; cases s\<^sub>2; cases s\<^sub>3) (simp add: tsubst_comp rsubst_comp)

lemma scomp_sid[simp]: \<open>s \<odot> sid = s\<close> \<open>sid \<odot> s = s\<close>
  by (cases s; simp add: sid_def)+

lemma sapp_simps[simp]:
  \<open>sapp s (TV a) = fst s a\<close> \<open>sapp s (TB a) = TB a\<close> \<open>sapp s (TK a) = TK a\<close> \<open>sapp s (TA d j) = TA d j\<close>
  \<open>sapp s (TC c ts) = TC c (map (sapp s) ts)\<close> \<open>sapp s (TApp t\<^sub>1 t\<^sub>2) = TApp (sapp s t\<^sub>1) (sapp s t\<^sub>2)\<close>
  \<open>sapp s (TFn t\<^sub>1 e t\<^sub>2) = TFn (sapp s t\<^sub>1) (sappr s e) (sapp s t\<^sub>2)\<close>
  \<open>sapp s (TDep i sg m e t) = TDep i sg m (sappr s e) (sapp s t)\<close>
  \<open>sappr s RNil = RNil\<close> \<open>sappr s (RV v) = snd s v\<close> \<open>sappr s (RB v) = RB v\<close>
  \<open>sappr s (RCons l r) = RCons l (sappr s r)\<close>
  by (cases s; simp)+

subsection \<open>Closed entries\<close>

text \<open>Every entry of a basis other than a value's scheme is built by a
  declaration or a signature and mentions no unification variable (this
  makes lookups through structures invariant under substitution).\<close>

definition cenv :: \<open>tenv \<Rightarrow> bool\<close> where
  \<open>cenv B \<longleftrightarrow> (\<forall>(x, e) \<in> set B. (\<exists>\<sigma>. e = TEval \<sigma>) \<or> ftv_ent e = {} \<and> frv_ent e = {})\<close>

lemma cenv_Nil[simp]: \<open>cenv []\<close>
  by (simp add: cenv_def)

lemma cenv_Cons[simp]:
  \<open>cenv ((x, e) # B) \<longleftrightarrow> ((\<exists>\<sigma>. e = TEval \<sigma>) \<or> ftv_ent e = {} \<and> frv_ent e = {}) \<and> cenv B\<close>
  by (simp add: cenv_def)

lemma cenv_append[simp]: \<open>cenv (E\<^sub>1 @ E\<^sub>2) \<longleftrightarrow> cenv E\<^sub>1 \<and> cenv E\<^sub>2\<close>
  by (simp add: cenv_def ball_Un)

lemma sub_ent_closed: \<open>ftv_ent e = {} \<Longrightarrow> frv_ent e = {} \<Longrightarrow> sub_ent \<theta> \<rho> e = e\<close>
  by (cases e) (auto simp: sub_scheme_closed)

lemma sub_env_simps[simp]:
  \<open>sub_env \<theta> \<rho> [] = []\<close> \<open>sub_env \<theta> \<rho> ((x, e) # E) = (x, sub_ent \<theta> \<rho> e) # sub_env \<theta> \<rho> E\<close>
  by (simp_all add: sub_env_def)

lemma sub_env_closed: \<open>ftv_env E = {} \<Longrightarrow> frv_env E = {} \<Longrightarrow> sub_env \<theta> \<rho> E = E\<close>
  by (induction E) (auto simp: sub_env_def sub_ent_closed)

lemma sappe_closed: \<open>ftv_env E = {} \<Longrightarrow> frv_env E = {} \<Longrightarrow> sappe s E = E\<close>
  by (cases s) (simp add: sub_env_closed)

lemma cenv_sub_env: \<open>cenv B \<Longrightarrow> cenv (sub_env \<theta> \<rho> B)\<close>
  by (induction B) (auto simp: sub_env_def cenv_def sub_ent_closed)

lemma cenv_sappe: \<open>cenv B \<Longrightarrow> cenv (sappe s B)\<close>
  by (cases s) (simp add: cenv_sub_env)

lemma cenv_binders[simp]: \<open>cenv (binders \<Gamma>)\<close>
  by (induction \<Gamma>) (auto simp: cenv_def)

lemma map_of_sub_env: \<open>map_of (sub_env \<theta> \<rho> E) x = map_option (sub_ent \<theta> \<rho>) (map_of E x)\<close>
  by (induction E) (auto simp: sub_env_def)

lemma ftv_env_append[simp]: \<open>ftv_env (E\<^sub>1 @ E\<^sub>2) = ftv_env E\<^sub>1 \<union> ftv_env E\<^sub>2\<close>
  by (induction E\<^sub>1) auto

lemma frv_env_append[simp]: \<open>frv_env (E\<^sub>1 @ E\<^sub>2) = frv_env E\<^sub>1 \<union> frv_env E\<^sub>2\<close>
  by (induction E\<^sub>1) auto

lemma ftv_env_map_of: \<open>map_of E x = Some e \<Longrightarrow> ftv_ent e \<subseteq> ftv_env E\<close>
  by (induction E) (auto split: if_split_asm)

lemma frv_env_map_of: \<open>map_of E x = Some e \<Longrightarrow> frv_ent e \<subseteq> frv_env E\<close>
  by (induction E) (auto split: if_split_asm)

lemma ftv_env_tlookup: \<open>tlookup E p = Some e \<Longrightarrow> ftv_ent e \<subseteq> ftv_env E\<close>
  by (induction E p rule: tlookup.induct)
     (fastforce simp: ftv_env_map_of split: option.split_asm tentry.split_asm
                dest!: ftv_env_map_of)+

lemma frv_env_tlookup: \<open>tlookup E p = Some e \<Longrightarrow> frv_ent e \<subseteq> frv_env E\<close>
  by (induction E p rule: tlookup.induct)
     (fastforce simp: frv_env_map_of split: option.split_asm tentry.split_asm
                dest!: frv_env_map_of)+

text \<open>Lookups through a substituted basis:\<close>

lemma tlookup_sub_env:
  assumes \<open>cenv B\<close>
  shows \<open>tlookup (sub_env \<theta> \<rho> B) p = map_option (sub_ent \<theta> \<rho>) (tlookup B p)\<close>
proof (cases p)
  case Nil then show ?thesis by simp
next
  case (Cons x xs)
  show ?thesis
  proof (cases xs)
    case Nil with Cons show ?thesis by (simp add: map_of_sub_env)
  next
    case (Cons y ys)
    have \<open>tlookup ex (y # ys) = Some e \<Longrightarrow> ftv_ent e = {} \<and> frv_ent e = {}\<close>
      if \<open>map_of B x = Some (TEstr ex) \<or> map_of B x = Some (TEinst ex)\<close> for ex e
      using that assms ftv_env_tlookup[of ex \<open>y # ys\<close> e] frv_env_tlookup[of ex \<open>y # ys\<close> e]
      by (auto simp: cenv_def dest!: map_of_SomeD)
    then have \<open>tlookup ex (y # ys) = map_option (sub_ent \<theta> \<rho>) (tlookup ex (y # ys))\<close>
      if \<open>map_of B x = Some (TEstr ex) \<or> map_of B x = Some (TEinst ex)\<close> for ex
      using that by (cases \<open>tlookup ex (y # ys)\<close>) (auto simp: sub_ent_closed)
    then show ?thesis
      using \<open>p = x # xs\<close> Cons by (auto simp: map_of_sub_env split: option.split tentry.split)
  qed
qed

lemma tlookup_sappe_val:
  \<open>cenv B \<Longrightarrow>
    tlookup (sappe s B) p = Some (TEval \<sigma>') \<longleftrightarrow>
    (\<exists>\<sigma>. tlookup B p = Some (TEval \<sigma>) \<and> \<sigma>' = sapps s \<sigma>)\<close>
  by (cases s) (auto simp: tlookup_sub_env elim!: sub_ent.elims)

lemma sub_ent_eq_nonval: \<open>(\<forall>\<sigma>. e \<noteq> TEval \<sigma>) \<Longrightarrow> sub_ent \<theta> \<rho> z = e \<longleftrightarrow> z = e\<close>
  by (cases z) auto

lemma tlookup_sappe_other:
  \<open>cenv B \<Longrightarrow> (\<forall>\<sigma>. e \<noteq> TEval \<sigma>) \<Longrightarrow> tlookup (sappe s B) p = Some e \<longleftrightarrow> tlookup B p = Some e\<close>
  by (cases s) (auto simp: tlookup_sub_env sub_ent_eq_nonval)

subsection \<open>A confinement calculus for substitutions\<close>

text \<open>A substitution is confined to \<open>(V, R)\<close> when it is the identity
  outside them and never introduces a variable outside them. Confinement
  is closed under composition with a substitution confined to a larger
  region.\<close>

definition sconf :: \<open>ksub \<Rightarrow> tvar set \<Rightarrow> rvar set \<Rightarrow> bool\<close> where
  \<open>sconf s V R \<longleftrightarrow>
     (\<forall>a. a \<notin> V \<longrightarrow> fst s a = TV a) \<and> (\<forall>v. v \<notin> R \<longrightarrow> snd s v = RV v) \<and>
     (\<forall>a\<in>V. ftv (fst s a) \<subseteq> V \<and> frv (fst s a) \<subseteq> R) \<and> (\<forall>v\<in>R. frv_row (snd s v) \<subseteq> R)\<close>

text \<open>The four parts of \<^const>\<open>sconf\<close>, one per fact:\<close>

lemma
  assumes \<open>sconf (\<theta>, \<rho>) V R\<close>
  shows sconf_out_TV: \<open>a \<notin> V \<Longrightarrow> \<theta> a = TV a\<close>
    and sconf_in_vars: \<open>a \<in> V \<Longrightarrow> ftv (\<theta> a) \<subseteq> V \<and> frv (\<theta> a) \<subseteq> R\<close>
    and sconf_out_RV: \<open>v \<notin> R \<Longrightarrow> \<rho> v = RV v\<close>
    and sconf_in_rvars: \<open>v \<in> R \<Longrightarrow> frv_row (\<rho> v) \<subseteq> R\<close>
  using assms by (auto simp: sconf_def)

lemma sconf_sid[simp]: \<open>sconf sid V R\<close>
  by (auto simp: sconf_def sid_def)

lemma sconf_mono:
  assumes s: \<open>sconf s V R\<close> and vv: \<open>V \<subseteq> V'\<close> and rr: \<open>R \<subseteq> R'\<close>
  shows \<open>sconf s V' R'\<close>
proof -
  obtain \<theta> \<rho> where e: \<open>s = (\<theta>, \<rho>)\<close> by (cases s)
  note supt = sconf_out_TV[OF s[unfolded e]] and imt = sconf_in_vars[OF s[unfolded e]]
    and supr = sconf_out_RV[OF s[unfolded e]] and imr = sconf_in_rvars[OF s[unfolded e]]
  have \<open>ftv (\<theta> a) \<subseteq> V' \<and> frv (\<theta> a) \<subseteq> R'\<close> if \<open>a \<in> V'\<close> for a
    using imt[of a] supt[of a] vv rr that by (cases \<open>a \<in> V\<close>) auto
  moreover have \<open>frv_row (\<rho> v) \<subseteq> R'\<close> if \<open>v \<in> R'\<close> for v
    using imr[of v] supr[of v] rr that by (cases \<open>v \<in> R\<close>) auto
  moreover have \<open>\<theta> a = TV a\<close> if \<open>a \<notin> V'\<close> for a using supt vv that by auto
  moreover have \<open>\<rho> v = RV v\<close> if \<open>v \<notin> R'\<close> for v using supr rr that by auto
  ultimately show ?thesis unfolding sconf_def e by simp
qed

lemma sconf_scomp_mono:
  assumes s1: \<open>sconf s\<^sub>1 V R\<close> and s2: \<open>sconf s\<^sub>2 V' R'\<close> and vv: \<open>V \<subseteq> V'\<close> and rr: \<open>R \<subseteq> R'\<close>
  shows \<open>sconf (s\<^sub>2 \<odot> s\<^sub>1) V' R'\<close>
proof -
  obtain \<theta>\<^sub>1 \<rho>\<^sub>1 where e1: \<open>s\<^sub>1 = (\<theta>\<^sub>1, \<rho>\<^sub>1)\<close> by (cases s\<^sub>1)
  obtain \<theta>\<^sub>2 \<rho>\<^sub>2 where e2: \<open>s\<^sub>2 = (\<theta>\<^sub>2, \<rho>\<^sub>2)\<close> by (cases s\<^sub>2)
  note s1' = sconf_mono[OF s1 vv rr]
  note supt1 = sconf_out_TV[OF s1'[unfolded e1]] and imt1 = sconf_in_vars[OF s1'[unfolded e1]]
    and supr1 = sconf_out_RV[OF s1'[unfolded e1]] and imr1 = sconf_in_rvars[OF s1'[unfolded e1]]
  note supt2 = sconf_out_TV[OF s2[unfolded e2]] and imt2 = sconf_in_vars[OF s2[unfolded e2]]
    and supr2 = sconf_out_RV[OF s2[unfolded e2]] and imr2 = sconf_in_rvars[OF s2[unfolded e2]]
  have tim: \<open>ftv (tsubst \<theta>\<^sub>2 \<rho>\<^sub>2 (\<theta>\<^sub>1 a)) \<subseteq> V' \<and> frv (tsubst \<theta>\<^sub>2 \<rho>\<^sub>2 (\<theta>\<^sub>1 a)) \<subseteq> R'\<close>
    if \<open>a \<in> V'\<close> for a
    using imt1[OF that] imt2 imr2 unfolding ftv_tsubst frv_tsubst by blast
  have rim: \<open>frv_row (rsubst \<rho>\<^sub>2 (\<rho>\<^sub>1 v)) \<subseteq> R'\<close> if \<open>v \<in> R'\<close> for v
    using imr1[OF that] imr2 unfolding frv_rsubst by blast
  have sup: \<open>tsubst \<theta>\<^sub>2 \<rho>\<^sub>2 (\<theta>\<^sub>1 a) = TV a\<close> if \<open>a \<notin> V'\<close> for a
    using supt1[OF that] supt2[OF that] by simp
  have supr: \<open>rsubst \<rho>\<^sub>2 (\<rho>\<^sub>1 v) = RV v\<close> if \<open>v \<notin> R'\<close> for v
    using supr1[OF that] supr2[OF that] by simp
  show ?thesis
    unfolding sconf_def e1 e2 scomp.simps fst_conv snd_conv using sup supr tim rim by simp
qed

lemma sconf_scomp: \<open>sconf s\<^sub>1 V R \<Longrightarrow> sconf s\<^sub>2 V R \<Longrightarrow> sconf (s\<^sub>2 \<odot> s\<^sub>1) V R\<close>
  by (rule sconf_scomp_mono) auto

lemma ftv_tsubst_sconf: \<open>sconf (\<theta>, \<rho>) V R \<Longrightarrow> ftv t \<subseteq> V \<Longrightarrow> ftv (tsubst \<theta> \<rho> t) \<subseteq> V\<close>
  unfolding sconf_def ftv_tsubst fst_conv snd_conv by (intro UN_least) blast

lemma frv_tsubst_sconf: \<open>sconf (\<theta>, \<rho>) V R \<Longrightarrow> ftv t \<subseteq> V \<Longrightarrow> frv t \<subseteq> R \<Longrightarrow> frv (tsubst \<theta> \<rho> t) \<subseteq> R\<close>
  unfolding sconf_def frv_tsubst fst_conv snd_conv by (intro Un_least UN_least) blast+

lemma frv_rsubst_sconf: \<open>sconf (\<theta>, \<rho>) V R \<Longrightarrow> frv_row r \<subseteq> R \<Longrightarrow> frv_row (rsubst \<rho> r) \<subseteq> R\<close>
  unfolding sconf_def frv_rsubst fst_conv snd_conv by (intro UN_least) blast

lemma ftv_sapp_sconf: \<open>sconf s V R \<Longrightarrow> ftv t \<subseteq> V \<Longrightarrow> ftv (sapp s t) \<subseteq> V\<close>
  by (cases s) (simp add: ftv_tsubst_sconf)

lemma frv_sapp_sconf: \<open>sconf s V R \<Longrightarrow> ftv t \<subseteq> V \<Longrightarrow> frv t \<subseteq> R \<Longrightarrow> frv (sapp s t) \<subseteq> R\<close>
  by (cases s) (simp add: frv_tsubst_sconf)

lemma frv_sappr_sconf: \<open>sconf s V R \<Longrightarrow> frv_row r \<subseteq> R \<Longrightarrow> frv_row (sappr s r) \<subseteq> R\<close>
  by (cases s) (simp add: frv_rsubst_sconf)

lemma ftv_sub_scheme_sconf: \<open>sconf (\<theta>, \<rho>) V R \<Longrightarrow> ftv_sch \<sigma> \<subseteq> V \<Longrightarrow> ftv_sch (sub_scheme \<theta> \<rho> \<sigma>) \<subseteq> V\<close>
  by (cases \<sigma>) (simp_all add: ftv_tsubst_sconf)

lemma frv_sub_scheme_sconf:
  \<open>sconf (\<theta>, \<rho>) V R \<Longrightarrow> ftv_sch \<sigma> \<subseteq> V \<Longrightarrow> frv_sch \<sigma> \<subseteq> R \<Longrightarrow> frv_sch (sub_scheme \<theta> \<rho> \<sigma>) \<subseteq> R\<close>
  by (cases \<sigma>) (simp_all add: frv_tsubst_sconf)

lemma ftv_sapps_sconf: \<open>sconf s V R \<Longrightarrow> ftv_sch \<sigma> \<subseteq> V \<Longrightarrow> ftv_sch (sapps s \<sigma>) \<subseteq> V\<close>
  by (cases s) (simp add: ftv_sub_scheme_sconf)

lemma frv_sapps_sconf: \<open>sconf s V R \<Longrightarrow> ftv_sch \<sigma> \<subseteq> V \<Longrightarrow> frv_sch \<sigma> \<subseteq> R \<Longrightarrow> frv_sch (sapps s \<sigma>) \<subseteq> R\<close>
  by (cases s) (simp add: frv_sub_scheme_sconf)

lemma ftv_sub_ent_sconf:
  \<open>sconf (\<theta>, \<rho>) V R \<Longrightarrow> ftv_ent e \<subseteq> V \<Longrightarrow> ftv_ent (sub_ent \<theta> \<rho> e) \<subseteq> V\<close>
  by (cases e) (simp_all add: ftv_sub_scheme_sconf)

lemma frv_sub_ent_sconf:
  \<open>sconf (\<theta>, \<rho>) V R \<Longrightarrow> ftv_ent e \<subseteq> V \<Longrightarrow> frv_ent e \<subseteq> R \<Longrightarrow> frv_ent (sub_ent \<theta> \<rho> e) \<subseteq> R\<close>
  by (cases e) (simp_all add: frv_sub_scheme_sconf)

lemma ftv_sub_env_sconf: \<open>sconf (\<theta>, \<rho>) V R \<Longrightarrow> ftv_env B \<subseteq> V \<Longrightarrow> ftv_env (sub_env \<theta> \<rho> B) \<subseteq> V\<close>
proof (induction B)
  case (Cons xe B)
  then show ?case
    using ftv_sub_ent_sconf[of \<theta> \<rho> V R \<open>snd xe\<close>] by (cases xe) (auto simp: sub_env_def)
qed (simp add: sub_env_def)

lemma frv_sub_env_sconf:
  \<open>sconf (\<theta>, \<rho>) V R \<Longrightarrow> ftv_env B \<subseteq> V \<Longrightarrow> frv_env B \<subseteq> R \<Longrightarrow> frv_env (sub_env \<theta> \<rho> B) \<subseteq> R\<close>
proof (induction B)
  case (Cons xe B)
  then show ?case
    using frv_sub_ent_sconf[of \<theta> \<rho> V R \<open>snd xe\<close>] by (cases xe) (auto simp: sub_env_def)
qed (simp add: sub_env_def)

lemma ftv_sappe_sconf: \<open>sconf s V R \<Longrightarrow> ftv_env B \<subseteq> V \<Longrightarrow> ftv_env (sappe s B) \<subseteq> V\<close>
  by (cases s) (simp add: ftv_sub_env_sconf)

lemma frv_sappe_sconf:
  \<open>sconf s V R \<Longrightarrow> ftv_env B \<subseteq> V \<Longrightarrow> frv_env B \<subseteq> R \<Longrightarrow> frv_env (sappe s B) \<subseteq> R\<close>
  by (cases s) (simp add: frv_sub_env_sconf)

text \<open>A confined substitution fixes variables outside its region and keeps
  them out of its ranges, which is what closing over them needs.\<close>

definition sub_avoids :: \<open>ksub \<Rightarrow> tvar set \<Rightarrow> rvar set \<Rightarrow> bool\<close> where
  \<open>sub_avoids s as rs \<longleftrightarrow>
     (\<forall>a\<in>as. fst s a = TV a) \<and> (\<forall>v\<in>rs. snd s v = RV v) \<and>
     (\<forall>a. ftv (fst s a) \<inter> as = {} \<or> a \<in> as) \<and> (\<forall>a. frv (fst s a) \<inter> rs = {}) \<and>
     (\<forall>v. frv_row (snd s v) \<inter> rs = {} \<or> v \<in> rs)\<close>

lemma sub_avoids_of_sconf:
  assumes s: \<open>sconf s V R\<close> and dv: \<open>as \<inter> V = {}\<close> and dr: \<open>rs \<inter> R = {}\<close>
  shows \<open>sub_avoids s as rs\<close>
proof -
  obtain \<theta> \<rho> where e: \<open>s = (\<theta>, \<rho>)\<close> by (cases s)
  note supt = sconf_out_TV[OF s[unfolded e]] and imt = sconf_in_vars[OF s[unfolded e]]
    and supr = sconf_out_RV[OF s[unfolded e]] and imr = sconf_in_rvars[OF s[unfolded e]]
  have \<open>\<theta> a = TV a\<close> if \<open>a \<in> as\<close> for a using supt dv that by auto
  moreover have \<open>\<rho> v = RV v\<close> if \<open>v \<in> rs\<close> for v using supr dr that by auto
  moreover have \<open>ftv (\<theta> a) \<inter> as = {} \<or> a \<in> as\<close> for a
    using imt[of a] supt[of a] dv by (cases \<open>a \<in> V\<close>) auto
  moreover have \<open>frv (\<theta> a) \<inter> rs = {}\<close> for a
    using imt[of a] supt[of a] dr by (cases \<open>a \<in> V\<close>) auto
  moreover have \<open>frv_row (\<rho> v) \<inter> rs = {} \<or> v \<in> rs\<close> for v
    using imr[of v] supr[of v] dr by (cases \<open>v \<in> R\<close>) auto
  ultimately show ?thesis unfolding sub_avoids_def e by simp
qed

lemma close_ty_sapp:
  assumes \<open>sub_avoids s as rs\<close>
  shows \<open>sapp s (close_ty as rs t) = close_ty as rs (sapp s t)\<close>
proof -
  obtain \<theta> \<rho> where e: \<open>s = (\<theta>, \<rho>)\<close> by (cases s)
  define clt where \<open>clt = (\<lambda>a. if a \<in> as then TB a else TV a)\<close>
  define clr where \<open>clr = (\<lambda>v. if v \<in> rs then RB v else RV v)\<close>
  have fixt: \<open>\<And>a. a \<in> as \<Longrightarrow> \<theta> a = TV a\<close> and fixr: \<open>\<And>v. v \<in> rs \<Longrightarrow> \<rho> v = RV v\<close>
    and rngt: \<open>\<And>a. a \<notin> as \<Longrightarrow> ftv (\<theta> a) \<inter> as = {}\<close> and rngtr: \<open>\<And>a. frv (\<theta> a) \<inter> rs = {}\<close>
    and rngr: \<open>\<And>v. v \<notin> rs \<Longrightarrow> frv_row (\<rho> v) \<inter> rs = {}\<close>
    using assms unfolding e sub_avoids_def by auto
  have rows: \<open>rsubst \<rho> (rsubst clr r) = rsubst clr (rsubst \<rho> r)\<close> for r
  proof (induction r)
    case (RV v)
    show ?case
    proof (cases \<open>v \<in> rs\<close>)
      case True then show ?thesis by (simp add: clr_def fixr)
    next
      case False
      then have \<open>rsubst clr (\<rho> v) = \<rho> v\<close>
        using rngr[OF False] by (auto intro!: rsubst_id_on simp: clr_def)
      with False show ?thesis by (simp add: clr_def)
    qed
  qed (auto simp: clr_def)
  have \<open>tsubst \<theta> \<rho> (tsubst clt clr u) = tsubst clt clr (tsubst \<theta> \<rho> u)\<close> for u
  proof (induction u)
    case (TV a)
    show ?case
    proof (cases \<open>a \<in> as\<close>)
      case True then show ?thesis by (simp add: clt_def clr_def fixt)
    next
      case False
      then have \<open>tsubst clt clr (\<theta> a) = \<theta> a\<close>
        using rngt[OF False] rngtr[of a] by (auto intro!: tsubst_id_on simp: clt_def clr_def)
      with False show ?thesis by (simp add: clt_def)
    qed
  qed (auto simp: rows cong: map_cong)
  then show ?thesis by (simp add: close_ty_def e clt_def clr_def)
qed

lemma close_sch_sapp:
  \<open>sub_avoids s as rs \<Longrightarrow> sapps s (close_sch as rs t) = close_sch as rs (sapp s t)\<close>
  using close_ty_sapp[of s as rs t] by (cases s) (simp add: close_sch_def)

subsection \<open>Hygiene: abstract types and bound variables in ranges\<close>

text \<open>The free abstract types of a range are among the parameters in scope
  (\<open>FK\<close>), and no range mentions a scheme's bound variables.\<close>

definition khyg :: \<open>ksub \<Rightarrow> tvar set \<Rightarrow> bool\<close> where
  \<open>khyg s FK \<longleftrightarrow> (\<forall>a. ktv (fst s a) \<subseteq> FK)\<close>

definition bfree :: \<open>kty \<Rightarrow> bool\<close> where
  \<open>bfree t \<longleftrightarrow> btv t = {} \<and> brv t = {}\<close>

definition bfree_sub :: \<open>ksub \<Rightarrow> bool\<close> where
  \<open>bfree_sub s \<longleftrightarrow> (\<forall>a. bfree (fst s a) \<and> taclosed (fst s a)) \<and> (\<forall>v. brv_row (snd s v) = {})\<close>

lemma khyg_sid[simp]: \<open>khyg sid FK\<close>
  by (simp add: khyg_def sid_def)

lemma bfree_sub_sid[simp]: \<open>bfree_sub sid\<close>
  by (simp add: bfree_sub_def bfree_def sid_def)

lemma khyg_mono: \<open>khyg s FK \<Longrightarrow> FK \<subseteq> FK' \<Longrightarrow> khyg s FK'\<close>
  by (auto simp: khyg_def)

lemma ktv_tsubst: \<open>ktv (tsubst \<theta> \<rho> t) \<subseteq> ktv t \<union> (\<Union>a\<in>ftv t. ktv (\<theta> a))\<close>
proof (induction t)
  case (TC c ts) then show ?case by fastforce
qed auto

lemma ktv_tsubst_TV[simp]: \<open>ktv (tsubst TV \<rho> t) = ktv t\<close>
  by (induction t) auto

lemma ktv_tsubst_sub: \<open>(\<And>a. ktv (\<theta> a) \<subseteq> FK) \<Longrightarrow> ktv t \<subseteq> FK \<Longrightarrow> ktv (tsubst \<theta> \<rho> t) \<subseteq> FK\<close>
  using ktv_tsubst[of \<theta> \<rho> t] by blast

lemma khyg_sapp: \<open>khyg s FK \<Longrightarrow> ktv t \<subseteq> FK \<Longrightarrow> ktv (sapp s t) \<subseteq> FK\<close>
  by (cases s) (simp add: khyg_def ktv_tsubst_sub)

lemma khyg_scomp: \<open>khyg s\<^sub>1 FK \<Longrightarrow> khyg s\<^sub>2 FK \<Longrightarrow> khyg (s\<^sub>2 \<odot> s\<^sub>1) FK\<close>
  by (cases s\<^sub>1; cases s\<^sub>2) (simp add: khyg_def ktv_tsubst_sub)

lemma bfree_sapp: \<open>bfree_sub s \<Longrightarrow> bfree t \<Longrightarrow> bfree (sapp s t)\<close>
  by (cases s) (auto simp: bfree_sub_def bfree_def btv_tsubst brv_tsubst)

lemma bfree_sappr: \<open>bfree_sub s \<Longrightarrow> brv_row r = {} \<Longrightarrow> brv_row (sappr s r) = {}\<close>
  by (cases s) (auto simp: bfree_sub_def brv_rsubst)

lemma bfree_sub_scomp: \<open>bfree_sub s\<^sub>1 \<Longrightarrow> bfree_sub s\<^sub>2 \<Longrightarrow> bfree_sub (s\<^sub>2 \<odot> s\<^sub>1)\<close>
  using bfree_sapp[of s\<^sub>2] bfree_sappr[of s\<^sub>2]
  by (cases s\<^sub>1; cases s\<^sub>2) (auto simp: bfree_sub_def intro: taok_tsubst)

text \<open>Instantiating a scheme commutes with a substitution whose ranges are
  free of bound variables.\<close>

lemma rsubst_brsubst:
  \<open>\<forall>v \<in> frv_row r. brv_row (\<rho> v) = {} \<Longrightarrow>
   rsubst \<rho> (brsubst \<rho>\<^sub>b r) = brsubst (\<lambda>v. rsubst \<rho> (\<rho>\<^sub>b v)) (rsubst \<rho> r)\<close>
  by (induction r) (auto simp: brsubst_id)

lemma tsubst_bsubst:
  \<open>\<forall>a \<in> ftv t. bfree (\<theta> a) \<Longrightarrow> \<forall>v \<in> frv t. brv_row (\<rho> v) = {} \<Longrightarrow>
   tsubst \<theta> \<rho> (bsubst \<theta>\<^sub>b \<rho>\<^sub>b t) =
     bsubst (\<lambda>a. tsubst \<theta> \<rho> (\<theta>\<^sub>b a)) (\<lambda>v. rsubst \<rho> (\<rho>\<^sub>b v)) (tsubst \<theta> \<rho> t)\<close>
  by (induction t) (auto simp: bfree_def bsubst_id rsubst_brsubst cong: map_cong)

lemma sinst_sapp:
  assumes bs: \<open>bfree_sub s\<close> and inst: \<open>\<sigma> \<succeq> \<tau>\<close>
  shows \<open>sapps s \<sigma> \<succeq> sapp s \<tau>\<close>
proof (cases \<sigma>)
  case (Sch t)
  obtain \<theta> \<rho> where e: \<open>s = (\<theta>, \<rho>)\<close> by (cases s)
  from inst Sch obtain \<theta>\<^sub>b \<rho>\<^sub>b where \<open>\<tau> = bsubst \<theta>\<^sub>b \<rho>\<^sub>b t\<close>
    and bf: \<open>btv \<tau> = {}\<close> \<open>brv \<tau> = {}\<close> and im: \<open>\<forall>a. taclosed (\<theta>\<^sub>b a)\<close>
    by (auto simp: sinst_Sch)
  have bfs: \<open>btv (sapp (\<theta>, \<rho>) \<tau>) = {}\<close> \<open>brv (sapp (\<theta>, \<rho>) \<tau>) = {}\<close>
    using bfree_sapp[OF bs] bf unfolding e by (auto simp: bfree_def)
  have im': \<open>taclosed (tsubst \<theta> \<rho> (\<theta>\<^sub>b a))\<close> for a
    using bs im unfolding e by (auto simp: bfree_sub_def intro: taok_tsubst)
  have tb: \<open>tsubst \<theta> \<rho> (bsubst \<theta>\<^sub>b \<rho>\<^sub>b t) =
            bsubst (\<lambda>a. tsubst \<theta> \<rho> (\<theta>\<^sub>b a)) (\<lambda>v. rsubst \<rho> (\<rho>\<^sub>b v)) (tsubst \<theta> \<rho> t)\<close>
    using bs unfolding e by (intro tsubst_bsubst) (auto simp: bfree_sub_def)
  from im' bfs \<open>\<tau> = bsubst \<theta>\<^sub>b \<rho>\<^sub>b t\<close> show ?thesis
    unfolding Sch e
    by (auto simp: sinst_Sch tb intro!: exI[of _ \<open>\<lambda>a. tsubst \<theta> \<rho> (\<theta>\<^sub>b a)\<close>])
qed (use assms in \<open>cases s, auto simp: sinst_Sch\<close>)

text \<open>A type whose variables all lie in the closed sets is an instance of
  its closure at any substitution.\<close>

lemma close_sch_inst:
  assumes ts: \<open>ftv t \<subseteq> as\<close> \<open>frv t \<subseteq> rs\<close> and bt: \<open>bfree t\<close> and bs: \<open>bfree_sub s\<close>
  shows \<open>close_sch as rs t \<succeq> sapp s t\<close>
proof -
  obtain \<theta> \<rho> where e: \<open>s = (\<theta>, \<rho>)\<close> by (cases s)
  define \<theta>\<^sub>b where \<open>\<theta>\<^sub>b = (\<lambda>a. if a \<in> as then \<theta> a else TB a)\<close>
  define \<rho>\<^sub>b where \<open>\<rho>\<^sub>b = (\<lambda>v. if v \<in> rs then \<rho> v else RB v)\<close>
  have rows: \<open>brsubst \<rho>\<^sub>b (rsubst (\<lambda>v. if v \<in> rs then RB v else RV v) r) = rsubst \<rho> r\<close>
    if \<open>frv_row r \<subseteq> rs\<close> \<open>brv_row r = {}\<close> for r
    using that by (induction r) (auto simp: \<rho>\<^sub>b_def)
  have inst: \<open>bsubst \<theta>\<^sub>b \<rho>\<^sub>b
      (tsubst (\<lambda>a. if a \<in> as then TB a else TV a) (\<lambda>v. if v \<in> rs then RB v else RV v) t)
    = tsubst \<theta> \<rho> t\<close>
    using ts bt unfolding bfree_def
    by (induction t) (auto simp: rows \<theta>\<^sub>b_def UN_subset_iff cong: map_cong)
  have fta\<^sub>b: \<open>taclosed (\<theta>\<^sub>b a)\<close> for a
    using bs unfolding \<theta>\<^sub>b_def e by (auto simp: bfree_sub_def)
  then show ?thesis
    using bfree_sapp[OF bs bt] inst
    unfolding close_sch_def close_ty_def e
    by (auto simp: sinst_Sch bfree_def intro!: exI[of _ \<theta>\<^sub>b] exI[of _ \<rho>\<^sub>b])
qed

subsection \<open>The unifiers: monotone counters, confinement, hygiene\<close>

lemma runify_mono: \<open>runify n r\<^sub>1 r\<^sub>2 = Some (\<sigma>, n') \<Longrightarrow> n \<le> n'\<close>
  by (auto simp: runify_def split: krow.splits if_split_asm)

lemma uni_row_mono: \<open>uni_row r\<^sub>1 r\<^sub>2 n = Some (s, n') \<Longrightarrow> n \<le> n'\<close>
  by (auto simp: uni_row_def dest: runify_mono split: option.splits)

lemma
  shows kunify_mono: \<open>kunify f cs n = Some (\<theta>, \<rho>, n') \<Longrightarrow> n \<le> n'\<close>
    and kbind_mono: \<open>kbind f a u cs n = Some (\<theta>, \<rho>, n') \<Longrightarrow> n \<le> n'\<close>
proof (induction f cs n and f a u cs n
       arbitrary: \<theta> \<rho> n' and \<theta> \<rho> n' rule: kunify_induct)
  case (kunify_Cons_TFn_TFn f u\<^sub>1 e u\<^sub>2 w\<^sub>1 g w\<^sub>2 cs n)
  then show ?case using runify_mono by (fastforce split: option.split_asm dest: order_trans)
next
  case (kunify_Cons_TDep_TDep f i sg T e u i' sg' T' g w cs n)
  then show ?case
    using runify_mono by (fastforce split: option.split_asm if_split_asm dest: order_trans)
next
  case (kunify_Cons_TAct_TAct f l T e u l' T' g w cs n)
  then show ?case
    using runify_mono by (fastforce split: option.split_asm if_split_asm dest: order_trans)
qed (auto split: if_split_asm option.split_asm)

lemma unis_mono: \<open>unis f cs n = Some (s, n') \<Longrightarrow> n \<le> n'\<close>
  by (auto simp: unis_def dest: kunify_mono split: option.split_asm)

lemma uni_mono: \<open>uni f t\<^sub>1 t\<^sub>2 n = Some (s, n') \<Longrightarrow> n \<le> n'\<close>
  by (simp add: uni_def unis_mono)

lemma frv_row_mk_row[simp]: \<open>frv_row (mk_row xs t) = frv_row t\<close>
proof -
  have \<open>frv_row (foldr RCons xs r) = frv_row r\<close> for r by (induction xs) auto
  then show ?thesis by (simp add: mk_row_def)
qed

lemma frv_row_row_tail[simp]: \<open>frv_row (row_tail r) = frv_row r\<close>
  by (induction r) auto

lemma runify_dom:
  assumes \<open>runify n r\<^sub>1 r\<^sub>2 = Some (\<sigma>, n')\<close> \<open>\<sigma> v = Some w\<close>
  shows \<open>v \<in> frv_row r\<^sub>1 \<union> frv_row r\<^sub>2 \<and> frv_row w \<subseteq> frv_row r\<^sub>1 \<union> frv_row r\<^sub>2 \<union> {n ..< n'}\<close>
  using assms row_tail_is_tail[of r\<^sub>1] row_tail_is_tail[of r\<^sub>2] unfolding runify_def
  by (cases \<open>row_tail r\<^sub>1\<close>; cases \<open>row_tail r\<^sub>2\<close>)
     (auto simp: frv_row_tail[of r\<^sub>1] frv_row_tail[of r\<^sub>2] split: if_split_asm)

lemma runify_sconf:
  assumes \<open>runify n r\<^sub>1 r\<^sub>2 = Some (\<sigma>, n')\<close>
  shows \<open>sconf (TV, mk_rsub \<sigma>) V (frv_row r\<^sub>1 \<union> frv_row r\<^sub>2 \<union> {n ..< n'})\<close>
  using runify_dom[OF assms] unfolding sconf_def mk_rsub_def
  by (auto split: option.splits)

lemma uni_row_sconf:
  assumes \<open>uni_row r\<^sub>1 r\<^sub>2 n = Some (s, n')\<close>
  shows \<open>sconf s V (frv_row r\<^sub>1 \<union> frv_row r\<^sub>2 \<union> {n ..< n'})\<close>
proof -
  from assms obtain \<sigma> where \<open>s = (TV, mk_rsub \<sigma>)\<close> \<open>runify n r\<^sub>1 r\<^sub>2 = Some (\<sigma>, n')\<close>
    unfolding uni_row_def by (auto split: option.split_asm)
  then show ?thesis by (simp add: runify_sconf)
qed

definition frv_cs :: \<open>(kty \<times> kty) list \<Rightarrow> rvar set\<close> where
  \<open>frv_cs cs = (\<Union>(t, u) \<in> set cs. frv t \<union> frv u)\<close>

lemma ftv_cs_simps[simp]:
  \<open>ftv_cs [] = {}\<close> \<open>ftv_cs ((t, u) # cs) = ftv t \<union> ftv u \<union> ftv_cs cs\<close>
  by (auto simp: ftv_cs_def)

lemma frv_cs_simps[simp]:
  \<open>frv_cs [] = {}\<close> \<open>frv_cs ((t, u) # cs) = frv t \<union> frv u \<union> frv_cs cs\<close>
  by (auto simp: frv_cs_def)

lemma ftv_cs_append: \<open>ftv_cs (cs\<^sub>1 @ cs\<^sub>2) = ftv_cs cs\<^sub>1 \<union> ftv_cs cs\<^sub>2\<close>
  by (auto simp: ftv_cs_def)

lemma frv_cs_append: \<open>frv_cs (cs\<^sub>1 @ cs\<^sub>2) = frv_cs cs\<^sub>1 \<union> frv_cs cs\<^sub>2\<close>
  by (auto simp: frv_cs_def)

lemma ftv_cs_zip: \<open>ftv_cs (zip ts ts') \<subseteq> (\<Union>t\<in>set ts. ftv t) \<union> (\<Union>t\<in>set ts'. ftv t)\<close>
  by (fastforce simp: ftv_cs_def dest: set_zip_leftD set_zip_rightD)

lemma frv_cs_zip: \<open>frv_cs (zip ts ts') \<subseteq> (\<Union>t\<in>set ts. frv t) \<union> (\<Union>t\<in>set ts'. frv t)\<close>
  by (fastforce simp: frv_cs_def dest: set_zip_leftD set_zip_rightD)

lemma ftv_tsubst_TV[simp]: \<open>ftv (tsubst TV \<rho> t) = ftv t\<close>
  by (simp add: ftv_tsubst)

lemma frv_tsubst_TV: \<open>frv (tsubst TV \<rho> t) = (\<Union>v\<in>frv t. frv_row (\<rho> v))\<close>
  by (simp add: frv_tsubst)

lemma ftv_cs_map_TV:
  \<open>ftv_cs (map (\<lambda>(x, y). (tsubst TV \<rho> x, tsubst TV \<rho> y)) cs) = ftv_cs cs\<close>
  by (induction cs) (auto simp: ftv_cs_def)

lemma frv_cs_map_TV:
  \<open>frv_cs (map (\<lambda>(x, y). (tsubst TV \<rho> x, tsubst TV \<rho> y)) cs) = (\<Union>v\<in>frv_cs cs. frv_row (\<rho> v))\<close>
  by (induction cs) (auto simp: frv_cs_def frv_tsubst_TV)

lemma sconf_sing:
  \<open>a \<in> V \<Longrightarrow> ftv u \<subseteq> V \<Longrightarrow> frv u \<subseteq> R \<Longrightarrow> sconf (sing a u, RV) V R\<close>
  unfolding sconf_def sing_def by auto

lemma ftv_cs_map_sing:
  \<open>ftv_cs (map (\<lambda>(x, y). (tsubst (sing a u) RV x, tsubst (sing a u) RV y)) cs) \<subseteq> ftv u \<union> ftv_cs cs\<close>
  by (induction cs) (auto simp: ftv_cs_def ftv_tsubst sing_def split: if_split_asm)

lemma frv_cs_map_sing:
  \<open>frv_cs (map (\<lambda>(x, y). (tsubst (sing a u) RV x, tsubst (sing a u) RV y)) cs) \<subseteq> frv u \<union> frv_cs cs\<close>
  by (induction cs) (auto simp: frv_cs_def frv_tsubst sing_def split: if_split_asm)

text \<open>The row half of a row-unifier's range: labels of the inputs over a
  tail of the inputs or the fresh variable.\<close>

lemma runify_range:
  assumes \<open>runify n r\<^sub>1 r\<^sub>2 = Some (\<sigma>, n')\<close>
  shows \<open>frv_row (mk_rsub \<sigma> v) \<subseteq> (frv_row r\<^sub>1 \<union> frv_row r\<^sub>2 \<union> {n ..< n'}) \<union> {v}\<close>
  using runify_sconf[OF assms, of \<open>{}\<close>] unfolding sconf_def
  by (cases \<open>v \<in> frv_row r\<^sub>1 \<union> frv_row r\<^sub>2 \<union> {n ..< n'}\<close>) auto

text \<open>Type unification binds only variables of its constraints, and its
  rows only those and the fresh ones.\<close>

lemma
  shows kunify_sconf: \<open>kunify f cs n = Some (\<theta>, \<rho>, n') \<Longrightarrow>
      sconf (\<theta>, \<rho>) (ftv_cs cs) (frv_cs cs \<union> {n ..< n'})\<close>
    and kbind_sconf: \<open>kbind f a u cs n = Some (\<theta>, \<rho>, n') \<Longrightarrow>
      sconf (\<theta>, \<rho>) (insert a (ftv u \<union> ftv_cs cs)) (frv u \<union> frv_cs cs \<union> {n ..< n'})\<close>
proof (induction f cs n and f a u cs n
       arbitrary: \<theta> \<rho> n' and \<theta> \<rho> n' rule: kunify_induct)
  case (kunify_Cons_TC_TC f c ts c' ts' cs n)
  from kunify_Cons_TC_TC.prems have len: \<open>c = c' \<and> length ts = length ts'\<close>
    and ku: \<open>kunify f (zip ts ts' @ cs) n = Some (\<theta>, \<rho>, n')\<close>
    by (auto split: if_split_asm)
  show ?case
    by (rule sconf_mono[OF kunify_Cons_TC_TC.IH[OF _ ku]])
       (use len ftv_cs_zip[of ts ts'] frv_cs_zip[of ts ts'] in
         \<open>auto simp: ftv_cs_append frv_cs_append\<close>)
next
  case (kunify_Cons_TFn_TFn f u\<^sub>1 e u\<^sub>2 w\<^sub>1 g w\<^sub>2 cs n)
  from kunify_Cons_TFn_TFn.prems obtain \<rho>m n\<^sub>1 \<theta>\<^sub>1 \<rho>\<^sub>1 where
    rm: \<open>runify n e g = Some (\<rho>m, n\<^sub>1)\<close> and
    ku: \<open>kunify f (map (\<lambda>(x, y). (tsubst TV (mk_rsub \<rho>m) x, tsubst TV (mk_rsub \<rho>m) y))
                       ((u\<^sub>1, w\<^sub>1) # (u\<^sub>2, w\<^sub>2) # cs)) n\<^sub>1 = Some (\<theta>\<^sub>1, \<rho>\<^sub>1, n')\<close> and
    \<theta>: \<open>\<theta> = \<theta>\<^sub>1\<close> and \<rho>: \<open>\<rho> = (\<lambda>v. rsubst \<rho>\<^sub>1 (mk_rsub \<rho>m v))\<close>
    by (auto split: option.split_asm)
  have nn: \<open>n \<le> n\<^sub>1\<close> \<open>n\<^sub>1 \<le> n'\<close> using runify_mono[OF rm] kunify_mono[OF ku] by simp_all
  define V where \<open>V = ftv_cs ((TFn u\<^sub>1 e u\<^sub>2, TFn w\<^sub>1 g w\<^sub>2) # cs)\<close>
  define R where \<open>R = frv_cs ((TFn u\<^sub>1 e u\<^sub>2, TFn w\<^sub>1 g w\<^sub>2) # cs) \<union> {n ..< n'}\<close>
  have s1: \<open>sconf (TV, mk_rsub \<rho>m) V R\<close>
    by (rule sconf_mono[OF runify_sconf[OF rm, of V]]) (use nn in \<open>auto simp: R_def\<close>)
  have s2: \<open>sconf (\<theta>\<^sub>1, \<rho>\<^sub>1) V R\<close>
  proof (rule sconf_mono[OF kunify_Cons_TFn_TFn.IH[OF rm _ ku]])
    show \<open>ftv_cs (map (\<lambda>(x, y). (tsubst TV (mk_rsub \<rho>m) x, tsubst TV (mk_rsub \<rho>m) y))
                      ((u\<^sub>1, w\<^sub>1) # (u\<^sub>2, w\<^sub>2) # cs)) \<subseteq> V\<close>
      unfolding V_def ftv_cs_map_TV by auto
    have \<open>frv_row (mk_rsub \<rho>m v) \<subseteq> R\<close> if \<open>v \<in> frv_cs ((u\<^sub>1, w\<^sub>1) # (u\<^sub>2, w\<^sub>2) # cs)\<close> for v
      using runify_range[OF rm, of v] that nn unfolding R_def by (auto simp: frv_cs_def)
    then show \<open>frv_cs (map (\<lambda>(x, y). (tsubst TV (mk_rsub \<rho>m) x, tsubst TV (mk_rsub \<rho>m) y))
                      ((u\<^sub>1, w\<^sub>1) # (u\<^sub>2, w\<^sub>2) # cs)) \<union> {n\<^sub>1 ..< n'} \<subseteq> R\<close>
      unfolding frv_cs_map_TV using nn by (auto simp: R_def)
  qed simp
  have \<open>sconf ((\<theta>\<^sub>1, \<rho>\<^sub>1) \<odot> (TV, mk_rsub \<rho>m)) V R\<close>
    by (rule sconf_scomp_mono[OF s1 s2 subset_refl subset_refl])
  then show ?case unfolding V_def R_def \<theta> \<rho> by simp
next
  case (kunify_Cons_TDep_TDep f i sg T e u i' sg' T' g w cs n)
  from kunify_Cons_TDep_TDep.prems obtain \<rho>m n\<^sub>1 \<theta>\<^sub>1 \<rho>\<^sub>1 where
    eq: \<open>i = i'\<close> \<open>sg = sg'\<close> \<open>T = T'\<close> and
    rm: \<open>runify n e g = Some (\<rho>m, n\<^sub>1)\<close> and
    ku: \<open>kunify f (map (\<lambda>(x, y). (tsubst TV (mk_rsub \<rho>m) x, tsubst TV (mk_rsub \<rho>m) y))
                       ((u, w) # cs)) n\<^sub>1 = Some (\<theta>\<^sub>1, \<rho>\<^sub>1, n')\<close> and
    \<theta>: \<open>\<theta> = \<theta>\<^sub>1\<close> and \<rho>: \<open>\<rho> = (\<lambda>v. rsubst \<rho>\<^sub>1 (mk_rsub \<rho>m v))\<close>
    by (auto split: option.split_asm if_split_asm)
  have nn: \<open>n \<le> n\<^sub>1\<close> \<open>n\<^sub>1 \<le> n'\<close> using runify_mono[OF rm] kunify_mono[OF ku] by simp_all
  define V where \<open>V = ftv_cs ((TDep i sg T e u, TDep i' sg' T' g w) # cs)\<close>
  define R where \<open>R = frv_cs ((TDep i sg T e u, TDep i' sg' T' g w) # cs) \<union> {n ..< n'}\<close>
  have s1: \<open>sconf (TV, mk_rsub \<rho>m) V R\<close>
    by (rule sconf_mono[OF runify_sconf[OF rm, of V]]) (use nn in \<open>auto simp: R_def\<close>)
  have IH: \<open>sconf (\<theta>\<^sub>1, \<rho>\<^sub>1)
      (ftv_cs (map (\<lambda>(x, y). (tsubst TV (mk_rsub \<rho>m) x, tsubst TV (mk_rsub \<rho>m) y)) ((u, w) # cs)))
      (frv_cs (map (\<lambda>(x, y). (tsubst TV (mk_rsub \<rho>m) x, tsubst TV (mk_rsub \<rho>m) y)) ((u, w) # cs))
        \<union> {n\<^sub>1 ..< n'})\<close>
    using kunify_Cons_TDep_TDep.IH[OF _ rm _ ku] eq rm by fastforce
  have s2: \<open>sconf (\<theta>\<^sub>1, \<rho>\<^sub>1) V R\<close>
  proof (rule sconf_mono[OF IH])
    show \<open>ftv_cs (map (\<lambda>(x, y). (tsubst TV (mk_rsub \<rho>m) x, tsubst TV (mk_rsub \<rho>m) y))
                      ((u, w) # cs)) \<subseteq> V\<close>
      unfolding V_def ftv_cs_map_TV by auto
    have \<open>frv_row (mk_rsub \<rho>m v) \<subseteq> R\<close> if \<open>v \<in> frv_cs ((u, w) # cs)\<close> for v
      using runify_range[OF rm, of v] that nn unfolding R_def by (auto simp: frv_cs_def)
    then show \<open>frv_cs (map (\<lambda>(x, y). (tsubst TV (mk_rsub \<rho>m) x, tsubst TV (mk_rsub \<rho>m) y))
                      ((u, w) # cs)) \<union> {n\<^sub>1 ..< n'} \<subseteq> R\<close>
      unfolding frv_cs_map_TV using nn by (auto simp: R_def)
  qed
  have \<open>sconf ((\<theta>\<^sub>1, \<rho>\<^sub>1) \<odot> (TV, mk_rsub \<rho>m)) V R\<close>
    by (rule sconf_scomp_mono[OF s1 s2 subset_refl subset_refl])
  then show ?case unfolding V_def R_def \<theta> \<rho> by simp
next
  case (kunify_Cons_TAct_TAct f l T e u l' T' g w cs n)
  from kunify_Cons_TAct_TAct.prems obtain \<rho>m n\<^sub>1 \<theta>\<^sub>1 \<rho>\<^sub>1 where
    eq: \<open>T = T'\<close> and
    rm: \<open>runify n e g = Some (\<rho>m, n\<^sub>1)\<close> and
    ku: \<open>kunify f (map (\<lambda>(x, y). (tsubst TV (mk_rsub \<rho>m) x, tsubst TV (mk_rsub \<rho>m) y))
                       ((l, l') # (u, w) # cs)) n\<^sub>1 = Some (\<theta>\<^sub>1, \<rho>\<^sub>1, n')\<close> and
    \<theta>: \<open>\<theta> = \<theta>\<^sub>1\<close> and \<rho>: \<open>\<rho> = (\<lambda>v. rsubst \<rho>\<^sub>1 (mk_rsub \<rho>m v))\<close>
    by (auto split: option.split_asm if_split_asm)
  have nn: \<open>n \<le> n\<^sub>1\<close> \<open>n\<^sub>1 \<le> n'\<close> using runify_mono[OF rm] kunify_mono[OF ku] by simp_all
  define V where \<open>V = ftv_cs ((TAct l T e u, TAct l' T' g w) # cs)\<close>
  define R where \<open>R = frv_cs ((TAct l T e u, TAct l' T' g w) # cs) \<union> {n ..< n'}\<close>
  have s1: \<open>sconf (TV, mk_rsub \<rho>m) V R\<close>
    by (rule sconf_mono[OF runify_sconf[OF rm, of V]]) (use nn in \<open>auto simp: R_def\<close>)
  have IH: \<open>sconf (\<theta>\<^sub>1, \<rho>\<^sub>1)
      (ftv_cs (map (\<lambda>(x, y). (tsubst TV (mk_rsub \<rho>m) x, tsubst TV (mk_rsub \<rho>m) y))
        ((l, l') # (u, w) # cs)))
      (frv_cs (map (\<lambda>(x, y). (tsubst TV (mk_rsub \<rho>m) x, tsubst TV (mk_rsub \<rho>m) y))
        ((l, l') # (u, w) # cs)) \<union> {n\<^sub>1 ..< n'})\<close>
    using kunify_Cons_TAct_TAct.IH[OF _ rm _ ku] eq rm by fastforce
  have s2: \<open>sconf (\<theta>\<^sub>1, \<rho>\<^sub>1) V R\<close>
  proof (rule sconf_mono[OF IH])
    show \<open>ftv_cs (map (\<lambda>(x, y). (tsubst TV (mk_rsub \<rho>m) x, tsubst TV (mk_rsub \<rho>m) y))
                      ((l, l') # (u, w) # cs)) \<subseteq> V\<close>
      unfolding V_def ftv_cs_map_TV by auto
    have \<open>frv_row (mk_rsub \<rho>m v) \<subseteq> R\<close> if \<open>v \<in> frv_cs ((l, l') # (u, w) # cs)\<close> for v
      using runify_range[OF rm, of v] that nn unfolding R_def by (auto simp: frv_cs_def)
    then show \<open>frv_cs (map (\<lambda>(x, y). (tsubst TV (mk_rsub \<rho>m) x, tsubst TV (mk_rsub \<rho>m) y))
                      ((l, l') # (u, w) # cs)) \<union> {n\<^sub>1 ..< n'} \<subseteq> R\<close>
      unfolding frv_cs_map_TV using nn by (auto simp: R_def)
  qed
  have \<open>sconf ((\<theta>\<^sub>1, \<rho>\<^sub>1) \<odot> (TV, mk_rsub \<rho>m)) V R\<close>
    by (rule sconf_scomp_mono[OF s1 s2 subset_refl subset_refl])
  then show ?case unfolding V_def R_def \<theta> \<rho> by simp
next
  case (kbind_Suc f a u cs n)
  show ?case
  proof (cases \<open>u = TV a\<close>)
    case True
    with kbind_Suc.prems have ku: \<open>kunify f cs n = Some (\<theta>, \<rho>, n')\<close> by simp
    from True ku have \<open>sconf (\<theta>, \<rho>) (ftv_cs cs) (frv_cs cs \<union> {n ..< n'})\<close>
      by (rule kbind_Suc.IH)
    then show ?thesis by (rule sconf_mono) auto
  next
    case notv: False
    show ?thesis
    proof (cases \<open>a \<in> ftv u\<close>)
      case True with notv kbind_Suc.prems show ?thesis by simp
    next
      case notin: False
      let ?cs = \<open>map (\<lambda>(x, y). (tsubst (sing a u) RV x, tsubst (sing a u) RV y)) cs\<close>
      from kbind_Suc.prems notv notin obtain \<theta>\<^sub>1 \<rho>\<^sub>1 where
        fa: \<open>taclosed u\<close> and ku: \<open>kunify f ?cs n = Some (\<theta>\<^sub>1, \<rho>\<^sub>1, n')\<close> and
        \<theta>: \<open>\<theta> = (\<lambda>b. tsubst \<theta>\<^sub>1 \<rho>\<^sub>1 (sing a u b))\<close> and \<rho>: \<open>\<rho> = \<rho>\<^sub>1\<close>
        by (auto split: option.split_asm if_split_asm)
      have nb: \<open>\<not> (a \<in> ftv u \<or> \<not> taclosed u)\<close> using notin fa by simp
      from notv nb ku have IH: \<open>sconf (\<theta>\<^sub>1, \<rho>\<^sub>1) (ftv_cs ?cs) (frv_cs ?cs \<union> {n ..< n'})\<close>
        by (rule kbind_Suc.IH)
      define V where \<open>V = insert a (ftv u \<union> ftv_cs cs)\<close>
      define R where \<open>R = frv u \<union> frv_cs cs \<union> {n ..< n'}\<close>
      have s1: \<open>sconf (sing a u, RV) V R\<close> by (rule sconf_sing) (auto simp: V_def R_def)
      have s2: \<open>sconf (\<theta>\<^sub>1, \<rho>\<^sub>1) V R\<close>
        by (rule sconf_mono[OF IH])
           (use ftv_cs_map_sing[of a u cs] frv_cs_map_sing[of a u cs] in \<open>auto simp: V_def R_def\<close>)
      have \<open>sconf ((\<theta>\<^sub>1, \<rho>\<^sub>1) \<odot> (sing a u, RV)) V R\<close>
        by (rule sconf_scomp_mono[OF s1 s2 subset_refl subset_refl])
      then show ?thesis unfolding V_def R_def \<theta> \<rho> by simp
    qed
  qed
qed (auto simp: sconf_sid[unfolded sid_def] Un_ac split: if_split_asm option.split_asm)

lemma unis_sconf:
  \<open>unis f cs n = Some (s, n') \<Longrightarrow> sconf s (ftv_cs cs) (frv_cs cs \<union> {n ..< n'})\<close>
  using kunify_sconf by (auto simp: unis_def split: option.split_asm)

lemma uni_sconf:
  \<open>uni f t\<^sub>1 t\<^sub>2 n = Some (s, n') \<Longrightarrow> sconf s (ftv t\<^sub>1 \<union> ftv t\<^sub>2) (frv t\<^sub>1 \<union> frv t\<^sub>2 \<union> {n ..< n'})\<close>
  using unis_sconf[of f \<open>[(t\<^sub>1, t\<^sub>2)]\<close> n s n'] by (simp add: uni_def Un_assoc)

text \<open>Hygiene of the abstract types: the unifier of constraints whose free
  abstract types lie in \<open>FK\<close> has ranges whose free abstract types lie in
  \<open>FK\<close>. The scope check at a binder is what keeps the bound ones inside.\<close>

definition ktv_cs :: \<open>(kty \<times> kty) list \<Rightarrow> tvar set\<close> where
  \<open>ktv_cs cs = (\<Union>(t, u) \<in> set cs. ktv t \<union> ktv u)\<close>

lemma ktv_cs_simps[simp]:
  \<open>ktv_cs [] = {}\<close> \<open>ktv_cs ((t, u) # cs) = ktv t \<union> ktv u \<union> ktv_cs cs\<close>
  by (auto simp: ktv_cs_def)

lemma ktv_cs_append: \<open>ktv_cs (cs\<^sub>1 @ cs\<^sub>2) = ktv_cs cs\<^sub>1 \<union> ktv_cs cs\<^sub>2\<close>
  by (auto simp: ktv_cs_def)

lemma ktv_cs_zip: \<open>ktv_cs (zip ts ts') \<subseteq> (\<Union>t\<in>set ts. ktv t) \<union> (\<Union>t\<in>set ts'. ktv t)\<close>
  by (fastforce simp: ktv_cs_def dest: set_zip_leftD set_zip_rightD)

lemma ktv_cs_map_TV:
  \<open>ktv_cs (map (\<lambda>(x, y). (tsubst TV \<rho> x, tsubst TV \<rho> y)) cs) = ktv_cs cs\<close>
  by (induction cs) (auto simp: ktv_cs_def)

lemma ktv_sing: \<open>ktv (sing a u b) \<subseteq> ktv u\<close>
  by (simp add: sing_def)

lemma ktv_tsubst_sing: \<open>ktv (tsubst (sing a u) RV t) \<subseteq> ktv t \<union> ktv u\<close>
  using ktv_tsubst[of \<open>sing a u\<close> RV t] ktv_sing[of a u] by blast

lemma ktv_cs_map_sing:
  \<open>ktv_cs (map (\<lambda>(x, y). (tsubst (sing a u) RV x, tsubst (sing a u) RV y)) cs) \<subseteq> ktv u \<union> ktv_cs cs\<close>
  unfolding ktv_cs_def by (auto dest!: subsetD[OF ktv_tsubst_sing])

lemma
  shows kunify_khyg: \<open>kunify f cs n = Some (\<theta>, \<rho>, n') \<Longrightarrow> ktv_cs cs \<subseteq> FK \<Longrightarrow> \<forall>a. ktv (\<theta> a) \<subseteq> FK\<close>
    and kbind_khyg: \<open>kbind f a u cs n = Some (\<theta>, \<rho>, n') \<Longrightarrow> ktv u \<subseteq> FK \<Longrightarrow>
      ktv_cs cs \<subseteq> FK \<Longrightarrow> \<forall>b. ktv (\<theta> b) \<subseteq> FK\<close>
proof (induction f cs n and f a u cs n
       arbitrary: \<theta> \<rho> n' FK and \<theta> \<rho> n' FK rule: kunify_induct)
  case (kunify_Cons_TC_TC f c ts c' ts' cs n)
  from kunify_Cons_TC_TC.prems have len: \<open>c = c' \<and> length ts = length ts'\<close>
    and ku: \<open>kunify f (zip ts ts' @ cs) n = Some (\<theta>, \<rho>, n')\<close>
    by (auto split: if_split_asm)
  have \<open>ktv_cs ((TC c ts, TC c' ts') # cs) \<subseteq> FK\<close> by fact
  then have k: \<open>ktv_cs (zip ts ts' @ cs) \<subseteq> FK\<close>
    using subset_trans[OF ktv_cs_zip[of ts ts'] Un_least] unfolding ktv_cs_append by auto
  show ?case by (rule kunify_Cons_TC_TC.IH[OF _ ku k]) (use len in simp)
next
  case (kunify_Cons_TFn_TFn f u\<^sub>1 e u\<^sub>2 w\<^sub>1 g w\<^sub>2 cs n)
  from kunify_Cons_TFn_TFn.prems obtain \<rho>m n\<^sub>1 \<rho>\<^sub>1 where
    rm: \<open>runify n e g = Some (\<rho>m, n\<^sub>1)\<close> and
    ku: \<open>kunify f (map (\<lambda>(x, y). (tsubst TV (mk_rsub \<rho>m) x, tsubst TV (mk_rsub \<rho>m) y))
                       ((u\<^sub>1, w\<^sub>1) # (u\<^sub>2, w\<^sub>2) # cs)) n\<^sub>1 = Some (\<theta>, \<rho>\<^sub>1, n')\<close>
    by (auto split: option.split_asm)
  have k: \<open>ktv_cs ((TFn u\<^sub>1 e u\<^sub>2, TFn w\<^sub>1 g w\<^sub>2) # cs) \<subseteq> FK\<close> by fact
  show ?case by (rule kunify_Cons_TFn_TFn.IH[OF rm _ ku]) (use k in \<open>auto simp: ktv_cs_map_TV\<close>)
next
  case (kunify_Cons_TDep_TDep f i sg T e u i' sg' T' g w cs n)
  from kunify_Cons_TDep_TDep.prems obtain \<rho>m n\<^sub>1 \<rho>\<^sub>1 where
    eq: \<open>i = i'\<close> \<open>sg = sg'\<close> \<open>T = T'\<close> and
    rm: \<open>runify n e g = Some (\<rho>m, n\<^sub>1)\<close> and
    ku: \<open>kunify f (map (\<lambda>(x, y). (tsubst TV (mk_rsub \<rho>m) x, tsubst TV (mk_rsub \<rho>m) y))
                       ((u, w) # cs)) n\<^sub>1 = Some (\<theta>, \<rho>\<^sub>1, n')\<close>
    by (auto split: option.split_asm if_split_asm)
  have \<open>ktv_cs ((TDep i sg T e u, TDep i' sg' T' g w) # cs) \<subseteq> FK\<close> by fact
  then show ?case
    using kunify_Cons_TDep_TDep.IH[of _ \<rho>m n\<^sub>1 \<theta> \<rho>\<^sub>1 n' FK] eq rm ku
    by (auto simp: ktv_cs_map_TV)
next
  case (kunify_Cons_TAct_TAct f l T e u l' T' g w cs n)
  from kunify_Cons_TAct_TAct.prems obtain \<rho>m n\<^sub>1 \<rho>\<^sub>1 where
    eq: \<open>T = T'\<close> and
    rm: \<open>runify n e g = Some (\<rho>m, n\<^sub>1)\<close> and
    ku: \<open>kunify f (map (\<lambda>(x, y). (tsubst TV (mk_rsub \<rho>m) x, tsubst TV (mk_rsub \<rho>m) y))
                       ((l, l') # (u, w) # cs)) n\<^sub>1 = Some (\<theta>, \<rho>\<^sub>1, n')\<close> and
    chk: \<open>\<forall>a \<in> ftv_cs ((l, l') # (u, w) # cs). set T \<inter> ktv (\<theta> a) = {}\<close>
    by (auto split: option.split_asm if_split_asm)
  have \<open>ktv_cs ((TAct l T e u, TAct l' T' g w) # cs) \<subseteq> FK\<close> by fact
  then have IH: \<open>\<forall>a. ktv (\<theta> a) \<subseteq> FK \<union> set T\<close>
    using kunify_Cons_TAct_TAct.IH[of _ \<rho>m n\<^sub>1 \<theta> \<rho>\<^sub>1 n' \<open>FK \<union> set T\<close>] eq rm ku
    by (auto simp: ktv_cs_map_TV) blast
  have id: \<open>\<theta> a = TV a\<close> if \<open>a \<notin> ftv_cs ((l, l') # (u, w) # cs)\<close> for a
    using kunify_sconf[OF ku] that unfolding sconf_def ftv_cs_map_TV by simp
  show ?case
  proof (rule allI)
    fix a show \<open>ktv (\<theta> a) \<subseteq> FK\<close>
    proof (cases \<open>a \<in> ftv_cs ((l, l') # (u, w) # cs)\<close>)
      case True
      then show ?thesis using IH[rule_format, of a] chk[rule_format, OF True] by blast
    qed (simp add: id)
  qed
next
  case (kbind_Suc f a u cs n)
  show ?case
  proof (cases \<open>u = TV a\<close>)
    case True
    with kbind_Suc.prems have ku: \<open>kunify f cs n = Some (\<theta>, \<rho>, n')\<close> by simp
    from True ku \<open>ktv_cs cs \<subseteq> FK\<close> show ?thesis by (rule kbind_Suc.IH)
  next
    case notv: False
    show ?thesis
    proof (cases \<open>a \<in> ftv u\<close>)
      case True with notv kbind_Suc.prems show ?thesis by simp
    next
      case notin: False
      from kbind_Suc.prems notv notin obtain \<theta>\<^sub>1 \<rho>\<^sub>1 where
        fa: \<open>taclosed u\<close> and
        ku: \<open>kunify f (map (\<lambda>(x, y). (tsubst (sing a u) RV x, tsubst (sing a u) RV y)) cs) n
               = Some (\<theta>\<^sub>1, \<rho>\<^sub>1, n')\<close> and
        \<theta>: \<open>\<theta> = (\<lambda>b. tsubst \<theta>\<^sub>1 \<rho>\<^sub>1 (sing a u b))\<close>
        by (auto split: option.split_asm if_split_asm)
      have nb: \<open>\<not> (a \<in> ftv u \<or> \<not> taclosed u)\<close> using notin fa by simp
      from notv nb ku have IH: \<open>\<forall>b. ktv (\<theta>\<^sub>1 b) \<subseteq> FK\<close>
        by (rule kbind_Suc.IH)
           (use \<open>ktv u \<subseteq> FK\<close> \<open>ktv_cs cs \<subseteq> FK\<close> ktv_cs_map_sing[of a u cs] in auto)
      have \<open>ktv (sing a u b) \<subseteq> FK\<close> for b using \<open>ktv u \<subseteq> FK\<close> ktv_sing[of a u b] by blast
      then show ?thesis unfolding \<theta> by (intro allI ktv_tsubst_sub) (use IH in auto)
    qed
  qed
qed (auto split: if_split_asm option.split_asm)

lemma unis_khyg:
  assumes u: \<open>unis f cs n = Some (s, n')\<close> and k: \<open>ktv_cs cs \<subseteq> FK\<close>
  shows \<open>khyg s FK\<close>
proof -
  from u obtain \<theta> \<rho> where \<open>s = (\<theta>, \<rho>)\<close> and ku: \<open>kunify f cs n = Some (\<theta>, \<rho>, n')\<close>
    unfolding unis_def by (auto split: option.split_asm)
  then show ?thesis using kunify_khyg[OF ku k] by (simp add: khyg_def)
qed

lemma uni_khyg: \<open>uni f t\<^sub>1 t\<^sub>2 n = Some (s, n') \<Longrightarrow> ktv t\<^sub>1 \<subseteq> FK \<Longrightarrow> ktv t\<^sub>2 \<subseteq> FK \<Longrightarrow> khyg s FK\<close>
  using unis_khyg[of f \<open>[(t\<^sub>1, t\<^sub>2)]\<close> n s n' FK] by (simp add: uni_def)

lemma uni_row_khyg: \<open>uni_row r\<^sub>1 r\<^sub>2 n = Some (s, n') \<Longrightarrow> khyg s FK\<close>
  by (auto simp: uni_row_def khyg_def split: option.split_asm)

text \<open>Ranges are free of bound variables when the constraints are.\<close>

definition bfree_cs :: \<open>(kty \<times> kty) list \<Rightarrow> bool\<close> where
  \<open>bfree_cs cs \<longleftrightarrow> (\<forall>(t, u) \<in> set cs. bfree t \<and> bfree u)\<close>

lemma bfree_cs_simps[simp]:
  \<open>bfree_cs []\<close> \<open>bfree_cs ((t, u) # cs) \<longleftrightarrow> bfree t \<and> bfree u \<and> bfree_cs cs\<close>
  by (auto simp: bfree_cs_def)

lemma bfree_cs_append: \<open>bfree_cs (cs\<^sub>1 @ cs\<^sub>2) \<longleftrightarrow> bfree_cs cs\<^sub>1 \<and> bfree_cs cs\<^sub>2\<close>
  by (auto simp: bfree_cs_def)

lemma bfree_cs_zip: \<open>\<forall>t\<in>set ts. bfree t \<Longrightarrow> \<forall>t\<in>set ts'. bfree t \<Longrightarrow> bfree_cs (zip ts ts')\<close>
  by (fastforce simp: bfree_cs_def dest: set_zip_leftD set_zip_rightD)

lemma bfree_simps[simp]:
  \<open>bfree (TV a)\<close> \<open>bfree (TK a)\<close> \<open>bfree (TA d j)\<close> \<open>bfree (TC c ts) \<longleftrightarrow> (\<forall>t\<in>set ts. bfree t)\<close>
  \<open>bfree (TApp t\<^sub>1 t\<^sub>2) \<longleftrightarrow> bfree t\<^sub>1 \<and> bfree t\<^sub>2\<close>
  \<open>bfree (TFn t\<^sub>1 e t\<^sub>2) \<longleftrightarrow> bfree t\<^sub>1 \<and> brv_row e = {} \<and> bfree t\<^sub>2\<close>
  \<open>bfree (TDep i sg m e t) \<longleftrightarrow> brv_row e = {} \<and> bfree t\<close>
  \<open>bfree (TEv l s t) \<longleftrightarrow> bfree l \<and> bfree s \<and> bfree t\<close>
  \<open>bfree (TAct l K e t) \<longleftrightarrow> bfree l \<and> brv_row e = {} \<and> bfree t\<close>
  by (auto simp: bfree_def)

lemma brv_row_mk_row[simp]: \<open>brv_row (mk_row xs t) = brv_row t\<close>
proof -
  have \<open>brv_row (foldr RCons xs r) = brv_row r\<close> for r by (induction xs) auto
  then show ?thesis by (simp add: mk_row_def)
qed

lemma brv_row_tail: \<open>brv_row r = (case row_tail r of RB v \<Rightarrow> {v} | _ \<Rightarrow> {})\<close>
  by (induction r) (auto split: krow.split)

lemma runify_bfree:
  assumes \<open>runify n r\<^sub>1 r\<^sub>2 = Some (\<sigma>, n')\<close> \<open>brv_row r\<^sub>1 = {}\<close> \<open>brv_row r\<^sub>2 = {}\<close>
  shows \<open>brv_row (mk_rsub \<sigma> v) = {}\<close>
  using assms row_tail_is_tail[of r\<^sub>1] row_tail_is_tail[of r\<^sub>2]
  unfolding runify_def mk_rsub_def brv_row_tail
  by (auto split: krow.splits if_split_asm)

lemma bfree_tsubst:
  \<open>(\<And>a. bfree (\<theta> a)) \<Longrightarrow> (\<And>v. brv_row (\<rho> v) = {}) \<Longrightarrow> bfree t \<Longrightarrow> bfree (tsubst \<theta> \<rho> t)\<close>
  by (auto simp: bfree_def btv_tsubst brv_tsubst)

lemma bfree_sing: \<open>bfree u \<Longrightarrow> bfree (sing a u b)\<close>
  by (simp add: sing_def)

lemma bfree_cs_map_row:
  \<open>bfree_cs cs \<Longrightarrow> (\<And>v. brv_row (\<rho> v) = {}) \<Longrightarrow>
   bfree_cs (map (\<lambda>(x, y). (tsubst TV \<rho> x, tsubst TV \<rho> y)) cs)\<close>
  by (auto simp: bfree_cs_def intro!: bfree_tsubst)

lemma bfree_cs_map_sing:
  \<open>bfree_cs cs \<Longrightarrow> bfree u \<Longrightarrow>
   bfree_cs (map (\<lambda>(x, y). (tsubst (sing a u) RV x, tsubst (sing a u) RV y)) cs)\<close>
  by (auto simp: bfree_cs_def intro!: bfree_tsubst bfree_sing)

lemma
  shows kunify_bfree: \<open>kunify f cs n = Some (\<theta>, \<rho>, n') \<Longrightarrow> bfree_cs cs \<Longrightarrow> bfree_sub (\<theta>, \<rho>)\<close>
    and kbind_bfree: \<open>kbind f a u cs n = Some (\<theta>, \<rho>, n') \<Longrightarrow> bfree u \<Longrightarrow> bfree_cs cs \<Longrightarrow> bfree_sub (\<theta>, \<rho>)\<close>
proof (induction f cs n and f a u cs n
       arbitrary: \<theta> \<rho> n' and \<theta> \<rho> n' rule: kunify_induct)
  case (kunify_Cons_TC_TC f c ts c' ts' cs n)
  from kunify_Cons_TC_TC.prems have len: \<open>c = c' \<and> length ts = length ts'\<close>
    and ku: \<open>kunify f (zip ts ts' @ cs) n = Some (\<theta>, \<rho>, n')\<close>
    by (auto split: if_split_asm)
  have bc: \<open>bfree_cs ((TC c ts, TC c' ts') # cs)\<close> by fact
  show ?case
    by (rule kunify_Cons_TC_TC.IH[OF _ ku])
       (use len bc in \<open>auto simp: bfree_cs_append bfree_cs_zip\<close>)
next
  case (kunify_Cons_TFn_TFn f u\<^sub>1 e u\<^sub>2 w\<^sub>1 g w\<^sub>2 cs n)
  from kunify_Cons_TFn_TFn.prems obtain \<rho>m n\<^sub>1 \<theta>\<^sub>1 \<rho>\<^sub>1 where
    rm: \<open>runify n e g = Some (\<rho>m, n\<^sub>1)\<close> and
    ku: \<open>kunify f (map (\<lambda>(x, y). (tsubst TV (mk_rsub \<rho>m) x, tsubst TV (mk_rsub \<rho>m) y))
                       ((u\<^sub>1, w\<^sub>1) # (u\<^sub>2, w\<^sub>2) # cs)) n\<^sub>1 = Some (\<theta>\<^sub>1, \<rho>\<^sub>1, n')\<close> and
    \<theta>: \<open>\<theta> = \<theta>\<^sub>1\<close> and \<rho>: \<open>\<rho> = (\<lambda>v. rsubst \<rho>\<^sub>1 (mk_rsub \<rho>m v))\<close>
    by (auto split: option.split_asm)
  have bc: \<open>bfree_cs ((TFn u\<^sub>1 e u\<^sub>2, TFn w\<^sub>1 g w\<^sub>2) # cs)\<close> by fact
  have rb: \<open>brv_row (mk_rsub \<rho>m v) = {}\<close> for v
    using runify_bfree[OF rm] bc by simp
  have \<open>bfree_cs ((u\<^sub>1, w\<^sub>1) # (u\<^sub>2, w\<^sub>2) # cs)\<close> using bc by simp
  from bfree_cs_map_row[OF this rb] have \<open>bfree_sub (\<theta>\<^sub>1, \<rho>\<^sub>1)\<close>
    using kunify_Cons_TFn_TFn.IH[OF rm _ ku] rm by fastforce
  then show ?case unfolding \<theta> \<rho> using rb by (auto simp: bfree_sub_def brv_rsubst)
next
  case (kunify_Cons_TDep_TDep f i sg T e u i' sg' T' g w cs n)
  from kunify_Cons_TDep_TDep.prems obtain \<rho>m n\<^sub>1 \<theta>\<^sub>1 \<rho>\<^sub>1 where
    eq: \<open>i = i'\<close> \<open>sg = sg'\<close> \<open>T = T'\<close> and
    rm: \<open>runify n e g = Some (\<rho>m, n\<^sub>1)\<close> and
    ku: \<open>kunify f (map (\<lambda>(x, y). (tsubst TV (mk_rsub \<rho>m) x, tsubst TV (mk_rsub \<rho>m) y))
                       ((u, w) # cs)) n\<^sub>1 = Some (\<theta>\<^sub>1, \<rho>\<^sub>1, n')\<close> and
    \<theta>: \<open>\<theta> = \<theta>\<^sub>1\<close> and \<rho>: \<open>\<rho> = (\<lambda>v. rsubst \<rho>\<^sub>1 (mk_rsub \<rho>m v))\<close>
    by (auto split: option.split_asm if_split_asm)
  have bc: \<open>bfree_cs ((TDep i sg T e u, TDep i' sg' T' g w) # cs)\<close> by fact
  have rb: \<open>brv_row (mk_rsub \<rho>m v) = {}\<close> for v
    using runify_bfree[OF rm] bc by simp
  have \<open>bfree_cs ((u, w) # cs)\<close> using bc by simp
  from bfree_cs_map_row[OF this rb] have \<open>bfree_sub (\<theta>\<^sub>1, \<rho>\<^sub>1)\<close>
    using kunify_Cons_TDep_TDep.IH[OF _ rm _ ku] eq rm by fastforce
  then show ?case unfolding \<theta> \<rho> using rb by (auto simp: bfree_sub_def brv_rsubst)
next
  case (kunify_Cons_TAct_TAct f l T e u l' T' g w cs n)
  from kunify_Cons_TAct_TAct.prems obtain \<rho>m n\<^sub>1 \<theta>\<^sub>1 \<rho>\<^sub>1 where
    eq: \<open>T = T'\<close> and
    rm: \<open>runify n e g = Some (\<rho>m, n\<^sub>1)\<close> and
    ku: \<open>kunify f (map (\<lambda>(x, y). (tsubst TV (mk_rsub \<rho>m) x, tsubst TV (mk_rsub \<rho>m) y))
                       ((l, l') # (u, w) # cs)) n\<^sub>1 = Some (\<theta>\<^sub>1, \<rho>\<^sub>1, n')\<close> and
    \<theta>: \<open>\<theta> = \<theta>\<^sub>1\<close> and \<rho>: \<open>\<rho> = (\<lambda>v. rsubst \<rho>\<^sub>1 (mk_rsub \<rho>m v))\<close>
    by (auto split: option.split_asm if_split_asm)
  have bc: \<open>bfree_cs ((TAct l T e u, TAct l' T' g w) # cs)\<close> by fact
  have rb: \<open>brv_row (mk_rsub \<rho>m v) = {}\<close> for v
    using runify_bfree[OF rm] bc by simp
  have \<open>bfree_cs ((l, l') # (u, w) # cs)\<close> using bc by simp
  from bfree_cs_map_row[OF this rb] have \<open>bfree_sub (\<theta>\<^sub>1, \<rho>\<^sub>1)\<close>
    using kunify_Cons_TAct_TAct.IH[OF _ rm _ ku] eq rm by fastforce
  then show ?case unfolding \<theta> \<rho> using rb by (auto simp: bfree_sub_def brv_rsubst)
next
  case (kbind_Suc f a u cs n)
  show ?case
  proof (cases \<open>u = TV a\<close>)
    case True
    with kbind_Suc.prems have ku: \<open>kunify f cs n = Some (\<theta>, \<rho>, n')\<close> by simp
    from True ku \<open>bfree_cs cs\<close> show ?thesis by (rule kbind_Suc.IH)
  next
    case notv: False
    show ?thesis
    proof (cases \<open>a \<in> ftv u\<close>)
      case True with notv kbind_Suc.prems show ?thesis by simp
    next
      case notin: False
      from kbind_Suc.prems notv notin obtain \<theta>\<^sub>1 \<rho>\<^sub>1 where
        fa: \<open>taclosed u\<close> and
        ku: \<open>kunify f (map (\<lambda>(x, y). (tsubst (sing a u) RV x, tsubst (sing a u) RV y)) cs) n
               = Some (\<theta>\<^sub>1, \<rho>\<^sub>1, n')\<close> and
        \<theta>: \<open>\<theta> = (\<lambda>b. tsubst \<theta>\<^sub>1 \<rho>\<^sub>1 (sing a u b))\<close> and \<rho>: \<open>\<rho> = \<rho>\<^sub>1\<close>
        by (auto split: option.split_asm if_split_asm)
      have nb: \<open>\<not> (a \<in> ftv u \<or> \<not> taclosed u)\<close> using notin fa by simp
      from notv nb ku have IH: \<open>bfree_sub (\<theta>\<^sub>1, \<rho>\<^sub>1)\<close>
        by (rule kbind_Suc.IH)
           (use \<open>bfree u\<close> \<open>bfree_cs cs\<close> in \<open>auto simp: bfree_cs_map_sing\<close>)
      show ?thesis
        unfolding \<theta> \<rho> using IH \<open>bfree u\<close> bfree_sapp[of \<open>(\<theta>\<^sub>1, \<rho>\<^sub>1)\<close>] fa
        by (auto simp: bfree_sub_def sing_def intro: taok_tsubst)
    qed
  qed
qed (auto simp: bfree_sub_def bfree_def split: if_split_asm option.split_asm)

lemma unis_bfree: \<open>unis f cs n = Some (s, n') \<Longrightarrow> bfree_cs cs \<Longrightarrow> bfree_sub s\<close>
  using kunify_bfree by (auto simp: unis_def split: option.split_asm)

lemma uni_bfree: \<open>uni f t\<^sub>1 t\<^sub>2 n = Some (s, n') \<Longrightarrow> bfree t\<^sub>1 \<Longrightarrow> bfree t\<^sub>2 \<Longrightarrow> bfree_sub s\<close>
  using unis_bfree[of f \<open>[(t\<^sub>1, t\<^sub>2)]\<close> n s n'] by (simp add: uni_def)

lemma uni_row_bfree:
  \<open>uni_row r\<^sub>1 r\<^sub>2 n = Some (s, n') \<Longrightarrow> brv_row r\<^sub>1 = {} \<Longrightarrow> brv_row r\<^sub>2 = {} \<Longrightarrow> bfree_sub s\<close>
  by (auto simp: uni_row_def bfree_sub_def bfree_def runify_bfree split: option.split_asm)


subsection \<open>Static elaboration is invariant under substitution\<close>

text \<open>Signatures, annotations, constructor and operation lookups,
  exhaustiveness, the value restriction and implicit resolution read only
  the entries substitution leaves alone: two bases whose lookups agree up
  to the schemes of values give the same results.

  \<^text>\<open>lookup_eq\<close> is that agreement (\<^text>\<open>ent_sim\<close> relates any two value
  entries and every other entry to itself), and a basis agrees with each of
  its substitution instances (\<^text>\<open>lookup_eq_sappe\<close>).\<close>

fun ent_sim :: \<open>tentry \<Rightarrow> tentry \<Rightarrow> bool\<close> where
  \<open>ent_sim (TEval \<sigma>) e' \<longleftrightarrow> (\<exists>\<sigma>'. e' = TEval \<sigma>')\<close>
| \<open>ent_sim e e' \<longleftrightarrow> e' = e\<close>

definition lookup_eq :: \<open>tenv \<Rightarrow> tenv \<Rightarrow> bool\<close> where
  \<open>lookup_eq B B' \<longleftrightarrow> (\<forall>p. rel_option ent_sim (tlookup B p) (tlookup B' p))\<close>

lemma ent_sim_refl[simp]: \<open>ent_sim e e\<close>
  by (cases e) auto

lemma ent_sim_sub_ent: \<open>ent_sim e (sub_ent \<theta> \<rho> e)\<close>
  by (cases e) auto

lemma lookup_eq_refl[simp]: \<open>lookup_eq B B\<close>
  by (simp add: lookup_eq_def option.rel_refl)

lemma lookup_eqE:
  assumes \<open>lookup_eq B B'\<close>
  obtains (None) \<open>tlookup B p = None\<close> \<open>tlookup B' p = None\<close>
    | (Val) \<sigma> \<sigma>' where \<open>tlookup B p = Some (TEval \<sigma>)\<close> \<open>tlookup B' p = Some (TEval \<sigma>')\<close>
    | (Other) e where \<open>tlookup B p = Some e\<close> \<open>tlookup B' p = Some e\<close> \<open>\<forall>\<sigma>. e \<noteq> TEval \<sigma>\<close>
proof -
  have \<open>rel_option ent_sim (tlookup B p) (tlookup B' p)\<close> using assms by (simp add: lookup_eq_def)
  then show thesis
    by (cases \<open>tlookup B p\<close>; cases \<open>tlookup B' p\<close>)
       (auto intro: None Val Other elim!: ent_sim.elims)
qed

lemma lookup_eq_sub_env: \<open>lookup_eq B (sub_env \<theta> \<rho> B)\<close>
proof (unfold lookup_eq_def, intro allI)
  fix p show \<open>rel_option ent_sim (tlookup B p) (tlookup (sub_env \<theta> \<rho> B) p)\<close>
  proof (cases p)
    case (Cons x xs)
    then show ?thesis
      by (cases xs) (auto simp: map_of_sub_env ent_sim_sub_ent option.rel_map
                          intro!: option.rel_refl_strong split: option.split tentry.split)
  qed simp
qed

lemma lookup_eq_sappe: \<open>lookup_eq B (sappe s B)\<close>
  by (cases s) (simp add: lookup_eq_sub_env)

lemma tlookup_Cons:
  \<open>tlookup ((x, e) # B) (y # ys) =
   (if y = x
    then (case ys of [] \<Rightarrow> Some e
          | _ \<Rightarrow> (case e of TEstr ex \<Rightarrow> tlookup ex ys | TEinst ex \<Rightarrow> tlookup ex ys | _ \<Rightarrow> None))
    else tlookup B (y # ys))\<close>
  by (cases ys) (auto split: tentry.split)

lemma lookup_eq_Cons: \<open>lookup_eq B B' \<Longrightarrow> lookup_eq ((x, e) # B) ((x, e) # B')\<close>
proof (unfold lookup_eq_def, intro allI)
  fix p assume a: \<open>\<forall>p. rel_option ent_sim (tlookup B p) (tlookup B' p)\<close>
  show \<open>rel_option ent_sim (tlookup ((x, e) # B) p) (tlookup ((x, e) # B') p)\<close>
    by (cases p) (auto simp: tlookup_Cons a option.rel_refl split: list.split tentry.split)
qed

lemma lookup_eq_append: \<open>lookup_eq B B' \<Longrightarrow> lookup_eq (E @ B) (E @ B')\<close>
  by (induction E) (auto simp: lookup_eq_Cons)

lemma bind_eq_cong: \<open>x = y \<Longrightarrow> (\<And>v. x = Some v \<Longrightarrow> f v = g v) \<Longrightarrow> x \<bind> f = y \<bind> g\<close>
  by (cases x) auto

lemma head_stat_eq: \<open>lookup_eq B B' \<Longrightarrow> head_stat B fr ve n p args = head_stat B' fr ve n p args\<close>
  by (cases rule: lookup_eqE[of B B' \<open>path_nms p\<close>]) (cases ve, auto)+

lemma eff_at_eq: \<open>lookup_eq B B' \<Longrightarrow> eff_at B p ar = eff_at B' p ar\<close>
  by (cases rule: lookup_eqE[of B B' \<open>path_nms p\<close>]) (auto simp: eff_at_def)

lemma name_at_eq:
  assumes \<open>lookup_eq B B'\<close>
  shows \<open>name_at B p = name_at B' p\<close>
proof (cases \<open>path_nms p\<close>)
  case (Cons x xs)
  show ?thesis unfolding name_at_def Cons
    by (cases rule: lookup_eqE[OF assms, of \<open>[nkey x]\<close>]) (auto split: list.split)
qed (simp add: name_at_def)

lemma label_stat_eq:
  assumes \<open>lookup_eq B B'\<close>
  shows \<open>label_stat B t = label_stat B' t\<close>
proof (cases \<open>(B, t)\<close> rule: label_stat_cases)
  case (TSpine_Cons_TPath_Nil B\<^sub>1 p)
  then have t: \<open>t = TSpine [TPath p]\<close> by simp
  have *: \<open>(case tlookup B (path_nms p) of
               Some (TEeff l ls ar) \<Rightarrow> Some (map (mangle l) ls) | _ \<Rightarrow> None)
         = (case tlookup B' (path_nms p) of
               Some (TEeff l ls ar) \<Rightarrow> Some (map (mangle l) ls) | _ \<Rightarrow> None)\<close>
    by (cases rule: lookup_eqE[OF assms, of \<open>path_nms p\<close>]) auto
  show ?thesis unfolding t label_stat.simps name_at_eq[OF assms] * ..
qed simp_all

lemma labels_stat_eq: \<open>lookup_eq B B' \<Longrightarrow> labels_stat B ts = labels_stat B' ts\<close>
  by (induction ts) (auto simp: label_stat_eq)

lemma
  shows ty_stat_eq: \<open>lookup_eq B B' \<Longrightarrow> ty_stat B fr ve n t = ty_stat B' fr ve n t\<close>
    and atoms_stat_eq: \<open>lookup_eq B B' \<Longrightarrow> atoms_stat B fr ve n as = atoms_stat B' fr ve n as\<close>
    and atom_stat_eq: \<open>lookup_eq B B' \<Longrightarrow> atom_stat B fr ve n a = atom_stat B' fr ve n a\<close>
    and tys_stat_eq: \<open>lookup_eq B B' \<Longrightarrow> tys_stat B fr ve n ts = tys_stat B' fr ve n ts\<close>
    and spine_stat_eq: \<open>lookup_eq B B' \<Longrightarrow> spine_stat B fr ve n as = spine_stat B' fr ve n as\<close>
    and row_stat_eq: \<open>lookup_eq B B' \<Longrightarrow> row_stat B fr ve n ro = row_stat B' fr ve n ro\<close>
proof (induction B fr ve n t and B fr ve n as and B fr ve n a and B fr ve n ts and B fr ve n as
       and B fr ve n ro arbitrary: B' and B' and B' and B' and B' and B'
       rule: ty_stat_induct)
  case (ty_stat_TArrow B fr ve n as ro t)
  have IH1: \<open>spine_stat B fr ve n as = spine_stat B' fr ve n as\<close>
    using ty_stat_TArrow.prems by (rule ty_stat_TArrow.IH)
  show ?case
    unfolding ty_stat.simps
  proof (rule bind_eq_cong[OF IH1], goal_cases spine)
    case (spine v)
    obtain t\<^sub>1 tvs\<^sub>1 rvs\<^sub>1 n\<^sub>1 where v: \<open>v = (t\<^sub>1, (tvs\<^sub>1, rvs\<^sub>1), n\<^sub>1)\<close> by (cases v) auto
    have IH2: \<open>row_stat B fr (tvs\<^sub>1, rvs\<^sub>1) n\<^sub>1 ro = row_stat B' fr (tvs\<^sub>1, rvs\<^sub>1) n\<^sub>1 ro\<close>
      using spine[unfolded v] refl refl ty_stat_TArrow.prems by (rule ty_stat_TArrow.IH)
    show ?case
      unfolding v prod.case
    proof (rule bind_eq_cong[OF IH2], goal_cases row)
      case (row w)
      obtain e tvs\<^sub>2 rvs\<^sub>2 n\<^sub>2 where w: \<open>w = (e, (tvs\<^sub>2, rvs\<^sub>2), n\<^sub>2)\<close> by (cases w) auto
      have \<open>ty_stat B fr (tvs\<^sub>2, rvs\<^sub>2) n\<^sub>2 t = ty_stat B' fr (tvs\<^sub>2, rvs\<^sub>2) n\<^sub>2 t\<close>
        using spine[unfolded v] refl refl row[unfolded w] refl refl ty_stat_TArrow.prems
        by (rule ty_stat_TArrow.IH)
      then show ?case unfolding w prod.case by simp
    qed
  qed
next
  case (atom_stat_TParen B fr ve n ts)
  show ?case
  proof (cases ts)
    case Nil then show ?thesis by simp
  next
    case (Cons t ts')
    show ?thesis
    proof (cases ts')
      case Nil
      have \<open>ty_stat B fr ve n t = ty_stat B' fr ve n t\<close>
        using atom_stat_TParen.IH atom_stat_TParen.prems Cons Nil by blast
      then show ?thesis using Cons Nil by simp
    next
      case (Cons t' ts'')
      have \<open>tys_stat B fr ve n ts = tys_stat B' fr ve n ts\<close>
        using atom_stat_TParen.IH atom_stat_TParen.prems \<open>ts = t # ts'\<close> Cons by blast
      then show ?thesis using \<open>ts = t # ts'\<close> Cons by simp
    qed
  qed
next
  case (atom_stat_TName B fr ve n e)
  show ?case
  proof (cases e)
    case (Cons x as)
    show ?thesis
    proof (cases x)
      case (TPath p)
      have \<open>atoms_stat B fr ve n as = atoms_stat B' fr ve n as\<close> if fr
        using Cons TPath that atom_stat_TName.prems by (rule atom_stat_TName.IH)
      then show ?thesis
        unfolding Cons TPath
        by (auto simp: eff_at_eq[OF atom_stat_TName.prems] split: prod.split cong: Option.bind_cong)
    qed (use Cons in simp_all)
  qed simp
next
  case (ty_stat_TArrowName B fr ve n f e ro t)
  note L = lookup_eq_Cons[OF ty_stat_TArrowName.prems]
  show ?case
  proof (cases e)
    case (Cons x as)
    show ?thesis
    proof (cases x)
      case (TPath p)
      show ?thesis
      proof (cases \<open>nm_ok (n_txt f)\<close>)
        case True
        have IH1: \<open>atoms_stat B fr ve n as = atoms_stat B' fr ve n as\<close>
          using Cons TPath True ty_stat_TArrowName.prems by (rule ty_stat_TArrowName.IH)
        show ?thesis
          unfolding Cons TPath ty_stat.simps list.case tatom.case if_P[OF True]
        proof (rule bind_eq_cong[OF IH1], goal_cases args)
          case (args v)
          obtain ts ve\<^sub>1 n\<^sub>1 where v: \<open>v = (ts, ve\<^sub>1, n\<^sub>1)\<close> by (cases v) auto
          show ?case
            unfolding v prod.case
          proof (rule bind_eq_cong[OF eff_at_eq[OF ty_stat_TArrowName.prems]], goal_cases eff)
            case (eff u)
            obtain l ls where u: \<open>u = (l, ls)\<close> by (cases u) auto
            have IH2: \<open>row_stat ((nkey (n_txt f), TEeff l ls (length ts)) # B) fr ve\<^sub>1 n\<^sub>1 ro =
                       row_stat ((nkey (n_txt f), TEeff l ls (length ts)) # B') fr ve\<^sub>1 n\<^sub>1 ro\<close>
              using Cons TPath True args[unfolded v] refl refl eff[unfolded u] refl L
              by (rule ty_stat_TArrowName.IH)
            show ?case
              unfolding u prod.case
            proof (rule bind_eq_cong[OF IH2], goal_cases row)
              case (row w)
              obtain \<epsilon> ve\<^sub>2 n\<^sub>2 where w: \<open>w = (\<epsilon>, ve\<^sub>2, n\<^sub>2)\<close> by (cases w) auto
              have IH3: \<open>ty_stat ((nkey (n_txt f), TEeff l ls (length ts)) # B) fr ve\<^sub>2 n\<^sub>2 t =
                         ty_stat ((nkey (n_txt f), TEeff l ls (length ts)) # B') fr ve\<^sub>2 n\<^sub>2 t\<close>
                using Cons TPath True args[unfolded v] refl refl eff[unfolded u] refl
                  row[unfolded w] refl refl L
                by (rule ty_stat_TArrowName.IH)
              show ?case unfolding w prod.case by (rule bind_eq_cong[OF IH3]) simp
            qed
          qed
        qed
      next
        case False
        then show ?thesis unfolding Cons TPath by simp
      qed
    qed (use Cons in simp_all)
  qed simp
next
  case (ty_stat_THand B fr ve n e a ro b)
  show ?case
  proof (cases e)
    case (Cons x as)
    show ?thesis
    proof (cases x)
      case (TPath p)
      have IH1: \<open>atoms_stat B fr ve n as = atoms_stat B' fr ve n as\<close>
        using Cons TPath ty_stat_THand.prems by (rule ty_stat_THand.IH)
      show ?thesis
        unfolding Cons TPath ty_stat.simps list.case tatom.case
      proof (rule bind_eq_cong[OF IH1], goal_cases args)
        case (args v)
        obtain ts ve\<^sub>1 n\<^sub>1 where v: \<open>v = (ts, ve\<^sub>1, n\<^sub>1)\<close> by (cases v) auto
        have IH2: \<open>spine_stat B fr ve\<^sub>1 n\<^sub>1 a = spine_stat B' fr ve\<^sub>1 n\<^sub>1 a\<close>
          using Cons TPath args[unfolded v] refl refl ty_stat_THand.prems by (rule ty_stat_THand.IH)
        show ?case
          unfolding v prod.case
        proof (rule bind_eq_cong[OF IH2], goal_cases act)
          case (act w)
          obtain \<tau>\<^sub>0 ve\<^sub>2 n\<^sub>2 where w: \<open>w = (\<tau>\<^sub>0, ve\<^sub>2, n\<^sub>2)\<close> by (cases w) auto
          have IH3: \<open>row_stat B fr ve\<^sub>2 n\<^sub>2 ro = row_stat B' fr ve\<^sub>2 n\<^sub>2 ro\<close>
            using Cons TPath args[unfolded v] refl refl act[unfolded w] refl refl
              ty_stat_THand.prems
            by (rule ty_stat_THand.IH)
          show ?case
            unfolding w prod.case
          proof (rule bind_eq_cong[OF IH3], goal_cases row)
            case (row u)
            obtain \<epsilon> ve\<^sub>3 n\<^sub>3 where u: \<open>u = (\<epsilon>, ve\<^sub>3, n\<^sub>3)\<close> by (cases u) auto
            have IH4: \<open>spine_stat B fr ve\<^sub>3 n\<^sub>3 b = spine_stat B' fr ve\<^sub>3 n\<^sub>3 b\<close>
              using Cons TPath args[unfolded v] refl refl act[unfolded w] refl refl
                row[unfolded u] refl refl ty_stat_THand.prems
              by (rule ty_stat_THand.IH)
            show ?case
              unfolding u prod.case
              by (rule bind_eq_cong[OF IH4]) (auto simp: eff_at_eq[OF ty_stat_THand.prems])
          qed
        qed
      qed
    qed (use Cons in simp_all)
  qed simp
next
  case (atoms_stat_Cons B fr ve n a as)
  have IH1: \<open>atom_stat B fr ve n a = atom_stat B' fr ve n a\<close>
    using atoms_stat_Cons.prems by (rule atoms_stat_Cons.IH)
  show ?case
    unfolding atoms_stat.simps
  proof (rule bind_eq_cong[OF IH1], goal_cases atom)
    case (atom v)
    obtain t ve\<^sub>1 n\<^sub>1 where v: \<open>v = (t, ve\<^sub>1, n\<^sub>1)\<close> by (cases v) auto
    have \<open>atoms_stat B fr ve\<^sub>1 n\<^sub>1 as = atoms_stat B' fr ve\<^sub>1 n\<^sub>1 as\<close>
      using atom[unfolded v] refl refl atoms_stat_Cons.prems by (rule atoms_stat_Cons.IH)
    then show ?case unfolding v prod.case by simp
  qed
next
  case (tys_stat_Cons B fr ve n t ts)
  have IH1: \<open>ty_stat B fr ve n t = ty_stat B' fr ve n t\<close>
    using tys_stat_Cons.prems by (rule tys_stat_Cons.IH)
  show ?case
    unfolding tys_stat.simps
  proof (rule bind_eq_cong[OF IH1], goal_cases ty)
    case (ty v)
    obtain t' ve\<^sub>1 n\<^sub>1 where v: \<open>v = (t', ve\<^sub>1, n\<^sub>1)\<close> by (cases v) auto
    have \<open>tys_stat B fr ve\<^sub>1 n\<^sub>1 ts = tys_stat B' fr ve\<^sub>1 n\<^sub>1 ts\<close>
      using ty[unfolded v] refl refl tys_stat_Cons.prems by (rule tys_stat_Cons.IH)
    then show ?case unfolding v prod.case by simp
  qed
next
  case (ty_stat_TArrowMod B fr ve n b t)
  have IH: \<open>ty_stat ((mbind_nm b, TEstr (param_env (real_env (dep_vars T [n ..< n + length T]) E)))
        # B) fr ve (n + length T) t =
      ty_stat ((mbind_nm b, TEstr (param_env (real_env (dep_vars T [n ..< n + length T]) E)))
        # B') fr ve (n + length T) t\<close>
    if \<open>mbind_sig b = SPath p []\<close> \<open>tlookup B (path_nms p) = Some (TEsig (T, E))\<close> \<open>abs_ok T E\<close>
    for p T E
    using ty_stat_TArrowMod.IH that lookup_eq_Cons[OF ty_stat_TArrowMod.prems] by blast
  show ?case
  proof (cases \<open>mbind_sig b\<close>)
    case (SPath p refs)
    then show ?thesis
      by (cases rule: lookup_eqE[OF ty_stat_TArrowMod.prems, of \<open>path_nms p\<close>])
         (auto simp: IH Let_def split: list.split tentry.split prod.split cong: Option.bind_cong)
  qed simp_all
next
  case (spine_stat_Cons B fr ve n a as)
  then show ?case
    by (auto simp: head_stat_eq split: tatom.split prod.split cong: Option.bind_cong)
next
  case (row_stat_Some B fr ve n r)
  then show ?case
    by (auto simp: labels_stat_eq split: ty.split option.split list.split cong: Option.bind_cong)
qed (auto simp: head_stat_eq split: list.split prod.split cong: Option.bind_cong)

lemma cons_stat_eq:
  \<open>lookup_eq B B' \<Longrightarrow> cons_stat B ve ps c n alts = cons_stat B' ve ps c n alts\<close>
proof (induction B ve ps c n alts arbitrary: B' rule: cons_stat_induct)
  case (Cons B ve ps c n cn args alts)
  show ?case
    unfolding cons_stat.simps
  proof (rule bind_eq_cong[OF atoms_stat_eq[OF Cons.prems]], goal_cases args)
    case (args v)
    obtain ts ve\<^sub>1 n\<^sub>1 where v: \<open>v = (ts, ve\<^sub>1, n\<^sub>1)\<close> by (cases v) auto
    have \<open>cons_stat B ve ps c (n\<^sub>1 + length ts) alts = cons_stat B' ve ps c (n\<^sub>1 + length ts) alts\<close>
      using Cons.IH args[unfolded v] Cons.prems by blast
    then show ?case unfolding v prod.case Let_def by simp
  qed
qed simp

lemma ops_stat_eq: \<open>lookup_eq B B' \<Longrightarrow> ops_stat B pre ps ve n ops = ops_stat B' pre ps ve n ops\<close>
proof (induction B pre ps ve n ops arbitrary: B' rule: ops_stat_induct)
  case (Cons B pre ps ve n opn ty ops)
  show ?case
    unfolding ops_stat.simps
  proof (rule bind_eq_cong[OF ty_stat_eq[OF Cons.prems]], goal_cases ty)
    case (ty v)
    obtain \<tau> ve\<^sub>1 n\<^sub>1 where v: \<open>v = (\<tau>, ve\<^sub>1, n\<^sub>1)\<close> by (cases v) auto
    have \<open>ops_stat B pre ps ve n\<^sub>1 ops = ops_stat B' pre ps ve n\<^sub>1 ops\<close>
      if \<open>\<tau> = TFn t\<^sub>1 e t\<^sub>2\<close> for t\<^sub>1 e t\<^sub>2
      using Cons.IH ty[unfolded v] Cons.prems that by blast
    then show ?case unfolding v prod.case by (cases \<tau>) simp_all
  qed
qed simp

lemma sig_stat_eq:
  \<open>lookup_eq B B' \<Longrightarrow> sig_stat B n sg = sig_stat B' n sg\<close>
  \<open>lookup_eq B B' \<Longrightarrow> refn_stat B n \<Sigma> refs = refn_stat B' n \<Sigma> refs\<close>
  \<open>lookup_eq B B' \<Longrightarrow> spec_stat B n T acc ss = spec_stat B' n T acc ss\<close>
proof (induction B n sg and B n \<Sigma> refs and B n T acc ss arbitrary: B' and B' and B'
       rule: sig_stat_induct)
  case (sig_stat_SPath B n p refs)
  then show ?case
    by (cases rule: lookup_eqE[OF sig_stat_SPath.prems, of \<open>path_nms p\<close>])
       (auto split: tentry.split)
next
  case (refn_stat_Cons_RType B n T E t ty refs)
  show ?case
  proof (cases \<open>\<exists>c. map_of E (n_txt t) = Some (TEtyp (TyAbs c 0)) \<and> stamp c \<in> set T\<close>)
    case True
    then obtain c where E_t: \<open>map_of E (n_txt t) = Some (TEtyp (TyAbs c 0))\<close>
      and c_T: \<open>stamp c \<in> set T\<close>
      by blast
    have \<open>ty_stat B False ([], []) n ty \<bind> (\<lambda>(\<tau>, _, n'). if rep_ok T c \<tau>
            then refn_stat B n' (removeAll (stamp c) T, real_env [(stamp c, TyFn [] \<tau>)] E) refs
            else None) =
          ty_stat B' False ([], []) n ty \<bind> (\<lambda>(\<tau>, _, n'). if rep_ok T c \<tau>
            then refn_stat B' n' (removeAll (stamp c) T, real_env [(stamp c, TyFn [] \<tau>)] E) refs
            else None)\<close>
    proof (rule bind_eq_cong[OF ty_stat_eq[OF refn_stat_Cons_RType.prems]], goal_cases ty)
      case (ty v)
      obtain \<tau> ve n' where v: \<open>v = (\<tau>, ve, n')\<close> by (cases v) auto
      have \<open>refn_stat B n' (removeAll (stamp c) T, real_env [(stamp c, TyFn [] \<tau>)] E) refs =
          refn_stat B' n' (removeAll (stamp c) T, real_env [(stamp c, TyFn [] \<tau>)] E) refs\<close>
        if \<open>rep_ok T c \<tau>\<close>
        using E_t refl refl refl c_T ty[unfolded v] refl refl that refn_stat_Cons_RType.prems
        by (rule refn_stat_Cons_RType.IH)
      then show ?case unfolding v prod.case by simp
    qed
    then show ?thesis using E_t c_T by simp
  next
    case False
    then show ?thesis by (auto split: option.split tentry.split tydef.split nat.split)
  qed
next
  case (refn_stat_Cons_RMod B n T E M P refs)
  then show ?case
    by (cases rule: lookup_eqE[OF refn_stat_Cons_RMod.prems, of \<open>path_nms P\<close>])
       (auto split: option.split tentry.split prod.split cong: Option.bind_cong)
next
  case (spec_stat_Cons_SpType_Some B n T acc t as ty ss)
  note eq = ty_stat_eq[OF lookup_eq_append[OF spec_stat_Cons_SpType_Some.prems]]
  show ?case
    unfolding spec_stat.simps Let_def
  proof (rule bind_eq_cong[OF eq], goal_cases ty)
    case (ty v)
    obtain \<tau> ve n' where v: \<open>v = (\<tau>, ve, n')\<close> by (cases v) auto
    show ?case
      unfolding v prod.case
      using spec_stat_Cons_SpType_Some.IH ty[unfolded v] spec_stat_Cons_SpType_Some.prems
      by blast
  qed
next
  case (spec_stat_Cons_SpData B n T acc t as alts ss)
  note eq = cons_stat_eq[OF lookup_eq_Cons[OF lookup_eq_append[OF spec_stat_Cons_SpData.prems]]]
  show ?case
  proof (cases \<open>distinct (map (n_txt \<circ> fst) alts) \<and> list_all (\<lambda>(cn, _). nm_ok (n_txt cn)) alts\<close>)
    case False then show ?thesis by (simp only: spec_stat.simps Let_def if_not_P[OF False] if_False)
  next
    case True
    show ?thesis
      unfolding spec_stat.simps Let_def if_P[OF True]
    proof (rule bind_eq_cong[OF eq], goal_cases cons)
      case (cons v)
      obtain cs n' where v: \<open>v = (cs, n')\<close> by (cases v) auto
      show ?case
        unfolding v prod.case
        using spec_stat_Cons_SpData.IH True cons[unfolded v] spec_stat_Cons_SpData.prems by blast
    qed
  qed
next
  case (spec_stat_Cons_SpVal B n T acc x ty ss)
  note eq = ty_stat_eq[OF lookup_eq_append[OF spec_stat_Cons_SpVal.prems]]
  show ?case
  proof (cases \<open>nm_ok (n_txt x)\<close>)
    case False then show ?thesis by simp
  next
    case True
    show ?thesis
      unfolding spec_stat.simps if_P[OF True]
    proof (rule bind_eq_cong[OF eq], goal_cases ty)
      case (ty v)
      obtain \<tau> ve n' where v: \<open>v = (\<tau>, ve, n')\<close> by (cases v) auto
      show ?case
        unfolding v prod.case
        using spec_stat_Cons_SpVal.IH True ty[unfolded v] spec_stat_Cons_SpVal.prems by blast
    qed
  qed
next
  case (spec_stat_Cons_SpEff B n T acc x as ops ss)
  show ?case
  proof (cases \<open>distinct (map n_txt as)\<close>)
    case False then show ?thesis by (simp only: spec_stat.simps if_not_P[OF False] if_False)
  next
    case True
    note eq = ops_stat_eq[OF lookup_eq_append[OF spec_stat_Cons_SpEff.prems]]
    show ?thesis
      unfolding spec_stat.simps if_P[OF True]
    proof (rule bind_eq_cong[OF eq], goal_cases ops)
      case (ops v)
      obtain es n' where v: \<open>v = (es, n')\<close> by (cases v) auto
      show ?case
        unfolding v prod.case
        using spec_stat_Cons_SpEff.IH True ops[unfolded v] spec_stat_Cons_SpEff.prems by blast
    qed
  qed
next
  case (spec_stat_Cons_SpMod B n T acc x sg ss)
  show ?case
  proof (cases \<open>nm_ok (n_txt x)\<close>)
    case False then show ?thesis by simp
  next
    case True
    have eq: \<open>sig_stat (acc @ B) n sg = sig_stat (acc @ B') n sg\<close>
      using True lookup_eq_append[OF spec_stat_Cons_SpMod.prems] by (rule spec_stat_Cons_SpMod.IH)
    show ?thesis
      unfolding spec_stat.simps if_P[OF True]
    proof (rule bind_eq_cong[OF eq], goal_cases sig)
      case (sig v)
      obtain T' E' n' where v: \<open>v = ((T', E'), n')\<close> by (cases v) auto
      show ?case
        unfolding v prod.case
        using spec_stat_Cons_SpMod.IH True sig[unfolded v] spec_stat_Cons_SpMod.prems by blast
    qed
  qed
next
  case (spec_stat_Cons_SpInc B n T acc sg ss)
  have eq: \<open>sig_stat (acc @ B) n sg = sig_stat (acc @ B') n sg\<close>
    using lookup_eq_append[OF spec_stat_Cons_SpInc.prems] by (rule spec_stat_Cons_SpInc.IH)
  show ?case
    unfolding spec_stat.simps
  proof (rule bind_eq_cong[OF eq], goal_cases sig)
    case (sig v)
    obtain T' E' n' where v: \<open>v = ((T', E'), n')\<close> by (cases v) auto
    show ?case
      unfolding v prod.case
      using spec_stat_Cons_SpInc.IH sig[unfolded v] spec_stat_Cons_SpInc.prems by blast
  qed
qed (auto simp: Let_def split: option.split tentry.split cong: Option.bind_cong)

lemma dep_env_eq: \<open>lookup_eq B B' \<Longrightarrow> dep_env B n sg K = dep_env B' n sg K\<close>
  by (simp add: dep_env_def sig_stat_eq)

lemma is_con_eq: \<open>lookup_eq B B' \<Longrightarrow> is_con B x = is_con B' x\<close>
  by (cases rule: lookup_eqE[of B B' \<open>[x]\<close>]) (auto simp: is_con_def)

lemma irrefutable_eq:
  \<open>lookup_eq B B' \<Longrightarrow> irrefutable B p = irrefutable B' p\<close>
  \<open>lookup_eq B B' \<Longrightarrow> irrefutable_atom B a = irrefutable_atom B' a\<close>
  by (induction B p and B a arbitrary: B' and B' rule: irrefutable_irrefutable_atom.induct)
     (auto simp: is_con_eq list_all_iff)

lemma tlookup_single: \<open>tlookup B [x] = map_of B x\<close>
  by simp

lemma op_stat_eq: \<open>lookup_eq B B' \<Longrightarrow> op_stat B opr = op_stat B' opr\<close>
  unfolding op_stat_def
  by (cases rule: lookup_eqE[of B B' \<open>[opr]\<close>]; cases rule: lookup_eqE[of B B' \<open>[fix_key opr]\<close>])
     (simp_all add: tlookup_single[symmetric] del: tlookup.simps)

lemma ops_of_eq: \<open>lookup_eq B B' \<Longrightarrow> ops_of B oprs = ops_of B' oprs\<close>
  by (induction oprs) (auto simp: op_stat_eq)

lemma chain_tree_eq: \<open>lookup_eq B B' \<Longrightarrow> chain_tree B oprs = chain_tree B' oprs\<close>
  by (simp add: chain_tree_def ops_of_eq)

text \<open>Resolving an operator pattern reads only fixities, so it is invariant too, and with it
  the constructor head of a pattern:\<close>

lemma pat_resolve_eq:
  \<open>lookup_eq B B' \<Longrightarrow> pat_resolve B p = pat_resolve B' p\<close>
  \<open>lookup_eq B B' \<Longrightarrow> patom_resolve B a = patom_resolve B' a\<close>
  \<open>lookup_eq B B' \<Longrightarrow> chain_resolve B p = chain_resolve B' p\<close>
  \<open>lookup_eq B B' \<Longrightarrow> pats_resolve B ps = pats_resolve B' ps\<close>
  \<open>lookup_eq B B' \<Longrightarrow> patoms_resolve B as = patoms_resolve B' as\<close>
  \<open>lookup_eq B B' \<Longrightarrow> fields_resolve B fs = fields_resolve B' fs\<close>
  by (induction B p and B a and B p and B ps and B as and B fs rule: pat_resolve_induct)
     (auto simp: chain_tree_eq cong: Option.bind_cong)

lemma con_head_eq: \<open>lookup_eq B B' \<Longrightarrow> con_head B p = con_head B' p\<close>
  by (induction B p rule: con_head.induct) (simp_all add: pat_resolve_eq del: pat_resolve.simps)

lemma con_clause_eq: \<open>lookup_eq B B' \<Longrightarrow> con_clause B k C n p = con_clause B' k C n p\<close>
  unfolding con_clause_def
  by (cases \<open>con_head B p\<close>;
      cases rule: lookup_eqE[of B B' \<open>path_nms (fst (the (con_head B p)))\<close>])
     (auto simp: irrefutable_eq con_head_eq list_all_iff split: option.split tentry.split)

lemma covers_eq: \<open>lookup_eq B B' \<Longrightarrow> covers B \<tau> ps = covers B' \<tau> ps\<close>
  unfolding covers_def
  by (auto simp: irrefutable_eq con_clause_eq list_ex_iff list_all_iff split: kty.split prod.split)

lemma
  shows val_exp_eq: \<open>lookup_eq B B' \<Longrightarrow> val_exp B e = val_exp B' e\<close>
    and val_atom_eq: \<open>lookup_eq B B' \<Longrightarrow> val_atom B a = val_atom B' a\<close>
proof (induction B e and B a arbitrary: B' and B' rule: val_exp_induct)
  case (val_exp_ESpine_Cons_APath_Cons B p as)
  then show ?case
    by (cases rule: lookup_eqE[OF val_exp_ESpine_Cons_APath_Cons.prems, of \<open>path_nms p\<close>])
       (auto simp: list_all_iff)
next
  case (val_atom_APath B p)
  then show ?case by (cases rule: lookup_eqE[OF val_atom_APath.prems, of \<open>path_nms p\<close>]) auto
qed (auto simp: list_all_iff)

lemma val_exp_subst_imp:
  \<open>val_exp B (subst_imp tab e) = val_exp B e\<close>
  \<open>val_atom B (subst_imp_atom tab a) = val_atom B a\<close>
proof (induction B e and B a rule: val_exp_induct)
  case (val_exp_ESpine_Cons_APath_Cons B p as)
  then show ?case by (auto simp: list_all_iff split: option.splits tentry.splits)
qed (auto simp: list_all_iff split: list.splits option.splits)

lemma hlabels_eq: \<open>lookup_eq B B' \<Longrightarrow> hlabels B cls = hlabels B' cls\<close>
proof (induction B cls arbitrary: B' rule: hlabels_induct)
  case (Cons_HOp B opn ps k b cls)
  have ih: \<open>hlabels B cls = hlabels B' cls\<close>
  proof (cases \<open>tlookup B [n_txt opn]\<close>)
    case (Some e)
    with Cons_HOp.prems show ?thesis by (cases e) (blast intro: Cons_HOp.IH)+
  qed (blast intro: Cons_HOp.IH Cons_HOp.prems)
  show ?case
    by (cases rule: lookup_eqE[OF Cons_HOp.prems, of \<open>[n_txt opn]\<close>])
      (simp_all add: ih cong: tentry.case_cong)
qed auto

text \<open>Implicit resolution reads only the instance entries, which substitution leaves alone:\<close>

lemma cands_sub_env: \<open>cands (sub_env \<theta> \<rho> B) = cands B\<close>
proof -
  have mo: \<open>map_of (map (apsnd (sub_ent \<theta> \<rho>)) B) x = Some (TEinst E) \<longleftrightarrow>
      map_of B x = Some (TEinst E)\<close> for x E
    using map_of_sub_env[of \<theta> \<rho> B x] unfolding sub_env_def by (auto elim!: sub_ent.elims)
  have \<open>List.map_filter (\<lambda>(x, e). case e of
        TEinst E \<Rightarrow> (if map_of (map (apsnd (sub_ent \<theta> \<rho>)) B) x = Some e then Some (x, E) else None)
      | _ \<Rightarrow> None) (map (apsnd (sub_ent \<theta> \<rho>)) B') =
    List.map_filter (\<lambda>(x, e). case e of
        TEinst E \<Rightarrow> (if map_of B x = Some e then Some (x, E) else None)
      | _ \<Rightarrow> None) B'\<close> for B'
    by (induction B') (auto simp: mo split: tentry.split)
  then show ?thesis unfolding cands_def sub_env_def by simp
qed

lemma cands_sappe: \<open>cands (sappe s B) = cands B\<close>
  by (cases s) (simp add: cands_sub_env)

subsection \<open>Instantiation and type elaboration mint fresh variables\<close>

text \<open>Instantiating a scheme and elaborating a type allocate fresh variables from a counter
  that only grows. What they return mentions only the variables of the input and the fresh
  ones, and no bound variable.\<close>

fun bfree_sch :: \<open>scheme \<Rightarrow> bool\<close> where
  \<open>bfree_sch (Sch t) = True\<close>
| \<open>bfree_sch (Mono t) = bfree t\<close>

lemma bfree_bsubst:
  \<open>(\<And>a. a \<in> btv t \<Longrightarrow> bfree (\<theta> a)) \<Longrightarrow> (\<And>v. v \<in> brv t \<Longrightarrow> brv_row (\<rho> v) = {})
    \<Longrightarrow> bfree (bsubst \<theta> \<rho> t)\<close>
  by (auto simp: bfree_def btv_bsubst brv_bsubst)

lemma map_of_zip_range:
  \<open>length xs = length ys \<Longrightarrow> x \<in> set xs \<Longrightarrow> \<exists>y. map_of (zip xs ys) x = Some y \<and> y \<in> set ys\<close>
  by (metis map_of_zip_is_Some map_of_SomeD set_zip_rightD)

lemma inst_scheme_wf:
  assumes \<open>inst_scheme n \<sigma> = (\<tau>, n')\<close> \<open>bfree_sch \<sigma>\<close>
  shows \<open>n \<le> n' \<and> ftv \<tau> \<subseteq> ftv_sch \<sigma> \<union> {n ..< n'} \<and> frv \<tau> \<subseteq> frv_sch \<sigma> \<union> {n ..< n'} \<and>
         ktv \<tau> \<subseteq> ktv_sch \<sigma> \<and> bfree \<tau>\<close>
proof (cases \<sigma>)
  case (Mono t)
  with assms show ?thesis by (auto simp: bfree_def)
next
  case (Sch t)
  define avs where \<open>avs = remdups (sort (btv_list t))\<close>
  define rvs where \<open>rvs = remdups (sort (brv_list t))\<close>
  define \<theta> where \<open>\<theta> = (\<lambda>a.
      case map_of (zip avs (map TV [n ..< n + length avs])) a of
        Some \<tau> \<Rightarrow> \<tau> | None \<Rightarrow> TB a)\<close>
  define \<rho> where \<open>\<rho> = (\<lambda>v.
      case map_of (zip rvs (map RV [n + length avs ..< n + length avs + length rvs])) v of
        Some r \<Rightarrow> r | None \<Rightarrow> RB v)\<close>
  have \<tau>: \<open>\<tau> = bsubst \<theta> \<rho> t\<close> and n': \<open>n' = n + length avs + length rvs\<close>
    using assms unfolding Sch inst_scheme.simps Let_def avs_def rvs_def \<theta>_def \<rho>_def by auto
  have \<theta>: \<open>\<exists>k. \<theta> a = TV k \<and> n \<le> k \<and> k < n'\<close> if \<open>a \<in> btv t\<close> for a
    using map_of_zip_range[of avs \<open>map TV [n ..< n + length avs]\<close> a] that
    unfolding \<theta>_def n' avs_def by auto
  have \<rho>: \<open>\<exists>k. \<rho> v = RV k \<and> n \<le> k \<and> k < n'\<close> if \<open>v \<in> brv t\<close> for v
    using map_of_zip_range[of rvs \<open>map RV [n + length avs ..< n + length avs + length rvs]\<close> v]
      that
    unfolding \<rho>_def n' rvs_def by auto
  have \<open>ftv (bsubst \<theta> \<rho> t) \<subseteq> ftv t \<union> {n ..< n'}\<close>
    unfolding ftv_bsubst using \<theta> by fastforce
  moreover have \<open>frv (bsubst \<theta> \<rho> t) \<subseteq> frv t \<union> {n ..< n'}\<close>
    unfolding frv_bsubst using \<theta> \<rho> by fastforce
  moreover have \<open>ktv (bsubst \<theta> \<rho> t) \<subseteq> ktv t\<close>
    using ktv_bsubst[of \<theta> \<rho> t] \<theta> by fastforce
  moreover have \<open>bfree (bsubst \<theta> \<rho> t)\<close>
    by (rule bfree_bsubst) (auto dest!: \<theta> \<rho> simp: bfree_def)
  ultimately show ?thesis unfolding \<tau> Sch n' by simp
qed

lemma ktv_env_map_of: \<open>map_of E x = Some e \<Longrightarrow> ktv_ent e \<subseteq> ktv_env E\<close>
  by (induction E) (auto split: if_split_asm)

lemma ktv_env_tlookup: \<open>tlookup E p = Some e \<Longrightarrow> ktv_ent e \<subseteq> ktv_env E\<close>
  by (induction E p rule: tlookup.induct)
     (fastforce simp: ktv_env_map_of split: option.split_asm tentry.split_asm
        dest!: ktv_env_map_of)+

lemma cenv_tlookup:
  \<open>cenv B \<Longrightarrow> tlookup B p = Some e \<Longrightarrow> (\<exists>\<sigma>. e = TEval \<sigma>) \<or> ftv_ent e = {} \<and> frv_ent e = {}\<close>
proof (induction B p rule: tlookup_induct)
  case (Cons_Nil env x)
  then show ?case by (auto simp: cenv_def dest!: map_of_SomeD)
next
  case (Cons_Cons env x y ys)
  from Cons_Cons.prems obtain ex
    where env_x: \<open>map_of env x = Some (TEstr ex) \<or> map_of env x = Some (TEinst ex)\<close>
      and ex: \<open>tlookup ex (y # ys) = Some e\<close>
    by (auto split: option.split_asm tentry.split_asm)
  from \<open>cenv env\<close> env_x have \<open>ftv_env ex = {}\<close> \<open>frv_env ex = {}\<close>
    by (auto simp: cenv_def dest!: map_of_SomeD)
  then show ?case using ftv_env_tlookup[OF ex] frv_env_tlookup[OF ex] by auto
qed simp

lemma cenv_tlookup_nonval:
  \<open>cenv B \<Longrightarrow> tlookup B p = Some e \<Longrightarrow> \<forall>\<sigma>. e \<noteq> TEval \<sigma> \<Longrightarrow> ftv_ent e = {} \<and> frv_ent e = {}\<close>
  by (auto dest: cenv_tlookup)

text \<open>The type and row variables of a type-variable environment, and its well-formedness: it holds
  no abstract type and no bound variable.\<close>

definition tvars :: \<open>tvenv \<Rightarrow> tvar set\<close> where
  \<open>tvars ve = (\<Union>(x, t) \<in> set (fst ve). ftv t)\<close>

definition rvars :: \<open>tvenv \<Rightarrow> rvar set\<close> where
  \<open>rvars ve = (\<Union>(x, t) \<in> set (fst ve). frv t) \<union> (\<Union>(x, r) \<in> set (snd ve). frv_row r)\<close>

definition tve_ok :: \<open>tvenv \<Rightarrow> bool\<close> where
  \<open>tve_ok ve \<longleftrightarrow>
     (\<forall>(x, t) \<in> set (fst ve). ktv t = {} \<and> bfree t) \<and> (\<forall>(x, r) \<in> set (snd ve). brv_row r = {})\<close>

lemma tapp_vars[simp]:
  \<open>ftv (tapp f x) = ftv f \<union> ftv x\<close> \<open>frv (tapp f x) = frv f \<union> frv x\<close>
  \<open>ktv (tapp f x) = ktv f \<union> ktv x\<close> \<open>bfree (tapp f x) \<longleftrightarrow> bfree f \<and> bfree x\<close>
  by (cases f; auto simp: bfree_def)+

lemma foldl_tapp_vars:
  \<open>ftv (foldl tapp t ts) = ftv t \<union> \<Union>(ftv ` set ts)\<close>
  \<open>frv (foldl tapp t ts) = frv t \<union> \<Union>(frv ` set ts)\<close>
  \<open>ktv (foldl tapp t ts) = ktv t \<union> \<Union>(ktv ` set ts)\<close>
  \<open>bfree (foldl tapp t ts) \<longleftrightarrow> bfree t \<and> (\<forall>t \<in> set ts. bfree t)\<close>
  by (induction ts arbitrary: t) auto

lemma tvars_simps[simp]:
  \<open>tvars (tvs, rvs) = (\<Union>(x, t) \<in> set tvs. ftv t)\<close>
  \<open>rvars (tvs, rvs) = (\<Union>(x, t) \<in> set tvs. frv t) \<union> (\<Union>(x, r) \<in> set rvs. frv_row r)\<close>
  \<open>tve_ok (tvs, rvs) \<longleftrightarrow>
     (\<forall>(x, t) \<in> set tvs. ktv t = {} \<and> bfree t) \<and> (\<forall>(x, r) \<in> set rvs. brv_row r = {})\<close>
  by (simp_all add: tvars_def rvars_def tve_ok_def)

lemma tydef_app_vars:
  \<open>ftv (tydef_app d ts) \<subseteq> ftv_tydef d \<union> \<Union>(ftv ` set ts) \<and>
   frv (tydef_app d ts) \<subseteq> frv_tydef d \<union> \<Union>(frv ` set ts) \<and>
   ktv (tydef_app d ts) \<subseteq> ktv_tydef d \<union> \<Union>(ktv ` set ts) \<and>
   ((\<forall>t \<in> set ts. bfree t) \<longrightarrow> bfree (tydef_app d ts))\<close>
proof (cases d)
  case (TyFn ps b)
  let ?\<theta> = \<open>\<lambda>a. case map_of (zip ps ts) a of Some t \<Rightarrow> t | None \<Rightarrow> unit_ty\<close>
  have \<theta>: \<open>ftv (?\<theta> a) \<subseteq> \<Union>(ftv ` set ts)\<close> \<open>frv (?\<theta> a) \<subseteq> \<Union>(frv ` set ts)\<close>
    and \<theta>_ktv: \<open>ktv (?\<theta> a) \<subseteq> \<Union>(ktv ` set ts)\<close>
    and \<theta>_bfree: \<open>(\<forall>t \<in> set ts. bfree t) \<Longrightarrow> bfree (?\<theta> a)\<close> for a
    by (auto split: option.split dest!: map_of_SomeD set_zip_rightD)
  show ?thesis
  proof (intro conjI impI)
    show \<open>ftv (tydef_app d ts) \<subseteq> ftv_tydef d \<union> \<Union>(ftv ` set ts)\<close>
      unfolding TyFn tydef_app.simps ftv_bsubst by (intro Un_least UN_least) (use \<theta> in auto)
    show \<open>frv (tydef_app d ts) \<subseteq> frv_tydef d \<union> \<Union>(frv ` set ts)\<close>
      unfolding TyFn tydef_app.simps frv_bsubst by (intro Un_least UN_least) (use \<theta> in auto)
    show \<open>ktv (tydef_app d ts) \<subseteq> ktv_tydef d \<union> \<Union>(ktv ` set ts)\<close>
      unfolding TyFn tydef_app.simps
      by (rule subset_trans[OF ktv_bsubst]) (intro Un_least UN_least, use subsetD[OF \<theta>_ktv] in auto)
    show \<open>bfree (tydef_app d ts)\<close> if \<open>\<forall>t \<in> set ts. bfree t\<close>
      unfolding TyFn tydef_app.simps by (intro bfree_bsubst) (use \<theta>_bfree[OF that] in auto)
  qed
qed auto

lemmas tydef_app_ftv = tydef_app_vars[THEN conjunct1]
  and tydef_app_frv = tydef_app_vars[THEN conjunct2, THEN conjunct1]
  and tydef_app_ktv = tydef_app_vars[THEN conjunct2, THEN conjunct2, THEN conjunct1]
  and tydef_app_bfree = tydef_app_vars[THEN conjunct2, THEN conjunct2, THEN conjunct2, THEN mp]

subsection \<open>Elaborating a type mints only fresh variables\<close>

text \<open>\<^text>\<open>tve_step ve n ve' n'\<close>: elaboration took the type-variable environment
  \<^text>\<open>ve\<close> at counter \<^text>\<open>n\<close> to \<^text>\<open>ve'\<close> at \<^text>\<open>n'\<close>,
  keeping the old variables and adding only fresh ones. \<^text>\<open>fresh_ty ve n n' B \<tau>\<close>:
  \<^text>\<open>\<tau>\<close> mentions only variables of \<^text>\<open>ve\<close> or fresh in
  \<^text>\<open>[n, n')\<close>, abstract types of \<^text>\<open>B\<close>, and no bound variable.\<close>

definition tve_step :: \<open>tvenv \<Rightarrow> nat \<Rightarrow> tvenv \<Rightarrow> nat \<Rightarrow> bool\<close> where
  \<open>tve_step ve n ve' n' \<longleftrightarrow>
     n \<le> n' \<and> tve_ok ve' \<and> tvars ve \<subseteq> tvars ve' \<and> rvars ve \<subseteq> rvars ve' \<and>
     tvars ve' \<subseteq> tvars ve \<union> {n ..< n'} \<and> rvars ve' \<subseteq> rvars ve \<union> {n ..< n'}\<close>

definition fresh_ty :: \<open>tvenv \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> tenv \<Rightarrow> kty \<Rightarrow> bool\<close> where
  \<open>fresh_ty ve n n' B \<tau> \<longleftrightarrow>
     ftv \<tau> \<subseteq> tvars ve \<union> {n ..< n'} \<and> frv \<tau> \<subseteq> rvars ve \<union> {n ..< n'} \<and>
     ktv \<tau> \<subseteq> ktv_env B \<and> bfree \<tau>\<close>

lemma tve_step_refl: \<open>tve_ok ve \<Longrightarrow> tve_step ve n ve n\<close>
  by (simp add: tve_step_def)

lemma tve_step_le: \<open>tve_step ve n ve' n' \<Longrightarrow> n \<le> n'\<close>
  and tve_step_ok: \<open>tve_step ve n ve' n' \<Longrightarrow> tve_ok ve'\<close>
  by (simp_all add: tve_step_def)

lemma ivl_mono: \<open>n\<^sub>0 \<le> n \<Longrightarrow> n' \<le> n\<^sub>1 \<Longrightarrow> {n ..< n'} \<subseteq> {n\<^sub>0 ..< (n\<^sub>1 :: nat)}\<close>
  unfolding subset_iff atLeastLessThan_iff by (intro allI impI conjI) linarith+

lemma ivl_chain:
  assumes A: \<open>A \<subseteq> V\<^sub>1 \<union> {m ..< n\<^sub>2}\<close> and V\<^sub>1: \<open>V\<^sub>1 \<subseteq> V \<union> {n ..< n\<^sub>1}\<close>
    and \<open>n \<le> m\<close> \<open>n\<^sub>2 \<le> n'\<close> \<open>n\<^sub>1 \<le> (n' :: nat)\<close>
  shows \<open>A \<subseteq> V \<union> {n ..< n'}\<close>
proof -
  from A V\<^sub>1 have \<open>A \<subseteq> V \<union> {n ..< n\<^sub>1} \<union> {m ..< n\<^sub>2}\<close> by blast
  moreover have \<open>{n ..< n\<^sub>1} \<subseteq> {n ..< n'}\<close> \<open>{m ..< n\<^sub>2} \<subseteq> {n ..< n'}\<close>
    using assms by (simp_all add: ivl_mono)
  ultimately show ?thesis by blast
qed

lemma tve_step_trans:
  assumes a: \<open>tve_step ve n ve\<^sub>1 n\<^sub>1\<close> and b: \<open>tve_step ve\<^sub>1 n\<^sub>1 ve' n'\<close>
  shows \<open>tve_step ve n ve' n'\<close>
proof -
  have le: \<open>n \<le> n\<^sub>1\<close> \<open>n\<^sub>1 \<le> n'\<close> using a b by (simp_all add: tve_step_def)
  have \<open>tvars ve' \<subseteq> tvars ve \<union> {n ..< n'}\<close>
    by (rule ivl_chain[of _ \<open>tvars ve\<^sub>1\<close> n\<^sub>1 n' \<open>tvars ve\<close> n n\<^sub>1])
       (use a b le in \<open>simp_all add: tve_step_def\<close>)
  moreover have \<open>rvars ve' \<subseteq> rvars ve \<union> {n ..< n'}\<close>
    by (rule ivl_chain[of _ \<open>rvars ve\<^sub>1\<close> n\<^sub>1 n' \<open>rvars ve\<close> n n\<^sub>1])
       (use a b le in \<open>simp_all add: tve_step_def\<close>)
  moreover have \<open>n \<le> n'\<close> using le by (rule le_trans)
  ultimately show ?thesis using a b unfolding tve_step_def by blast
qed

lemma tve_step_mono:
  \<open>tve_step ve n ve' n' \<Longrightarrow> n\<^sub>0 \<le> n \<Longrightarrow> n' \<le> n\<^sub>1 \<Longrightarrow> tve_step ve n\<^sub>0 ve' n\<^sub>1\<close>
  unfolding tve_step_def using ivl_mono[of n\<^sub>0 n n' n\<^sub>1] by (blast intro: le_trans)

lemma fresh_ty_mono:
  \<open>fresh_ty ve n n\<^sub>1 B \<tau> \<Longrightarrow> n\<^sub>0 \<le> n \<Longrightarrow> n\<^sub>1 \<le> n' \<Longrightarrow> fresh_ty ve n\<^sub>0 n' B \<tau>\<close>
  unfolding fresh_ty_def using ivl_mono[of n\<^sub>0 n n\<^sub>1 n'] by auto

lemma fresh_ty_step:
  assumes \<open>fresh_ty ve\<^sub>1 m n\<^sub>2 B \<tau>\<close> \<open>tve_step ve n ve\<^sub>1 n\<^sub>1\<close>
    and \<open>n \<le> m\<close> \<open>n\<^sub>2 \<le> n'\<close> \<open>n\<^sub>1 \<le> n'\<close>
  shows \<open>fresh_ty ve n n' B \<tau>\<close>
  using assms ivl_chain[of \<open>ftv \<tau>\<close> \<open>tvars ve\<^sub>1\<close> m n\<^sub>2 \<open>tvars ve\<close> n n\<^sub>1 n']
        ivl_chain[of \<open>frv \<tau>\<close> \<open>rvars ve\<^sub>1\<close> m n\<^sub>2 \<open>rvars ve\<close> n n\<^sub>1 n']
  unfolding fresh_ty_def tve_step_def by auto

lemma fresh_ty_grow:
  \<open>fresh_ty ve n\<^sub>0 m B \<tau> \<Longrightarrow> tve_step ve n ve\<^sub>1 n\<^sub>1 \<Longrightarrow> fresh_ty ve\<^sub>1 n\<^sub>0 m B \<tau>\<close>
  unfolding fresh_ty_def tve_step_def by blast

lemma frv_row_step:
  \<open>frv_row r \<subseteq> rvars ve\<^sub>1 \<union> {n\<^sub>1 ..< n\<^sub>2} \<Longrightarrow> tve_step ve n ve\<^sub>1 n\<^sub>1 \<Longrightarrow> n\<^sub>2 \<le> n' \<Longrightarrow>
   n\<^sub>1 \<le> n' \<Longrightarrow> frv_row r \<subseteq> rvars ve \<union> {n ..< n'}\<close>
  using ivl_chain[of \<open>frv_row r\<close> \<open>rvars ve\<^sub>1\<close> n\<^sub>1 n\<^sub>2 \<open>rvars ve\<close> n n\<^sub>1 n']
  unfolding tve_step_def by auto

lemma fresh_ty_TV: \<open>tve_ok ve \<Longrightarrow> fresh_ty ve n (Suc n) B (TV n)\<close>
  by (simp add: fresh_ty_def bfree_def)

lemma fresh_ty_TFn:
  \<open>fresh_ty ve n n' B t\<^sub>1 \<Longrightarrow> frv_row e \<subseteq> rvars ve \<union> {n ..< n'} \<Longrightarrow> brv_row e = {} \<Longrightarrow>
   fresh_ty ve n n' B t\<^sub>2 \<Longrightarrow> fresh_ty ve n n' B (TFn t\<^sub>1 e t\<^sub>2)\<close>
  by (auto simp: fresh_ty_def bfree_def)

lemma fresh_ty_TEv:
  \<open>fresh_ty ve n n' B l \<Longrightarrow> fresh_ty ve n n' B s \<Longrightarrow> fresh_ty ve n n' B t \<Longrightarrow>
   fresh_ty ve n n' B (TEv l s t)\<close>
  by (auto simp: fresh_ty_def bfree_def)

lemma fresh_ty_TAct:
  \<open>fresh_ty ve n n' B l \<Longrightarrow> frv_row e \<subseteq> rvars ve \<union> {n ..< n'} \<Longrightarrow> brv_row e = {} \<Longrightarrow>
   fresh_ty ve n n' B t \<Longrightarrow> fresh_ty ve n n' B (TAct l K e t)\<close>
  by (auto simp: fresh_ty_def bfree_def)

lemma fresh_ty_eff_ty: \<open>\<forall>\<tau> \<in> set \<tau>s. fresh_ty ve n n' B \<tau> \<Longrightarrow> fresh_ty ve n n' B (eff_ty l \<tau>s)\<close>
  by (auto simp: fresh_ty_def bfree_def eff_ty_def)

lemma fresh_ty_tuple: \<open>\<forall>\<tau> \<in> set \<tau>s. fresh_ty ve n n' B \<tau> \<Longrightarrow> fresh_ty ve n n' B (tuple \<tau>s)\<close>
  by (auto simp: fresh_ty_def bfree_def)

lemma fresh_ty_foldl_tapp:
  \<open>fresh_ty ve n n' B t \<Longrightarrow> \<forall>\<tau> \<in> set ts. fresh_ty ve n n' B \<tau> \<Longrightarrow>
   fresh_ty ve n n' B (foldl tapp t ts)\<close>
  by (auto simp: fresh_ty_def foldl_tapp_vars)

lemma fresh_ty_tve: \<open>tve_ok ve \<Longrightarrow> (x, t) \<in> set (fst ve) \<Longrightarrow> fresh_ty ve n n' B t\<close>
  unfolding fresh_ty_def tve_ok_def tvars_def rvars_def by (cases ve) auto

lemma head_stat_wf:
  assumes hs: \<open>head_stat B fr ve n p args = Some (\<tau>, ve', n')\<close> and cB: \<open>cenv B\<close>
    and ve_ok: \<open>tve_ok ve\<close> and n\<^sub>0: \<open>n\<^sub>0 \<le> n\<close>
    and args: \<open>\<forall>t \<in> set args. fresh_ty ve n\<^sub>0 n B t\<close>
  shows \<open>tve_step ve n ve' n' \<and> fresh_ty ve n\<^sub>0 n' B \<tau>\<close>
proof -
  obtain tvs rvs where ve: \<open>ve = (tvs, rvs)\<close> by (cases ve)
  show ?thesis
  proof (cases \<open>tlookup B (path_nms p)\<close>)
    case (Some e)
    then obtain d where d: \<open>e = TEtyp d\<close> \<open>\<tau> = tydef_app d args\<close> \<open>ve' = ve\<close> \<open>n' = n\<close>
      using hs unfolding ve by (auto split: tentry.split_asm if_split_asm)
    have cl: \<open>ftv_tydef d = {}\<close> \<open>frv_tydef d = {}\<close>
      using cenv_tlookup_nonval[OF cB Some] d by auto
    have k: \<open>ktv_tydef d \<subseteq> ktv_env B\<close> using ktv_env_tlookup[OF Some] d by simp
    have \<open>fresh_ty ve n\<^sub>0 n B (tydef_app d args)\<close>
      unfolding fresh_ty_def
    proof (intro conjI)
      show \<open>ftv (tydef_app d args) \<subseteq> tvars ve \<union> {n\<^sub>0 ..< n}\<close>
        by (rule subset_trans[OF tydef_app_ftv]) (use cl args in \<open>auto simp: fresh_ty_def\<close>)
      show \<open>frv (tydef_app d args) \<subseteq> rvars ve \<union> {n\<^sub>0 ..< n}\<close>
        by (rule subset_trans[OF tydef_app_frv]) (use cl args in \<open>auto simp: fresh_ty_def\<close>)
      show \<open>ktv (tydef_app d args) \<subseteq> ktv_env B\<close>
        by (rule subset_trans[OF tydef_app_ktv]) (use k args in \<open>auto simp: fresh_ty_def\<close>)
      show \<open>bfree (tydef_app d args)\<close>
        by (rule tydef_app_bfree) (use args in \<open>simp add: fresh_ty_def\<close>)
    qed
    then show ?thesis using tve_step_refl[OF ve_ok] unfolding d by simp
  next
    case None
    then obtain a where pa: \<open>path_nms p = [a]\<close>
      using hs unfolding ve by (auto split: list.split_asm)
    show ?thesis
    proof (cases \<open>map_of tvs a\<close>)
      case (Some t)
      have e: \<open>\<tau> = foldl tapp t args\<close> \<open>ve' = ve\<close> \<open>n' = n\<close>
        using hs None pa Some unfolding ve by auto
      have \<open>fresh_ty ve n\<^sub>0 n B t\<close>
        using fresh_ty_tve[OF ve_ok, of a t] Some unfolding ve by (auto dest: map_of_SomeD)
      then show ?thesis
        using fresh_ty_foldl_tapp[OF _ args] tve_step_refl[OF ve_ok] unfolding e by simp
    next
      case NoneT: None
      have e: \<open>fr\<close> \<open>\<tau> = foldl tapp (TV n) args\<close> \<open>ve' = ((a, TV n) # tvs, rvs)\<close> \<open>n' = Suc n\<close>
        using hs None pa NoneT unfolding ve by (auto split: if_split_asm)
      have st: \<open>tve_step ve n ((a, TV n) # tvs, rvs) (Suc n)\<close>
        using ve_ok unfolding ve tve_step_def by (auto simp: bfree_def)
      have \<open>\<forall>\<tau> \<in> set args. fresh_ty ve n\<^sub>0 (Suc n) B \<tau>\<close>
        using args fresh_ty_mono[of ve n\<^sub>0 n B _ n\<^sub>0 \<open>Suc n\<close>] by auto
      then have \<open>fresh_ty ve n\<^sub>0 (Suc n) B (foldl tapp (TV n) args)\<close>
        by (rule fresh_ty_foldl_tapp[OF fresh_ty_mono[OF fresh_ty_TV[OF ve_ok] n\<^sub>0 le_refl]])
      then show ?thesis using st unfolding e by simp
    qed
  qed
qed

lemma frv_row_foldr[simp]: \<open>frv_row (foldr RCons ls r) = frv_row r\<close>
  by (induction ls) auto

lemma brv_row_foldr[simp]: \<open>brv_row (foldr RCons ls r) = brv_row r\<close>
  by (induction ls) auto

lemma frv_row_canon_row[simp]: \<open>frv_row (canon_row r) = frv_row r\<close>
  by (metis canon_row_tail frv_row_row_tail)

lemma brv_row_canon_row[simp]: \<open>brv_row (canon_row r) = brv_row r\<close>
  by (simp add: brv_row_tail)

lemma row_stat_SomeD:
  assumes \<open>row_stat B fr (tvs, rvs) n (Some rt) = Some (r, ve', n')\<close>
  shows \<open>(\<exists>ls'. r = canon_row (foldr RCons ls' RNil) \<and> ve' = (tvs, rvs) \<and> n' = n)
       \<or> (\<exists>ls' v r'. r = canon_row (foldr RCons ls' r') \<and> map_of rvs v = Some r' \<and>
           ve' = (tvs, rvs) \<and> n' = n)
       \<or> (\<exists>ls' v. r = canon_row (foldr RCons ls' (RV n)) \<and> ve' = (tvs, (v, RV n) # rvs) \<and>
           n' = Suc n)\<close>
proof (cases rt)
  case (TRow ls tail)
  show ?thesis
  proof (cases tail)
    case None
    then show ?thesis using assms TRow by (auto split: Option.bind_split_asm)
  next
    case (Some t)
    obtain p where t: \<open>t = TSpine [TPath p]\<close>
      using assms TRow Some
      by (cases t) (auto split: Option.bind_split_asm list.split_asm tatom.split_asm)
    obtain v where pv: \<open>path_nms p = [v]\<close>
      using assms TRow Some t by (auto split: Option.bind_split_asm list.split_asm)
    show ?thesis
    proof (cases \<open>map_of rvs v\<close>)
      case (Some r')
      then show ?thesis
        using assms TRow \<open>tail = Some t\<close> t pv by (auto split: Option.bind_split_asm)
    next
      case None
      then show ?thesis
        using assms TRow \<open>tail = Some t\<close> t pv by (auto split: Option.bind_split_asm if_split_asm)
    qed
  qed
qed (use assms in auto)

text \<open>Elaborating a type, an atom list, a spine or a row is a \<^const>\<open>tve_step\<close> and returns
  types fresh in the sense of \<^const>\<open>fresh_ty\<close>:\<close>

lemma
  shows ty_stat_wf: \<open>ty_stat B fr ve n t = Some (\<tau>, ve', n') \<Longrightarrow> cenv B \<Longrightarrow> tve_ok ve \<Longrightarrow>
      tve_step ve n ve' n' \<and> fresh_ty ve n n' B \<tau>\<close>
    and atoms_stat_wf: \<open>atoms_stat B fr ve n as = Some (\<tau>s, ve', n') \<Longrightarrow> cenv B \<Longrightarrow> tve_ok ve \<Longrightarrow>
      tve_step ve n ve' n' \<and> (\<forall>\<tau> \<in> set \<tau>s. fresh_ty ve n n' B \<tau>)\<close>
    and atom_stat_wf: \<open>atom_stat B fr ve n a = Some (\<tau>, ve', n') \<Longrightarrow> cenv B \<Longrightarrow> tve_ok ve \<Longrightarrow>
      tve_step ve n ve' n' \<and> fresh_ty ve n n' B \<tau>\<close>
    and tys_stat_wf: \<open>tys_stat B fr ve n ts = Some (\<tau>s, ve', n') \<Longrightarrow> cenv B \<Longrightarrow> tve_ok ve \<Longrightarrow>
      tve_step ve n ve' n' \<and> (\<forall>\<tau> \<in> set \<tau>s. fresh_ty ve n n' B \<tau>)\<close>
    and spine_stat_wf: \<open>spine_stat B fr ve n as = Some (\<tau>, ve', n') \<Longrightarrow> cenv B \<Longrightarrow> tve_ok ve \<Longrightarrow>
      tve_step ve n ve' n' \<and> fresh_ty ve n n' B \<tau>\<close>
    and row_stat_wf: \<open>row_stat B fr ve n ro = Some (r, ve', n') \<Longrightarrow> cenv B \<Longrightarrow> tve_ok ve \<Longrightarrow>
      tve_step ve n ve' n' \<and> frv_row r \<subseteq> rvars ve \<union> {n ..< n'} \<and> brv_row r = {}\<close>
proof (induction B fr ve n t and B fr ve n as and B fr ve n a and B fr ve n ts and B fr ve n as
       and B fr ve n ro
       arbitrary: \<tau> ve' n' and \<tau>s ve' n' and \<tau> ve' n' and \<tau>s ve' n' and \<tau> ve' n' and r ve' n'
       rule: ty_stat_induct)
  case (ty_stat_TSpine B fr ve n as)
  then show ?case by simp
next
  case (ty_stat_TArrow B fr ve n as ro t)
  from ty_stat_TArrow.prems obtain t\<^sub>1 tvs\<^sub>1 rvs\<^sub>1 n\<^sub>1 e tvs\<^sub>2 rvs\<^sub>2 n\<^sub>2 t\<^sub>2 where
    sp: \<open>spine_stat B fr ve n as = Some (t\<^sub>1, (tvs\<^sub>1, rvs\<^sub>1), n\<^sub>1)\<close> and
    ro: \<open>row_stat B fr (tvs\<^sub>1, rvs\<^sub>1) n\<^sub>1 ro = Some (e, (tvs\<^sub>2, rvs\<^sub>2), n\<^sub>2)\<close> and
    tt: \<open>ty_stat B fr (tvs\<^sub>2, rvs\<^sub>2) n\<^sub>2 t = Some (t\<^sub>2, ve', n')\<close> and
    \<tau>: \<open>\<tau> = TFn t\<^sub>1 e t\<^sub>2\<close>
    by (auto split: Option.bind_split_asm prod.split_asm)
  have ih1: \<open>tve_step ve n (tvs\<^sub>1, rvs\<^sub>1) n\<^sub>1 \<and> fresh_ty ve n n\<^sub>1 B t\<^sub>1\<close>
    using sp \<open>cenv B\<close> \<open>tve_ok ve\<close> by (rule ty_stat_TArrow.IH)
  have ih2: \<open>tve_step (tvs\<^sub>1, rvs\<^sub>1) n\<^sub>1 (tvs\<^sub>2, rvs\<^sub>2) n\<^sub>2 \<and>
      frv_row e \<subseteq> rvars (tvs\<^sub>1, rvs\<^sub>1) \<union> {n\<^sub>1 ..< n\<^sub>2} \<and> brv_row e = {}\<close>
    using sp refl refl ro \<open>cenv B\<close> tve_step_ok[OF ih1[THEN conjunct1]] by (rule ty_stat_TArrow.IH)
  have ih3: \<open>tve_step (tvs\<^sub>2, rvs\<^sub>2) n\<^sub>2 ve' n' \<and> fresh_ty (tvs\<^sub>2, rvs\<^sub>2) n\<^sub>2 n' B t\<^sub>2\<close>
    using sp refl refl ro refl refl tt \<open>cenv B\<close> tve_step_ok[OF ih2[THEN conjunct1]]
    by (rule ty_stat_TArrow.IH)
  have st: \<open>tve_step ve n ve' n'\<close>
    using tve_step_trans[OF tve_step_trans[OF ih1[THEN conjunct1] ih2[THEN conjunct1]]
        ih3[THEN conjunct1]] .
  have le: \<open>n \<le> n\<^sub>1\<close> \<open>n\<^sub>1 \<le> n\<^sub>2\<close> \<open>n\<^sub>2 \<le> n'\<close>
    using tve_step_le[OF ih1[THEN conjunct1]] tve_step_le[OF ih2[THEN conjunct1]]
      tve_step_le[OF ih3[THEN conjunct1]] .
  have \<open>fresh_ty ve n n' B t\<^sub>1\<close>
    using fresh_ty_mono[OF ih1[THEN conjunct2] le_refl] le by (blast intro: le_trans)
  moreover have \<open>frv_row e \<subseteq> rvars ve \<union> {n ..< n'}\<close>
    using frv_row_step[OF ih2[THEN conjunct2, THEN conjunct1] ih1[THEN conjunct1]] le
    by (blast intro: le_trans)
  moreover have \<open>fresh_ty ve n n' B t\<^sub>2\<close>
    using fresh_ty_step[OF ih3[THEN conjunct2]
        tve_step_trans[OF ih1[THEN conjunct1] ih2[THEN conjunct1]]] le
    by (blast intro: le_trans)
  ultimately show ?case using st ih2 unfolding \<tau> by (auto intro: fresh_ty_TFn)
next
  case (ty_stat_TArrowMod B fr ve n b t)
  obtain p T E where
    sg: \<open>mbind_sig b = SPath p []\<close> and lk: \<open>tlookup B (path_nms p) = Some (TEsig (T, E))\<close> and
    ok: \<open>abs_ok T E\<close>
    using ty_stat_TArrowMod.prems
    by (auto simp: Let_def split: msig.split_asm list.split_asm option.split_asm tentry.split_asm
                                  prod.split_asm if_split_asm Option.bind_split_asm)
  obtain n\<^sub>1 t' where
    tt: \<open>ty_stat ((mbind_nm b, TEstr (param_env (real_env (dep_vars T [n ..< n + length T]) E)))
              # B) fr ve (n + length T) t = Some (t', ve', n\<^sub>1)\<close> and
    \<tau>: \<open>\<tau> = TDep (is_imp b) (mbind_sig b) (length T) (if fr then RV n\<^sub>1 else RNil)
              (kclose [n ..< n + length T] t')\<close> and
    n': \<open>n' = (if fr then Suc n\<^sub>1 else n\<^sub>1)\<close>
    using ty_stat_TArrowMod.prems sg lk ok
    by (auto simp: Let_def split: prod.split_asm if_split_asm Option.bind_split_asm)
  have clE: \<open>ftv_env E = {}\<close> \<open>frv_env E = {}\<close>
    using cenv_tlookup_nonval[OF \<open>cenv B\<close> lk] by auto
  have kE: \<open>ktv_env E \<subseteq> ktv_env B\<close> using ktv_env_tlookup[OF lk] by simp
  let ?X = \<open>param_env (real_env (dep_vars T [n ..< n + length T]) E)\<close>
  have clX: \<open>ftv_env ?X = {}\<close> \<open>frv_env ?X = {}\<close>
    using param_env_ftv[of \<open>real_env (dep_vars T [n ..< n + length T]) E\<close>]
          param_env_frv[of \<open>real_env (dep_vars T [n ..< n + length T]) E\<close>]
          real_env_ftv[of \<open>dep_vars T [n ..< n + length T]\<close> E]
          real_env_frv[of \<open>dep_vars T [n ..< n + length T]\<close> E]
          clE dep_vars_ftv[of T \<open>[n ..< n + length T]\<close>]
          dep_vars_frv[of T \<open>[n ..< n + length T]\<close>] by auto
  have kX: \<open>ktv_env ?X \<subseteq> ktv_env B \<union> set [n ..< n + length T]\<close>
    by (rule subset_trans[OF param_env_ktv], rule subset_trans[OF real_env_ktv])
       (use kE dep_vars_ktv[of T \<open>[n ..< n + length T]\<close>] in auto)
  have cX: \<open>cenv ((mbind_nm b, TEstr ?X) # B)\<close> using \<open>cenv B\<close> clX by simp
  note ih = ty_stat_TArrowMod.IH[OF sg refl lk refl refl refl refl ok tt cX \<open>tve_ok ve\<close>]
  have st: \<open>tve_step ve n ve' n'\<close>
    using tve_step_mono[OF ih[THEN conjunct1], of n n'] unfolding n' by auto
  have ktvc: \<open>ktv (kclose [n ..< n + length T] t') \<subseteq> ktv_env B\<close>
  proof -
    have \<open>ktv t' \<subseteq> ktv_env ?X \<union> ktv_env B\<close> using ih[THEN conjunct2] by (simp add: fresh_ty_def)
    then show ?thesis using kX by auto
  qed
  have \<open>fresh_ty ve n n' B \<tau>\<close>
    using ih[THEN conjunct2] ktvc tve_step_le[OF ih[THEN conjunct1]]
    unfolding fresh_ty_def n' \<tau> by (auto simp: bfree_def)
  with st show ?case by simp
next
  case (spine_stat_Cons B fr ve n a as)
  show ?case
  proof (cases a)
    case (TPath p)
    from spine_stat_Cons.prems obtain ts ve\<^sub>1 n\<^sub>1 where
      at: \<open>atoms_stat B fr ve n as = Some (ts, ve\<^sub>1, n\<^sub>1)\<close> and
      hd: \<open>head_stat B fr ve\<^sub>1 n\<^sub>1 p ts = Some (\<tau>, ve', n')\<close>
      unfolding TPath by (auto split: Option.bind_split_asm prod.split_asm)
    have ih: \<open>tve_step ve n ve\<^sub>1 n\<^sub>1 \<and> (\<forall>\<tau> \<in> set ts. fresh_ty ve n n\<^sub>1 B \<tau>)\<close>
      using TPath at \<open>cenv B\<close> \<open>tve_ok ve\<close> by (rule spine_stat_Cons.IH)
    have args: \<open>\<forall>t \<in> set ts. fresh_ty ve\<^sub>1 n n\<^sub>1 B t\<close>
      using ih[THEN conjunct2] fresh_ty_grow[OF _ ih[THEN conjunct1]] by blast
    note hw = head_stat_wf[OF hd \<open>cenv B\<close> tve_step_ok[OF ih[THEN conjunct1]]
        tve_step_le[OF ih[THEN conjunct1]] args]
    have \<open>fresh_ty ve n n' B \<tau>\<close>
      by (rule fresh_ty_step[OF hw[THEN conjunct2] ih[THEN conjunct1] le_refl le_refl])
         (use tve_step_le[OF hw[THEN conjunct1]] in simp)
    then show ?thesis using tve_step_trans[OF ih[THEN conjunct1] hw[THEN conjunct1]] by simp
  next
    case (TWild x)
    then show ?thesis using spine_stat_Cons.prems spine_stat_Cons.IH by (auto split: if_split_asm)
  next
    case (TParen ts)
    then show ?thesis using spine_stat_Cons.prems spine_stat_Cons.IH by (auto split: if_split_asm)
  next
    case (TName x)
    then show ?thesis using spine_stat_Cons.prems spine_stat_Cons.IH by (auto split: if_split_asm)
  qed
next
  case (ty_stat_TArrowName B fr ve n f e ro t)
  from ty_stat_TArrowName.prems obtain p as args ve\<^sub>1 n\<^sub>1 l ls \<epsilon> ve\<^sub>2 n\<^sub>2 \<tau>\<^sub>0 ve\<^sub>3 n\<^sub>3 where
    e: \<open>e = TPath p # as\<close> and ok: \<open>nm_ok (n_txt f)\<close> and
    at: \<open>atoms_stat B fr ve n as = Some (args, ve\<^sub>1, n\<^sub>1)\<close> and
    ef: \<open>eff_at B p (length args) = Some (l, ls)\<close> and
    ro: \<open>row_stat ((nkey (n_txt f), TEeff l ls (length args)) # B) fr ve\<^sub>1 n\<^sub>1 ro
           = Some (\<epsilon>, ve\<^sub>2, n\<^sub>2)\<close> and
    tt: \<open>ty_stat ((nkey (n_txt f), TEeff l ls (length args)) # B) fr ve\<^sub>2 n\<^sub>2 t
           = Some (\<tau>\<^sub>0, ve\<^sub>3, n\<^sub>3)\<close> and
    \<tau>: \<open>\<tau> = TAct (eff_ty l args) [n\<^sub>3] (canon_row (rext (map (nlbl \<circ> mangle l) ls) \<epsilon>)) \<tau>\<^sub>0\<close> and
    ve': \<open>ve' = ve\<^sub>3\<close> and n': \<open>n' = Suc n\<^sub>3\<close>
    by (auto split: list.split_asm tatom.split_asm if_split_asm Option.bind_split_asm
                    prod.split_asm)
  have cB: \<open>cenv ((nkey (n_txt f), TEeff l ls (length args)) # B)\<close> using \<open>cenv B\<close> by simp
  have ih1: \<open>tve_step ve n ve\<^sub>1 n\<^sub>1 \<and> (\<forall>\<tau> \<in> set args. fresh_ty ve n n\<^sub>1 B \<tau>)\<close>
    using e refl ok at \<open>cenv B\<close> \<open>tve_ok ve\<close> by (rule ty_stat_TArrowName.IH)
  have ih2: \<open>tve_step ve\<^sub>1 n\<^sub>1 ve\<^sub>2 n\<^sub>2 \<and> frv_row \<epsilon> \<subseteq> rvars ve\<^sub>1 \<union> {n\<^sub>1 ..< n\<^sub>2} \<and> brv_row \<epsilon> = {}\<close>
    using e refl ok at refl refl ef refl ro cB tve_step_ok[OF ih1[THEN conjunct1]]
    by (rule ty_stat_TArrowName.IH)
  have ih3': \<open>tve_step ve\<^sub>2 n\<^sub>2 ve\<^sub>3 n\<^sub>3 \<and>
      fresh_ty ve\<^sub>2 n\<^sub>2 n\<^sub>3 ((nkey (n_txt f), TEeff l ls (length args)) # B) \<tau>\<^sub>0\<close>
    using e refl ok at refl refl ef refl ro refl refl tt cB tve_step_ok[OF ih2[THEN conjunct1]]
    by (rule ty_stat_TArrowName.IH)
  have ih3: \<open>tve_step ve\<^sub>2 n\<^sub>2 ve\<^sub>3 n\<^sub>3 \<and> fresh_ty ve\<^sub>2 n\<^sub>2 n\<^sub>3 B \<tau>\<^sub>0\<close>
    using ih3' by (simp add: fresh_ty_def)
  have st\<^sub>2: \<open>tve_step ve n ve\<^sub>2 n\<^sub>2\<close>
    using tve_step_trans[OF ih1[THEN conjunct1] ih2[THEN conjunct1]] .
  have st\<^sub>3: \<open>tve_step ve n ve\<^sub>3 n\<^sub>3\<close> using tve_step_trans[OF st\<^sub>2 ih3[THEN conjunct1]] .
  have le: \<open>n \<le> n\<^sub>1\<close> \<open>n\<^sub>1 \<le> n\<^sub>2\<close> \<open>n\<^sub>2 \<le> n\<^sub>3\<close>
    using tve_step_le[OF ih1[THEN conjunct1]] tve_step_le[OF ih2[THEN conjunct1]]
      tve_step_le[OF ih3[THEN conjunct1]] .
  then have le': \<open>n\<^sub>1 \<le> Suc n\<^sub>3\<close> \<open>n\<^sub>2 \<le> Suc n\<^sub>3\<close> \<open>n\<^sub>3 \<le> Suc n\<^sub>3\<close> \<open>n \<le> n\<^sub>2\<close>
    by linarith+
  have args: \<open>\<forall>\<tau> \<in> set args. fresh_ty ve n (Suc n\<^sub>3) B \<tau>\<close>
    using ih1 by (blast intro: fresh_ty_mono[OF _ le_refl le'(1)])
  have row: \<open>frv_row \<epsilon> \<subseteq> rvars ve \<union> {n ..< Suc n\<^sub>3}\<close>
    using frv_row_step[OF ih2[THEN conjunct2, THEN conjunct1] ih1[THEN conjunct1]
        le'(2) le'(1)] .
  have t\<^sub>0: \<open>fresh_ty ve n (Suc n\<^sub>3) B \<tau>\<^sub>0\<close>
    using fresh_ty_step[OF ih3[THEN conjunct2] st\<^sub>2 le'(4) le'(3) le'(2)] .
  have act: \<open>fresh_ty ve n (Suc n\<^sub>3) B
      (TAct (eff_ty l args) [n\<^sub>3] (canon_row (rext (map (nlbl \<circ> mangle l) ls) \<epsilon>)) \<tau>\<^sub>0)\<close>
    by (rule fresh_ty_TAct[OF fresh_ty_eff_ty[OF args] _ _ t\<^sub>0])
       (use row ih2 in \<open>simp_all add: rext_def\<close>)
  show ?case
    using tve_step_mono[OF st\<^sub>3 le_refl le'(3)] act unfolding \<tau> ve' n' by simp
next
  case (ty_stat_THand B fr ve n e a ro b)
  from ty_stat_THand.prems obtain p as args ve\<^sub>1 n\<^sub>1 \<tau>\<^sub>0 ve\<^sub>2 n\<^sub>2 \<epsilon> ve\<^sub>3 n\<^sub>3 \<tau>\<^sub>1 ve\<^sub>4 n\<^sub>4 l ls where
    e: \<open>e = TPath p # as\<close> and
    at: \<open>atoms_stat B fr ve n as = Some (args, ve\<^sub>1, n\<^sub>1)\<close> and
    sp: \<open>spine_stat B fr ve\<^sub>1 n\<^sub>1 a = Some (\<tau>\<^sub>0, ve\<^sub>2, n\<^sub>2)\<close> and
    ro: \<open>row_stat B fr ve\<^sub>2 n\<^sub>2 ro = Some (\<epsilon>, ve\<^sub>3, n\<^sub>3)\<close> and
    sb: \<open>spine_stat B fr ve\<^sub>3 n\<^sub>3 b = Some (\<tau>\<^sub>1, ve\<^sub>4, n\<^sub>4)\<close> and
    \<tau>: \<open>\<tau> = TFn (TAct (eff_ty l args) [n\<^sub>4] (canon_row (rext (map (nlbl \<circ> mangle l) ls) \<epsilon>)) \<tau>\<^sub>0)
             \<epsilon> \<tau>\<^sub>1\<close> and
    ve': \<open>ve' = ve\<^sub>4\<close> and n': \<open>n' = Suc n\<^sub>4\<close>
    by (auto split: list.split_asm tatom.split_asm Option.bind_split_asm prod.split_asm)
  have ih1: \<open>tve_step ve n ve\<^sub>1 n\<^sub>1 \<and> (\<forall>\<tau> \<in> set args. fresh_ty ve n n\<^sub>1 B \<tau>)\<close>
    using e refl at \<open>cenv B\<close> \<open>tve_ok ve\<close> by (rule ty_stat_THand.IH)
  have ih2: \<open>tve_step ve\<^sub>1 n\<^sub>1 ve\<^sub>2 n\<^sub>2 \<and> fresh_ty ve\<^sub>1 n\<^sub>1 n\<^sub>2 B \<tau>\<^sub>0\<close>
    using e refl at refl refl sp \<open>cenv B\<close> tve_step_ok[OF ih1[THEN conjunct1]]
    by (rule ty_stat_THand.IH)
  have ih3: \<open>tve_step ve\<^sub>2 n\<^sub>2 ve\<^sub>3 n\<^sub>3 \<and> frv_row \<epsilon> \<subseteq> rvars ve\<^sub>2 \<union> {n\<^sub>2 ..< n\<^sub>3} \<and> brv_row \<epsilon> = {}\<close>
    using e refl at refl refl sp refl refl ro \<open>cenv B\<close> tve_step_ok[OF ih2[THEN conjunct1]]
    by (rule ty_stat_THand.IH)
  have ih4: \<open>tve_step ve\<^sub>3 n\<^sub>3 ve\<^sub>4 n\<^sub>4 \<and> fresh_ty ve\<^sub>3 n\<^sub>3 n\<^sub>4 B \<tau>\<^sub>1\<close>
    using e refl at refl refl sp refl refl ro refl refl sb \<open>cenv B\<close>
      tve_step_ok[OF ih3[THEN conjunct1]]
    by (rule ty_stat_THand.IH)
  have st\<^sub>2: \<open>tve_step ve n ve\<^sub>2 n\<^sub>2\<close>
    using tve_step_trans[OF ih1[THEN conjunct1] ih2[THEN conjunct1]] .
  have st\<^sub>3: \<open>tve_step ve n ve\<^sub>3 n\<^sub>3\<close> using tve_step_trans[OF st\<^sub>2 ih3[THEN conjunct1]] .
  have st\<^sub>4: \<open>tve_step ve n ve\<^sub>4 n\<^sub>4\<close> using tve_step_trans[OF st\<^sub>3 ih4[THEN conjunct1]] .
  have le: \<open>n \<le> n\<^sub>1\<close> \<open>n\<^sub>1 \<le> n\<^sub>2\<close> \<open>n\<^sub>2 \<le> n\<^sub>3\<close> \<open>n\<^sub>3 \<le> n\<^sub>4\<close>
    using tve_step_le[OF ih1[THEN conjunct1]] tve_step_le[OF ih2[THEN conjunct1]]
      tve_step_le[OF ih3[THEN conjunct1]] tve_step_le[OF ih4[THEN conjunct1]] .
  then have le': \<open>n\<^sub>1 \<le> Suc n\<^sub>4\<close> \<open>n\<^sub>2 \<le> Suc n\<^sub>4\<close> \<open>n\<^sub>3 \<le> Suc n\<^sub>4\<close> \<open>n\<^sub>4 \<le> Suc n\<^sub>4\<close> \<open>n \<le> n\<^sub>3\<close>
    by linarith+
  have args: \<open>\<forall>\<tau> \<in> set args. fresh_ty ve n (Suc n\<^sub>4) B \<tau>\<close>
    using ih1 by (blast intro: fresh_ty_mono[OF _ le_refl le'(1)])
  have t\<^sub>0: \<open>fresh_ty ve n (Suc n\<^sub>4) B \<tau>\<^sub>0\<close>
    using fresh_ty_step[OF ih2[THEN conjunct2] ih1[THEN conjunct1] le(1) le'(2) le'(1)] .
  have row: \<open>frv_row \<epsilon> \<subseteq> rvars ve \<union> {n ..< Suc n\<^sub>4}\<close>
    using frv_row_step[OF ih3[THEN conjunct2, THEN conjunct1] st\<^sub>2 le'(3) le'(2)] .
  have t\<^sub>1: \<open>fresh_ty ve n (Suc n\<^sub>4) B \<tau>\<^sub>1\<close>
    using fresh_ty_step[OF ih4[THEN conjunct2] st\<^sub>3 le'(5) le'(4) le'(3)] .
  have act: \<open>fresh_ty ve n (Suc n\<^sub>4) B
      (TAct (eff_ty l args) [n\<^sub>4] (canon_row (rext (map (nlbl \<circ> mangle l) ls) \<epsilon>)) \<tau>\<^sub>0)\<close>
    by (rule fresh_ty_TAct[OF fresh_ty_eff_ty[OF args] _ _ t\<^sub>0])
       (use row ih3 in \<open>simp_all add: rext_def\<close>)
  show ?case
    using tve_step_mono[OF st\<^sub>4 le_refl le'(4)]
      fresh_ty_TFn[OF act row ih3[THEN conjunct2, THEN conjunct2] t\<^sub>1]
    unfolding \<tau> ve' n' by simp
next
  case (atom_stat_TPath B fr ve n p)
  then show ?case using head_stat_wf[OF _ \<open>cenv B\<close> \<open>tve_ok ve\<close>, of fr n p \<open>[]\<close> \<tau> ve' n' n] by simp
next
  case (atom_stat_TWild B fr ve n x)
  then show ?case by (auto simp: tve_step_def fresh_ty_def bfree_def split: if_split_asm)
next
  case (atom_stat_TName B fr ve n e)
  from atom_stat_TName.prems obtain p as args ve\<^sub>1 n\<^sub>1 l where
    e: \<open>e = TPath p # as\<close> and fr: \<open>fr\<close> and
    at: \<open>atoms_stat B fr ve n as = Some (args, ve\<^sub>1, n\<^sub>1)\<close> and
    \<tau>: \<open>\<tau> = TEv (eff_ty l args) (TV n\<^sub>1) (tuple args)\<close> and ve': \<open>ve' = ve\<^sub>1\<close> and n': \<open>n' = Suc n\<^sub>1\<close>
    by (auto split: list.split_asm tatom.split_asm if_split_asm Option.bind_split_asm
                    prod.split_asm)
  have ih: \<open>tve_step ve n ve\<^sub>1 n\<^sub>1 \<and> (\<forall>\<tau> \<in> set args. fresh_ty ve n n\<^sub>1 B \<tau>)\<close>
    using e refl fr at \<open>cenv B\<close> \<open>tve_ok ve\<close> by (rule atom_stat_TName.IH)
  have args: \<open>\<forall>\<tau> \<in> set args. fresh_ty ve n (Suc n\<^sub>1) B \<tau>\<close>
    using ih by (blast intro: fresh_ty_mono[OF _ le_refl le_SucI[OF le_refl]])
  have \<open>fresh_ty ve n (Suc n\<^sub>1) B (TV n\<^sub>1)\<close>
    using tve_step_le[OF ih[THEN conjunct1]] tve_step_ok[OF ih[THEN conjunct1]]
    by (auto simp: fresh_ty_def bfree_def)
  then show ?case
    using tve_step_mono[OF ih[THEN conjunct1] le_refl le_SucI[OF le_refl]]
      fresh_ty_TEv[OF fresh_ty_eff_ty[OF args] _ fresh_ty_tuple[OF args]]
    unfolding \<tau> ve' n' by simp
next
  case (atom_stat_TParen B fr ve n ts)
  consider (nil) \<open>ts = []\<close> | (single) t where \<open>ts = [t]\<close>
    | (multi) t t' ts' where \<open>ts = t # t' # ts'\<close>
    by (cases ts; cases \<open>tl ts\<close>) auto
  then show ?case
  proof cases
    case nil
    then show ?thesis
      using atom_stat_TParen.prems tve_step_refl by (auto simp: fresh_ty_def bfree_def)
  next
    case (single t)
    then have tt: \<open>ty_stat B fr ve n t = Some (\<tau>, ve', n')\<close> using atom_stat_TParen.prems by simp
    from single refl tt \<open>cenv B\<close> \<open>tve_ok ve\<close> show ?thesis by (rule atom_stat_TParen.IH)
  next
    case (multi t t' ts')
    then obtain \<tau>s where tys: \<open>tys_stat B fr ve n ts = Some (\<tau>s, ve', n')\<close>
      and \<tau>: \<open>\<tau> = tuple \<tau>s\<close>
      using atom_stat_TParen.prems by (auto split: Option.bind_split_asm prod.split_asm)
    from multi refl tys \<open>cenv B\<close> \<open>tve_ok ve\<close>
    have \<open>tve_step ve n ve' n' \<and> (\<forall>\<tau> \<in> set \<tau>s. fresh_ty ve n n' B \<tau>)\<close>
      by (rule atom_stat_TParen.IH)
    then show ?thesis unfolding \<tau> by (auto intro: fresh_ty_tuple)
  qed
next
  case (atoms_stat_Cons B fr ve n a as)
  from atoms_stat_Cons.prems obtain t ve\<^sub>1 n\<^sub>1 ts where
    at: \<open>atom_stat B fr ve n a = Some (t, ve\<^sub>1, n\<^sub>1)\<close> and
    ats: \<open>atoms_stat B fr ve\<^sub>1 n\<^sub>1 as = Some (ts, ve', n')\<close> and \<tau>s: \<open>\<tau>s = t # ts\<close>
    by (auto split: Option.bind_split_asm prod.split_asm)
  have ih1: \<open>tve_step ve n ve\<^sub>1 n\<^sub>1 \<and> fresh_ty ve n n\<^sub>1 B t\<close>
    using at \<open>cenv B\<close> \<open>tve_ok ve\<close> by (rule atoms_stat_Cons.IH)
  have ih2: \<open>tve_step ve\<^sub>1 n\<^sub>1 ve' n' \<and> (\<forall>\<tau> \<in> set ts. fresh_ty ve\<^sub>1 n\<^sub>1 n' B \<tau>)\<close>
    using at refl refl ats \<open>cenv B\<close> tve_step_ok[OF ih1[THEN conjunct1]] by (rule atoms_stat_Cons.IH)
  have \<open>fresh_ty ve n n' B t\<close>
    using fresh_ty_mono[OF ih1[THEN conjunct2] le_refl tve_step_le[OF ih2[THEN conjunct1]]] .
  moreover have \<open>fresh_ty ve n n' B \<tau>\<close> if \<open>\<tau> \<in> set ts\<close> for \<tau>
    using fresh_ty_step[OF ih2[THEN conjunct2, THEN bspec, OF that] ih1[THEN conjunct1]
        tve_step_le[OF ih1[THEN conjunct1]] le_refl tve_step_le[OF ih2[THEN conjunct1]]] .
  ultimately show ?case
    using tve_step_trans[OF ih1[THEN conjunct1] ih2[THEN conjunct1]] unfolding \<tau>s by auto
next
  case (tys_stat_Cons B fr ve n t ts)
  from tys_stat_Cons.prems obtain t' ve\<^sub>1 n\<^sub>1 ts' where
    tt: \<open>ty_stat B fr ve n t = Some (t', ve\<^sub>1, n\<^sub>1)\<close> and
    tts: \<open>tys_stat B fr ve\<^sub>1 n\<^sub>1 ts = Some (ts', ve', n')\<close> and \<tau>s: \<open>\<tau>s = t' # ts'\<close>
    by (auto split: Option.bind_split_asm prod.split_asm)
  have ih1: \<open>tve_step ve n ve\<^sub>1 n\<^sub>1 \<and> fresh_ty ve n n\<^sub>1 B t'\<close>
    using tt \<open>cenv B\<close> \<open>tve_ok ve\<close> by (rule tys_stat_Cons.IH)
  have ih2: \<open>tve_step ve\<^sub>1 n\<^sub>1 ve' n' \<and> (\<forall>\<tau> \<in> set ts'. fresh_ty ve\<^sub>1 n\<^sub>1 n' B \<tau>)\<close>
    using tt refl refl tts \<open>cenv B\<close> tve_step_ok[OF ih1[THEN conjunct1]] by (rule tys_stat_Cons.IH)
  have \<open>fresh_ty ve n n' B t'\<close>
    using fresh_ty_mono[OF ih1[THEN conjunct2] le_refl tve_step_le[OF ih2[THEN conjunct1]]] .
  moreover have \<open>fresh_ty ve n n' B \<tau>\<close> if \<open>\<tau> \<in> set ts'\<close> for \<tau>
    using fresh_ty_step[OF ih2[THEN conjunct2, THEN bspec, OF that] ih1[THEN conjunct1]
        tve_step_le[OF ih1[THEN conjunct1]] le_refl tve_step_le[OF ih2[THEN conjunct1]]] .
  ultimately show ?case
    using tve_step_trans[OF ih1[THEN conjunct1] ih2[THEN conjunct1]] unfolding \<tau>s by auto
next
  case (row_stat_None B fr ve n)
  then show ?case by (auto simp: tve_step_def split: if_split_asm)
next
  case (row_stat_Some B fr ve n rt)
  obtain tvs rvs where ve: \<open>ve = (tvs, rvs)\<close> by (cases ve)
  from row_stat_SomeD[OF \<open>row_stat B fr ve n (Some rt) = Some (r, ve', n')\<close>[unfolded ve]]
  show ?case
  proof (elim disjE exE conjE)
    fix ls' assume \<open>r = canon_row (foldr RCons ls' RNil)\<close> \<open>ve' = (tvs, rvs)\<close> \<open>n' = n\<close>
    then show ?case using tve_step_refl[OF \<open>tve_ok ve\<close>] ve by simp
  next
    fix ls' v r'
    assume a: \<open>r = canon_row (foldr RCons ls' r')\<close> \<open>ve' = (tvs, rvs)\<close> \<open>n' = n\<close>
      and v: \<open>map_of rvs v = Some r'\<close>
    from v have vr: \<open>(v, r') \<in> set rvs\<close> by (rule map_of_SomeD)
    have f: \<open>frv_row r' \<subseteq> rvars ve\<close>
      using UN_upper[OF vr, of \<open>\<lambda>(x, r). frv_row r\<close>] unfolding ve rvars_def
      by (intro subset_trans[OF _ Un_upper2]) simp
    have b: \<open>brv_row r' = {}\<close>
      using \<open>tve_ok ve\<close>[unfolded ve tvars_simps, THEN conjunct2, THEN bspec, OF vr] by simp
    show ?case using a f b tve_step_refl[OF \<open>tve_ok ve\<close>] ve by simp
  next
    fix ls' v
    assume \<open>r = canon_row (foldr RCons ls' (RV n))\<close> \<open>ve' = (tvs, (v, RV n) # rvs)\<close> \<open>n' = Suc n\<close>
    then show ?case using \<open>tve_ok ve\<close> unfolding ve by (auto simp: tve_step_def)
  qed
qed (auto simp: tve_step_def)


subsection \<open>Patterns\<close>

text \<open>Pattern inference touches only the variables it mints: constructor
  schemes are closed and annotations elaborate to fresh variables. It is
  sound at any later substitution with ranges free of bound variables.\<close>

lemma con_ty_sapp:
  \<open>con_ty m \<tau> = Some (\<tau>s, t) \<Longrightarrow>
    con_ty m (sapp s \<tau>) = Some (map (sapp s) \<tau>s, sapp s t)\<close>
  by (induction m \<tau> arbitrary: \<tau>s t rule: con_ty.induct) (auto split: Option.bind_split_asm)

lemma ktv_sub_scheme:
  \<open>khyg (\<theta>, \<rho>) FK \<Longrightarrow> ktv_sch \<sigma> \<subseteq> FK \<Longrightarrow> ktv_sch (sub_scheme \<theta> \<rho> \<sigma>) \<subseteq> FK\<close>
  by (cases \<sigma>) (simp_all add: khyg_def ktv_tsubst_sub)

lemma ktv_sub_ent:
  \<open>khyg (\<theta>, \<rho>) FK \<Longrightarrow> ktv_ent e \<subseteq> FK \<Longrightarrow> ktv_ent (sub_ent \<theta> \<rho> e) \<subseteq> FK\<close>
  by (cases e) (auto simp: ktv_sub_scheme)

lemma ktv_env_sub_env:
  \<open>khyg (\<theta>, \<rho>) FK \<Longrightarrow> ktv_env B \<subseteq> FK \<Longrightarrow> ktv_env (sub_env \<theta> \<rho> B) \<subseteq> FK\<close>
proof (induction B)
  case (Cons xe B)
  then show ?case using ktv_sub_ent[of \<theta> \<rho> FK \<open>snd xe\<close>] by (cases xe) auto
qed simp

lemma ktv_env_sappe: \<open>khyg s FK \<Longrightarrow> ktv_env B \<subseteq> FK \<Longrightarrow> ktv_env (sappe s B) \<subseteq> FK\<close>
  by (cases s) (simp add: ktv_env_sub_env)

text \<open>\<open>fresh_ok\<close> says that a type built by inference between counters \<open>n\<close>
  and \<open>n'\<close> mentions only the type and row variables minted in that window,
  only kind variables of \<open>FK\<close>, and no bound variable.\<close>

definition fresh_ok :: \<open>kty \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> tvar set \<Rightarrow> bool\<close> where
  \<open>fresh_ok \<tau> n n' FK \<longleftrightarrow>
     ftv \<tau> \<subseteq> {n ..< n'} \<and> frv \<tau> \<subseteq> {n ..< n'} \<and> ktv \<tau> \<subseteq> FK \<and> bfree \<tau>\<close>

lemma fresh_ok_sapp:
  assumes \<open>fresh_ok \<tau> n n' FK\<close> \<open>sconf s {n ..< n'} {n ..< n'}\<close> \<open>khyg s FK\<close> \<open>bfree_sub s\<close>
  shows \<open>fresh_ok (sapp s \<tau>) n n' FK\<close>
  using assms by (auto simp: fresh_ok_def ftv_sapp_sconf frv_sapp_sconf khyg_sapp bfree_sapp)

lemma fresh_ok_mono:
  assumes \<open>fresh_ok \<tau> n n' FK\<close> \<open>n\<^sub>0 \<le> n\<close> \<open>n' \<le> n\<^sub>1\<close>
  shows \<open>fresh_ok \<tau> n\<^sub>0 n\<^sub>1 FK\<close>
  using assms(1) ivl_mono[OF assms(2,3)] unfolding fresh_ok_def by (blast intro: subset_trans)

text \<open>\<open>binds_ok\<close> lifts \<^const>\<open>fresh_ok\<close> to the binders a pattern
  introduces.\<close>

definition binds_ok :: \<open>(name \<times> kty) list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> tvar set \<Rightarrow> bool\<close> where
  \<open>binds_ok \<Gamma> n n' FK \<longleftrightarrow> (\<forall>x t. (x, t) \<in> set \<Gamma> \<longrightarrow> fresh_ok t n n' FK)\<close>

lemma binds_ok_mono:
  \<open>binds_ok \<Gamma> n n' FK \<Longrightarrow> n\<^sub>0 \<le> n \<Longrightarrow> n' \<le> n\<^sub>1 \<Longrightarrow> binds_ok \<Gamma> n\<^sub>0 n\<^sub>1 FK\<close>
  unfolding binds_ok_def by (blast intro: fresh_ok_mono)

lemma binds_ok_sapp:
  assumes \<open>binds_ok \<Gamma> n n' FK\<close> \<open>sconf s {n ..< n'} {n ..< n'}\<close> \<open>khyg s FK\<close> \<open>bfree_sub s\<close>
  shows \<open>binds_ok (map (apsnd (sapp s)) \<Gamma>) n n' FK\<close>
proof (unfold binds_ok_def, intro allI impI)
  fix x t assume \<open>(x, t) \<in> set (map (apsnd (sapp s)) \<Gamma>)\<close>
  then obtain t\<^sub>0 where \<open>(x, t\<^sub>0) \<in> set \<Gamma>\<close> \<open>t = sapp s t\<^sub>0\<close> by auto
  then show \<open>fresh_ok t n n' FK\<close>
    using assms fresh_ok_sapp[of t\<^sub>0 n n' FK s] unfolding binds_ok_def by auto
qed

subsection \<open>Entries free of bound variables\<close>

text \<open>A binder's type and a constructor's or extern's monomorphic scheme
  mention no bound variable; the algorithm's bases satisfy this, and it
  keeps unifiers free of bound variables.\<close>

fun bfree_ent :: \<open>tentry \<Rightarrow> bool\<close> and bfree_env :: \<open>tenv \<Rightarrow> bool\<close> where
  \<open>bfree_ent (TEval \<sigma>) = bfree_sch \<sigma>\<close>
| \<open>bfree_ent (TEcon \<sigma> n) = bfree_sch \<sigma>\<close>
| \<open>bfree_ent (TEffi s \<sigma>) = bfree_sch \<sigma>\<close>
| \<open>bfree_ent (TEop l ps t\<^sub>1 t\<^sub>2) =
     (btv t\<^sub>1 \<subseteq> set ps \<and> btv t\<^sub>2 \<subseteq> set ps \<and> brv t\<^sub>1 = {} \<and> brv t\<^sub>2 = {})\<close>
| \<open>bfree_ent (TEstr ex) = bfree_env ex\<close>
| \<open>bfree_ent (TEinst ex) = bfree_env ex\<close>
| \<open>bfree_ent (TEsig (T, E)) = bfree_env E\<close>
| \<open>bfree_ent (TEfun ps (T, E)) =
     (list_all (\<lambda>(x, T, E). bfree_env E) ps \<and> bfree_env E)\<close>
| \<open>bfree_ent e = True\<close>
| \<open>bfree_env [] = True\<close>
| \<open>bfree_env ((x, e) # ex) = (bfree_ent e \<and> bfree_env ex)\<close>

lemma bfree_env_append[simp]: \<open>bfree_env (E\<^sub>1 @ E\<^sub>2) \<longleftrightarrow> bfree_env E\<^sub>1 \<and> bfree_env E\<^sub>2\<close>
  by (induction E\<^sub>1) auto

lemma bfree_env_map_of: \<open>bfree_env E \<Longrightarrow> map_of E x = Some e \<Longrightarrow> bfree_ent e\<close>
  by (induction E) (auto split: if_split_asm)

lemma bfree_env_tlookup: \<open>bfree_env E \<Longrightarrow> tlookup E p = Some e \<Longrightarrow> bfree_ent e\<close>
  by (induction E p rule: tlookup.induct)
     (auto split: option.split_asm tentry.split_asm dest: bfree_env_map_of)

lemma bfree_sub_scheme:
  \<open>bfree_sub (\<theta>, \<rho>) \<Longrightarrow> bfree_sch \<sigma> \<Longrightarrow> bfree_sch (sub_scheme \<theta> \<rho> \<sigma>)\<close>
  by (cases \<sigma>) (auto intro: bfree_sapp[of \<open>(\<theta>, \<rho>)\<close>, simplified])

lemma bfree_env_sub_env:
  \<open>bfree_sub (\<theta>, \<rho>) \<Longrightarrow> bfree_env B \<Longrightarrow> bfree_env (sub_env \<theta> \<rho> B)\<close>
proof (induction B)
  case (Cons xe B)
  then show ?case by (cases xe; cases \<open>snd xe\<close>) (auto simp: bfree_sub_scheme)
qed simp

lemma bfree_env_sappe: \<open>bfree_sub s \<Longrightarrow> bfree_env B \<Longrightarrow> bfree_env (sappe s B)\<close>
  by (cases s) (simp add: bfree_env_sub_env)

lemma bfree_env_binders: \<open>binds_ok \<Gamma> n n' FK \<Longrightarrow> bfree_env (binders \<Gamma>)\<close>
  by (induction \<Gamma>) (auto simp: binds_ok_def fresh_ok_def)

subsection \<open>Unifier steps over fresh variables\<close>

text \<open>Each inference step mints variables above its input counter and
  unifies types built from them. These lemmas show that the step's
  substitution stays confined to the window of minted variables
  (\<^const>\<open>sconf\<close>), keeps kind variables in \<open>FK\<close> and bound variables
  out (such that \<^const>\<open>fresh_ok\<close> and \<^const>\<open>binds_ok\<close> survive it).\<close>

lemma sconf_fresh_mono:
  \<open>sconf s {n\<^sub>1 ..< n\<^sub>2} {n\<^sub>1 ..< n\<^sub>2} \<Longrightarrow> n \<le> n\<^sub>1 \<Longrightarrow> n\<^sub>2 \<le> n' \<Longrightarrow>
    sconf s {n ..< n'} {n ..< n'}\<close>
  by (rule sconf_mono[OF _ ivl_mono ivl_mono])

lemma sconf_fresh_scomp:
  assumes \<open>sconf s\<^sub>1 {n ..< n\<^sub>1} {n ..< n\<^sub>1}\<close> \<open>sconf s\<^sub>2 {n ..< n'} {n ..< n'}\<close> \<open>n\<^sub>1 \<le> n'\<close>
  shows \<open>sconf (s\<^sub>2 \<odot> s\<^sub>1) {n ..< n'} {n ..< n'}\<close>
  by (rule sconf_scomp_mono[OF assms(1,2)
        ivl_mono[OF order_refl assms(3)] ivl_mono[OF order_refl assms(3)]])

lemma fresh_ok_sapp':
  \<open>fresh_ok \<tau> n n\<^sub>1 FK \<Longrightarrow> sconf s {n ..< n'} {n ..< n'} \<Longrightarrow> n\<^sub>1 \<le> n' \<Longrightarrow>
    khyg s FK \<Longrightarrow> bfree_sub s \<Longrightarrow> fresh_ok (sapp s \<tau>) n n' FK\<close>
  by (rule fresh_ok_sapp[OF fresh_ok_mono[OF _ order_refl]])

lemma binds_ok_sapp':
  \<open>binds_ok \<Gamma> n n\<^sub>1 FK \<Longrightarrow> sconf s {n ..< n'} {n ..< n'} \<Longrightarrow> n\<^sub>1 \<le> n' \<Longrightarrow>
    khyg s FK \<Longrightarrow> bfree_sub s \<Longrightarrow> binds_ok (map (apsnd (sapp s)) \<Gamma>) n n' FK\<close>
  by (rule binds_ok_sapp[OF binds_ok_mono[OF _ order_refl]])

lemma binds_ok_append[simp]:
  \<open>binds_ok (\<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2) n n' FK \<longleftrightarrow> binds_ok \<Gamma>\<^sub>1 n n' FK \<and> binds_ok \<Gamma>\<^sub>2 n n' FK\<close>
  by (auto simp: binds_ok_def)

lemma binds_ok_Nil[simp]: \<open>binds_ok [] n n' FK\<close>
  by (simp add: binds_ok_def)

lemma binds_ok_Cons[simp]:
  \<open>binds_ok ((x, t) # \<Gamma>) n n' FK \<longleftrightarrow> fresh_ok t n n' FK \<and> binds_ok \<Gamma> n n' FK\<close>
  by (auto simp: binds_ok_def)

lemma fresh_ok_TV: \<open>fresh_ok (TV n) n (Suc n) FK\<close>
  by (simp add: fresh_ok_def bfree_def)

lemma fresh_ok_TC0: \<open>fresh_ok (TC c []) n n' FK\<close>
  by (simp add: fresh_ok_def bfree_def)

lemma fresh_ok_tuple: \<open>\<forall>\<tau> \<in> set \<tau>s. fresh_ok \<tau> n n' FK \<Longrightarrow> fresh_ok (tuple \<tau>s) n n' FK\<close>
  by (auto simp: fresh_ok_def bfree_def)

lemma fresh_ok_list: \<open>fresh_ok \<tau> n n' FK \<Longrightarrow> fresh_ok (TC list_ty [\<tau>]) n n' FK\<close>
  by (auto simp: fresh_ok_def bfree_def)

lemma unis_fresh:
  assumes \<open>unis uf cs n = Some (s, n')\<close> \<open>ftv_cs cs \<subseteq> {n\<^sub>0 ..< n}\<close> \<open>frv_cs cs \<subseteq> {n\<^sub>0 ..< n}\<close>
    \<open>ktv_cs cs \<subseteq> FK\<close> \<open>bfree_cs cs\<close> \<open>n\<^sub>0 \<le> n\<close>
  shows \<open>n \<le> n' \<and> sconf s {n\<^sub>0 ..< n'} {n\<^sub>0 ..< n'} \<and> khyg s FK \<and> bfree_sub s\<close>
proof -
  have le: \<open>n \<le> n'\<close> by (rule unis_mono[OF assms(1)])
  have \<open>sconf s {n\<^sub>0 ..< n'} {n\<^sub>0 ..< n'}\<close>
  proof (rule sconf_mono[OF unis_sconf[OF assms(1)]])
    show \<open>ftv_cs cs \<subseteq> {n\<^sub>0 ..< n'}\<close>
      using assms(2) ivl_mono[OF order_refl le, of n\<^sub>0] by blast
    show \<open>frv_cs cs \<union> {n ..< n'} \<subseteq> {n\<^sub>0 ..< n'}\<close>
      using assms(3) ivl_mono[OF order_refl le, of n\<^sub>0] ivl_mono[OF assms(6) order_refl, of n']
      by blast
  qed
  then show ?thesis using le unis_khyg[OF assms(1,4)] unis_bfree[OF assms(1,5)] by simp
qed

lemma uni_fresh:
  assumes \<open>uni uf t\<^sub>1 t\<^sub>2 n = Some (s, n')\<close> \<open>fresh_ok t\<^sub>1 n\<^sub>0 n FK\<close> \<open>fresh_ok t\<^sub>2 n\<^sub>0 n FK\<close>
    \<open>n\<^sub>0 \<le> n\<close>
  shows \<open>n \<le> n' \<and> sconf s {n\<^sub>0 ..< n'} {n\<^sub>0 ..< n'} \<and> khyg s FK \<and> bfree_sub s\<close>
  using unis_fresh[of uf \<open>[(t\<^sub>1, t\<^sub>2)]\<close> n s n' n\<^sub>0 FK] assms
  by (simp add: uni_def fresh_ok_def)

lemma uni_row_fresh:
  assumes \<open>uni_row r\<^sub>1 r\<^sub>2 n = Some (s, n')\<close> \<open>frv_row r\<^sub>1 \<subseteq> {n\<^sub>0 ..< n}\<close>
    \<open>frv_row r\<^sub>2 \<subseteq> {n\<^sub>0 ..< n}\<close> \<open>brv_row r\<^sub>1 = {}\<close> \<open>brv_row r\<^sub>2 = {}\<close> \<open>n\<^sub>0 \<le> n\<close>
  shows \<open>n \<le> n' \<and> sconf s {n\<^sub>0 ..< n'} {n\<^sub>0 ..< n'} \<and> khyg s FK \<and> bfree_sub s\<close>
proof -
  have le: \<open>n \<le> n'\<close> by (rule uni_row_mono[OF assms(1)])
  have \<open>sconf s {n\<^sub>0 ..< n'} {n\<^sub>0 ..< n'}\<close>
    by (rule sconf_mono[OF uni_row_sconf[OF assms(1)] subset_refl])
      (use assms(2,3) ivl_mono[OF order_refl le, of n\<^sub>0] ivl_mono[OF assms(6) order_refl, of n']
        in blast)
  then show ?thesis using le uni_row_khyg[OF assms(1)] uni_row_bfree[OF assms(1,4,5)] by simp
qed

lemma con_inst_fresh:
  assumes \<open>cenv B\<close> \<open>bfree_env B\<close> \<open>ktv_env B \<subseteq> FK\<close> \<open>tlookup B p = Some (TEcon \<sigma> m)\<close>
    \<open>inst_scheme n \<sigma> = (\<tau>, n')\<close>
  shows \<open>n \<le> n' \<and> fresh_ok \<tau> n n' FK\<close>
proof -
  have cl: \<open>ftv_sch \<sigma> = {}\<close> \<open>frv_sch \<sigma> = {}\<close> using cenv_tlookup_nonval[OF assms(1,4)] by auto
  have bf: \<open>bfree_sch \<sigma>\<close> using bfree_env_tlookup[OF assms(2,4)] by simp
  have k: \<open>ktv_sch \<sigma> \<subseteq> FK\<close> using ktv_env_tlookup[OF assms(4)] assms(3) by auto
  show ?thesis using inst_scheme_wf[OF assms(5) bf] cl k by (auto simp: fresh_ok_def)
qed

lemma fresh_ok_TFn_D:
  \<open>fresh_ok (TFn \<tau>\<^sub>1 e \<tau>\<^sub>2) n n' FK \<Longrightarrow> fresh_ok \<tau>\<^sub>1 n n' FK \<and> fresh_ok \<tau>\<^sub>2 n n' FK\<close>
  by (auto simp: fresh_ok_def bfree_def)

lemma con_ty_fresh:
  \<open>con_ty m \<tau> = Some (\<tau>s, t) \<Longrightarrow> fresh_ok \<tau> n n' FK \<Longrightarrow>
    (\<forall>u \<in> set \<tau>s. fresh_ok u n n' FK) \<and> fresh_ok t n n' FK\<close>
proof (induction m \<tau> arbitrary: \<tau>s t rule: con_ty_induct)
  case (TFn m \<tau>\<^sub>1 e \<tau>\<^sub>2)
  from TFn.prems obtain ts where c: \<open>con_ty m \<tau>\<^sub>2 = Some (ts, t)\<close> \<open>\<tau>s = \<tau>\<^sub>1 # ts\<close>
    and d: \<open>fresh_ok \<tau>\<^sub>1 n n' FK\<close> \<open>fresh_ok \<tau>\<^sub>2 n n' FK\<close>
    by (auto split: Option.bind_split_asm dest: fresh_ok_TFn_D)
  show ?case using TFn.IH[OF c(1) d(2)] d(1) c(2) by auto
qed auto

lemma ftv_cs_zip_fresh:
  assumes \<open>\<forall>u \<in> set us. fresh_ok u n n' FK\<close> \<open>\<forall>u \<in> set ws. fresh_ok u n n' FK\<close>
  shows \<open>ftv_cs (zip us ws) \<subseteq> {n ..< n'}\<close> \<open>frv_cs (zip us ws) \<subseteq> {n ..< n'}\<close>
    \<open>ktv_cs (zip us ws) \<subseteq> FK\<close> \<open>bfree_cs (zip us ws)\<close>
proof -
  have ftvL: \<open>ftv t \<subseteq> {n ..< n'}\<close> and frvL: \<open>frv t \<subseteq> {n ..< n'}\<close>
    and ktvL: \<open>ktv t \<subseteq> FK\<close> and bfL: \<open>bfree t\<close>
    if \<open>t \<in> set us\<close> for t using assms(1) that by (auto simp: fresh_ok_def)
  have ftvR: \<open>ftv u \<subseteq> {n ..< n'}\<close> and frvR: \<open>frv u \<subseteq> {n ..< n'}\<close>
    and ktvR: \<open>ktv u \<subseteq> FK\<close> and bfR: \<open>bfree u\<close>
    if \<open>u \<in> set ws\<close> for u using assms(2) that by (auto simp: fresh_ok_def)
  show \<open>ftv_cs (zip us ws) \<subseteq> {n ..< n'}\<close>
    unfolding ftv_cs_def by (rule UN_least) (auto dest: set_zip_leftD set_zip_rightD ftvL ftvR)
  show \<open>frv_cs (zip us ws) \<subseteq> {n ..< n'}\<close>
    unfolding frv_cs_def by (rule UN_least) (auto dest: set_zip_leftD set_zip_rightD frvL frvR)
  show \<open>ktv_cs (zip us ws) \<subseteq> FK\<close>
    unfolding ktv_cs_def by (rule UN_least) (auto dest: set_zip_leftD set_zip_rightD ktvL ktvR)
  show \<open>bfree_cs (zip us ws)\<close>
    unfolding bfree_cs_def by (auto dest: set_zip_leftD set_zip_rightD bfL bfR)
qed

lemma ftv_cs_map_TV_fresh:
  assumes \<open>\<forall>u \<in> set us. fresh_ok u n n' FK\<close> \<open>n \<le> m\<close> \<open>m < n'\<close>
  shows \<open>ftv_cs (map (\<lambda>\<tau>. (\<tau>, TV m)) us) \<subseteq> {n ..< n'}\<close>
    \<open>frv_cs (map (\<lambda>\<tau>. (\<tau>, TV m)) us) \<subseteq> {n ..< n'}\<close>
    \<open>ktv_cs (map (\<lambda>\<tau>. (\<tau>, TV m)) us) \<subseteq> FK\<close> \<open>bfree_cs (map (\<lambda>\<tau>. (\<tau>, TV m)) us)\<close>
proof -
  have b: \<open>ftv u \<subseteq> {n ..< n'}\<close> \<open>frv u \<subseteq> {n ..< n'}\<close> \<open>ktv u \<subseteq> FK\<close> \<open>bfree u\<close>
    if \<open>u \<in> set us\<close> for u
    using assms(1) that by (auto simp: fresh_ok_def)
  show \<open>ftv_cs (map (\<lambda>\<tau>. (\<tau>, TV m)) us) \<subseteq> {n ..< n'}\<close>
    unfolding ftv_cs_def using assms(2,3) by (intro UN_least) (auto dest: b)
  show \<open>frv_cs (map (\<lambda>\<tau>. (\<tau>, TV m)) us) \<subseteq> {n ..< n'}\<close>
    unfolding frv_cs_def by (intro UN_least) (auto dest: b)
  show \<open>ktv_cs (map (\<lambda>\<tau>. (\<tau>, TV m)) us) \<subseteq> FK\<close>
    unfolding ktv_cs_def by (rule UN_least) (auto dest: b)
  show \<open>bfree_cs (map (\<lambda>\<tau>. (\<tau>, TV m)) us)\<close>
    unfolding bfree_cs_def by (auto dest: b)
qed

subsection \<open>Pattern inference is well formed\<close>

text \<open>Pattern inference returns a substitution confined to the variables it
  minted, free of bound variables and with kind variables in \<open>FK\<close>, and a
  type and binders that are \<^const>\<open>fresh_ok\<close> in the window it minted.\<close>

lemma con_pat_step:
  assumes B: \<open>cenv B\<close> \<open>bfree_env B\<close> \<open>ktv_env B \<subseteq> FK\<close>
    and lk: \<open>tlookup B (path_nms p) = Some (TEcon \<sigma> m)\<close>
    and inst: \<open>inst_scheme n \<sigma> = (\<tau>\<^sub>c, n\<^sub>1)\<close> and cty: \<open>con_ty m \<tau>\<^sub>c = Some (\<tau>s, \<tau>\<^sub>0)\<close>
    and ih: \<open>n\<^sub>1 \<le> n\<^sub>2 \<and> sconf sp {n\<^sub>1 ..< n\<^sub>2} {n\<^sub>1 ..< n\<^sub>2} \<and> khyg sp FK \<and> bfree_sub sp \<and>
      (\<forall>\<tau> \<in> set \<tau>s'. fresh_ok \<tau> n\<^sub>1 n\<^sub>2 FK) \<and> binds_ok \<Gamma> n\<^sub>1 n\<^sub>2 FK\<close>
    and un: \<open>unis uf (zip \<tau>s' (map (sapp sp) \<tau>s)) n\<^sub>2 = Some (s\<^sub>1, n\<^sub>3)\<close>
  shows \<open>n \<le> n\<^sub>3 \<and> sconf (s\<^sub>1 \<odot> sp) {n ..< n\<^sub>3} {n ..< n\<^sub>3} \<and> khyg (s\<^sub>1 \<odot> sp) FK \<and>
    bfree_sub (s\<^sub>1 \<odot> sp) \<and> fresh_ok (sapp s\<^sub>1 (sapp sp \<tau>\<^sub>0)) n n\<^sub>3 FK \<and>
    binds_ok (map (apsnd (sapp s\<^sub>1)) \<Gamma>) n n\<^sub>3 FK\<close>
proof -
  note ci = con_inst_fresh[OF B lk inst]
  note ct = con_ty_fresh[OF cty ci[THEN conjunct2]]
  have le1: \<open>n \<le> n\<^sub>1\<close> \<open>n\<^sub>1 \<le> n\<^sub>2\<close> using ci ih by simp_all
  have sp: \<open>sconf sp {n ..< n\<^sub>2} {n ..< n\<^sub>2}\<close>
    using sconf_fresh_mono[OF _ le1(1) order_refl] ih by simp
  have args: \<open>\<forall>u \<in> set (map (sapp sp) \<tau>s). fresh_ok u n n\<^sub>2 FK\<close>
    using ct ih fresh_ok_sapp'[OF _ sp le1(2)] by auto
  have args': \<open>\<forall>u \<in> set \<tau>s'. fresh_ok u n n\<^sub>2 FK\<close>
    using ih fresh_ok_mono[OF _ le1(1) order_refl] by auto
  note cs = ftv_cs_zip_fresh[OF args' args]
  note uf = unis_fresh[OF un cs order_trans[OF le1(1) le1(2)]]
  have le2: \<open>n\<^sub>2 \<le> n\<^sub>3\<close> using uf by simp
  have s: \<open>sconf (s\<^sub>1 \<odot> sp) {n ..< n\<^sub>3} {n ..< n\<^sub>3}\<close>
    using sconf_fresh_scomp[OF sp _ le2] uf by simp
  have \<tau>0: \<open>fresh_ok (sapp s\<^sub>1 (sapp sp \<tau>\<^sub>0)) n n\<^sub>3 FK\<close>
    using fresh_ok_sapp'[OF fresh_ok_sapp'[OF ct[THEN conjunct2] sp le1(2)] _ le2] ih uf by simp
  have \<Gamma>: \<open>binds_ok (map (apsnd (sapp s\<^sub>1)) \<Gamma>) n n\<^sub>3 FK\<close>
    using binds_ok_sapp'[OF binds_ok_mono[OF _ le1(1) order_refl] _ le2] ih uf by simp
  show ?thesis
    using le1 le2 s \<tau>0 \<Gamma> khyg_scomp[of sp FK s\<^sub>1] bfree_sub_scomp[of sp s\<^sub>1] ih uf by simp
qed

lemma infer_pat_wf:
  \<open>infer_pat uf B p n = Some (s, \<tau>, \<Gamma>, n') \<Longrightarrow>
    cenv B \<Longrightarrow> bfree_env B \<Longrightarrow> ktv_env B \<subseteq> FK \<Longrightarrow>
    n \<le> n' \<and> sconf s {n ..< n'} {n ..< n'} \<and> khyg s FK \<and> bfree_sub s \<and>
    fresh_ok \<tau> n n' FK \<and> binds_ok \<Gamma> n n' FK\<close>
  \<open>infer_patom uf B a n = Some (s, \<tau>, \<Gamma>, n') \<Longrightarrow>
    cenv B \<Longrightarrow> bfree_env B \<Longrightarrow> ktv_env B \<subseteq> FK \<Longrightarrow>
    n \<le> n' \<and> sconf s {n ..< n'} {n ..< n'} \<and> khyg s FK \<and> bfree_sub s \<and>
    fresh_ok \<tau> n n' FK \<and> binds_ok \<Gamma> n n' FK\<close>
  \<open>infer_patoms uf B as n = Some (s, \<tau>s, \<Gamma>, n') \<Longrightarrow>
    cenv B \<Longrightarrow> bfree_env B \<Longrightarrow> ktv_env B \<subseteq> FK \<Longrightarrow>
    n \<le> n' \<and> sconf s {n ..< n'} {n ..< n'} \<and> khyg s FK \<and> bfree_sub s \<and>
    (\<forall>\<tau> \<in> set \<tau>s. fresh_ok \<tau> n n' FK) \<and> binds_ok \<Gamma> n n' FK\<close>
  \<open>infer_pats uf B ps n = Some (s, \<tau>s, \<Gamma>, n') \<Longrightarrow>
    cenv B \<Longrightarrow> bfree_env B \<Longrightarrow> ktv_env B \<subseteq> FK \<Longrightarrow>
    n \<le> n' \<and> sconf s {n ..< n'} {n ..< n'} \<and> khyg s FK \<and> bfree_sub s \<and>
    (\<forall>\<tau> \<in> set \<tau>s. fresh_ok \<tau> n n' FK) \<and> binds_ok \<Gamma> n n' FK\<close>
proof (induction uf B p n and uf B a n and uf B as n and uf B ps n
       arbitrary: s \<tau> \<Gamma> n' and s \<tau> \<Gamma> n' and s \<tau>s \<Gamma> n' and s \<tau>s \<Gamma> n'
       rule: infer_pat_induct)
  case (infer_pat_PatApp_Cons_Nil uf B a n)
  then show ?case by simp
next
  case (infer_pat_PatOp uf B as opr p n)
  from infer_pat_PatOp.prems obtain q where q: \<open>pat_resolve B (PatOp as opr p) = Some q\<close>
    and d: \<open>infer_pat uf B q n = Some (s, \<tau>, \<Gamma>, n')\<close>
    by (auto simp del: pat_resolve.simps split: option.split_asm)
  show ?case by (rule infer_pat_PatOp.IH[OF q d]) (fact infer_pat_PatOp.prems)+
next
  case (infer_pat_PatApp_Cons_PQid_Cons uf B p v va n)
  from infer_pat_PatApp_Cons_PQid_Cons.prems
  obtain \<sigma> m \<tau>\<^sub>c n\<^sub>1 \<tau>s \<tau>\<^sub>0 sp \<tau>s' \<Gamma>\<^sub>1 n\<^sub>2 s\<^sub>1 where
    wf: \<open>cenv B\<close> \<open>bfree_env B\<close> \<open>ktv_env B \<subseteq> FK\<close> and
    lk: \<open>tlookup B (path_nms p) = Some (TEcon \<sigma> m)\<close> and
    mlen: \<open>m = length (v # va) \<and> v # va \<noteq> []\<close> and
    inst: \<open>inst_scheme n \<sigma> = (\<tau>\<^sub>c, n\<^sub>1)\<close> and cty: \<open>con_ty m \<tau>\<^sub>c = Some (\<tau>s, \<tau>\<^sub>0)\<close> and
    pa: \<open>infer_patoms uf B (v # va) n\<^sub>1 = Some (sp, \<tau>s', \<Gamma>\<^sub>1, n\<^sub>2)\<close> and
    un: \<open>unis uf (zip \<tau>s' (map (sapp sp) \<tau>s)) n\<^sub>2 = Some (s\<^sub>1, n')\<close> and
    e: \<open>s = s\<^sub>1 \<odot> sp\<close> \<open>\<tau> = sapp s\<^sub>1 (sapp sp \<tau>\<^sub>0)\<close> \<open>\<Gamma> = map (apsnd (sapp s\<^sub>1)) \<Gamma>\<^sub>1\<close>
    by (auto split: option.split_asm tentry.split_asm if_split_asm prod.split_asm
        Option.bind_split_asm)
  note ih = infer_pat_PatApp_Cons_PQid_Cons.IH[OF lk refl mlen inst[symmetric] cty refl pa wf]
  show ?case unfolding e by (rule con_pat_step[OF wf lk inst cty ih un])
next
  case (infer_pat_PatAs uf B p x n)
  then show ?case by (auto split: Option.bind_split_asm prod.split_asm if_split_asm)
next
  case (infer_pat_PatAnn uf B p ty n)
  from infer_pat_PatAnn.prems obtain s\<^sub>1 \<tau>\<^sub>1 \<Gamma>\<^sub>1 n\<^sub>1 \<tau>\<^sub>a ve n\<^sub>2 s\<^sub>2 where
    wf: \<open>cenv B\<close> \<open>bfree_env B\<close> \<open>ktv_env B \<subseteq> FK\<close> and
    ip: \<open>infer_pat uf B p n = Some (s\<^sub>1, \<tau>\<^sub>1, \<Gamma>\<^sub>1, n\<^sub>1)\<close> and
    ts: \<open>ty_stat (sappe s\<^sub>1 B) True ([], []) n\<^sub>1 ty = Some (\<tau>\<^sub>a, ve, n\<^sub>2)\<close> and
    un: \<open>uni uf \<tau>\<^sub>1 \<tau>\<^sub>a n\<^sub>2 = Some (s\<^sub>2, n')\<close> and
    e: \<open>s = s\<^sub>2 \<odot> s\<^sub>1\<close> \<open>\<tau> = sapp s\<^sub>2 \<tau>\<^sub>1\<close> \<open>\<Gamma> = map (apsnd (sapp s\<^sub>2)) \<Gamma>\<^sub>1\<close>
    by (auto split: prod.split_asm Option.bind_split_asm)
  note ih = infer_pat_PatAnn.IH[OF ip wf]
  have le1: \<open>n \<le> n\<^sub>1\<close> using ih by simp
  note tw = ty_stat_wf[OF ts cenv_sappe[OF wf(1)]]
  have le2: \<open>n\<^sub>1 \<le> n\<^sub>2\<close> using tw by (simp add: tve_step_def tve_ok_def)
  have \<tau>a: \<open>fresh_ok \<tau>\<^sub>a n n\<^sub>2 FK\<close>
    using tw ktv_env_sappe[OF _ wf(3), of s\<^sub>1] ih le1
    by (auto simp: fresh_ty_def fresh_ok_def tve_ok_def tvars_def rvars_def
        intro: subset_trans[OF _ ivl_mono[OF le1 order_refl]])
  have \<tau>1: \<open>fresh_ok \<tau>\<^sub>1 n n\<^sub>2 FK\<close> using ih fresh_ok_mono[OF _ order_refl le2] by simp
  note uf = uni_fresh[OF un \<tau>1 \<tau>a order_trans[OF le1 le2]]
  have le3: \<open>n\<^sub>2 \<le> n'\<close> using uf by simp
  have s1: \<open>sconf s\<^sub>1 {n ..< n'} {n ..< n'}\<close>
    using sconf_fresh_mono[OF _ order_refl order_trans[OF le2 le3]] ih by simp
  have s2: \<open>sconf s\<^sub>2 {n ..< n'} {n ..< n'}\<close> \<open>khyg s\<^sub>2 FK\<close> \<open>bfree_sub s\<^sub>2\<close>
    using uf by simp_all
  have F: \<open>fresh_ok (sapp s\<^sub>2 \<tau>\<^sub>1) n n' FK\<close> by (rule fresh_ok_sapp'[OF \<tau>1 s2(1) le3 s2(2,3)])
  have G: \<open>binds_ok (map (apsnd (sapp s\<^sub>2)) \<Gamma>\<^sub>1) n n' FK\<close>
    using binds_ok_sapp'[OF _ s2(1) order_trans[OF le2 le3] s2(2,3), of \<Gamma>\<^sub>1] ih by simp
  show ?case
    unfolding e
    using ih uf le1 le2 le3 sconf_fresh_scomp[OF s1 s2(1) order_refl] khyg_scomp[of s\<^sub>1 FK s\<^sub>2]
      bfree_sub_scomp[of s\<^sub>1 s\<^sub>2] F G
    by simp
next
  case (infer_patom_PWild uf B ux n)
  then have e: \<open>s = sid\<close> \<open>\<tau> = TV n\<close> \<open>\<Gamma> = []\<close> \<open>n' = Suc n\<close> by simp_all
  show ?case unfolding e by (simp add: fresh_ok_TV)
next
  case (infer_patom_PQid_Cons_Nil uf B x n)
  from infer_patom_PQid_Cons_Nil.prems
  have wf: \<open>cenv B\<close> \<open>bfree_env B\<close> \<open>ktv_env B \<subseteq> FK\<close> by simp_all
  show ?case
  proof (cases \<open>\<exists>\<sigma> m. tlookup B [n_txt x] = Some (TEcon \<sigma> m)\<close>)
    case True
    then obtain \<sigma> m where lk: \<open>tlookup B [n_txt x] = Some (TEcon \<sigma> m)\<close> by blast
    with infer_patom_PQid_Cons_Nil.prems
    have inst: \<open>inst_scheme n \<sigma> = (\<tau>, n')\<close> \<open>m = 0\<close> \<open>s = sid\<close> \<open>\<Gamma> = []\<close>
      by (auto split: if_split_asm prod.split_asm)
    show ?thesis using con_inst_fresh[OF wf lk[unfolded \<open>m = 0\<close>] inst(1)] inst by simp
  next
    case False
    with infer_patom_PQid_Cons_Nil.prems show ?thesis
      by (auto simp: fresh_ok_TV split: option.split_asm tentry.split_asm if_split_asm)
  qed
next
  case (infer_patom_PQid_Cons_Cons uf B va vc vd n)
  from infer_patom_PQid_Cons_Cons.prems obtain \<sigma> where
    wf: \<open>cenv B\<close> \<open>bfree_env B\<close> \<open>ktv_env B \<subseteq> FK\<close> and
    lk: \<open>tlookup B (path_nms (MkPath (va # vc # vd))) = Some (TEcon \<sigma> 0)\<close> and
    inst: \<open>inst_scheme n \<sigma> = (\<tau>, n')\<close> \<open>s = sid\<close> \<open>\<Gamma> = []\<close>
    by (auto split: option.split_asm tentry.split_asm nat.split_asm prod.split_asm)
  show ?case using con_inst_fresh[OF wf lk inst(1)] inst by simp
next
  case (infer_patom_PNum_None uf B l v n)
  then show ?case by (auto simp: fresh_ok_TC0 split: if_split_asm)
next
  case (infer_patom_PNum_Some uf B l v k n)
  then show ?case by (auto simp: fresh_ok_TC0 split: if_split_asm)
next
  case (infer_patom_PStr uf B l cs n)
  then show ?case by (auto simp: fresh_ok_TC0)
next
  case (infer_patom_PChar uf B l c n)
  then show ?case by (auto simp: fresh_ok_TC0)
next
  case (infer_patom_PParen_Cons_Nil uf B p n)
  then show ?case by simp
next
  case (infer_patom_PParen_Nil uf B n)
  then have e: \<open>s = sid\<close> \<open>\<tau> = unit_ty\<close> \<open>\<Gamma> = []\<close> \<open>n' = n\<close>
    by (auto split: Option.bind_split_asm)
  show ?case unfolding e by (simp add: fresh_ok_TC0)
next
  case (infer_patom_PParen_Cons_Cons uf B v vb vc n)
  from infer_patom_PParen_Cons_Cons.prems obtain s' \<tau>s \<Gamma>' where
    wf: \<open>cenv B\<close> \<open>bfree_env B\<close> \<open>ktv_env B \<subseteq> FK\<close> and
    ps: \<open>infer_pats uf B (v # vb # vc) n = Some (s', \<tau>s, \<Gamma>', n')\<close> and
    e: \<open>s = s'\<close> \<open>\<tau> = tuple \<tau>s\<close> \<open>\<Gamma> = \<Gamma>'\<close>
    by (auto split: prod.split_asm Option.bind_split_asm)
  note ih = infer_patom_PParen_Cons_Cons.IH[OF ps wf]
  show ?case unfolding e using ih by (auto intro: fresh_ok_tuple)
next
  case (infer_patom_PList uf B ps n)
  from infer_patom_PList.prems obtain s\<^sub>1 \<tau>s \<Gamma>\<^sub>1 n\<^sub>1 s\<^sub>2 where
    wf: \<open>cenv B\<close> \<open>bfree_env B\<close> \<open>ktv_env B \<subseteq> FK\<close> and
    ps: \<open>infer_pats uf B ps n = Some (s\<^sub>1, \<tau>s, \<Gamma>\<^sub>1, n\<^sub>1)\<close> and
    un: \<open>unis uf (map (\<lambda>\<tau>. (\<tau>, TV n\<^sub>1)) \<tau>s) (Suc n\<^sub>1) = Some (s\<^sub>2, n')\<close> and
    e: \<open>s = s\<^sub>2 \<odot> s\<^sub>1\<close> \<open>\<tau> = TC list_ty [sapp s\<^sub>2 (TV n\<^sub>1)]\<close>
      \<open>\<Gamma> = map (apsnd (sapp s\<^sub>2)) \<Gamma>\<^sub>1\<close>
    by (auto split: prod.split_asm Option.bind_split_asm)
  note ih = infer_patom_PList.IH[OF ps wf]
  have le1: \<open>n \<le> n\<^sub>1\<close> using ih by simp
  have \<tau>s: \<open>\<forall>u \<in> set \<tau>s. fresh_ok u n (Suc n\<^sub>1) FK\<close>
    using ih fresh_ok_mono[OF _ order_refl le_SucI[OF order_refl]] by auto
  note cs = ftv_cs_map_TV_fresh[OF \<tau>s le1 lessI]
  note uf = unis_fresh[OF un cs le_SucI[OF le1]]
  have le2: \<open>Suc n\<^sub>1 \<le> n'\<close> using uf by simp
  have s1: \<open>sconf s\<^sub>1 {n ..< n'} {n ..< n'}\<close>
    using sconf_fresh_mono[OF _ order_refl order_trans[OF le_SucI[OF order_refl] le2]] ih by simp
  have s2: \<open>sconf s\<^sub>2 {n ..< n'} {n ..< n'}\<close> \<open>khyg s\<^sub>2 FK\<close> \<open>bfree_sub s\<^sub>2\<close>
    using uf by simp_all
  have tv: \<open>fresh_ok (sapp s\<^sub>2 (TV n\<^sub>1)) n n' FK\<close>
    using fresh_ok_sapp'[OF fresh_ok_mono[OF fresh_ok_TV le1 order_refl] s2(1) le2 s2(2,3)] .
  have ihb: \<open>binds_ok \<Gamma>\<^sub>1 n n\<^sub>1 FK\<close> using ih by simp
  have G: \<open>binds_ok (map (apsnd (sapp s\<^sub>2)) \<Gamma>\<^sub>1) n n' FK\<close>
    using binds_ok_sapp'[OF binds_ok_mono[OF ihb order_refl le_SucI[OF order_refl]] s2(1) le2
        s2(2,3)] .
  show ?case
    unfolding e
    using ih s2(2,3) le1 le2 sconf_fresh_scomp[OF s1 s2(1) order_refl] khyg_scomp[of s\<^sub>1 FK s\<^sub>2]
      bfree_sub_scomp[of s\<^sub>1 s\<^sub>2] fresh_ok_list[OF tv] G
    by simp
next
  case (infer_patoms_Nil uf B n)
  then show ?case by simp
next
  case (infer_patoms_Cons uf B a as n)
  from infer_patoms_Cons.prems obtain s\<^sub>1 \<tau>\<^sub>1 \<Gamma>\<^sub>1 n\<^sub>1 s\<^sub>2 \<tau>s\<^sub>2 \<Gamma>\<^sub>2 where
    wf: \<open>cenv B\<close> \<open>bfree_env B\<close> \<open>ktv_env B \<subseteq> FK\<close> and
    pa: \<open>infer_patom uf B a n = Some (s\<^sub>1, \<tau>\<^sub>1, \<Gamma>\<^sub>1, n\<^sub>1)\<close> and
    ps: \<open>infer_patoms uf (sappe s\<^sub>1 B) as n\<^sub>1 = Some (s\<^sub>2, \<tau>s\<^sub>2, \<Gamma>\<^sub>2, n')\<close> and
    e: \<open>s = s\<^sub>2 \<odot> s\<^sub>1\<close> \<open>\<tau>s = sapp s\<^sub>2 \<tau>\<^sub>1 # \<tau>s\<^sub>2\<close> \<open>\<Gamma> = map (apsnd (sapp s\<^sub>2)) \<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2\<close>
    by (auto split: prod.split_asm Option.bind_split_asm)
  from pa wf have ih1: \<open>n \<le> n\<^sub>1 \<and> sconf s\<^sub>1 {n ..< n\<^sub>1} {n ..< n\<^sub>1} \<and> khyg s\<^sub>1 FK \<and>
    bfree_sub s\<^sub>1 \<and> fresh_ok \<tau>\<^sub>1 n n\<^sub>1 FK \<and> binds_ok \<Gamma>\<^sub>1 n n\<^sub>1 FK\<close>
    by (rule infer_patoms_Cons.IH)
  have le1: \<open>n \<le> n\<^sub>1\<close> and k1: \<open>khyg s\<^sub>1 FK\<close> and b1: \<open>bfree_sub s\<^sub>1\<close> using ih1 by simp_all
  from pa refl refl refl ps cenv_sappe[OF wf(1)] bfree_env_sappe[OF b1 wf(2)]
    ktv_env_sappe[OF k1 wf(3)]
  have ih2: \<open>n\<^sub>1 \<le> n' \<and> sconf s\<^sub>2 {n\<^sub>1 ..< n'} {n\<^sub>1 ..< n'} \<and> khyg s\<^sub>2 FK \<and> bfree_sub s\<^sub>2 \<and>
    (\<forall>\<tau> \<in> set \<tau>s\<^sub>2. fresh_ok \<tau> n\<^sub>1 n' FK) \<and> binds_ok \<Gamma>\<^sub>2 n\<^sub>1 n' FK\<close>
    by (rule infer_patoms_Cons.IH)
  have le2: \<open>n\<^sub>1 \<le> n'\<close> using ih2 by simp
  have s1: \<open>sconf s\<^sub>1 {n ..< n'} {n ..< n'}\<close> using sconf_fresh_mono[OF _ order_refl le2] ih1 by simp
  have s2: \<open>sconf s\<^sub>2 {n ..< n'} {n ..< n'}\<close> using sconf_fresh_mono[OF _ le1 order_refl] ih2 by simp
  have \<tau>s2: \<open>\<forall>u \<in> set \<tau>s\<^sub>2. fresh_ok u n n' FK\<close>
    using ih2 fresh_ok_mono[OF _ le1 order_refl] by auto
  have \<Gamma>2: \<open>binds_ok \<Gamma>\<^sub>2 n n' FK\<close> using ih2 binds_ok_mono[OF _ le1 order_refl] by auto
  show ?case
    unfolding e
    using ih1 ih2 le1 le2 sconf_fresh_scomp[OF s1 s2 order_refl] khyg_scomp[of s\<^sub>1 FK s\<^sub>2]
      bfree_sub_scomp[of s\<^sub>1 s\<^sub>2] fresh_ok_sapp'[OF _ s2 le2, of \<tau>\<^sub>1]
      binds_ok_sapp'[OF _ s2 le2, of \<Gamma>\<^sub>1] \<tau>s2 \<Gamma>2
    by simp
next
  case (infer_pats_Nil uf B n)
  then show ?case by simp
next
  case (infer_pats_Cons uf B p ps n)
  from infer_pats_Cons.prems obtain s\<^sub>1 \<tau>\<^sub>1 \<Gamma>\<^sub>1 n\<^sub>1 s\<^sub>2 \<tau>s\<^sub>2 \<Gamma>\<^sub>2 where
    wf: \<open>cenv B\<close> \<open>bfree_env B\<close> \<open>ktv_env B \<subseteq> FK\<close> and
    pa: \<open>infer_pat uf B p n = Some (s\<^sub>1, \<tau>\<^sub>1, \<Gamma>\<^sub>1, n\<^sub>1)\<close> and
    ps: \<open>infer_pats uf (sappe s\<^sub>1 B) ps n\<^sub>1 = Some (s\<^sub>2, \<tau>s\<^sub>2, \<Gamma>\<^sub>2, n')\<close> and
    e: \<open>s = s\<^sub>2 \<odot> s\<^sub>1\<close> \<open>\<tau>s = sapp s\<^sub>2 \<tau>\<^sub>1 # \<tau>s\<^sub>2\<close> \<open>\<Gamma> = map (apsnd (sapp s\<^sub>2)) \<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2\<close>
    by (auto split: prod.split_asm Option.bind_split_asm)
  from pa wf have ih1: \<open>n \<le> n\<^sub>1 \<and> sconf s\<^sub>1 {n ..< n\<^sub>1} {n ..< n\<^sub>1} \<and> khyg s\<^sub>1 FK \<and>
    bfree_sub s\<^sub>1 \<and> fresh_ok \<tau>\<^sub>1 n n\<^sub>1 FK \<and> binds_ok \<Gamma>\<^sub>1 n n\<^sub>1 FK\<close>
    by (rule infer_pats_Cons.IH)
  have le1: \<open>n \<le> n\<^sub>1\<close> and k1: \<open>khyg s\<^sub>1 FK\<close> and b1: \<open>bfree_sub s\<^sub>1\<close> using ih1 by simp_all
  from pa refl refl refl ps cenv_sappe[OF wf(1)] bfree_env_sappe[OF b1 wf(2)]
    ktv_env_sappe[OF k1 wf(3)]
  have ih2: \<open>n\<^sub>1 \<le> n' \<and> sconf s\<^sub>2 {n\<^sub>1 ..< n'} {n\<^sub>1 ..< n'} \<and> khyg s\<^sub>2 FK \<and> bfree_sub s\<^sub>2 \<and>
    (\<forall>\<tau> \<in> set \<tau>s\<^sub>2. fresh_ok \<tau> n\<^sub>1 n' FK) \<and> binds_ok \<Gamma>\<^sub>2 n\<^sub>1 n' FK\<close>
    by (rule infer_pats_Cons.IH)
  have le2: \<open>n\<^sub>1 \<le> n'\<close> using ih2 by simp
  have s1: \<open>sconf s\<^sub>1 {n ..< n'} {n ..< n'}\<close> using sconf_fresh_mono[OF _ order_refl le2] ih1 by simp
  have s2: \<open>sconf s\<^sub>2 {n ..< n'} {n ..< n'}\<close> using sconf_fresh_mono[OF _ le1 order_refl] ih2 by simp
  have \<tau>s2: \<open>\<forall>u \<in> set \<tau>s\<^sub>2. fresh_ok u n n' FK\<close>
    using ih2 fresh_ok_mono[OF _ le1 order_refl] by auto
  have \<Gamma>2: \<open>binds_ok \<Gamma>\<^sub>2 n n' FK\<close> using ih2 binds_ok_mono[OF _ le1 order_refl] by auto
  show ?case
    unfolding e
    using ih1 ih2 le1 le2 sconf_fresh_scomp[OF s1 s2 order_refl] khyg_scomp[of s\<^sub>1 FK s\<^sub>2]
      bfree_sub_scomp[of s\<^sub>1 s\<^sub>2] fresh_ok_sapp'[OF _ s2 le2, of \<tau>\<^sub>1]
      binds_ok_sapp'[OF _ s2 le2, of \<Gamma>\<^sub>1] \<tau>s2 \<Gamma>2
    by simp
qed simp_all

end
