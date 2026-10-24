theory Infer_Scope
  imports Infer
begin

section \<open>Signature names of the expression algorithm\<close>

text \<open>The expression algorithm only mentions signatures in scope: every signature name of a
  type it builds is bound by the basis or already occurs in one of its types
  (\<^const>\<open>sig_scope\<close>). This is what \<open>D_let\<close> and \<open>D_letrec\<close> ask of a declared type.

  The statements are relative to a fixed set \<open>X\<close> of names, as those of \<open>infer_wf\<close> are to
  \<open>FK\<close>: a basis is over \<open>X\<close> (\<open>sigs_in\<close>), a substitution is hygienic for \<open>X\<close>
  (\<open>shyg\<close>), and everything the algorithm builds stays over \<open>X\<close>. The main results are
  \<open>ty_stat_sigs\<close> and \<open>sig_stat_sigs\<close> for written types and signatures, \<open>infer_pat_sigs\<close>
  for patterns and \<open>infer_sigs\<close> for expressions. A basis is over its own scope
  (\<open>sigs_in_scope\<close>), which gives the statement above.\<close>

subsection \<open>Types\<close>

lemma tsigs_tsubst_le:
  \<open>(\<And>a. tsigs (\<theta> a) \<subseteq> X) \<Longrightarrow> tsigs t \<subseteq> X \<Longrightarrow> tsigs (tsubst \<theta> \<rho> t) \<subseteq> X\<close>
  by (induction t) (auto simp: UN_subset_iff)

lemma tsigs_bsubst:
  \<open>(\<And>a. tsigs (\<theta> a) \<subseteq> X) \<Longrightarrow> tsigs t \<subseteq> X \<Longrightarrow> tsigs (bsubst \<theta> \<rho> t) \<subseteq> X\<close>
  by (induction t) (auto simp: UN_subset_iff)

lemma tsigs_bsubst_eq: \<open>(\<And>a. tsigs (\<theta> a) = {}) \<Longrightarrow> tsigs (bsubst \<theta> \<rho> t) = tsigs t\<close>
  by (induction t) auto

lemma tsigs_kclose_at [simp]: \<open>tsigs (kclose_at d K t) = tsigs t\<close>
  by (induction t arbitrary: d) (auto split: option.split)

lemma tsigs_bsubstl_le:
  \<open>(\<And>a. tsigs (\<theta> a) \<subseteq> X) \<Longrightarrow> tsigs t \<subseteq> X \<Longrightarrow> tsigs (bsubstl \<theta> \<rho> t) \<subseteq> X\<close>
  by (induction t arbitrary: \<theta>) (auto simp: UN_subset_iff)

lemma tsigs_kopen_at:
  \<open>(\<And>i. tsigs (\<phi> i) \<subseteq> X) \<Longrightarrow> tsigs t \<subseteq> X \<Longrightarrow> tsigs (kopen_at d \<phi> t) \<subseteq> X\<close>
  by (induction t arbitrary: d) (auto simp: UN_subset_iff)

lemma tsigs_ksubst:
  \<open>(\<And>a. tsigs (\<phi> a) \<subseteq> X) \<Longrightarrow> tsigs t \<subseteq> X \<Longrightarrow> tsigs (ksubst \<phi> t) \<subseteq> X\<close>
  by (induction t) (auto simp: UN_subset_iff)

lemma tsigs_tapp [simp]: \<open>tsigs (tapp f x) = tsigs f \<union> tsigs x\<close>
  by (cases f) auto

lemma tsigs_foldl_tapp: \<open>tsigs (foldl tapp t args) = tsigs t \<union> \<Union>(tsigs ` set args)\<close>
  by (induction args arbitrary: t) auto

lemma tsigs_zip_case:
  \<open>tsigs d \<subseteq> X \<Longrightarrow> \<forall>t \<in> set ts. tsigs t \<subseteq> X
    \<Longrightarrow> tsigs (case map_of (zip ps ts) a of Some t \<Rightarrow> t | None \<Rightarrow> d) \<subseteq> X\<close>
  by (auto split: option.split dest!: map_of_SomeD set_zip_rightD)

lemma tsigs_tydef_app:
  assumes \<open>tsigs_tydef d \<subseteq> X\<close> \<open>\<forall>t \<in> set ts. tsigs t \<subseteq> X\<close>
  shows \<open>tsigs (tydef_app d ts) \<subseteq> X\<close>
proof (cases d)
  case (TyFn ps b)
  have \<open>tsigs (case map_of (zip ps ts) a of Some t \<Rightarrow> t | None \<Rightarrow> unit_ty) \<subseteq> X\<close> for a
    by (rule tsigs_zip_case) (use assms in simp_all)
  then show ?thesis using assms TyFn by (simp add: tsigs_bsubst)
qed (use assms in auto)

lemma tsigs_treal_le:
  assumes \<phi>: \<open>\<And>k d. map_of \<phi> k = Some d \<Longrightarrow> tsigs_tydef d \<subseteq> X\<close>
  shows \<open>tsigs t \<subseteq> X \<Longrightarrow> tsigs (treal \<phi> t) \<subseteq> X\<close>
proof (induction t)
  case (TC c ts)
  have ts: \<open>tsigs (treal \<phi> u) \<subseteq> X\<close> if \<open>u \<in> set ts\<close> for u
    by (rule TC.IH[OF that]) (use TC.prems that in auto)
  show ?case
  proof (cases \<open>map_of \<phi> (stamp c)\<close>)
    case (Some d)
    then show ?thesis
    proof (cases d)
      case (TyFn ps b)
      have \<open>tsigs b \<subseteq> X\<close> using \<phi>[OF Some] TyFn by simp
      moreover have
        \<open>tsigs (case map_of (zip ps (map (treal \<phi>) ts)) a of Some t \<Rightarrow> t | None \<Rightarrow> unit_ty) \<subseteq> X\<close>
        for a
        by (rule tsigs_zip_case) (use ts in auto)
      ultimately show ?thesis using Some TyFn by (simp add: tsigs_bsubstl_le)
    qed (use ts in auto)
  qed (use ts in auto)
qed auto

lemma tsigs_real:
  assumes \<open>\<And>k d. map_of \<phi> k = Some d \<Longrightarrow> tsigs_tydef d \<subseteq> X\<close>
  shows \<open>tsigs_ent e \<subseteq> X \<Longrightarrow> tsigs_ent (real_ent \<phi> e) \<subseteq> X\<close>
    and \<open>tsigs_env E \<subseteq> X \<Longrightarrow> tsigs_env (real_env \<phi> E) \<subseteq> X\<close>
proof (induction e and E rule: tsigs_ent_induct)
  case (tsigs_ent_TEval \<sigma>) then show ?case using tsigs_treal_le[OF assms] by (cases \<sigma>) auto
next
  case (tsigs_ent_TEcon \<sigma> n) then show ?case using tsigs_treal_le[OF assms] by (cases \<sigma>) auto
next
  case (tsigs_ent_TEtyp d) then show ?case
    using assms tsigs_treal_le[OF assms] by (cases d) (auto split: option.split)
next
  case (tsigs_ent_TEfun ps T E)
  have \<open>tsigs_env (real_env \<phi> E') \<subseteq> X\<close> if \<open>(y, T', E') \<in> set ps\<close> for y T' E'
    by (rule tsigs_ent_TEfun.IH) (use that tsigs_ent_TEfun.prems in auto)
  moreover have \<open>tsigs_env (real_env \<phi> E) \<subseteq> X\<close>
    by (rule tsigs_ent_TEfun.IH) (use tsigs_ent_TEfun.prems in auto)
  ultimately show ?case by (auto split: prod.splits)
next
  case (tsigs_ent_TEop l ps t\<^sub>1 t\<^sub>2) then show ?case using tsigs_treal_le[OF assms] by auto
next
  case (tsigs_ent_TEffi s \<sigma>) then show ?case using tsigs_treal_le[OF assms] by (cases \<sigma>) auto
next
  case (tsigs_ent_TEoff x r) then show ?case using tsigs_treal_le[OF assms] by auto
qed (auto split: prod.splits)

lemma tsigs_inst_scheme: \<open>inst_scheme n \<sigma> = (\<tau>, n') \<Longrightarrow> tsigs \<tau> \<subseteq> tsigs_sch \<sigma>\<close>
proof (cases \<sigma>)
  case (Sch t)
  have \<open>tsigs (case map_of (zip as (map TV vs)) a of None \<Rightarrow> TB a | Some \<tau> \<Rightarrow> \<tau>) = {}\<close>
    for as vs a
    by (auto split: option.split dest!: map_of_SomeD set_zip_rightD)
  then show \<open>inst_scheme n \<sigma> = (\<tau>, n') \<Longrightarrow> tsigs \<tau> \<subseteq> tsigs_sch \<sigma>\<close>
    using Sch by (auto simp: Let_def tsigs_bsubst_eq)
qed simp

lemma tsigs_op_inst:
  \<open>\<forall>t \<in> set args. tsigs t \<subseteq> X \<Longrightarrow> tsigs \<tau> \<subseteq> X \<Longrightarrow> tsigs (op_inst ps args \<tau>) \<subseteq> X\<close>
proof -
  assume a: \<open>\<forall>t \<in> set args. tsigs t \<subseteq> X\<close> \<open>tsigs \<tau> \<subseteq> X\<close>
  have \<open>tsigs (case map_of (zip ps args) a of Some t \<Rightarrow> t | None \<Rightarrow> TB a) \<subseteq> X\<close> for a
    by (rule tsigs_zip_case) (use a in simp_all)
  then show ?thesis using a by (simp add: op_inst_def tsigs_bsubstl_le)
qed

lemma tsigs_tsp: \<open>\<forall>(k, t) \<in> set \<phi>. tsigs t \<subseteq> X \<Longrightarrow> tsigs (tsp K \<phi> i) \<subseteq> X\<close>
  by (auto simp: tsp_def tsl_def split: option.split dest!: map_of_SomeD)

lemma tsigs_fn_ty: \<open>tsigs (fn_ty \<tau>s) = \<Union>(tsigs ` set \<tau>s)\<close>
  by (cases \<tau>s rule: fn_ty.cases) auto

lemma tsigs_rec_of: \<open>tsigs (rec_of fs t) = \<Union>(tsigs ` snd ` set fs) \<union> tsigs t\<close>
  by (induction fs) auto

lemma tsigs_rec_of_zipD: \<open>x \<in> tsigs (rec_of (zip ls \<tau>s) TRNil) \<Longrightarrow> \<exists>\<tau> \<in> set \<tau>s. x \<in> tsigs \<tau>\<close>
  by (auto simp: tsigs_rec_of dest: set_zip_rightD)

lemma tsigs_eff_ty [simp]: \<open>tsigs (eff_ty l ts) = \<Union>(tsigs ` set ts)\<close>
  by (simp add: eff_ty_def)

lemma tsigs_env_append [simp]: \<open>tsigs_env (A @ B) = tsigs_env A \<union> tsigs_env B\<close>
  by (induction A) auto

lemma has_sig_append [simp]: \<open>has_sig S (A @ B) \<longleftrightarrow> has_sig S A \<or> has_sig S B\<close>
  by (induction A) auto

lemma tsigs_tlookup: \<open>tlookup B p = Some e \<Longrightarrow> tsigs_ent e \<subseteq> tsigs_env B\<close>
proof (induction B p rule: tlookup_induct)
  case (Cons_Nil B x)
  then show ?case by (induction B) (auto split: if_split_asm)
next
  case (Cons_Cons B x v va)
  obtain e\<^sub>1 where m: \<open>map_of B x = Some e\<^sub>1\<close>
    using Cons_Cons.prems by (auto split: option.split_asm)
  then obtain E\<^sub>1 where ent: \<open>e\<^sub>1 = TEstr E\<^sub>1 \<or> e\<^sub>1 = TEinst E\<^sub>1\<close>
    and lk: \<open>tlookup E\<^sub>1 (v # va) = Some e\<close>
    using Cons_Cons.prems by (auto split: tentry.split_asm)
  have s1: \<open>tsigs_ent e\<^sub>1 \<subseteq> tsigs_env B\<close>
    using m by (induction B) (auto split: if_split_asm)
  have s2: \<open>tsigs_ent e \<subseteq> tsigs_env E\<^sub>1\<close> using Cons_Cons.IH ent m lk by auto
  have s3: \<open>tsigs_env E\<^sub>1 \<subseteq> tsigs_env B\<close> using s1 ent by auto
  show ?case using s2 s3 by (rule subset_trans)
qed simp


subsection \<open>Substitutions and unification\<close>

text \<open>A substitution is hygienic for \<open>X\<close> (\<open>shyg\<close>) when every type it substitutes
  mentions only signatures in \<open>X\<close>. Applying it keeps types, schemes and bases over \<open>X\<close>, and
  unification of constraints over \<open>X\<close> returns a hygienic substitution (\<open>kunify_tsigs\<close>,
  \<open>uni_shyg\<close>).\<close>

definition shyg :: \<open>ksub \<Rightarrow> name set \<Rightarrow> bool\<close> where
  \<open>shyg s X \<longleftrightarrow> (\<forall>a. tsigs (fst s a) \<subseteq> X)\<close>

lemma shyg_sid [simp]: \<open>shyg sid X\<close>
  by (simp add: shyg_def sid_def)

lemma tsigs_sapp: \<open>shyg s X \<Longrightarrow> tsigs t \<subseteq> X \<Longrightarrow> tsigs (sapp s t) \<subseteq> X\<close>
  by (cases s) (simp add: shyg_def tsigs_tsubst_le)

lemma tsigs_tsubst_TV [simp]: \<open>tsigs (tsubst TV \<rho> t) = tsigs t\<close>
  by (induction t) auto

lemma shyg_scomp: \<open>shyg s\<^sub>1 X \<Longrightarrow> shyg s\<^sub>2 X \<Longrightarrow> shyg (s\<^sub>2 \<odot> s\<^sub>1) X\<close>
  by (cases s\<^sub>1; cases s\<^sub>2) (simp add: shyg_def tsigs_tsubst_le)

lemma shyg_sproj: \<open>shyg s X \<Longrightarrow> shyg (sproj m s) X\<close>
  by (auto simp: shyg_def sproj_def)

lemma tsigs_sub_scheme:
  \<open>(\<And>a. tsigs (\<theta> a) \<subseteq> X) \<Longrightarrow> tsigs_sch \<sigma> \<subseteq> X \<Longrightarrow> tsigs_sch (sub_scheme \<theta> \<rho> \<sigma>) \<subseteq> X\<close>
  by (cases \<sigma>) (simp_all add: tsigs_tsubst_le)

lemma tsigs_sappe: \<open>shyg s X \<Longrightarrow> tsigs_env B \<subseteq> X \<Longrightarrow> tsigs_env (sappe s B) \<subseteq> X\<close>
proof (induction B)
  case (Cons xe B)
  obtain x e where xe: \<open>xe = (x, e)\<close> by (cases xe)
  obtain \<theta> \<rho> where s: \<open>s = (\<theta>, \<rho>)\<close> by (cases s)
  have \<open>tsigs_ent (sub_ent \<theta> \<rho> e) \<subseteq> X\<close>
    using Cons.prems unfolding xe s by (cases e) (simp_all add: shyg_def tsigs_sub_scheme tsigs_tsubst_le)
  then show ?case using Cons unfolding xe s by (simp add: sub_env_def)
qed (cases s, simp add: sub_env_def)

lemma has_sig_sappe [simp]: \<open>has_sig S (sappe s B) \<longleftrightarrow> has_sig S B\<close>
proof (cases s)
  case (Pair \<theta> \<rho>)
  have \<open>has_sig_ent S x (sub_ent \<theta> \<rho> e) = has_sig_ent S x e\<close> for x e by (cases e) auto
  then show ?thesis unfolding Pair by (induction B) (auto simp: sub_env_def)
qed

text \<open>The signature names of a list of unification constraints:\<close>

definition tsigs_cs :: \<open>(kty \<times> kty) list \<Rightarrow> name set\<close> where
  \<open>tsigs_cs cs = (\<Union>(t, u) \<in> set cs. tsigs t \<union> tsigs u)\<close>

lemma tsigs_cs_simps [simp]:
  \<open>tsigs_cs [] = {}\<close> \<open>tsigs_cs ((t, u) # cs) = tsigs t \<union> tsigs u \<union> tsigs_cs cs\<close>
  \<open>tsigs_cs (cs\<^sub>1 @ cs\<^sub>2) = tsigs_cs cs\<^sub>1 \<union> tsigs_cs cs\<^sub>2\<close>
  by (auto simp: tsigs_cs_def)

lemma tsigs_cs_zip: \<open>tsigs_cs (zip ts ts') \<subseteq> \<Union>(tsigs ` set ts) \<union> \<Union>(tsigs ` set ts')\<close>
  by (fastforce simp: tsigs_cs_def dest: set_zip_leftD set_zip_rightD)

lemma tsigs_cs_map_TV [simp]:
  \<open>tsigs_cs (map (\<lambda>(x, y). (tsubst TV \<rho> x, tsubst TV \<rho> y)) cs) = tsigs_cs cs\<close>
  by (induction cs) auto

lemma tsigs_sing: \<open>tsigs (sing a u b) \<subseteq> tsigs u\<close>
  by (simp add: sing_def)

lemma tsigs_cs_map_sing:
  \<open>tsigs_cs (map (\<lambda>(x, y). (tsubst (sing a u) RV x, tsubst (sing a u) RV y)) cs)
    \<subseteq> tsigs u \<union> tsigs_cs cs\<close>
proof -
  have \<open>tsigs (tsubst (sing a u) RV t) \<subseteq> tsigs u \<union> tsigs t\<close> for t
    by (rule tsigs_tsubst_le) (use tsigs_sing[of a u] in auto)
  then show ?thesis unfolding tsigs_cs_def by fastforce
qed

text \<open>Unification introduces no signature names: the substitution it returns maps every
  variable to a type over the names of the constraints.\<close>

lemma kunify_tsigs:
  \<open>kunify f cs n = Some (\<theta>, \<rho>, n') \<Longrightarrow> tsigs_cs cs \<subseteq> X \<Longrightarrow> \<forall>a. tsigs (\<theta> a) \<subseteq> X\<close>
  \<open>kbind f a u cs n = Some (\<theta>, \<rho>, n') \<Longrightarrow> tsigs u \<subseteq> X \<Longrightarrow> tsigs_cs cs \<subseteq> X
    \<Longrightarrow> \<forall>b. tsigs (\<theta> b) \<subseteq> X\<close>
proof (induction f cs n and f a u cs n arbitrary: \<theta> \<rho> n' and \<theta> \<rho> n' rule: kunify_induct)
  case (kunify_Cons_TC_TC f c ts c' ts' cs n)
  from kunify_Cons_TC_TC.prems have ku: \<open>kunify f (zip ts ts' @ cs) n = Some (\<theta>, \<rho>, n')\<close>
    by (auto split: if_split_asm)
  have \<open>tsigs_cs (zip ts ts') \<subseteq> X\<close>
    by (rule order_trans[OF tsigs_cs_zip]) (use kunify_Cons_TC_TC.prems in simp)
  then have \<open>tsigs_cs (zip ts ts' @ cs) \<subseteq> X\<close> using kunify_Cons_TC_TC.prems by simp
  then show ?case using kunify_Cons_TC_TC.IH kunify_Cons_TC_TC.prems ku
    by (auto split: if_split_asm)
next
  case (kunify_Cons_TFn_TFn f u\<^sub>1 e u\<^sub>2 w\<^sub>1 g w\<^sub>2 cs n)
  from kunify_Cons_TFn_TFn.prems obtain \<rho>m n\<^sub>1 \<rho>\<^sub>1 where rm: \<open>runify n e g = Some (\<rho>m, n\<^sub>1)\<close> and
    ku: \<open>kunify f (map (\<lambda>(x, y). (tsubst TV (mk_rsub \<rho>m) x, tsubst TV (mk_rsub \<rho>m) y))
                       ((u\<^sub>1, w\<^sub>1) # (u\<^sub>2, w\<^sub>2) # cs)) n\<^sub>1 = Some (\<theta>, \<rho>\<^sub>1, n')\<close>
    by (auto split: option.split_asm)
  show ?case
    by (rule kunify_Cons_TFn_TFn.IH[OF rm _ ku]) (use kunify_Cons_TFn_TFn.prems in simp_all)
next
  case (kunify_Cons_TDep_TDep f i sg T e u i' sg' T' g w cs n)
  from kunify_Cons_TDep_TDep.prems obtain \<rho>m n\<^sub>1 \<rho>\<^sub>1 where eq: \<open>i = i' \<and> sg = sg' \<and> T = T'\<close> and
    rm: \<open>runify n e g = Some (\<rho>m, n\<^sub>1)\<close> and
    ku: \<open>kunify f (map (\<lambda>(x, y). (tsubst TV (mk_rsub \<rho>m) x, tsubst TV (mk_rsub \<rho>m) y))
                       ((u, w) # cs)) n\<^sub>1 = Some (\<theta>, \<rho>\<^sub>1, n')\<close>
    by (auto split: option.split_asm if_split_asm)
  show ?case
    by (rule kunify_Cons_TDep_TDep.IH[OF eq rm _ ku]) (use kunify_Cons_TDep_TDep.prems in simp_all)
next
  case (kunify_Cons_TAct_TAct f l T e u l' T' g w cs n)
  from kunify_Cons_TAct_TAct.prems obtain \<rho>m n\<^sub>1 \<rho>\<^sub>1 where eq: \<open>T = T'\<close> and
    rm: \<open>runify n e g = Some (\<rho>m, n\<^sub>1)\<close> and
    ku: \<open>kunify f (map (\<lambda>(x, y). (tsubst TV (mk_rsub \<rho>m) x, tsubst TV (mk_rsub \<rho>m) y))
                       ((l, l') # (u, w) # cs)) n\<^sub>1 = Some (\<theta>, \<rho>\<^sub>1, n')\<close>
    by (auto split: option.split_asm if_split_asm)
  show ?case
    by (rule kunify_Cons_TAct_TAct.IH[OF eq rm _ ku]) (use kunify_Cons_TAct_TAct.prems in simp_all)
next
  case (kbind_Suc f a u cs n)
  show ?case
  proof (cases \<open>u = TV a\<close>)
    case True
    with kbind_Suc.prems have ku: \<open>kunify f cs n = Some (\<theta>, \<rho>, n')\<close> by simp
    from True ku show ?thesis by (rule kbind_Suc.IH) (use kbind_Suc.prems in simp)
  next
    case notv: False
    show ?thesis
    proof (cases \<open>a \<in> ftv u \<or> \<not> taclosed u\<close>)
      case True with notv kbind_Suc.prems show ?thesis by simp
    next
      case nb: False
      from kbind_Suc.prems notv nb obtain \<theta>\<^sub>1 \<rho>\<^sub>1 where
        ku: \<open>kunify f (map (\<lambda>(x, y). (tsubst (sing a u) RV x, tsubst (sing a u) RV y)) cs) n
               = Some (\<theta>\<^sub>1, \<rho>\<^sub>1, n')\<close> and
        \<theta>: \<open>\<theta> = (\<lambda>b. tsubst \<theta>\<^sub>1 \<rho>\<^sub>1 (sing a u b))\<close>
        by (auto split: option.split_asm)
      from notv nb ku have IH: \<open>\<forall>b. tsigs (\<theta>\<^sub>1 b) \<subseteq> X\<close>
        by (rule kbind_Suc.IH) (use kbind_Suc.prems tsigs_cs_map_sing[of a u cs] in auto)
      have \<open>tsigs (sing a u b) \<subseteq> X\<close> for b using kbind_Suc.prems tsigs_sing[of a u b] by blast
      then show ?thesis unfolding \<theta> by (intro allI tsigs_tsubst_le) (use IH in auto)
    qed
  qed
next
  case (kunify_Cons_TRCons_TRCons f l u r l' w r' cs n)
  show ?case
  proof (cases \<open>fpull l (TRCons l' w r')\<close>)
    case (Some p)
    then obtain w' r'' where p: \<open>fpull l (TRCons l' w r') = Some (w', r'')\<close> by (cases p) auto
    with kunify_Cons_TRCons_TRCons.prems have
      ku: \<open>kunify f ((u, w') # (r, r'') # cs) n = Some (\<theta>, \<rho>, n')\<close> by simp
    have ts: \<open>tsigs_cs ((u, w') # (r, r'') # cs) \<subseteq> X\<close>
      using kunify_Cons_TRCons_TRCons.prems fpull_tsigs[OF p] by auto
    show ?thesis by (rule kunify_Cons_TRCons_TRCons.IH(2)[OF p refl ku ts])
  next
    case None
    then obtain b where tl: \<open>rtail (TRCons l' w r') = TV b\<close> and ne: \<open>TV b \<noteq> rtail r\<close> and
      ku: \<open>kunify f ((TV b, TRCons l (TV n) (TV (Suc n))) # (TRCons l u r, TRCons l' w r') # cs)
                    (Suc (Suc n)) = Some (\<theta>, \<rho>, n')\<close>
      using kunify_Cons_TRCons_TRCons.prems by (auto split: kty.splits if_split_asm)
    have \<open>tsigs_cs ((TV b, TRCons l (TV n) (TV (Suc n))) #
                     (TRCons l u r, TRCons l' w r') # cs) \<subseteq> X\<close>
      using kunify_Cons_TRCons_TRCons.prems by simp
    then show ?thesis by (rule kunify_Cons_TRCons_TRCons.IH(1)[OF None tl ne ku])
  qed
qed (auto split: if_split_asm option.split_asm)

lemma unis_shyg: \<open>unis f cs n = Some (s, n') \<Longrightarrow> tsigs_cs cs \<subseteq> X \<Longrightarrow> shyg s X\<close>
proof -
  assume u: \<open>unis f cs n = Some (s, n')\<close> and c: \<open>tsigs_cs cs \<subseteq> X\<close>
  obtain \<theta> \<rho> where s: \<open>s = (\<theta>, \<rho>)\<close> and ku: \<open>kunify f cs n = Some (\<theta>, \<rho>, n')\<close>
    using u by (auto simp: unis_def split: option.split_asm)
  show ?thesis using kunify_tsigs(1)[OF ku c] by (simp add: shyg_def s)
qed

lemma uni_shyg:
  \<open>uni f t\<^sub>1 t\<^sub>2 n = Some (s, n') \<Longrightarrow> tsigs t\<^sub>1 \<subseteq> X \<Longrightarrow> tsigs t\<^sub>2 \<subseteq> X \<Longrightarrow> shyg s X\<close>
  using unis_shyg[of f \<open>[(t\<^sub>1, t\<^sub>2)]\<close> n s n' X] by (simp add: uni_def)

lemma uni_row_shyg: \<open>uni_row r\<^sub>1 r\<^sub>2 n = Some (s, n') \<Longrightarrow> shyg s X\<close>
  by (auto simp: uni_row_def shyg_def split: option.split_asm)


subsection \<open>Bases\<close>

text \<open>A basis is over \<open>X\<close> (\<open>sigs_in\<close>) when its types mention only names in \<open>X\<close>
  and every signature it binds is in \<open>X\<close>. A basis is always over its own
  \<^const>\<open>sig_scope\<close>. Lookup, \<^const>\<open>param_env\<close>, realisation and substitution by a
  hygienic substitution stay over \<open>X\<close>.\<close>

definition sigs_in :: \<open>tenv \<Rightarrow> name set \<Rightarrow> bool\<close> where
  \<open>sigs_in B X \<longleftrightarrow> tsigs_env B \<subseteq> X \<and> (\<forall>S. has_sig S B \<longrightarrow> S \<in> X)\<close>

lemma sigs_in_Nil [simp]: \<open>sigs_in [] X\<close>
  by (simp add: sigs_in_def)

lemma sigs_in_Cons [simp]:
  \<open>sigs_in ((x, e) # B) X
    \<longleftrightarrow> tsigs_ent e \<subseteq> X \<and> (\<forall>S. has_sig_ent S x e \<longrightarrow> S \<in> X) \<and> sigs_in B X\<close>
  by (auto simp: sigs_in_def)

lemma sigs_in_append [simp]: \<open>sigs_in (A @ B) X \<longleftrightarrow> sigs_in A X \<and> sigs_in B X\<close>
  by (auto simp: sigs_in_def)

lemma sigs_in_scope: \<open>sigs_in B (sig_scope B)\<close>
  by (simp add: sigs_in_def sig_scope_def)

lemma sigs_in_sappe: \<open>shyg s X \<Longrightarrow> sigs_in B X \<Longrightarrow> sigs_in (sappe s B) X\<close>
  by (simp add: sigs_in_def tsigs_sappe)

lemma has_sig_tlookup:
  \<open>tlookup B p = Some e \<Longrightarrow> p \<noteq> [] \<Longrightarrow> has_sig_ent S (last p) e \<Longrightarrow> has_sig S B\<close>
proof (induction B p rule: tlookup_induct)
  case (Cons_Nil B x)
  then show ?case by (induction B) (auto split: if_split_asm)
next
  case (Cons_Cons B x v va)
  obtain e\<^sub>1 where m: \<open>map_of B x = Some e\<^sub>1\<close>
    using Cons_Cons.prems by (auto split: option.split_asm)
  then obtain E\<^sub>1 where ent: \<open>e\<^sub>1 = TEstr E\<^sub>1 \<or> e\<^sub>1 = TEinst E\<^sub>1\<close>
    and lk: \<open>tlookup E\<^sub>1 (v # va) = Some e\<close>
    using Cons_Cons.prems by (auto split: tentry.split_asm)
  have \<open>has_sig S E\<^sub>1\<close> using Cons_Cons.IH ent m lk Cons_Cons.prems by auto
  moreover have \<open>has_sig_ent S x e\<^sub>1 \<Longrightarrow> has_sig S B\<close>
    using m by (induction B) (auto split: if_split_asm)
  ultimately show ?case using ent by auto
qed simp

lemma sigs_in_tlookup: \<open>sigs_in B X \<Longrightarrow> tlookup B p = Some e \<Longrightarrow> tsigs_ent e \<subseteq> X\<close>
  using tsigs_tlookup unfolding sigs_in_def by blast

lemma sigs_in_tlookup_env:
  assumes B: \<open>sigs_in B X\<close> and lk: \<open>tlookup B p = Some e\<close>
    and e: \<open>e = TEstr E \<or> e = TEinst E \<or> e = TEsig (T, E)\<close>
  shows \<open>sigs_in E X\<close>
proof -
  have p: \<open>p \<noteq> []\<close> using lk by (cases p) auto
  have \<open>tsigs_env E \<subseteq> X\<close> using sigs_in_tlookup[OF B lk] e by auto
  moreover have \<open>S \<in> X\<close> if \<open>has_sig S E\<close> for S
    using has_sig_tlookup[OF lk p, of S] that B e by (auto simp: sigs_in_def)
  ultimately show ?thesis by (simp add: sigs_in_def)
qed

lemma has_sig_param_env: \<open>has_sig S (param_env E) \<Longrightarrow> has_sig S E\<close>
  by (induction E rule: param_env.induct) auto

lemma tsigs_param_env: \<open>tsigs_env (param_env E) \<subseteq> tsigs_env E\<close>
  by (induction E rule: param_env.induct) auto

lemma sigs_in_param_env: \<open>sigs_in E X \<Longrightarrow> sigs_in (param_env E) X\<close>
  using tsigs_param_env[of E] has_sig_param_env[of _ E] unfolding sigs_in_def by blast

lemma has_sig_real:
  \<open>has_sig_ent S x (real_ent \<phi> e) = has_sig_ent S x e\<close>
  \<open>has_sig S (real_env \<phi> E) = has_sig S E\<close>
  by (induction e and E arbitrary: x rule: real_ent_real_env.induct) auto

lemma sigs_in_real:
  assumes a: \<open>sigs_in E X\<close> and b: \<open>\<And>k d. map_of \<phi> k = Some d \<Longrightarrow> tsigs_tydef d \<subseteq> X\<close>
  shows \<open>sigs_in (real_env \<phi> E) X\<close>
proof -
  have \<open>tsigs_env (real_env \<phi> E) \<subseteq> X\<close>
    using a[unfolded sigs_in_def] by (intro tsigs_real(2)[OF b]) blast+
  then show ?thesis using a by (simp add: sigs_in_def has_sig_real)
qed

lemma dep_vars_tsigs: \<open>map_of (dep_vars T K) k = Some d \<Longrightarrow> tsigs_tydef d \<subseteq> X\<close>
  by (auto simp: dep_vars_def dest!: map_of_SomeD)

lemma sigs_in_dep_vars: \<open>sigs_in E X \<Longrightarrow> sigs_in (real_env (dep_vars T K) E) X\<close>
  by (rule sigs_in_real) (auto dest: dep_vars_tsigs)

subsection \<open>Elaborated types and signatures\<close>

text \<open>Elaborating a written type or signature against a basis over \<open>X\<close> gives a type or a
  structure over \<open>X\<close> (\<open>ty_stat_sigs\<close>, \<open>sig_stat_sigs\<close>); the type-variable environment
  threaded through the elaboration stays over \<open>X\<close> as well (\<open>tsigs_ve\<close>).\<close>

definition tsigs_ve :: \<open>tvenv \<Rightarrow> name set\<close> where
  \<open>tsigs_ve ve = \<Union>(tsigs ` snd ` set (fst ve))\<close>

lemma tsigs_ve_simps [simp]:
  \<open>tsigs_ve ([], rs) = {}\<close> \<open>tsigs_ve ((a, t) # ts, rs) = tsigs t \<union> tsigs_ve (ts, rs)\<close>
  \<open>tsigs_ve (zip as (map TV ps), rs) = {}\<close>
  by (auto simp: tsigs_ve_def dest!: set_zip_rightD)

lemma head_stat_sigs:
  assumes h: \<open>head_stat B fr ve n p args = Some (\<tau>, ve', n')\<close> and B: \<open>sigs_in B X\<close>
    and v: \<open>tsigs_ve ve \<subseteq> X\<close> and a: \<open>\<forall>t \<in> set args. tsigs t \<subseteq> X\<close>
  shows \<open>tsigs \<tau> \<subseteq> X \<and> tsigs_ve ve' \<subseteq> X\<close>
proof -
  obtain tvs rvs where ve: \<open>ve = (tvs, rvs)\<close> by (cases ve)
  show ?thesis
  proof (cases \<open>tlookup B (path_nms p)\<close>)
    case (Some e)
    then obtain d where e: \<open>e = TEtyp d\<close> and \<tau>: \<open>\<tau> = tydef_app d args\<close> and ve': \<open>ve' = ve\<close>
      using h ve by (auto split: tentry.split_asm if_split_asm)
    have \<open>tsigs_tydef d \<subseteq> X\<close> using sigs_in_tlookup[OF B Some] e by simp
    then show ?thesis using a v \<tau> ve' by (simp add: tsigs_tydef_app)
  next
    case None
    then obtain x where p: \<open>path_nms p = [x]\<close> using h ve by (auto split: list.split_asm)
    show ?thesis
    proof (cases \<open>map_of tvs x\<close>)
      case (Some t)
      then have \<open>\<tau> = foldl tapp t args \<and> ve' = ve\<close> using h ve None p by auto
      moreover have \<open>tsigs t \<subseteq> X\<close> using v ve map_of_SomeD[OF Some] by (force simp: tsigs_ve_def)
      ultimately show ?thesis using a v by (auto simp: tsigs_foldl_tapp)
    next
      case nt: None
      then have \<open>\<tau> = foldl tapp (TV n) args \<and> ve' = ((x, TV n) # tvs, rvs)\<close>
        using h ve None p by (auto split: if_split_asm)
      then show ?thesis using a v ve by (auto simp: tsigs_foldl_tapp)
    qed
  qed
qed

lemma row_stat_SomeD':
  assumes \<open>row_stat B fr (tvs, rvs) n (Some rt) = Some (r, ve', n')\<close>
  shows \<open>(\<exists>ls'. r = canon_row (foldr RCons ls' RNil) \<and> ve' = (tvs, rvs) \<and> n' = n)
       \<or> (\<exists>ls' v r'. r = canon_row (foldr RCons ls' r') \<and> map_of rvs v = Some r'
           \<and> ve' = (tvs, rvs) \<and> n' = n)
       \<or> (\<exists>ls' v. r = canon_row (foldr RCons ls' (RV n)) \<and> ve' = (tvs, (v, RV n) # rvs)
           \<and> n' = Suc n)\<close>
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
      then show ?thesis using assms TRow \<open>tail = Some t\<close> t pv by (auto split: Option.bind_split_asm)
    next
      case None
      then show ?thesis
        using assms TRow \<open>tail = Some t\<close> t pv by (auto split: Option.bind_split_asm if_split_asm)
    qed
  qed
qed (use assms in auto)

text \<open>Elaborating a type over \<open>X\<close> gives a type over \<open>X\<close>:\<close>

lemma ty_stat_sigs:
  \<open>ty_stat B fr ve n t = Some (\<tau>, ve', n') \<Longrightarrow> sigs_in B X \<Longrightarrow> tsigs_ve ve \<subseteq> X \<Longrightarrow>
     tsigs \<tau> \<subseteq> X \<and> tsigs_ve ve' \<subseteq> X\<close>
  \<open>atoms_stat B fr ve n as = Some (ts, ve', n') \<Longrightarrow> sigs_in B X \<Longrightarrow> tsigs_ve ve \<subseteq> X \<Longrightarrow>
     (\<forall>t \<in> set ts. tsigs t \<subseteq> X) \<and> tsigs_ve ve' \<subseteq> X\<close>
  \<open>atom_stat B fr ve n a = Some (\<tau>, ve', n') \<Longrightarrow> sigs_in B X \<Longrightarrow> tsigs_ve ve \<subseteq> X \<Longrightarrow>
     tsigs \<tau> \<subseteq> X \<and> tsigs_ve ve' \<subseteq> X\<close>
  \<open>tys_stat B fr ve n tys = Some (ts, ve', n') \<Longrightarrow> sigs_in B X \<Longrightarrow> tsigs_ve ve \<subseteq> X \<Longrightarrow>
     (\<forall>t \<in> set ts. tsigs t \<subseteq> X) \<and> tsigs_ve ve' \<subseteq> X\<close>
  \<open>spine_stat B fr ve n as = Some (\<tau>, ve', n') \<Longrightarrow> sigs_in B X \<Longrightarrow> tsigs_ve ve \<subseteq> X \<Longrightarrow>
     tsigs \<tau> \<subseteq> X \<and> tsigs_ve ve' \<subseteq> X\<close>
  \<open>row_stat B fr ve n ro = Some (r, ve', n') \<Longrightarrow> sigs_in B X \<Longrightarrow> tsigs_ve ve \<subseteq> X \<Longrightarrow>
     tsigs_ve ve' \<subseteq> X\<close>
proof (induction B fr ve n t and B fr ve n as and B fr ve n a and B fr ve n tys
    and B fr ve n as and B fr ve n ro
    arbitrary: \<tau> ve' n' and ts ve' n' and \<tau> ve' n' and ts ve' n' and \<tau> ve' n' and r ve' n'
    rule: ty_stat_induct)
  case (ty_stat_TArrow B fr ve n as ro t)
  from ty_stat_TArrow.prems obtain t\<^sub>1 v\<^sub>1 n\<^sub>1 r v\<^sub>2 n\<^sub>2 t\<^sub>2
    where s: \<open>spine_stat B fr ve n as = Some (t\<^sub>1, v\<^sub>1, n\<^sub>1)\<close>
    and r: \<open>row_stat B fr v\<^sub>1 n\<^sub>1 ro = Some (r, v\<^sub>2, n\<^sub>2)\<close>
    and t: \<open>ty_stat B fr v\<^sub>2 n\<^sub>2 t = Some (t\<^sub>2, ve', n')\<close>
    and \<tau>: \<open>\<tau> = TFn t\<^sub>1 r t\<^sub>2\<close>
    by (auto simp: bind_eq_Some_conv)
  have a: \<open>tsigs t\<^sub>1 \<subseteq> X \<and> tsigs_ve v\<^sub>1 \<subseteq> X\<close>
    using s ty_stat_TArrow.prems by (blast dest: ty_stat_TArrow.IH)
  have b: \<open>tsigs_ve v\<^sub>2 \<subseteq> X\<close> using s r a ty_stat_TArrow.prems by (blast dest: ty_stat_TArrow.IH)
  have c: \<open>tsigs t\<^sub>2 \<subseteq> X \<and> tsigs_ve ve' \<subseteq> X\<close>
    using s r t b ty_stat_TArrow.prems by (blast dest: ty_stat_TArrow.IH)
  show ?case using a c \<tau> by simp
next
  case (ty_stat_TArrowMod B fr ve n b t)
  obtain p where sg: \<open>mbind_sig b = SPath p []\<close>
    using ty_stat_TArrowMod.prems by (auto split: msig.split_asm list.split_asm)
  obtain T E where lk: \<open>tlookup B (path_nms p) = Some (TEsig (T, E))\<close>
    using ty_stat_TArrowMod.prems sg by (auto split: option.split_asm tentry.split_asm)
  let ?K = \<open>[n ..< n + length T]\<close>
  let ?E = \<open>real_env (dep_vars T ?K) E\<close>
  let ?B = \<open>(mbind_nm b, TEstr (param_env ?E)) # B\<close>
  obtain t' v' m where ok: \<open>abs_ok T E\<close>
    and ts: \<open>ty_stat ?B fr ve (n + length T) t = Some (t', v', m)\<close>
    and \<tau>: \<open>\<tau> = TDep (is_imp b) (mbind_sig b) (length T) (if fr then RV m else RNil) (kclose ?K t')\<close>
    and v': \<open>ve' = v'\<close>
    using ty_stat_TArrowMod.prems sg lk
    by (auto simp: Let_def bind_eq_Some_conv split: if_split_asm)
  from ty_stat_TArrowMod.prems have B: \<open>sigs_in B X\<close> and v: \<open>tsigs_ve ve \<subseteq> X\<close> by blast+
  have E: \<open>sigs_in E X\<close> by (rule sigs_in_tlookup_env[OF B lk]) simp
  have B': \<open>sigs_in ?B X\<close>
    using sigs_in_param_env[OF sigs_in_dep_vars[OF E]] B by (simp add: sigs_in_def)
  have IH: \<open>tsigs t' \<subseteq> X \<and> tsigs_ve v' \<subseteq> X\<close>
    by (rule ty_stat_TArrowMod.IH[OF sg refl lk refl refl refl refl ok ts B' v])
  have p: \<open>path_nms p \<noteq> []\<close> using lk by (cases \<open>path_nms p\<close>) auto
  have \<open>last (path_nms p) \<in> X\<close>
    using has_sig_tlookup[OF lk p, of \<open>last (path_nms p)\<close>] B by (auto simp: sigs_in_def)
  then show ?case using IH sg v' unfolding \<tau> by simp
next
  case (spine_stat_Cons B fr ve n a as)
  show ?case
  proof (cases a)
    case (TPath p)
    from spine_stat_Cons.prems TPath obtain ts v m
      where at: \<open>atoms_stat B fr ve n as = Some (ts, v, m)\<close>
      and h: \<open>head_stat B fr v m p ts = Some (\<tau>, ve', n')\<close> by (auto simp: bind_eq_Some_conv)
    have i: \<open>(\<forall>t\<in>set ts. tsigs t \<subseteq> X) \<and> tsigs_ve v \<subseteq> X\<close>
      by (rule spine_stat_Cons.IH) (use TPath at spine_stat_Cons.prems in simp_all)
    show ?thesis using head_stat_sigs[OF h] spine_stat_Cons.prems i by blast
  next
  qed (use spine_stat_Cons.IH spine_stat_Cons.prems in \<open>auto split: if_split_asm\<close>)
next
  case (ty_stat_TArrowName B fr ve n f e ro t)
  from ty_stat_TArrowName.prems obtain p as args v\<^sub>1 n\<^sub>1 l ls r v\<^sub>2 n\<^sub>2 \<tau>\<^sub>0 v\<^sub>3 n\<^sub>3 where
    e: \<open>e = TPath p # as\<close> and ok: \<open>nm_ok (n_txt f)\<close> and
    at: \<open>atoms_stat B fr ve n as = Some (args, v\<^sub>1, n\<^sub>1)\<close> and
    ef: \<open>eff_at B p (length args) = Some (l, ls)\<close> and
    ro: \<open>row_stat ((nkey (n_txt f), TEeff l ls (length args)) # B) fr v\<^sub>1 n\<^sub>1 ro
           = Some (r, v\<^sub>2, n\<^sub>2)\<close> and
    tt: \<open>ty_stat ((nkey (n_txt f), TEeff l ls (length args)) # B) fr v\<^sub>2 n\<^sub>2 t
           = Some (\<tau>\<^sub>0, v\<^sub>3, n\<^sub>3)\<close> and
    \<tau>: \<open>\<tau> = TAct (eff_ty l args) [n\<^sub>3] (canon_row (rext (map (nlbl \<circ> mangle l) ls) r)) \<tau>\<^sub>0\<close> and
    ve': \<open>ve' = v\<^sub>3\<close>
    by (auto simp: bind_eq_Some_conv split: list.split_asm tatom.split_asm if_split_asm)
  from ty_stat_TArrowName.prems have B: \<open>sigs_in B X\<close> and v: \<open>tsigs_ve ve \<subseteq> X\<close> by blast+
  have B': \<open>sigs_in ((nkey (n_txt f), TEeff l ls (length args)) # B) X\<close> using B by simp
  have a: \<open>(\<forall>t \<in> set args. tsigs t \<subseteq> X) \<and> tsigs_ve v\<^sub>1 \<subseteq> X\<close>
    using e refl ok at B v by (rule ty_stat_TArrowName.IH)
  have b: \<open>tsigs_ve v\<^sub>2 \<subseteq> X\<close>
    using e refl ok at refl refl ef refl ro B' a[THEN conjunct2] by (rule ty_stat_TArrowName.IH)
  have c: \<open>tsigs \<tau>\<^sub>0 \<subseteq> X \<and> tsigs_ve v\<^sub>3 \<subseteq> X\<close>
    using e refl ok at refl refl ef refl ro refl refl tt B' b by (rule ty_stat_TArrowName.IH)
  show ?case using a b c unfolding \<tau> ve' by (auto simp: eff_ty_def)
next
  case (ty_stat_THand B fr ve n e a ro b)
  from ty_stat_THand.prems obtain p as args v\<^sub>1 n\<^sub>1 \<tau>\<^sub>0 v\<^sub>2 n\<^sub>2 r v\<^sub>3 n\<^sub>3 \<tau>\<^sub>1 v\<^sub>4 n\<^sub>4 l ls where
    e: \<open>e = TPath p # as\<close> and
    at: \<open>atoms_stat B fr ve n as = Some (args, v\<^sub>1, n\<^sub>1)\<close> and
    sp: \<open>spine_stat B fr v\<^sub>1 n\<^sub>1 a = Some (\<tau>\<^sub>0, v\<^sub>2, n\<^sub>2)\<close> and
    ro: \<open>row_stat B fr v\<^sub>2 n\<^sub>2 ro = Some (r, v\<^sub>3, n\<^sub>3)\<close> and
    sb: \<open>spine_stat B fr v\<^sub>3 n\<^sub>3 b = Some (\<tau>\<^sub>1, v\<^sub>4, n\<^sub>4)\<close> and
    \<tau>: \<open>\<tau> = TFn (TAct (eff_ty l args) [n\<^sub>4] (canon_row (rext (map (nlbl \<circ> mangle l) ls) r)) \<tau>\<^sub>0)
             r \<tau>\<^sub>1\<close> and
    ve': \<open>ve' = v\<^sub>4\<close>
    by (auto simp: bind_eq_Some_conv split: list.split_asm tatom.split_asm)
  from ty_stat_THand.prems have B: \<open>sigs_in B X\<close> and v: \<open>tsigs_ve ve \<subseteq> X\<close> by blast+
  have a: \<open>(\<forall>t \<in> set args. tsigs t \<subseteq> X) \<and> tsigs_ve v\<^sub>1 \<subseteq> X\<close>
    using e refl at B v by (rule ty_stat_THand.IH)
  have b: \<open>tsigs \<tau>\<^sub>0 \<subseteq> X \<and> tsigs_ve v\<^sub>2 \<subseteq> X\<close>
    using e refl at refl refl sp B a[THEN conjunct2] by (rule ty_stat_THand.IH)
  have c: \<open>tsigs_ve v\<^sub>3 \<subseteq> X\<close>
    using e refl at refl refl sp refl refl ro B b[THEN conjunct2] by (rule ty_stat_THand.IH)
  have d: \<open>tsigs \<tau>\<^sub>1 \<subseteq> X \<and> tsigs_ve v\<^sub>4 \<subseteq> X\<close>
    using e refl at refl refl sp refl refl ro refl refl sb B c by (rule ty_stat_THand.IH)
  show ?case using a b d unfolding \<tau> ve' by (auto simp: eff_ty_def)
next
  case (atom_stat_TName B fr ve n e)
  from atom_stat_TName.prems obtain p as args v m l where
    e: \<open>e = TPath p # as\<close> and fr: \<open>fr\<close> and
    at: \<open>atoms_stat B fr ve n as = Some (args, v, m)\<close> and
    \<tau>: \<open>\<tau> = TEv (eff_ty l args) (TV m) (tuple args)\<close> and ve': \<open>ve' = v\<close>
    by (auto simp: bind_eq_Some_conv split: list.split_asm tatom.split_asm if_split_asm)
  from atom_stat_TName.prems have B: \<open>sigs_in B X\<close> and v: \<open>tsigs_ve ve \<subseteq> X\<close> by blast+
  have \<open>(\<forall>t \<in> set args. tsigs t \<subseteq> X) \<and> tsigs_ve v \<subseteq> X\<close>
    using e refl fr at B v by (rule atom_stat_TName.IH)
  then show ?case unfolding \<tau> ve' by (auto simp: eff_ty_def)
next
  case (atom_stat_TPath B fr ve n p)
  then show ?case using head_stat_sigs[of B fr ve n p \<open>[]\<close> \<tau> ve' n' X] by simp
next
  case (atom_stat_TParen B fr ve n ts)
  show ?case
  proof (cases \<open>\<exists>t. ts = [t]\<close>)
    case True
    then obtain t where t: \<open>ts = [t]\<close> by blast
    then show ?thesis using atom_stat_TParen.IH atom_stat_TParen.prems by auto
  next
    case False
    from atom_stat_TParen.prems False obtain ts'
      where y: \<open>tys_stat B fr ve n ts = Some (ts', ve', n')\<close> and \<tau>: \<open>\<tau> = tuple ts'\<close>
      by (auto simp: bind_eq_Some_conv split: list.split_asm)
    have \<open>(\<forall>t\<in>set ts'. tsigs t \<subseteq> X) \<and> tsigs_ve ve' \<subseteq> X\<close>
    proof (cases ts)
      case Nil then show ?thesis using y atom_stat_TParen.prems by simp
    next
      case (Cons t r)
      moreover obtain t' r' where \<open>r = t' # r'\<close> using Cons False by (cases r) auto
      ultimately show ?thesis using y atom_stat_TParen.IH atom_stat_TParen.prems by auto
    qed
    then show ?thesis unfolding \<tau> by auto
  qed
next
  case (atoms_stat_Cons B fr ve n a as)
  from atoms_stat_Cons.prems obtain t v m ts' where at: \<open>atom_stat B fr ve n a = Some (t, v, m)\<close>
    and r: \<open>atoms_stat B fr v m as = Some (ts', ve', n')\<close> and ts: \<open>ts = t # ts'\<close>
    by (auto simp: bind_eq_Some_conv)
  have a: \<open>tsigs t \<subseteq> X \<and> tsigs_ve v \<subseteq> X\<close>
    using at atoms_stat_Cons.prems by (blast dest: atoms_stat_Cons.IH)
  have b: \<open>(\<forall>t\<in>set ts'. tsigs t \<subseteq> X) \<and> tsigs_ve ve' \<subseteq> X\<close>
    using at r a atoms_stat_Cons.prems by (blast dest: atoms_stat_Cons.IH)
  show ?case using a b ts by simp
next
  case (tys_stat_Cons B fr ve n t tys)
  from tys_stat_Cons.prems obtain t' v m ts' where at: \<open>ty_stat B fr ve n t = Some (t', v, m)\<close>
    and r: \<open>tys_stat B fr v m tys = Some (ts', ve', n')\<close> and ts: \<open>ts = t' # ts'\<close>
    by (auto simp: bind_eq_Some_conv)
  have a: \<open>tsigs t' \<subseteq> X \<and> tsigs_ve v \<subseteq> X\<close>
    using at tys_stat_Cons.prems by (blast dest: tys_stat_Cons.IH)
  have b: \<open>(\<forall>t\<in>set ts'. tsigs t \<subseteq> X) \<and> tsigs_ve ve' \<subseteq> X\<close>
    using at r a tys_stat_Cons.prems by (blast dest: tys_stat_Cons.IH)
  show ?case using a b ts by simp
next
  case (row_stat_Some B fr ve n r\<^sub>0)
  obtain tvs rvs where ve: \<open>ve = (tvs, rvs)\<close> by (cases ve)
  have \<open>fst ve' = fst ve\<close>
    using row_stat_SomeD'[of B fr tvs rvs n r\<^sub>0 r ve' n'] row_stat_Some.prems ve by auto
  then show ?case using row_stat_Some.prems by (simp add: tsigs_ve_def)
next
  case (ty_stat_TRec B fr ve n fs rt)
  from ty_stat_TRec.prems obtain ts v m where d: \<open>distinct (map (n_txt \<circ> fst) fs)\<close> and
    ts: \<open>tys_stat B fr ve n (map snd fs) = Some (ts, v, m)\<close>
    by (auto simp: bind_eq_Some_conv split: if_split_asm)
  have a: \<open>(\<forall>t \<in> set ts. tsigs t \<subseteq> X) \<and> tsigs_ve v \<subseteq> X\<close>
    using d ts ty_stat_TRec.prems by (blast dest: ty_stat_TRec.IH)
  show ?case
  proof (cases rt)
    case None
    then show ?thesis using ty_stat_TRec.prems ts a d by (auto dest!: tsigs_rec_of_zipD)
  next
    case (Some t)
    from ty_stat_TRec.prems obtain u v\<^sub>2 m\<^sub>2 where tu: \<open>ty_stat B fr v m t = Some (u, v\<^sub>2, m\<^sub>2)\<close>
      and e: \<open>\<tau> = rec_of (zip (map (n_txt \<circ> fst) fs) ts) u\<close> \<open>ve' = v\<^sub>2\<close>
      using d ts Some by (auto simp: bind_eq_Some_conv) (case_tac a; auto)
    have b: \<open>tsigs u \<subseteq> X \<and> tsigs_ve v\<^sub>2 \<subseteq> X\<close>
      using a ty_stat_TRec.prems(2) by (intro ty_stat_TRec.IH(2)[OF d ts refl refl Some tu]; simp)
    show ?thesis unfolding e using a b by (fastforce simp: tsigs_rec_of dest: set_zip_rightD)
  qed
qed (auto split: if_split_asm)

lemma tsigs_close_ty [simp]: \<open>tsigs (close_ty as rs t) = tsigs t\<close>
  unfolding close_ty_def by (induction t) auto

lemma tsigs_close_sch [simp]: \<open>tsigs_sch (close_sch as rs t) = tsigs t\<close>
  by (simp add: close_sch_def)

lemma tsigs_gen [simp]: \<open>tsigs_sch (gen B A \<tau>) = tsigs \<tau>\<close>
  by (simp add: gen_def split: prod.split)

lemma tsigs_map_of: \<open>map_of E x = Some e \<Longrightarrow> tsigs_ent e \<subseteq> tsigs_env E\<close>
  by (induction E) (auto split: if_split_asm)

lemma match_sig_mem:
  \<open>match_sig E T E\<^sub>1 = Some \<phi> \<Longrightarrow> (k, d) \<in> set \<phi> \<Longrightarrow> tsigs_tydef d \<subseteq> tsigs_env E\<close>
proof (induction E T E\<^sub>1 arbitrary: \<phi> rule: match_sig_induct)
  case (Cons_TEtyp_TyAbs E T t c k' r)
  then show ?case
    by (auto simp: bind_eq_Some_conv split: if_split_asm option.split_asm tentry.split_asm
        dest!: tsigs_map_of) blast+
next
  case (Cons_TEstr E T x E\<^sub>1 r)
  from Cons_TEstr.prems obtain E\<^sub>2 \<phi>\<^sub>1 \<phi>\<^sub>2 where m: \<open>map_of E x = Some (TEstr E\<^sub>2)\<close>
    and a\<^sub>1: \<open>match_sig E\<^sub>2 T E\<^sub>1 = Some \<phi>\<^sub>1\<close> and a\<^sub>2: \<open>match_sig E T r = Some \<phi>\<^sub>2\<close>
    and \<phi>: \<open>\<phi> = \<phi>\<^sub>1 @ \<phi>\<^sub>2\<close>
    by (auto simp: bind_eq_Some_conv split: option.split_asm tentry.split_asm)
  have e: \<open>tsigs_env E\<^sub>2 \<subseteq> tsigs_env E\<close> using tsigs_map_of[OF m] by simp
  show ?case
  proof (cases \<open>(k, d) \<in> set \<phi>\<^sub>1\<close>)
    case True then show ?thesis using Cons_TEstr.IH[OF m refl a\<^sub>1] e by blast
  next
    case False then show ?thesis
      using Cons_TEstr.IH[OF m refl a\<^sub>1] a\<^sub>2 Cons_TEstr.prems \<phi> by auto
  qed
qed auto

lemma match_sig_tsigs:
  \<open>match_sig E T E\<^sub>1 = Some \<phi> \<Longrightarrow> tsigs_env E \<subseteq> X \<Longrightarrow> map_of \<phi> k = Some d
    \<Longrightarrow> tsigs_tydef d \<subseteq> X\<close>
  using match_sig_mem by (blast dest: map_of_SomeD)

lemma tsigs_foldr_TFn:
  \<open>tsigs (foldr (\<lambda>(t, r) acc. TFn t (RV r) acc) (zip ts rs) \<tau>) \<subseteq> \<Union>(tsigs ` set ts) \<union> tsigs \<tau>\<close>
  by (induction ts arbitrary: rs; case_tac rs) auto

lemma cons_stat_sigs:
  \<open>cons_stat B ve ps c n alts = Some (cs, n') \<Longrightarrow> sigs_in B X \<Longrightarrow> tsigs_ve ve \<subseteq> X
    \<Longrightarrow> sigs_in cs X\<close>
proof (induction alts arbitrary: n cs n')
  case (Cons alt alts)
  obtain cn args where alt: \<open>alt = (cn, args)\<close> by (cases alt)
  from Cons.prems obtain ts v n\<^sub>1 es n\<^sub>2 where
    a: \<open>atoms_stat B False ve n args = Some (ts, v, n\<^sub>1)\<close> and
    r: \<open>cons_stat B ve ps c (n\<^sub>1 + length ts) alts = Some (es, n\<^sub>2)\<close> and
    cs: \<open>cs = (n_txt cn, TEcon (close_sch (set ps) (set [n ..< n\<^sub>1 + length ts])
               (foldr (\<lambda>(t, r) acc. TFn t (RV r) acc) (zip ts [n\<^sub>1 ..< n\<^sub>1 + length ts])
                 (TC c (map TV ps))))
               (length ts)) # es\<close>
    unfolding alt by (auto simp: Let_def bind_eq_Some_conv)
  have t: \<open>\<forall>t \<in> set ts. tsigs t \<subseteq> X\<close> using ty_stat_sigs(2)[OF a] Cons.prems by simp
  have f: \<open>tsigs (foldr (\<lambda>(t, r) acc. TFn t (RV r) acc) (zip ts [n\<^sub>1 ..< n\<^sub>1 + length ts])
      (TC c (map TV ps))) \<subseteq> X\<close>
    using tsigs_foldr_TFn[of ts \<open>[n\<^sub>1 ..< n\<^sub>1 + length ts]\<close> \<open>TC c (map TV ps)\<close>] t by auto
  show ?case using Cons.IH[OF r] Cons.prems f unfolding cs by simp
qed simp

lemma ops_stat_sigs:
  \<open>ops_stat B pre ps ve n ops = Some (es, n') \<Longrightarrow> sigs_in B X \<Longrightarrow> tsigs_ve ve \<subseteq> X
    \<Longrightarrow> sigs_in es X\<close>
proof (induction ops arbitrary: n es n')
  case (Cons op ops)
  obtain opn ty where op: \<open>op = (opn, ty)\<close> by (cases op)
  from Cons.prems obtain \<tau> v n\<^sub>1 where t: \<open>ty_stat B False ve n ty = Some (\<tau>, v, n\<^sub>1)\<close>
    and rest: \<open>(case \<tau> of TFn t\<^sub>1 _ t\<^sub>2 \<Rightarrow> ops_stat B pre ps ve n\<^sub>1 ops \<bind> (\<lambda>(es, n\<^sub>2).
              Some ((n_txt opn, TEop (mangle pre (n_txt opn)) ps (close_ty (set ps) {} t\<^sub>1)
                (close_ty (set ps) {} t\<^sub>2)) # es, n\<^sub>2))
           | _ \<Rightarrow> None) = Some (es, n')\<close>
    unfolding op by (auto simp: bind_eq_Some_conv)
  obtain t\<^sub>1 e t\<^sub>2 where \<tau>: \<open>\<tau> = TFn t\<^sub>1 e t\<^sub>2\<close> using rest by (cases \<tau>) auto
  from rest obtain es' n\<^sub>2 where r: \<open>ops_stat B pre ps ve n\<^sub>1 ops = Some (es', n\<^sub>2)\<close> and
    es: \<open>es = (n_txt opn, TEop (mangle pre (n_txt opn)) ps (close_ty (set ps) {} t\<^sub>1)
               (close_ty (set ps) {} t\<^sub>2)) # es'\<close>
    unfolding \<tau> by (auto simp: bind_eq_Some_conv)
  have \<open>tsigs \<tau> \<subseteq> X\<close> using ty_stat_sigs(1)[OF t] Cons.prems by simp
  then show ?case using Cons.IH[OF r] Cons.prems unfolding es \<tau> by simp
qed simp

lemma tsigs_env_rev [simp]: \<open>tsigs_env (rev A) = tsigs_env A\<close>
proof (induction A)
  case (Cons a A) then show ?case by (cases a) (simp add: Un_commute)
qed simp

lemma has_sig_rev [simp]: \<open>has_sig S (rev A) \<longleftrightarrow> has_sig S A\<close>
proof (induction A)
  case (Cons a A) then show ?case by (cases a) auto
qed simp

lemma sigs_in_rev [simp]: \<open>sigs_in (rev A) X \<longleftrightarrow> sigs_in A X\<close>
  by (simp add: sigs_in_def)

text \<open>Elaborating a signature over \<open>X\<close> gives a structure over \<open>X\<close>:\<close>

lemma sig_stat_sigs:
  \<open>sig_stat B n sg = Some (\<Sigma>, n') \<Longrightarrow> sigs_in B X \<Longrightarrow> sigs_in (snd \<Sigma>) X\<close>
  \<open>refn_stat B n \<Sigma> refs = Some (\<Sigma>', n') \<Longrightarrow> sigs_in B X \<Longrightarrow> sigs_in (snd \<Sigma>) X
    \<Longrightarrow> sigs_in (snd \<Sigma>') X\<close>
  \<open>spec_stat B n T acc ss = Some (\<Sigma>, n') \<Longrightarrow> sigs_in B X \<Longrightarrow> sigs_in acc X
    \<Longrightarrow> sigs_in (snd \<Sigma>) X\<close>
proof (induction B n sg and B n \<Sigma> refs and B n T acc ss arbitrary: \<Sigma> n' and \<Sigma>' n' and \<Sigma> n'
    rule: sig_stat_induct)
  case (sig_stat_SPath B n p refs)
  from sig_stat_SPath.prems obtain \<Sigma>\<^sub>0 where lk: \<open>tlookup B (path_nms p) = Some (TEsig \<Sigma>\<^sub>0)\<close>
    and r: \<open>refn_stat B n \<Sigma>\<^sub>0 refs = Some (\<Sigma>, n')\<close> by (auto split: option.split_asm tentry.split_asm)
  from sig_stat_SPath.prems have B: \<open>sigs_in B X\<close> by blast
  have \<open>sigs_in (snd \<Sigma>\<^sub>0) X\<close> by (cases \<Sigma>\<^sub>0) (auto intro: sigs_in_tlookup_env[OF B lk])
  then show ?case by (rule sig_stat_SPath.IH[OF lk refl r B])
next
  case (refn_stat_Cons_RType B n T E t ty refs)
  from refn_stat_Cons_RType.prems obtain c \<tau> v n\<^sub>1
    where m: \<open>map_of E (n_txt t) = Some (TEtyp (TyAbs c 0))\<close>
    and sc: \<open>stamp c \<in> set T\<close>
    and ts: \<open>ty_stat B False ([], []) n ty = Some (\<tau>, v, n\<^sub>1)\<close> and rp: \<open>rep_ok T c \<tau>\<close>
    and r: \<open>refn_stat B n\<^sub>1 (removeAll (stamp c) T, real_env [(stamp c, TyFn [] \<tau>)] E) refs
      = Some (\<Sigma>', n')\<close>
    by (auto simp: bind_eq_Some_conv
        split: option.split_asm tentry.split_asm tydef.split_asm nat.split_asm if_split_asm)
  from refn_stat_Cons_RType.prems have B: \<open>sigs_in B X\<close> and E: \<open>sigs_in E X\<close> by simp_all
  have \<open>tsigs \<tau> \<subseteq> X\<close> using ty_stat_sigs(1)[OF ts B] by (simp add: tsigs_ve_def)
  then have hr: \<open>sigs_in (real_env [(stamp c, TyFn [] \<tau>)] E) X\<close>
    using E by (intro sigs_in_real) (auto split: if_split_asm)
  show ?case
    by (rule refn_stat_Cons_RType.IH[OF m refl refl refl sc ts refl refl rp r B]) (use hr in simp)
next
  case (refn_stat_Cons_RMod B n T E M P refs)
  from refn_stat_Cons_RMod.prems obtain E\<^sub>M E\<^sub>P e \<phi>
    where m: \<open>map_of E (n_txt M) = Some (TEstr E\<^sub>M)\<close>
    and lk: \<open>tlookup B (path_nms P) = Some e\<close> and e: \<open>e = TEstr E\<^sub>P \<or> e = TEinst E\<^sub>P\<close>
    and ms: \<open>match_sig E\<^sub>P T E\<^sub>M = Some \<phi>\<close>
    and r: \<open>refn_stat B n (filter (\<lambda>k. map_of \<phi> k = None) T, real_env \<phi> E) refs = Some (\<Sigma>', n')\<close>
    by (auto simp: bind_eq_Some_conv split: option.split_asm tentry.split_asm)
  from refn_stat_Cons_RMod.prems have B: \<open>sigs_in B X\<close> and E: \<open>sigs_in E X\<close> by simp_all
  have P: \<open>sigs_in E\<^sub>P X\<close> using sigs_in_tlookup_env[OF B lk] e by blast
  have R: \<open>sigs_in (real_env \<phi> E) X\<close>
    using E match_sig_tsigs[OF ms] P by (intro sigs_in_real) (auto simp: sigs_in_def)
  from e show ?case
  proof (elim disjE)
    assume e': \<open>e = TEstr E\<^sub>P\<close>
    show ?thesis by (rule refn_stat_Cons_RMod.IH) (use m lk e' ms r R B in simp_all)
  next
    assume e': \<open>e = TEinst E\<^sub>P\<close>
    show ?thesis by (rule refn_stat_Cons_RMod.IH) (use m lk e' ms r R B in simp_all)
  qed
next
  case (spec_stat_Cons_SpType_Some B n T acc t as ty ss)
  let ?ps = \<open>[n ..< n + length as]\<close>
  from spec_stat_Cons_SpType_Some.prems obtain \<tau> v n\<^sub>1 where
    ts: \<open>ty_stat (acc @ B) False (zip (map n_txt as) (map TV ?ps), []) (n + length as) ty
      = Some (\<tau>, v, n\<^sub>1)\<close> and
    r: \<open>spec_stat B n\<^sub>1 T ((n_txt t, TEtyp (TyFn ?ps (close_ty (set ?ps) {} \<tau>))) # acc) ss
      = Some (\<Sigma>, n')\<close>
    by (auto simp: Let_def bind_eq_Some_conv)
  have hh: \<open>tsigs \<tau> \<subseteq> X\<close> using ty_stat_sigs(1)[OF ts] spec_stat_Cons_SpType_Some.prems by simp
  show ?case
    by (intro spec_stat_Cons_SpType_Some.IH)
      (use hh ts r spec_stat_Cons_SpType_Some.prems in \<open>simp_all add: Let_def del: set_upt\<close>)
next
  case (spec_stat_Cons_SpData B n T acc t as alts ss)
  let ?ps = \<open>[Suc n ..< Suc n + length as]\<close>
    and ?c = \<open>(n, n_txt t, map (\<lambda>(cn, args). (n_txt cn, length args)) alts)\<close>
  let ?B' = \<open>(n_txt t, TEtyp (TyAbs ?c (length as))) # acc @ B\<close>
  from spec_stat_Cons_SpData.prems obtain cs n\<^sub>1 where
    cs: \<open>cons_stat ?B' (zip (map n_txt as) (map TV ?ps), []) ?ps ?c (Suc n + length as) alts
      = Some (cs, n\<^sub>1)\<close> and
    r: \<open>spec_stat B n\<^sub>1 (T @ [n]) (rev cs @ (n_txt t, TEtyp (TyAbs ?c (length as))) # acc) ss
      = Some (\<Sigma>, n')\<close>
    and d: \<open>distinct (map (n_txt \<circ> fst) alts)\<close>
    and nm: \<open>list_all (\<lambda>(cn, _). nm_ok (n_txt cn)) alts\<close>
    by (auto simp: Let_def bind_eq_Some_conv split: if_split_asm)
  have hh: \<open>sigs_in cs X\<close>
    by (rule cons_stat_sigs[OF cs]) (use spec_stat_Cons_SpData.prems in simp_all)
  show ?case
    by (intro spec_stat_Cons_SpData.IH)
      (use hh d nm cs r spec_stat_Cons_SpData.prems in \<open>simp_all add: Let_def del: set_upt\<close>)
next
  case (spec_stat_Cons_SpVal B n T acc x ty ss)
  from spec_stat_Cons_SpVal.prems obtain \<tau> v n\<^sub>1
    where ts: \<open>ty_stat (acc @ B) True ([], []) n ty = Some (\<tau>, v, n\<^sub>1)\<close>
    and r: \<open>spec_stat B n\<^sub>1 T ((n_txt x, TEval (close_sch (set [n ..< n\<^sub>1]) (set [n ..< n\<^sub>1]) \<tau>))
        # acc) ss = Some (\<Sigma>, n')\<close>
    and nm: \<open>nm_ok (n_txt x)\<close>
    by (auto simp: bind_eq_Some_conv split: if_split_asm)
  have hh: \<open>tsigs \<tau> \<subseteq> X\<close>
    using ty_stat_sigs(1)[OF ts] spec_stat_Cons_SpVal.prems by (simp add: tsigs_ve_def)
  show ?case
    by (intro spec_stat_Cons_SpVal.IH) (use hh nm ts r spec_stat_Cons_SpVal.prems in simp_all)
next
  case (spec_stat_Cons_SpEff B n T acc x as ops ss)
  from spec_stat_Cons_SpEff.prems obtain es n\<^sub>1
    where c: \<open>distinct (map n_txt as)\<close>
    and os: \<open>ops_stat (acc @ B) (mangle (str ''%spec'') (n_txt x)) (eff_ps as n) (eff_ve as n)
        (n + length as) ops = Some (es, n\<^sub>1)\<close>
    and r: \<open>spec_stat B n\<^sub>1 T (rev es @ (n_txt x, TEeff (mangle (str ''%spec'') (n_txt x))
        (map fst es) (length as)) # acc) ss = Some (\<Sigma>, n')\<close>
    by (auto simp: bind_eq_Some_conv split: if_split_asm)
  have hh: \<open>sigs_in es X\<close>
    by (rule ops_stat_sigs[OF os]) (use spec_stat_Cons_SpEff.prems in simp_all)
  show ?case
    by (intro spec_stat_Cons_SpEff.IH) (use hh c os r spec_stat_Cons_SpEff.prems in simp_all)
next
  case (spec_stat_Cons_SpFix B n T acc f p opr ss)
  from spec_stat_Cons_SpFix.prems obtain prec where rn: \<open>read_nat (n_txt p) = Some prec\<close>
    and r: \<open>spec_stat B n T ((fix_key (n_txt opr), TEfix f prec) # acc) ss = Some (\<Sigma>, n')\<close>
    by (auto simp: bind_eq_Some_conv)
  show ?case by (intro spec_stat_Cons_SpFix.IH) (use rn r spec_stat_Cons_SpFix.prems in simp_all)
next
  case (spec_stat_Cons_SpMod B n T acc x sg ss)
  from spec_stat_Cons_SpMod.prems obtain T' E' n\<^sub>1
    where s: \<open>sig_stat (acc @ B) n sg = Some ((T', E'), n\<^sub>1)\<close>
    and r: \<open>spec_stat B n\<^sub>1 (T @ T') ((n_txt x, TEstr E') # acc) ss = Some (\<Sigma>, n')\<close>
    and nm: \<open>nm_ok (n_txt x)\<close>
    by (auto simp: bind_eq_Some_conv split: if_split_asm)
  from spec_stat_Cons_SpMod.prems have B: \<open>sigs_in B X\<close> and acc: \<open>sigs_in acc X\<close> by simp_all
  have hh: \<open>sigs_in E' X\<close> using spec_stat_Cons_SpMod.IH[OF nm s] B acc by simp
  have acc': \<open>sigs_in ((n_txt x, TEstr E') # acc) X\<close> using hh acc by (simp add: sigs_in_def)
  show ?case using nm s r B acc' by (blast intro: spec_stat_Cons_SpMod.IH)
next
  case (spec_stat_Cons_SpInc B n T acc sg ss)
  from spec_stat_Cons_SpInc.prems obtain T' E' n\<^sub>1
    where s: \<open>sig_stat (acc @ B) n sg = Some ((T', E'), n\<^sub>1)\<close>
    and r: \<open>spec_stat B n\<^sub>1 (T @ T') (rev E' @ acc) ss = Some (\<Sigma>, n')\<close>
    by (auto simp: bind_eq_Some_conv)
  from spec_stat_Cons_SpInc.prems have B: \<open>sigs_in B X\<close> and acc: \<open>sigs_in acc X\<close> by simp_all
  have hh: \<open>sigs_in E' X\<close> using spec_stat_Cons_SpInc.IH[OF s] B acc by simp
  have acc': \<open>sigs_in (rev E' @ acc) X\<close> using hh acc by simp
  show ?case using s r B acc' by (blast intro: spec_stat_Cons_SpInc.IH)
qed (auto split: if_split_asm)

lemma dep_env_sigs: \<open>dep_env B n sg m = Some (K, E\<^sub>K, n') \<Longrightarrow> sigs_in B X \<Longrightarrow> sigs_in E\<^sub>K X\<close>
  by (auto simp: dep_env_def bind_eq_Some_conv split: if_split_asm
      intro!: sigs_in_dep_vars dest!: sig_stat_sigs(1))

lemma match_dep_mem:
  \<open>match_dep E K E' = Some \<phi> \<Longrightarrow> (k, t) \<in> set \<phi> \<Longrightarrow> tsigs t \<subseteq> tsigs_env E\<close>
proof (induction E K E' arbitrary: \<phi> rule: match_dep_induct)
  case (Cons_TEtyp_TyFn_Nil_TK E K t\<^sub>0 k\<^sub>0 r)
  have a: \<open>tsigs (tydef_app d []) \<subseteq> tsigs_env E\<close> if \<open>map_of E t\<^sub>0 = Some (TEtyp d)\<close> for d
    using tsigs_tydef_app[of d \<open>tsigs_env E\<close> \<open>[]\<close>] tsigs_map_of[OF that] by simp
  show ?case using Cons_TEtyp_TyFn_Nil_TK.IH Cons_TEtyp_TyFn_Nil_TK.prems a
    by (auto simp: bind_eq_Some_conv split: if_split_asm option.split_asm tentry.split_asm) blast+
next
  case (Cons_TEstr E K x E\<^sub>1 r)
  from Cons_TEstr.prems obtain E\<^sub>2 \<phi>\<^sub>1 \<phi>\<^sub>2 where m: \<open>map_of E x = Some (TEstr E\<^sub>2)\<close>
    and a\<^sub>1: \<open>match_dep E\<^sub>2 K E\<^sub>1 = Some \<phi>\<^sub>1\<close> and a\<^sub>2: \<open>match_dep E K r = Some \<phi>\<^sub>2\<close>
    and \<phi>: \<open>\<phi> = \<phi>\<^sub>1 @ \<phi>\<^sub>2\<close>
    by (auto simp: bind_eq_Some_conv split: option.split_asm tentry.split_asm)
  have e: \<open>tsigs_env E\<^sub>2 \<subseteq> tsigs_env E\<close> using tsigs_map_of[OF m] by simp
  show ?case
  proof (cases \<open>(k, t) \<in> set \<phi>\<^sub>1\<close>)
    case True then show ?thesis using Cons_TEstr.IH[OF m refl a\<^sub>1] e by blast
  next
    case False then show ?thesis
      using Cons_TEstr.IH[OF m refl a\<^sub>1] a\<^sub>2 Cons_TEstr.prems \<phi> by auto
  qed
qed auto

lemma match_dep_tsigs:
  \<open>match_dep E K E' = Some \<phi> \<Longrightarrow> tsigs_env E \<subseteq> X \<Longrightarrow> \<forall>(k, t) \<in> set \<phi>. tsigs t \<subseteq> X\<close>
  using match_dep_mem by blast

subsection \<open>Pending requests\<close>

text \<open>The signature names in the realisations recorded by pending requests. Hygienic
  substitution and \<^const>\<open>resolve_inner\<close> keep them over \<open>X\<close>.\<close>

fun tsigs_preq :: \<open>preq \<Rightarrow> name set\<close> where
  \<open>tsigs_preq (PImp K \<phi> E cs r) = (\<Union>(k, t) \<in> set \<phi>. tsigs t)\<close>
| \<open>tsigs_preq (POff l r) = tsigs r\<close>

definition tsigs_pend :: \<open>pend \<Rightarrow> name set\<close> where
  \<open>tsigs_pend pd = (\<Union>(x, q) \<in> set pd. tsigs_preq q)\<close>

lemma tsigs_pend_simps [simp]:
  \<open>tsigs_pend [] = {}\<close>
  \<open>tsigs_pend ((x, q) # pd) = tsigs_preq q \<union> tsigs_pend pd\<close>
  by (auto simp: tsigs_pend_def)

lemma tsigs_sub_preq:
  assumes s: \<open>shyg s X\<close> and q: \<open>tsigs_preq q \<subseteq> X\<close>
  shows \<open>tsigs_preq (sub_preq s q) \<subseteq> X\<close>
proof (cases q)
  case (PImp K \<phi> E cs r)
  have \<open>(\<Union>(k, t)\<in>set (map (apsnd (sapp s)) \<phi>). tsigs t) \<subseteq> X\<close>
  proof (rule UN_least)
    fix kt assume \<open>kt \<in> set (map (apsnd (sapp s)) \<phi>)\<close>
    then obtain k t where kt: \<open>kt = (k, sapp s t)\<close> and k: \<open>(k, t) \<in> set \<phi>\<close> by auto
    have \<open>tsigs t \<subseteq> X\<close> using q k PImp by (auto simp: UN_subset_iff)
    then show \<open>(case kt of (k, t) \<Rightarrow> tsigs t) \<subseteq> X\<close> using tsigs_sapp[OF s] kt by simp
  qed
  then show ?thesis using PImp by simp
qed (use q tsigs_sapp[OF s] in simp)

lemma tsigs_sub_pend:
  assumes s: \<open>shyg s X\<close>
  shows \<open>tsigs_pend pd \<subseteq> X \<Longrightarrow> tsigs_pend (sub_pend s pd) \<subseteq> X\<close>
proof (induction pd)
  case Nil
  then show ?case by (simp add: sub_pend_def)
next
  case (Cons xq pd)
  obtain x q where xq: \<open>xq = (x, q)\<close> by (cases xq)
  have \<open>sub_pend s (xq # pd) = (x, sub_preq s q) # sub_pend s pd\<close>
    by (simp add: sub_pend_def xq)
  then show ?case using Cons xq tsigs_sub_preq[OF s] by simp
qed

lemma tsigs_resolve_inner: \<open>resolve_inner K pd = Some pd' \<Longrightarrow> tsigs_pend pd' = tsigs_pend pd\<close>
  by (induction K pd arbitrary: pd' rule: resolve_inner_induct)
     (fastforce simp: bind_eq_Some_conv split: if_split_asm)+


subsection \<open>Patterns\<close>

text \<open>Pattern inference against a basis over \<open>X\<close> returns a hygienic substitution and a type
  and bindings over \<open>X\<close> (\<open>infer_pat_sigs\<close>).\<close>

lemma con_ty_tsigs:
  \<open>con_ty m t = Some (\<tau>s, \<tau>) \<Longrightarrow> (\<forall>u \<in> set \<tau>s. tsigs u \<subseteq> tsigs t) \<and> tsigs \<tau> \<subseteq> tsigs t\<close>
  by (induction m t arbitrary: \<tau>s rule: con_ty.induct) (fastforce simp: bind_eq_Some_conv)+

abbreviation tsigs_bs :: \<open>(name \<times> kty) list \<Rightarrow> name set\<close> where
  \<open>tsigs_bs \<Gamma> \<equiv> \<Union>(tsigs ` snd ` set \<Gamma>)\<close>

lemma tsigs_bs_map:
  assumes s: \<open>shyg s X\<close> and \<Gamma>: \<open>tsigs_bs \<Gamma> \<subseteq> X\<close>
  shows \<open>tsigs_bs (map (apsnd (sapp s)) \<Gamma>) \<subseteq> X\<close>
proof (rule UN_least)
  fix u assume \<open>u \<in> snd ` set (map (apsnd (sapp s)) \<Gamma>)\<close>
  then obtain x t where \<open>(x, t) \<in> set \<Gamma>\<close> \<open>u = sapp s t\<close> by auto
  then show \<open>tsigs u \<subseteq> X\<close> using tsigs_sapp[OF s, of t] \<Gamma> by force
qed

lemma tsigs_map_sapp:
  \<open>shyg s X \<Longrightarrow> \<forall>t \<in> set ts. tsigs t \<subseteq> X \<Longrightarrow> \<forall>t \<in> set (map (sapp s) ts). tsigs t \<subseteq> X\<close>
  using tsigs_sapp by auto

lemma tsigs_cs_zip_sub:
  \<open>\<forall>t \<in> set ts. tsigs t \<subseteq> X \<Longrightarrow> \<forall>t \<in> set ts'. tsigs t \<subseteq> X
    \<Longrightarrow> tsigs_cs (zip ts ts') \<subseteq> X\<close>
  using tsigs_cs_zip[of ts ts'] by blast

text \<open>The constructor-application step of \<open>infer_pat_sigs\<close>, shared by plain and
  \<open>as\<close> patterns:\<close>

lemma con_pat_sigs:
  assumes B: \<open>sigs_in B X\<close> and lk: \<open>tlookup B p = Some (TEcon \<sigma> m)\<close>
    and inst: \<open>inst_scheme n \<sigma> = (\<tau>\<^sub>c, n\<^sub>1)\<close>
    and cty: \<open>con_ty m \<tau>\<^sub>c = Some (\<tau>s, \<tau>\<^sub>0)\<close>
    and ih: \<open>shyg sp X \<and> (\<forall>\<tau> \<in> set \<tau>s'. tsigs \<tau> \<subseteq> X) \<and> tsigs_bs \<Gamma>\<^sub>1 \<subseteq> X\<close>
    and un: \<open>unis uf (zip \<tau>s' (map (sapp sp) \<tau>s)) n\<^sub>2 = Some (s\<^sub>1, n')\<close>
  shows \<open>shyg (s\<^sub>1 \<odot> sp) X \<and> tsigs (sapp s\<^sub>1 (sapp sp \<tau>\<^sub>0)) \<subseteq> X
    \<and> tsigs_bs (map (apsnd (sapp s\<^sub>1)) \<Gamma>\<^sub>1) \<subseteq> X\<close>
proof -
  have c: \<open>tsigs \<tau>\<^sub>c \<subseteq> X\<close> using tsigs_inst_scheme[OF inst] sigs_in_tlookup[OF B lk] by auto
  have ct: \<open>\<forall>u \<in> set \<tau>s. tsigs u \<subseteq> X\<close> and c\<^sub>0: \<open>tsigs \<tau>\<^sub>0 \<subseteq> X\<close>
    using con_ty_tsigs[OF cty] c by blast+
  have sp: \<open>shyg sp X\<close> using ih by simp
  have z: \<open>tsigs_cs (zip \<tau>s' (map (sapp sp) \<tau>s)) \<subseteq> X\<close>
    by (rule tsigs_cs_zip_sub) (use ih tsigs_map_sapp[OF sp ct] in simp_all)
  have s\<^sub>1: \<open>shyg s\<^sub>1 X\<close> by (rule unis_shyg[OF un z])
  show ?thesis
    using shyg_scomp[OF sp s\<^sub>1] tsigs_sapp[OF s\<^sub>1 tsigs_sapp[OF sp c\<^sub>0]] tsigs_bs_map[OF s\<^sub>1] ih
    by simp
qed

lemma infer_pat_sigs:
  \<open>infer_pat uf B p n = Some (s, p\<^sub>x, \<tau>, \<Gamma>, n') \<Longrightarrow> sigs_in B X \<Longrightarrow>
     shyg s X \<and> tsigs \<tau> \<subseteq> X \<and> tsigs_bs \<Gamma> \<subseteq> X\<close>
  \<open>infer_patom uf B a n = Some (s, a\<^sub>x, \<tau>, \<Gamma>, n') \<Longrightarrow> sigs_in B X \<Longrightarrow>
     shyg s X \<and> tsigs \<tau> \<subseteq> X \<and> tsigs_bs \<Gamma> \<subseteq> X\<close>
  \<open>infer_patoms uf B as n = Some (s, as\<^sub>x, \<tau>s, \<Gamma>, n') \<Longrightarrow> sigs_in B X \<Longrightarrow>
     shyg s X \<and> (\<forall>\<tau> \<in> set \<tau>s. tsigs \<tau> \<subseteq> X) \<and> tsigs_bs \<Gamma> \<subseteq> X\<close>
  \<open>infer_pats uf B ps n = Some (s, ps\<^sub>x, \<tau>s, \<Gamma>, n') \<Longrightarrow> sigs_in B X \<Longrightarrow>
     shyg s X \<and> (\<forall>\<tau> \<in> set \<tau>s. tsigs \<tau> \<subseteq> X) \<and> tsigs_bs \<Gamma> \<subseteq> X\<close>
proof (induction uf B p n and uf B a n and uf B as n and uf B ps n
    arbitrary: s p\<^sub>x \<tau> \<Gamma> n' and s a\<^sub>x \<tau> \<Gamma> n' and s as\<^sub>x \<tau>s \<Gamma> n' and s ps\<^sub>x \<tau>s \<Gamma> n'
    rule: infer_pat_induct)
  case (infer_pat_PatOp uf B as opr p n)
  from infer_pat_PatOp.prems have B: \<open>sigs_in B X\<close> by blast
  from infer_pat_PatOp.prems obtain q p\<^sub>x where q: \<open>pat_resolve B (PatOp as opr p) = Some q\<close>
    and d: \<open>infer_pat uf B q n = Some (s, p\<^sub>x, \<tau>, \<Gamma>, n')\<close>
    by (auto simp del: pat_resolve.simps split: option.split_asm)
  show ?case by (rule infer_pat_PatOp.IH[OF q d B])
next
  case (infer_pat_PatApp_Cons_PQid_Cons uf B p v va n)
  from infer_pat_PatApp_Cons_PQid_Cons.prems have B: \<open>sigs_in B X\<close> by blast
  from infer_pat_PatApp_Cons_PQid_Cons.prems obtain \<sigma> m \<tau>\<^sub>c n\<^sub>1 \<tau>s \<tau>\<^sub>0 sp \<tau>s' \<Gamma>\<^sub>1 n\<^sub>2 s\<^sub>1 as\<^sub>x where
    lk: \<open>tlookup B (path_nms p) = Some (TEcon \<sigma> m)\<close> and
    mlen: \<open>m = length (v # va) \<and> v # va \<noteq> []\<close> and
    inst: \<open>inst_scheme n \<sigma> = (\<tau>\<^sub>c, n\<^sub>1)\<close> and cty: \<open>con_ty m \<tau>\<^sub>c = Some (\<tau>s, \<tau>\<^sub>0)\<close> and
    pa: \<open>infer_patoms uf B (v # va) n\<^sub>1 = Some (sp, as\<^sub>x, \<tau>s', \<Gamma>\<^sub>1, n\<^sub>2)\<close> and
    un: \<open>unis uf (zip \<tau>s' (map (sapp sp) \<tau>s)) n\<^sub>2 = Some (s\<^sub>1, n')\<close> and
    e: \<open>s = s\<^sub>1 \<odot> sp\<close> \<open>\<tau> = sapp s\<^sub>1 (sapp sp \<tau>\<^sub>0)\<close> \<open>\<Gamma> = map (apsnd (sapp s\<^sub>1)) \<Gamma>\<^sub>1\<close>
    by (auto split: option.split_asm tentry.split_asm if_split_asm prod.split_asm
        Option.bind_split_asm)
  note ih = infer_pat_PatApp_Cons_PQid_Cons.IH[OF lk refl mlen inst[symmetric] cty refl pa B]
  show ?case unfolding e by (rule con_pat_sigs[OF B lk inst cty ih un])
next
  case (infer_pat_PatAs uf B p x n)
  from infer_pat_PatAs.prems obtain \<Gamma>\<^sub>1 p\<^sub>x where nm: \<open>nm_ok (n_txt x)\<close>
    and ip: \<open>infer_pat uf B p n = Some (s, p\<^sub>x, \<tau>, \<Gamma>\<^sub>1, n')\<close>
    and g: \<open>\<Gamma> = (n_txt x, \<tau>) # \<Gamma>\<^sub>1\<close>
    by (auto split: if_split_asm Option.bind_split_asm prod.split_asm)
  have i: \<open>shyg s X \<and> tsigs \<tau> \<subseteq> X \<and> tsigs_bs \<Gamma>\<^sub>1 \<subseteq> X\<close>
    by (rule infer_pat_PatAs.IH[OF nm ip]) (use infer_pat_PatAs.prems in simp)
  show ?case using i g by simp
next
  case (infer_pat_PatAnn uf B p ty n)
  from infer_pat_PatAnn.prems have B: \<open>sigs_in B X\<close> by blast
  from infer_pat_PatAnn.prems obtain s\<^sub>1 \<tau>\<^sub>1 \<Gamma>\<^sub>1 n\<^sub>1 \<tau>\<^sub>a ve n\<^sub>2 s\<^sub>2 p\<^sub>x where
    ip: \<open>infer_pat uf B p n = Some (s\<^sub>1, p\<^sub>x, \<tau>\<^sub>1, \<Gamma>\<^sub>1, n\<^sub>1)\<close> and
    ts: \<open>ty_stat (sappe s\<^sub>1 B) True ([], []) n\<^sub>1 ty = Some (\<tau>\<^sub>a, ve, n\<^sub>2)\<close> and
    un: \<open>uni uf \<tau>\<^sub>1 \<tau>\<^sub>a n\<^sub>2 = Some (s\<^sub>2, n')\<close> and
    e: \<open>s = s\<^sub>2 \<odot> s\<^sub>1\<close> \<open>\<tau> = sapp s\<^sub>2 \<tau>\<^sub>1\<close> \<open>\<Gamma> = map (apsnd (sapp s\<^sub>2)) \<Gamma>\<^sub>1\<close>
    by (auto split: prod.split_asm Option.bind_split_asm)
  note ih = infer_pat_PatAnn.IH[OF ip B]
  have s1: \<open>shyg s\<^sub>1 X\<close> using ih by simp
  have ta: \<open>tsigs \<tau>\<^sub>a \<subseteq> X\<close> using ty_stat_sigs(1)[OF ts sigs_in_sappe[OF s1 B]] by simp
  have s2: \<open>shyg s\<^sub>2 X\<close> by (rule uni_shyg[OF un _ ta]) (use ih in simp)
  show ?case unfolding e using shyg_scomp[OF s1 s2] tsigs_sapp[OF s2] tsigs_bs_map[OF s2] ih by simp
next
  case (infer_patom_PQid_Cons_Nil uf B x n)
  show ?case
  proof (cases \<open>\<exists>\<sigma> m. tlookup B [n_txt x] = Some (TEcon \<sigma> m)\<close>)
    case True
    then obtain \<sigma> m where lk: \<open>tlookup B [n_txt x] = Some (TEcon \<sigma> m)\<close> by blast
    then have inst: \<open>inst_scheme n \<sigma> = (\<tau>, n')\<close> and e: \<open>s = sid\<close> \<open>\<Gamma> = []\<close>
      using infer_patom_PQid_Cons_Nil.prems by (auto split: if_split_asm prod.split_asm)
    show ?thesis
      using tsigs_inst_scheme[OF inst] sigs_in_tlookup[OF _ lk] infer_patom_PQid_Cons_Nil.prems e
      by auto
  next
    case False
    then show ?thesis
      using infer_patom_PQid_Cons_Nil.prems
      by (auto split: option.split_asm tentry.split_asm if_split_asm)
  qed
next
  case (infer_patom_PQid_Cons_Cons uf B va vc vd n)
  from infer_patom_PQid_Cons_Cons.prems obtain \<sigma> where
    lk: \<open>tlookup B (path_nms (MkPath (va # vc # vd))) = Some (TEcon \<sigma> 0)\<close> and
    inst: \<open>inst_scheme n \<sigma> = (\<tau>, n')\<close> and e: \<open>s = sid\<close> \<open>\<Gamma> = []\<close>
    by (auto split: option.split_asm tentry.split_asm nat.split_asm prod.split_asm)
  show ?case
    using tsigs_inst_scheme[OF inst] sigs_in_tlookup[OF _ lk] infer_patom_PQid_Cons_Cons.prems e
    by auto
next
  case (infer_patom_PParen_Cons_Cons uf B v vb vc n)
  from infer_patom_PParen_Cons_Cons.prems obtain s' \<tau>s \<Gamma>' ps\<^sub>x where
    ps: \<open>infer_pats uf B (v # vb # vc) n = Some (s', ps\<^sub>x, \<tau>s, \<Gamma>', n')\<close> and
    e: \<open>s = s'\<close> \<open>\<tau> = tuple \<tau>s\<close> \<open>\<Gamma> = \<Gamma>'\<close>
    by (auto split: prod.split_asm Option.bind_split_asm)
  show ?case
    unfolding e using infer_patom_PParen_Cons_Cons.IH[OF ps] infer_patom_PParen_Cons_Cons.prems
    by auto
next
  case (infer_patom_PList uf B ps n)
  from infer_patom_PList.prems have B: \<open>sigs_in B X\<close> by blast
  from infer_patom_PList.prems obtain s\<^sub>1 \<tau>s \<Gamma>\<^sub>1 n\<^sub>1 s\<^sub>2 ps\<^sub>x where
    ps: \<open>infer_pats uf B ps n = Some (s\<^sub>1, ps\<^sub>x, \<tau>s, \<Gamma>\<^sub>1, n\<^sub>1)\<close> and
    un: \<open>unis uf (map (\<lambda>\<tau>. (\<tau>, TV n\<^sub>1)) \<tau>s) (Suc n\<^sub>1) = Some (s\<^sub>2, n')\<close> and
    e: \<open>s = s\<^sub>2 \<odot> s\<^sub>1\<close> \<open>\<tau> = TC list_ty [sapp s\<^sub>2 (TV n\<^sub>1)]\<close> \<open>\<Gamma> = map (apsnd (sapp s\<^sub>2)) \<Gamma>\<^sub>1\<close>
    by (auto split: prod.split_asm Option.bind_split_asm)
  note ih = infer_patom_PList.IH[OF ps B]
  have s1: \<open>shyg s\<^sub>1 X\<close> using ih by simp
  have cs: \<open>tsigs_cs (map (\<lambda>\<tau>. (\<tau>, TV n\<^sub>1)) \<tau>s) \<subseteq> X\<close> using ih by (auto simp: tsigs_cs_def)
  have s2: \<open>shyg s\<^sub>2 X\<close> by (rule unis_shyg[OF un cs])
  have tv: \<open>tsigs (sapp s\<^sub>2 (TV n\<^sub>1)) \<subseteq> X\<close> by (rule tsigs_sapp[OF s2]) simp
  show ?case unfolding e using shyg_scomp[OF s1 s2] tv tsigs_bs_map[OF s2] ih by simp
next
  case (infer_patoms_Cons uf B a as n)
  from infer_patoms_Cons.prems have B: \<open>sigs_in B X\<close> by blast
  from infer_patoms_Cons.prems obtain s\<^sub>1 \<tau>\<^sub>1 \<Gamma>\<^sub>1 n\<^sub>1 s\<^sub>2 \<tau>s\<^sub>2 \<Gamma>\<^sub>2 a\<^sub>x as\<^sub>x where
    pa: \<open>infer_patom uf B a n = Some (s\<^sub>1, a\<^sub>x, \<tau>\<^sub>1, \<Gamma>\<^sub>1, n\<^sub>1)\<close> and
    ps: \<open>infer_patoms uf (sappe s\<^sub>1 B) as n\<^sub>1 = Some (s\<^sub>2, as\<^sub>x, \<tau>s\<^sub>2, \<Gamma>\<^sub>2, n')\<close> and
    e: \<open>s = s\<^sub>2 \<odot> s\<^sub>1\<close> \<open>\<tau>s = sapp s\<^sub>2 \<tau>\<^sub>1 # \<tau>s\<^sub>2\<close> \<open>\<Gamma> = map (apsnd (sapp s\<^sub>2)) \<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2\<close>
    by (auto split: prod.split_asm Option.bind_split_asm)
  have ih1: \<open>shyg s\<^sub>1 X \<and> tsigs \<tau>\<^sub>1 \<subseteq> X \<and> tsigs_bs \<Gamma>\<^sub>1 \<subseteq> X\<close>
    by (rule infer_patoms_Cons.IH) (use pa B in simp_all)
  then have s1: \<open>shyg s\<^sub>1 X\<close> by simp
  have ih2: \<open>shyg s\<^sub>2 X \<and> (\<forall>\<tau> \<in> set \<tau>s\<^sub>2. tsigs \<tau> \<subseteq> X) \<and> tsigs_bs \<Gamma>\<^sub>2 \<subseteq> X\<close>
    by (rule infer_patoms_Cons.IH) (use pa ps sigs_in_sappe[OF s1 B] in simp_all)
  then have s2: \<open>shyg s\<^sub>2 X\<close> by simp
  show ?case
    using shyg_scomp[OF s1 s2] tsigs_sapp[OF s2] tsigs_bs_map[OF s2] ih1 ih2 by (simp add: e)
next
  case (infer_pats_Cons uf B p ps n)
  from infer_pats_Cons.prems have B: \<open>sigs_in B X\<close> by blast
  from infer_pats_Cons.prems obtain s\<^sub>1 \<tau>\<^sub>1 \<Gamma>\<^sub>1 n\<^sub>1 s\<^sub>2 \<tau>s\<^sub>2 \<Gamma>\<^sub>2 p\<^sub>x ps\<^sub>x where
    pa: \<open>infer_pat uf B p n = Some (s\<^sub>1, p\<^sub>x, \<tau>\<^sub>1, \<Gamma>\<^sub>1, n\<^sub>1)\<close> and
    ps: \<open>infer_pats uf (sappe s\<^sub>1 B) ps n\<^sub>1 = Some (s\<^sub>2, ps\<^sub>x, \<tau>s\<^sub>2, \<Gamma>\<^sub>2, n')\<close> and
    e: \<open>s = s\<^sub>2 \<odot> s\<^sub>1\<close> \<open>\<tau>s = sapp s\<^sub>2 \<tau>\<^sub>1 # \<tau>s\<^sub>2\<close> \<open>\<Gamma> = map (apsnd (sapp s\<^sub>2)) \<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2\<close>
    by (auto split: prod.split_asm Option.bind_split_asm)
  have ih1: \<open>shyg s\<^sub>1 X \<and> tsigs \<tau>\<^sub>1 \<subseteq> X \<and> tsigs_bs \<Gamma>\<^sub>1 \<subseteq> X\<close>
    by (rule infer_pats_Cons.IH) (use pa B in simp_all)
  then have s1: \<open>shyg s\<^sub>1 X\<close> by simp
  have ih2: \<open>shyg s\<^sub>2 X \<and> (\<forall>\<tau> \<in> set \<tau>s\<^sub>2. tsigs \<tau> \<subseteq> X) \<and> tsigs_bs \<Gamma>\<^sub>2 \<subseteq> X\<close>
    by (rule infer_pats_Cons.IH) (use pa ps sigs_in_sappe[OF s1 B] in simp_all)
  then have s2: \<open>shyg s\<^sub>2 X\<close> by simp
  show ?case
    using shyg_scomp[OF s1 s2] tsigs_sapp[OF s2] tsigs_bs_map[OF s2] ih1 ih2 by (simp add: e)
next
  case (infer_patom_PRec_False uf B fs n)
  from infer_patom_PRec_False.prems obtain ps\<^sub>x \<tau>s where
    d: \<open>distinct (map (n_txt \<circ> fst) fs)\<close> and
    ps: \<open>infer_pats uf B (map snd fs) n = Some (s, ps\<^sub>x, \<tau>s, \<Gamma>, n')\<close> and
    e: \<open>\<tau> = rec_of (zip (map (n_txt \<circ> fst) fs) \<tau>s) TRNil\<close> and B: \<open>sigs_in B X\<close>
    by (auto split: prod.split_asm Option.bind_split_asm if_split_asm)
  have ih: \<open>shyg s X \<and> (\<forall>\<tau> \<in> set \<tau>s. tsigs \<tau> \<subseteq> X) \<and> tsigs_bs \<Gamma> \<subseteq> X\<close>
    by (rule infer_patom_PRec_False.IH[OF d ps B])
  show ?case using ih by (auto simp: e dest!: tsigs_rec_of_zipD)
next
  case (infer_pat_PatApp_Cons_Nil uf B a n)
  from infer_pat_PatApp_Cons_Nil.prems obtain a\<^sub>x where
    pa: \<open>infer_patom uf B a n = Some (s, a\<^sub>x, \<tau>, \<Gamma>, n')\<close> and B: \<open>sigs_in B X\<close>
    by (auto split: prod.split_asm Option.bind_split_asm)
  show ?case by (rule infer_pat_PatApp_Cons_Nil.IH[OF pa B])
next
  case (infer_patom_PParen_Cons_Nil uf B p n)
  from infer_patom_PParen_Cons_Nil.prems obtain p\<^sub>x where
    pa: \<open>infer_pat uf B p n = Some (s, p\<^sub>x, \<tau>, \<Gamma>, n')\<close> and B: \<open>sigs_in B X\<close>
    by (auto split: prod.split_asm Option.bind_split_asm)
  show ?case by (rule infer_patom_PParen_Cons_Nil.IH[OF pa B])
qed (auto split: Option.bind_split_asm if_split_asm)
subsection \<open>Operations, paths, application, operator trees\<close>

text \<open>The steps of the expression algorithm below the expression level: instantiating a
  scheme, an operation reference (\<^const>\<open>infer_opn\<close>), a path (\<open>apath_sigs\<close>), applying
  a function type to one argument (\<^const>\<open>app_arg\<close>) and an operator tree
  (\<^const>\<open>infer_tree\<close>).\<close>

lemma tsigs_inst_le: \<open>inst_scheme n \<sigma> = (\<tau>, n') \<Longrightarrow> tsigs_sch \<sigma> \<subseteq> X \<Longrightarrow> tsigs \<tau> \<subseteq> X\<close>
  using tsigs_inst_scheme by blast

lemma tsigs_map_TV [simp]: \<open>\<forall>t \<in> set (map TV xs). tsigs t \<subseteq> X\<close>
  by simp

lemma infer_opn_sigs:
  assumes B: \<open>sigs_in B X\<close> and P: \<open>tsigs_pend pd \<subseteq> X\<close>
    and E: \<open>infer_opn uf B pd p n = Some (s, a', \<tau>, pd', n')\<close>
  shows \<open>shyg s X \<and> tsigs \<tau> \<subseteq> X \<and> tsigs_pend pd' \<subseteq> X\<close>
proof -
  from E obtain x op \<sigma> lop ps \<tau>\<^sub>1 \<tau>\<^sub>2 l \<tau>\<^sub>x n\<^sub>1 n\<^sub>3 where
    lx: \<open>tlookup B [x] = Some (TEval \<sigma>)\<close> and
    lo: \<open>tlookup B [op] = Some (TEop lop ps \<tau>\<^sub>1 \<tau>\<^sub>2)\<close> and
    ins: \<open>inst_scheme n \<sigma> = (\<tau>\<^sub>x, n\<^sub>1)\<close> and
    un: \<open>uni uf \<tau>\<^sub>x (TEv (eff_ty l (map TV [n\<^sub>1 ..< n\<^sub>1 + length ps])) (TV (n\<^sub>1 + length ps))
      (tuple (map TV [n\<^sub>1 ..< n\<^sub>1 + length ps])))
             (Suc (n\<^sub>1 + length ps)) = Some (s, n\<^sub>3)\<close> and
    \<tau>: \<open>\<tau> = TFn (sapp s (op_inst ps (map TV [n\<^sub>1 ..< n\<^sub>1 + length ps]) \<tau>\<^sub>1))
      (canon_row (RCons (nlbl lop) (RV n\<^sub>3)))
                (sapp s (op_inst ps (map TV [n\<^sub>1 ..< n\<^sub>1 + length ps]) \<tau>\<^sub>2))\<close> and
    pd': \<open>pd' = sub_pend s pd\<close>
    by (auto simp: infer_opn_def Let_def bind_eq_Some_conv split: list.splits option.splits
      tentry.splits prod.splits)
  have \<tau>x: \<open>tsigs \<tau>\<^sub>x \<subseteq> X\<close> by (rule tsigs_inst_le[OF ins]) (use sigs_in_tlookup[OF B lx] in simp)
  have o: \<open>tsigs \<tau>\<^sub>1 \<subseteq> X\<close> \<open>tsigs \<tau>\<^sub>2 \<subseteq> X\<close> using sigs_in_tlookup[OF B lo] by simp_all
  have s: \<open>shyg s X\<close> by (rule uni_shyg[OF un \<tau>x]) simp
  show ?thesis
    using s tsigs_sapp[OF s tsigs_op_inst[OF tsigs_map_TV o(1)]]
      tsigs_sapp[OF s tsigs_op_inst[OF tsigs_map_TV o(2)]] tsigs_sub_pend[OF s P]
    by (simp add: \<tau> pd')
qed

text \<open>A path is looked up in the basis; one the basis does not bind is an operation
  reference:\<close>

lemma apath_sigs:
  assumes E: \<open>infer_atom uf B A pd (APath p) n = Some (s, a', \<tau>, pd', n')\<close>
    and B: \<open>sigs_in B X\<close> and P: \<open>tsigs_pend pd \<subseteq> X\<close>
  shows \<open>shyg s X \<and> tsigs \<tau> \<subseteq> X \<and> tsigs_pend pd' \<subseteq> X\<close>
proof (cases \<open>tlookup B (path_nms p)\<close>)
  case None
  then show ?thesis using infer_opn_sigs[OF B P] E by simp
next
  case (Some e)
  have t: \<open>tsigs_ent e \<subseteq> X\<close> by (rule sigs_in_tlookup[OF B Some])
  show ?thesis
  proof (cases e)
    case (TEval \<sigma>)
    from E Some TEval obtain \<tau>\<^sub>0 n\<^sub>1 evs pdo where
      i: \<open>inst_scheme n \<sigma> = (\<tau>\<^sub>0, n\<^sub>1)\<close> and o: \<open>off_evs n\<^sub>1 \<tau>\<^sub>0 = (evs, pdo, \<tau>, n')\<close> and
      se: \<open>s = sid\<close> \<open>pd' = pdo @ pd\<close>
      by (auto split: prod.split_asm)
    have t0: \<open>tsigs \<tau>\<^sub>0 \<subseteq> X\<close> using tsigs_inst_le[OF i] t TEval by simp
    have po: \<open>tsigs_pend pdo \<subseteq> X\<close>
    proof -
      have \<open>tsigs_preq q \<subseteq> X\<close> if m: \<open>(v, q) \<in> set pdo\<close> for v q
      proof -
        obtain x r where \<open>q = POff x r\<close> \<open>tsigs r \<subseteq> tsigs \<tau>\<^sub>0\<close>
          using conjunct2[OF off_evs_tsigs[OF o]] m by fastforce
        then show ?thesis using t0 by auto
      qed
      then show ?thesis unfolding tsigs_pend_def by blast
    qed
    show ?thesis using conjunct1[OF off_evs_tsigs[OF o]] t0 P se po by (auto simp: tsigs_pend_def)
  next
    case (TEcon \<sigma> m)
    from E Some TEcon have i: \<open>inst_scheme n \<sigma> = (\<tau>, n')\<close> \<open>s = sid\<close> \<open>pd' = pd\<close>
      by (auto split: prod.split_asm)
    show ?thesis using tsigs_inst_le[OF i(1)] t TEcon P i by simp
  next
    case (TEffi f \<sigma>)
    from E Some TEffi have i: \<open>inst_scheme n \<sigma> = (\<tau>, n')\<close> \<open>s = sid\<close> \<open>pd' = pd\<close>
      by (auto split: prod.split_asm)
    show ?thesis using tsigs_inst_le[OF i(1)] t TEffi P i by simp
  next
    case (TEop l ps \<tau>\<^sub>1 \<tau>\<^sub>2)
    from E Some TEop have i: \<open>\<tau> = TFn \<tau>\<^sub>1 (canon_row (RCons l (RV n))) \<tau>\<^sub>2\<close> \<open>s = sid\<close> \<open>pd' = pd\<close>
      by (auto split: if_split_asm)
    show ?thesis using t TEop P i by simp
  qed (use E Some in simp_all)
qed

lemma hpath_sigs:
  assumes E: \<open>infer_head uf B A pd (APath p) n = Some (s, a', \<tau>, pd', n')\<close>
    and B: \<open>sigs_in B X\<close> and P: \<open>tsigs_pend pd \<subseteq> X\<close>
  shows \<open>shyg s X \<and> tsigs \<tau> \<subseteq> X \<and> tsigs_pend pd' \<subseteq> X\<close>
proof (cases \<open>tlookup B (path_nms p)\<close>)
  case None
  then show ?thesis using infer_opn_sigs[OF B P] E by simp
next
  case (Some e)
  have t: \<open>tsigs_ent e \<subseteq> X\<close> by (rule sigs_in_tlookup[OF B Some])
  show ?thesis
  proof (cases e)
    case (TEval \<sigma>)
    from E Some TEval have i: \<open>inst_scheme n \<sigma> = (\<tau>, n')\<close> \<open>s = sid\<close> \<open>pd' = pd\<close>
      by (auto split: prod.split_asm)
    show ?thesis using tsigs_inst_le[OF i(1)] t TEval P i by simp
  next
    case (TEcon \<sigma> m)
    from E Some TEcon have i: \<open>inst_scheme n \<sigma> = (\<tau>, n')\<close> \<open>s = sid\<close> \<open>pd' = pd\<close>
      by (auto split: prod.split_asm)
    show ?thesis using tsigs_inst_le[OF i(1)] t TEcon P i by simp
  next
    case (TEffi f \<sigma>)
    from E Some TEffi have i: \<open>inst_scheme n \<sigma> = (\<tau>, n')\<close> \<open>s = sid\<close> \<open>pd' = pd\<close>
      by (auto split: prod.split_asm)
    show ?thesis using tsigs_inst_le[OF i(1)] t TEffi P i by simp
  next
    case (TEop l ps \<tau>\<^sub>1 \<tau>\<^sub>2)
    from E Some TEop have i: \<open>\<tau> = TFn \<tau>\<^sub>1 (canon_row (RCons l (RV n))) \<tau>\<^sub>2\<close> \<open>s = sid\<close> \<open>pd' = pd\<close>
      by (auto split: if_split_asm)
    show ?thesis using t TEop P i by simp
  qed (use E Some in simp_all)
qed

text \<open>Application first renames the bound names of an action type to those of the action
  argument (\<open>tsigs_act_rename\<close>); the renaming introduces no signature names.\<close>

lemma tsigs_ksubst_TK: \<open>tsigs (ksubst (tsl (zip K (map TK K'))) t) \<subseteq> tsigs t\<close>
  by (rule tsigs_ksubst) (auto simp: tsl_def split: option.split dest!: map_of_SomeD set_zip_rightD)

lemma tsigs_act_rename:
  assumes \<open>tsigs \<tau>\<^sub>h \<subseteq> X\<close>
  shows \<open>tsigs (case (\<tau>\<^sub>h, \<tau>\<^sub>a) of
      (TFn (TAct lt K \<epsilon>\<^sub>0 \<tau>\<^sub>0) \<epsilon>\<^sub>l \<tau>\<^sub>2, TAct lt' K' \<epsilon>\<^sub>0' \<tau>\<^sub>0') \<Rightarrow>
        (if length K = length K' \<and> set K \<inter> ktv_env B = {} \<and> set K \<inter> ktv \<tau>\<^sub>0 = {}
         then TFn (TAct lt K' \<epsilon>\<^sub>0 (ksubst (tsl (zip K (map TK K'))) \<tau>\<^sub>0)) \<epsilon>\<^sub>l \<tau>\<^sub>2
         else \<tau>\<^sub>h)
    | _ \<Rightarrow> \<tau>\<^sub>h) \<subseteq> X\<close>
proof (cases \<tau>\<^sub>h)
  case (TFn a e b)
  show ?thesis
  proof (cases a)
    case (TAct lt K \<epsilon>\<^sub>0 \<tau>\<^sub>0)
    then show ?thesis using assms TFn tsigs_ksubst_TK[of K _ \<tau>\<^sub>0] by (cases \<tau>\<^sub>a) auto
  qed (use assms TFn in simp_all)
qed (use assms in simp_all)

text \<open>The renaming of an annotation's action binders introduces no signature names.\<close>

lemma tsigs_act_rename_ann:
  assumes \<open>tsigs \<tau>\<^sub>a \<subseteq> X\<close>
  shows \<open>tsigs (act_rename B \<tau> \<tau>\<^sub>a) \<subseteq> X\<close>
proof (cases \<tau>)
  case (TAct lt K \<epsilon>\<^sub>0 \<tau>\<^sub>0)
  show ?thesis
  proof (cases \<tau>\<^sub>a)
    case (TAct lt' K' \<epsilon>\<^sub>0' \<tau>\<^sub>0')
    then show ?thesis using assms \<open>\<tau> = TAct lt K \<epsilon>\<^sub>0 \<tau>\<^sub>0\<close> tsigs_ksubst_TK[of K' K \<tau>\<^sub>0']
      by (auto simp: act_rename_def)
  qed (use assms \<open>\<tau> = TAct lt K \<epsilon>\<^sub>0 \<tau>\<^sub>0\<close> in \<open>simp_all add: act_rename_def\<close>)
qed (use assms in \<open>simp_all add: act_rename_def\<close>)

lemma tsigs_ann_ty:
  assumes \<open>tsigs \<tau>\<^sub>a \<subseteq> X\<close>
  shows \<open>tsigs (ann_ty B \<tau> \<tau>\<^sub>a) \<subseteq> X\<close>
proof (cases \<tau>)
  case (TFn t\<^sub>1 \<epsilon> t\<^sub>2)
  show ?thesis
  proof (cases \<tau>\<^sub>a)
    case (TFn t\<^sub>1' \<epsilon>' t\<^sub>2')
    then show ?thesis using assms \<open>\<tau> = TFn t\<^sub>1 \<epsilon> t\<^sub>2\<close> tsigs_act_rename_ann[of t\<^sub>1' X B t\<^sub>1]
      by (auto simp: ann_ty_def)
  qed (use assms \<open>\<tau> = TFn t\<^sub>1 \<epsilon> t\<^sub>2\<close> in \<open>simp_all add: ann_ty_def act_rename_def\<close>)
qed (use assms tsigs_act_rename_ann[OF assms, of B \<tau>] in \<open>simp_all add: ann_ty_def act_rename_def\<close>)

text \<open>Applying a function type to one argument:\<close>

lemma app_arg_sigs:
  assumes E: \<open>app_arg uf B A pd \<tau>\<^sub>h \<tau>\<^sub>a n = Some (s, \<tau>, pd', n')\<close>
    and P: \<open>tsigs_pend pd \<subseteq> X\<close> and h: \<open>tsigs \<tau>\<^sub>h \<subseteq> X\<close> and ta: \<open>tsigs \<tau>\<^sub>a \<subseteq> X\<close>
  shows \<open>shyg s X \<and> tsigs \<tau> \<subseteq> X \<and> tsigs_pend pd' \<subseteq> X\<close>
proof -
  define \<tau>\<^sub>h' where \<open>\<tau>\<^sub>h' = (case (\<tau>\<^sub>h, \<tau>\<^sub>a) of
      (TFn (TAct lt K \<epsilon>\<^sub>0 \<tau>\<^sub>0) \<epsilon>\<^sub>l \<tau>\<^sub>2, TAct lt' K' \<epsilon>\<^sub>0' \<tau>\<^sub>0') \<Rightarrow>
        (if length K = length K' \<and> set K \<inter> ktv_env B = {} \<and> set K \<inter> ktv \<tau>\<^sub>0 = {}
         then TFn (TAct lt K' \<epsilon>\<^sub>0 (ksubst (tsl (zip K (map TK K'))) \<tau>\<^sub>0)) \<epsilon>\<^sub>l \<tau>\<^sub>2
         else \<tau>\<^sub>h)
    | _ \<Rightarrow> \<tau>\<^sub>h)\<close>
  have h': \<open>tsigs \<tau>\<^sub>h' \<subseteq> X\<close> unfolding \<tau>\<^sub>h'_def by (rule tsigs_act_rename[OF h])
  from E obtain s\<^sub>0 n\<^sub>0 where un: \<open>uni uf \<tau>\<^sub>h' (TFn \<tau>\<^sub>a A (TV n)) (Suc n) = Some (s\<^sub>0, n\<^sub>0)\<close>
    and e: \<open>(s, \<tau>, pd', n') = (s\<^sub>0, sapp s\<^sub>0 (TV n), sub_pend s\<^sub>0 pd, n\<^sub>0)\<close>
    unfolding app_arg_def Let_def \<tau>\<^sub>h'_def[symmetric] by (auto simp: bind_eq_Some_conv)
  have s: \<open>shyg s\<^sub>0 X\<close> by (rule uni_shyg[OF un h']) (use ta in simp)
  show ?thesis using e s tsigs_sapp[OF s] tsigs_sub_pend[OF s P] by simp
qed

text \<open>An operator tree over operand types over \<open>X\<close>:\<close>

lemma infer_tree_sigs:
  \<open>infer_tree uf B A \<tau>s tr n = Some (s, \<tau>, n') \<Longrightarrow> sigs_in B X \<Longrightarrow> \<forall>t \<in> set \<tau>s. tsigs t \<subseteq> X \<Longrightarrow>
   shyg s X \<and> tsigs \<tau> \<subseteq> X\<close>
proof (induction uf B A \<tau>s tr n arbitrary: s \<tau> n' rule: infer_tree_induct)
  case (Node_OVar uf B A \<tau>s v l r n)
  from Node_OVar.prems have B: \<open>sigs_in B X\<close> and Ts: \<open>\<forall>t \<in> set \<tau>s. tsigs t \<subseteq> X\<close> by blast+
  from Node_OVar.prems obtain s\<^sub>1 \<tau>\<^sub>l n\<^sub>1 s\<^sub>2 \<tau>\<^sub>r n\<^sub>2 \<sigma> \<tau>\<^sub>f n\<^sub>3 s\<^sub>3 where
    l: \<open>infer_tree uf B A \<tau>s l n = Some (s\<^sub>1, \<tau>\<^sub>l, n\<^sub>1)\<close> and
    r: \<open>infer_tree uf (sappe s\<^sub>1 B) (sappr s\<^sub>1 A) (map (sapp s\<^sub>1) \<tau>s) r n\<^sub>1 = Some (s\<^sub>2, \<tau>\<^sub>r, n\<^sub>2)\<close> and
    lk: \<open>tlookup (sappe (s\<^sub>2 \<odot> s\<^sub>1) B) [v] = Some (TEval \<sigma>)\<close> and
    ins: \<open>inst_scheme n\<^sub>2 \<sigma> = (\<tau>\<^sub>f, n\<^sub>3)\<close> and
    un: \<open>uni uf \<tau>\<^sub>f (TFn (tuple [sapp s\<^sub>2 \<tau>\<^sub>l, \<tau>\<^sub>r]) (sappr (s\<^sub>2 \<odot> s\<^sub>1) A) (TV n\<^sub>3)) (Suc n\<^sub>3)
      = Some (s\<^sub>3, n')\<close> and
    e: \<open>s = s\<^sub>3 \<odot> s\<^sub>2 \<odot> s\<^sub>1\<close> \<open>\<tau> = sapp s\<^sub>3 (TV n\<^sub>3)\<close>
    by (auto split: Option.bind_split_asm prod.split_asm option.split_asm tentry.split_asm)
  have i1: \<open>shyg s\<^sub>1 X \<and> tsigs \<tau>\<^sub>l \<subseteq> X\<close>
    using l B Ts by (rule Node_OVar.IH)
  have i2: \<open>shyg s\<^sub>2 X \<and> tsigs \<tau>\<^sub>r \<subseteq> X\<close>
    using l refl refl r sigs_in_sappe[OF _ B] tsigs_map_sapp[OF _ Ts]
      by (rule Node_OVar.IH) (use i1 in simp_all)
  have s21: \<open>shyg (s\<^sub>2 \<odot> s\<^sub>1) X\<close> using shyg_scomp i1 i2 by blast
  have f: \<open>tsigs \<tau>\<^sub>f \<subseteq> X\<close>
    by (rule tsigs_inst_le[OF ins]) (use sigs_in_tlookup[OF sigs_in_sappe[OF s21 B] lk] in simp)
  have s3: \<open>shyg s\<^sub>3 X\<close> by (rule uni_shyg[OF un f]) (use i1 i2 tsigs_sapp in simp)
  show ?case
    using shyg_scomp[OF conjunct1[OF i1] shyg_scomp[OF conjunct1[OF i2] s3]] tsigs_sapp[OF s3]
    by (simp add: e)
next
  case (Node_OCon uf B A \<tau>s c l r n)
  from Node_OCon.prems have B: \<open>sigs_in B X\<close> and Ts: \<open>\<forall>t \<in> set \<tau>s. tsigs t \<subseteq> X\<close> by blast+
  from Node_OCon.prems obtain s\<^sub>1 \<tau>\<^sub>l n\<^sub>1 s\<^sub>2 \<tau>\<^sub>r n\<^sub>2 \<sigma> \<tau>\<^sub>c n\<^sub>3 s\<^sub>3 where
    l: \<open>infer_tree uf B A \<tau>s l n = Some (s\<^sub>1, \<tau>\<^sub>l, n\<^sub>1)\<close> and
    r: \<open>infer_tree uf (sappe s\<^sub>1 B) (sappr s\<^sub>1 A) (map (sapp s\<^sub>1) \<tau>s) r n\<^sub>1 = Some (s\<^sub>2, \<tau>\<^sub>r, n\<^sub>2)\<close> and
    lk: \<open>tlookup (sappe (s\<^sub>2 \<odot> s\<^sub>1) B) [c] = Some (TEcon \<sigma> 2)\<close> and
    ins: \<open>inst_scheme n\<^sub>2 \<sigma> = (\<tau>\<^sub>c, n\<^sub>3)\<close> and
    un: \<open>uni uf \<tau>\<^sub>c (TFn (sapp s\<^sub>2 \<tau>\<^sub>l) (RV n\<^sub>3) (TFn \<tau>\<^sub>r (RV (Suc n\<^sub>3)) (TV (Suc (Suc n\<^sub>3)))))
             (Suc (Suc (Suc n\<^sub>3))) = Some (s\<^sub>3, n')\<close> and
    e: \<open>s = s\<^sub>3 \<odot> s\<^sub>2 \<odot> s\<^sub>1\<close> \<open>\<tau> = sapp s\<^sub>3 (TV (Suc (Suc n\<^sub>3)))\<close>
    by (auto split: Option.bind_split_asm prod.split_asm option.split_asm tentry.split_asm
      if_split_asm)
  have i1: \<open>shyg s\<^sub>1 X \<and> tsigs \<tau>\<^sub>l \<subseteq> X\<close>
    using l B Ts by (rule Node_OCon.IH)
  have i2: \<open>shyg s\<^sub>2 X \<and> tsigs \<tau>\<^sub>r \<subseteq> X\<close>
    using l refl refl r sigs_in_sappe[OF _ B] tsigs_map_sapp[OF _ Ts]
      by (rule Node_OCon.IH) (use i1 in simp_all)
  have s21: \<open>shyg (s\<^sub>2 \<odot> s\<^sub>1) X\<close> using shyg_scomp i1 i2 by blast
  have f: \<open>tsigs \<tau>\<^sub>c \<subseteq> X\<close>
    by (rule tsigs_inst_le[OF ins]) (use sigs_in_tlookup[OF sigs_in_sappe[OF s21 B] lk] in simp)
  have s3: \<open>shyg s\<^sub>3 X\<close> by (rule uni_shyg[OF un f]) (use i1 i2 tsigs_sapp in simp)
  show ?case
    using shyg_scomp[OF conjunct1[OF i1] shyg_scomp[OF conjunct1[OF i2] s3]] tsigs_sapp[OF s3]
    by (simp add: e)
qed (auto split: if_split_asm)


subsection \<open>The expression algorithm\<close>

text \<open>The confinement of the expression algorithm, \<open>infer_sigs\<close>, by one induction over all
  its judgments. Before it come the helpers its cases share.\<close>

lemma infer_args_step_sigs:
  assumes E: \<open>infer_args uf B A pd d \<tau>\<^sub>0 as n = Some (s, as', \<tau>, pd', n')\<close>
    and B: \<open>sigs_in B X\<close> and P: \<open>tsigs_pend pd \<subseteq> X\<close> and F: \<open>tsigs \<tau>\<^sub>0 \<subseteq> X\<close>
    and nd: \<open>(\<forall>i sg K e t. \<tau>\<^sub>0 \<noteq> TDep i sg K e t) \<and> (\<forall>x r t. \<tau>\<^sub>0 \<noteq> TOff x r t)\<close>
    and IH\<^sub>1: \<open>\<And>a rest s\<^sub>1 a'' \<tau>\<^sub>a pd\<^sub>1 n\<^sub>1. as = a # rest \<Longrightarrow>
        infer_atom uf B A pd a n = Some (s\<^sub>1, a'', \<tau>\<^sub>a, pd\<^sub>1, n\<^sub>1) \<Longrightarrow> sigs_in B X \<Longrightarrow> tsigs_pend pd \<subseteq> X \<Longrightarrow>
        shyg s\<^sub>1 X \<and> tsigs \<tau>\<^sub>a \<subseteq> X \<and> tsigs_pend pd\<^sub>1 \<subseteq> X\<close>
    and IH\<^sub>2: \<open>\<And>a rest s\<^sub>1 a'' \<tau>\<^sub>a pd\<^sub>1 n\<^sub>1 s\<^sub>2 \<tau>\<^sub>r pd\<^sub>2 n\<^sub>2 s\<^sub>3 rest'' \<tau>' pd\<^sub>3 n\<^sub>3. as = a # rest \<Longrightarrow>
        infer_atom uf B A pd a n = Some (s\<^sub>1, a'', \<tau>\<^sub>a, pd\<^sub>1, n\<^sub>1) \<Longrightarrow>
        app_arg uf (sappe s\<^sub>1 B) (sappr s\<^sub>1 A) pd\<^sub>1 (sapp s\<^sub>1 \<tau>\<^sub>0) \<tau>\<^sub>a n\<^sub>1 = Some (s\<^sub>2, \<tau>\<^sub>r, pd\<^sub>2, n\<^sub>2) \<Longrightarrow>
        infer_args uf (sappe (s\<^sub>2 \<odot> s\<^sub>1) B) (sappr (s\<^sub>2 \<odot> s\<^sub>1) A) pd\<^sub>2 d \<tau>\<^sub>r rest n\<^sub>2
          = Some (s\<^sub>3, rest'', \<tau>', pd\<^sub>3, n\<^sub>3) \<Longrightarrow>
        sigs_in (sappe (s\<^sub>2 \<odot> s\<^sub>1) B) X \<Longrightarrow> tsigs_pend pd\<^sub>2 \<subseteq> X \<Longrightarrow> tsigs \<tau>\<^sub>r \<subseteq> X \<Longrightarrow>
        shyg s\<^sub>3 X \<and> tsigs \<tau>' \<subseteq> X \<and> tsigs_pend pd\<^sub>3 \<subseteq> X\<close>
  shows \<open>shyg s X \<and> tsigs \<tau> \<subseteq> X \<and> tsigs_pend pd' \<subseteq> X\<close>
proof (cases as)
  case Nil
  then show ?thesis using E F nd P by (cases \<tau>\<^sub>0) auto
next
  case (Cons a rest)
  obtain s\<^sub>1 a'' \<tau>\<^sub>a pd\<^sub>1 n\<^sub>1 s\<^sub>2 \<tau>\<^sub>r pd\<^sub>2 n\<^sub>2 s\<^sub>3 rest'' where
    d1: \<open>infer_atom uf B A pd a n = Some (s\<^sub>1, a'', \<tau>\<^sub>a, pd\<^sub>1, n\<^sub>1)\<close> and
    ap: \<open>app_arg uf (sappe s\<^sub>1 B) (sappr s\<^sub>1 A) pd\<^sub>1 (sapp s\<^sub>1 \<tau>\<^sub>0) \<tau>\<^sub>a n\<^sub>1 = Some (s\<^sub>2, \<tau>\<^sub>r, pd\<^sub>2, n\<^sub>2)\<close> and
    d2: \<open>infer_args uf (sappe (s\<^sub>2 \<odot> s\<^sub>1) B) (sappr (s\<^sub>2 \<odot> s\<^sub>1) A) pd\<^sub>2 d \<tau>\<^sub>r rest n\<^sub>2
           = Some (s\<^sub>3, rest'', \<tau>, pd', n')\<close> and
    se: \<open>s = s\<^sub>3 \<odot> (s\<^sub>2 \<odot> s\<^sub>1)\<close>
    using E[unfolded Cons infer_args_Cons_plain[OF conjunct1[OF nd] conjunct2[OF nd]]]
    by (auto simp del: infer_args.simps split: Option.bind_split_asm)
  have w1: \<open>shyg s\<^sub>1 X \<and> tsigs \<tau>\<^sub>a \<subseteq> X \<and> tsigs_pend pd\<^sub>1 \<subseteq> X\<close> by (rule IH\<^sub>1[OF Cons d1 B P])
  have w2: \<open>shyg s\<^sub>2 X \<and> tsigs \<tau>\<^sub>r \<subseteq> X \<and> tsigs_pend pd\<^sub>2 \<subseteq> X\<close>
    by (rule app_arg_sigs[OF ap]) (use w1 tsigs_sapp[OF _ F] in simp_all)
  have s21: \<open>shyg (s\<^sub>2 \<odot> s\<^sub>1) X\<close> using shyg_scomp w1 w2 by blast
  have w3: \<open>shyg s\<^sub>3 X \<and> tsigs \<tau> \<subseteq> X \<and> tsigs_pend pd' \<subseteq> X\<close>
    by (rule IH\<^sub>2[OF Cons d1 ap d2 sigs_in_sappe[OF s21 B]]) (use w2 in simp_all)
  show ?thesis using se shyg_scomp[OF s21 conjunct1[OF w3]] w3 by simp
qed


text \<open>The bindings that patterns and \<open>let\<close> add to the basis stay over \<open>X\<close>:\<close>

lemma sigs_in_mono_env: \<open>shyg s X \<Longrightarrow> tsigs_bs \<Gamma> \<subseteq> X \<Longrightarrow> sigs_in (mono_env s \<Gamma>) X\<close>
proof (induction \<Gamma>)
  case (Cons xt \<Gamma>)
  obtain x t where xt: \<open>xt = (x, t)\<close> by (cases xt)
  have \<open>tsigs (sapp s t) \<subseteq> X\<close> using Cons.prems xt by (intro tsigs_sapp) auto
  then show ?case using Cons xt by (simp add: mono_env_def)
qed (simp add: mono_env_def)

lemma sigs_in_vals_sapp:
  \<open>shyg s X \<Longrightarrow> tsigs_bs \<Gamma> \<subseteq> X \<Longrightarrow>
   sigs_in (map (\<lambda>(x, \<tau>). (x, TEval (close_sch as rs (sapp s \<tau>)))) \<Gamma>) X\<close>
  by (induction \<Gamma>) (auto simp: tsigs_sapp)

text \<open>The names in the key of a signature that elaborates against a basis over \<open>X\<close> lie in
  \<open>X\<close>:\<close>

lemma sig_stat_key: \<open>sig_stat B n sg = Some r \<Longrightarrow> sigs_in B X \<Longrightarrow> sig_key sg \<subseteq> X\<close>
proof (cases sg)
  case (SPath p refs)
  assume s: \<open>sig_stat B n sg = Some r\<close> and B: \<open>sigs_in B X\<close>
  show ?thesis
  proof (cases refs)
    case Nil
    from s SPath obtain \<Sigma> where lk: \<open>tlookup B (path_nms p) = Some (TEsig \<Sigma>)\<close>
      by (auto split: option.split_asm tentry.split_asm)
    have p: \<open>path_nms p \<noteq> []\<close> using lk by (cases \<open>path_nms p\<close>) auto
    have \<open>has_sig (last (path_nms p)) B\<close> by (rule has_sig_tlookup[OF lk p]) (cases \<Sigma>, simp)
    then show ?thesis using B SPath Nil by (simp add: sigs_in_def)
  qed (simp add: SPath)
qed simp_all

text \<open>The generalised bindings that \<open>let\<close> adds for the names of its pattern, as in
  \<^const>\<open>infer\<close>:\<close>

definition gen_env_s :: \<open>ksub \<Rightarrow> tvar set \<Rightarrow> rvar set \<Rightarrow> reqs \<Rightarrow> (name \<times> kty) list \<Rightarrow> tenv\<close> where
  \<open>gen_env_s s\<^sub>2 as rs reqs \<Gamma> =
     map (\<lambda>(x, \<tau>). (x, TEval (close_sch as rs (offs reqs (sapp s\<^sub>2 \<tau>))))) \<Gamma>\<close>

text \<open>Generalising over offset requests keeps the remaining requests over \<open>X\<close>, and the
  abstracted rows come from requests over \<open>X\<close>:\<close>

lemma gen_off_sigs:
  assumes g: \<open>gen_off B A pd n \<tau> = (as, rs, reqs, pdr)\<close> and P: \<open>tsigs_pend pd \<subseteq> X\<close>
  shows \<open>tsigs_pend pdr \<subseteq> X\<close> and \<open>tsigs \<tau>' \<subseteq> X \<Longrightarrow> tsigs (offs reqs \<tau>') \<subseteq> X\<close>
proof -
  from gen_off_pend[OF g] have sub: \<open>set pdr \<subseteq> set pd\<close>
    and rq: \<open>\<forall>(v, x, r) \<in> set reqs. (v, POff x r) \<in> set pd\<close> by blast+
  show \<open>tsigs_pend pdr \<subseteq> X\<close> using sub P unfolding tsigs_pend_def by blast
  show \<open>tsigs \<tau>' \<subseteq> X \<Longrightarrow> tsigs (offs reqs \<tau>') \<subseteq> X\<close>
  proof -
    assume t: \<open>tsigs \<tau>' \<subseteq> X\<close>
    have \<open>tsigs r \<subseteq> X\<close> if \<open>(v, x, r) \<in> set reqs\<close> for v x r
    proof -
      have \<open>(v, POff x r) \<in> set pd\<close> using rq that by auto
      then show ?thesis using P unfolding tsigs_pend_def by fastforce
    qed
    then show ?thesis unfolding offs_tsigs using t by auto
  qed
qed

lemma sigs_in_gen_env_s:
  assumes \<open>shyg s X\<close> \<open>tsigs_bs \<Gamma> \<subseteq> X\<close> \<open>\<And>\<tau>. tsigs \<tau> \<subseteq> X \<Longrightarrow> tsigs (offs reqs \<tau>) \<subseteq> X\<close>
  shows \<open>sigs_in (gen_env_s s as rs reqs \<Gamma>) X\<close>
  using assms unfolding gen_env_s_def by (induction \<Gamma>) (auto simp: tsigs_sapp)

text \<open>Over a basis and pending requests over \<open>X\<close>, the expression algorithm returns a
  hygienic substitution, types over \<open>X\<close> and pending requests over \<open>X\<close>:\<close>

lemma tsigs_tuple_from [simp]: \<open>tsigs (tuple_from i \<tau>s) = \<Union>(tsigs ` set \<tau>s)\<close>
  by (induction \<tau>s arbitrary: i) auto

text \<open>The scrutinee of a \<open>match\<close> with open patterns: its unifier, the tuple type of
  the selected fields and the pending projections stay over \<open>X\<close>.\<close>

lemma open_scrut_sigs:
  assumes os: \<open>open_scrut uf \<tau>\<^sub>0 pd ls n = Some (so, evs, \<tau>\<^sub>t, pdo, n\<^sub>1)\<close>
    and t: \<open>tsigs \<tau>\<^sub>0 \<subseteq> X\<close> and P: \<open>tsigs_pend pd \<subseteq> X\<close>
  shows \<open>shyg so X \<and> tsigs \<tau>\<^sub>t \<subseteq> X \<and> tsigs_pend pdo \<subseteq> X\<close>
proof -
  let ?k = \<open>length ls\<close>
  let ?row = \<open>rec_of (zip ls (map TV [n ..< n + length ls])) (TV (n + length ls))\<close>
  obtain n\<^sub>2 where u: \<open>uni uf \<tau>\<^sub>0 ?row (Suc (n + ?k)) = Some (so, n\<^sub>2)\<close>
    and te: \<open>\<tau>\<^sub>t = tuple (map (sapp so) (map TV [n ..< n + ?k]) @ [sapp so \<tau>\<^sub>0])\<close>
    and pe: \<open>pdo = map (\<lambda>(v, l). (imp_name v, POff l (sapp so ?row))) (zip [n\<^sub>2 ..< n\<^sub>2 + ?k] ls) @
                   sub_pend so pd\<close>
    using os unfolding open_scrut_def by (auto simp: Let_def bind_eq_Some_conv)
  have r: \<open>tsigs ?row = {}\<close> by (auto simp: tsigs_rec_of dest!: set_zip_rightD)
  have s: \<open>shyg so X\<close> by (rule uni_shyg[OF u t]) (simp add: r)
  have tv: \<open>tsigs (sapp so (TV i)) \<subseteq> X\<close> for i by (rule tsigs_sapp[OF s]) simp
  have tt: \<open>tsigs \<tau>\<^sub>t \<subseteq> X\<close> unfolding te using tsigs_sapp[OF s t] tv by auto
  have rr: \<open>tsigs (sapp so ?row) \<subseteq> X\<close> by (rule tsigs_sapp[OF s]) (simp add: r)
  have pp: \<open>tsigs_pend pdo \<subseteq> X\<close>
    using tsigs_sub_pend[OF s P] rr unfolding pe tsigs_pend_def by auto
  show ?thesis using s tt pp by simp
qed

lemma infer_sigs:
  \<open>infer uf B A pd e n = Some (s, e', \<tau>, pd', n') \<Longrightarrow> sigs_in B X \<Longrightarrow> tsigs_pend pd \<subseteq> X \<Longrightarrow>
     shyg s X \<and> tsigs \<tau> \<subseteq> X \<and> tsigs_pend pd' \<subseteq> X\<close>
  \<open>infer_head uf B A pd a n = Some (s, a', \<tau>, pd', n') \<Longrightarrow> sigs_in B X \<Longrightarrow> tsigs_pend pd \<subseteq> X \<Longrightarrow>
     shyg s X \<and> tsigs \<tau> \<subseteq> X \<and> tsigs_pend pd' \<subseteq> X\<close>
  \<open>infer_atom uf B A pd a n = Some (s, a', \<tau>, pd', n') \<Longrightarrow> sigs_in B X \<Longrightarrow> tsigs_pend pd \<subseteq> X \<Longrightarrow>
     shyg s X \<and> tsigs \<tau> \<subseteq> X \<and> tsigs_pend pd' \<subseteq> X\<close>
  \<open>infer_args uf B A pd d \<tau>\<^sub>0 as n = Some (s, as', \<tau>, pd', n') \<Longrightarrow> sigs_in B X \<Longrightarrow> tsigs_pend pd \<subseteq> X \<Longrightarrow>
     tsigs \<tau>\<^sub>0 \<subseteq> X \<Longrightarrow> shyg s X \<and> tsigs \<tau> \<subseteq> X \<and> tsigs_pend pd' \<subseteq> X\<close>
  \<open>infer_exps uf B A pd es n = Some (s, es', \<tau>s, pd', n') \<Longrightarrow> sigs_in B X \<Longrightarrow> tsigs_pend pd \<subseteq> X \<Longrightarrow>
     shyg s X \<and> (\<forall>\<tau> \<in> set \<tau>s. tsigs \<tau> \<subseteq> X) \<and> tsigs_pend pd' \<subseteq> X\<close>
  \<open>infer_chain uf B A pd e n = Some (s, e', oprs, \<tau>s, pd', n') \<Longrightarrow> sigs_in B X \<Longrightarrow> tsigs_pend pd \<subseteq> X \<Longrightarrow>
     shyg s X \<and> (\<forall>\<tau> \<in> set \<tau>s. tsigs \<tau> \<subseteq> X) \<and> tsigs_pend pd' \<subseteq> X\<close>
  \<open>infer_arms uf B A pd \<tau>\<^sub>0 \<tau>\<^sub>r arms n = Some (s, arms', pd', n') \<Longrightarrow> sigs_in B X \<Longrightarrow> tsigs_pend pd \<subseteq> X \<Longrightarrow>
     tsigs \<tau>\<^sub>0 \<subseteq> X \<Longrightarrow> tsigs \<tau>\<^sub>r \<subseteq> X \<Longrightarrow> shyg s X \<and> tsigs_pend pd' \<subseteq> X\<close>
  \<open>infer_cls uf B A pd nm \<tau>\<^sub>0 targs cls n = Some (s, cls', \<tau>, pd', n') \<Longrightarrow> sigs_in B X
    \<Longrightarrow> tsigs_pend pd \<subseteq> X \<Longrightarrow>
     tsigs \<tau>\<^sub>0 \<subseteq> X \<Longrightarrow> tsigs targs \<subseteq> X \<Longrightarrow> shyg s X \<and> tsigs \<tau> \<subseteq> X \<and> tsigs_pend pd' \<subseteq> X\<close>
proof (induction uf B A pd e n and uf B A pd a n and uf B A pd a n
         and uf B A pd d \<tau>\<^sub>0 as n and uf B A pd es n and uf B A pd e n
         and uf B A pd \<tau>\<^sub>0 \<tau>\<^sub>r arms n and uf B A pd nm \<tau>\<^sub>0 targs cls n
       arbitrary: s e' \<tau> pd' n' and s a' \<tau> pd' n' and s a' \<tau> pd' n'
         and s as' \<tau> pd' n' and s es' \<tau>s pd' n' and s e' oprs \<tau>s pd' n'
         and s arms' pd' n' and s cls' \<tau> pd' n'
       rule: infer_induct)
  case (infer_ESpine_Cons uf B A pd a as n s e' \<tau> pd' n')
  from infer_ESpine_Cons.prems have B: \<open>sigs_in B X\<close> and P: \<open>tsigs_pend pd \<subseteq> X\<close> by blast+
  from infer_ESpine_Cons.prems obtain s\<^sub>1 a'' \<tau>\<^sub>0 pd\<^sub>1 n\<^sub>1 s\<^sub>2 as'' where
    d1: \<open>infer_head uf B A pd a n = Some (s\<^sub>1, a'', \<tau>\<^sub>0, pd\<^sub>1, n\<^sub>1)\<close> and
    d2: \<open>infer_args uf (sappe s\<^sub>1 B) (sappr s\<^sub>1 A) pd\<^sub>1 uf \<tau>\<^sub>0 as n\<^sub>1 = Some (s\<^sub>2, as'', \<tau>, pd', n')\<close> and
    se: \<open>s = s\<^sub>2 \<odot> s\<^sub>1\<close>
    by (auto split: Option.bind_split_asm prod.split_asm)
  have i1: \<open>shyg s\<^sub>1 X \<and> tsigs \<tau>\<^sub>0 \<subseteq> X \<and> tsigs_pend pd\<^sub>1 \<subseteq> X\<close>
    using d1 B P by (rule infer_ESpine_Cons.IH)
  have i2: \<open>shyg s\<^sub>2 X \<and> tsigs \<tau> \<subseteq> X \<and> tsigs_pend pd' \<subseteq> X\<close>
    using d1 refl refl refl refl d2 sigs_in_sappe[OF conjunct1[OF i1] B]
      by (rule infer_ESpine_Cons.IH) (use i1 in simp_all)
  show ?case using i1 i2 se by (simp add: shyg_scomp)
next
  case (infer_EOp uf B A pd as opr e n s e' \<tau> pd' n')
  from infer_EOp.prems have B: \<open>sigs_in B X\<close> and P: \<open>tsigs_pend pd \<subseteq> X\<close> by blast+
  from infer_EOp.prems obtain s\<^sub>1 e'x oprs \<tau>s pd\<^sub>1 n\<^sub>1 tree s\<^sub>2 n\<^sub>2 where
    dc: \<open>infer_chain uf B A pd (EOp as opr e) n = Some (s\<^sub>1, e'x, oprs, \<tau>s, pd\<^sub>1, n\<^sub>1)\<close> and
    ct: \<open>chain_tree B oprs = Some tree\<close> and
    dt: \<open>infer_tree uf (sappe s\<^sub>1 B) (sappr s\<^sub>1 A) \<tau>s tree n\<^sub>1 = Some (s\<^sub>2, \<tau>, n\<^sub>2)\<close> and
    se: \<open>s = s\<^sub>2 \<odot> s\<^sub>1\<close> \<open>pd' = sub_pend s\<^sub>2 pd\<^sub>1\<close>
    by (auto split: Option.bind_split_asm prod.split_asm)
  have i1: \<open>shyg s\<^sub>1 X \<and> (\<forall>\<tau> \<in> set \<tau>s. tsigs \<tau> \<subseteq> X) \<and> tsigs_pend pd\<^sub>1 \<subseteq> X\<close>
    by (rule infer_EOp.IH[OF dc B P])
  have i2: \<open>shyg s\<^sub>2 X \<and> tsigs \<tau> \<subseteq> X\<close>
    by (rule infer_tree_sigs[OF dt sigs_in_sappe[OF _ B]]) (use i1 in simp_all)
  show ?case using i1 i2 se tsigs_sub_pend[of s\<^sub>2 X pd\<^sub>1] by (simp add: shyg_scomp)
next
  case (infer_EAnn uf B A pd e ty n s e' \<tau> pd' n')
  from infer_EAnn.prems have B: \<open>sigs_in B X\<close> and P: \<open>tsigs_pend pd \<subseteq> X\<close> by blast+
  from infer_EAnn.prems obtain s\<^sub>1 e'' \<tau>\<^sub>1 pd\<^sub>1 n\<^sub>1 \<tau>\<^sub>a ve n\<^sub>2 s\<^sub>2 n\<^sub>3 where
    d1: \<open>infer uf B A pd e n = Some (s\<^sub>1, e'', \<tau>\<^sub>1, pd\<^sub>1, n\<^sub>1)\<close> and
    ts: \<open>ty_stat (sappe s\<^sub>1 B) True ([], []) n\<^sub>1 ty = Some (\<tau>\<^sub>a, ve, n\<^sub>2)\<close> and
    un: \<open>uni uf \<tau>\<^sub>1 (ann_ty (sappe s\<^sub>1 B) \<tau>\<^sub>1 \<tau>\<^sub>a) n\<^sub>2 = Some (s\<^sub>2, n\<^sub>3)\<close> and
    se: \<open>s = s\<^sub>2 \<odot> s\<^sub>1\<close> \<open>\<tau> = sapp s\<^sub>2 \<tau>\<^sub>1\<close> \<open>pd' = sub_pend s\<^sub>2 pd\<^sub>1\<close>
    by (auto split: Option.bind_split_asm prod.split_asm)
  have i1: \<open>shyg s\<^sub>1 X \<and> tsigs \<tau>\<^sub>1 \<subseteq> X \<and> tsigs_pend pd\<^sub>1 \<subseteq> X\<close> by (rule infer_EAnn.IH[OF d1 B P])
  have ta: \<open>tsigs \<tau>\<^sub>a \<subseteq> X\<close> using ty_stat_sigs(1)[OF ts sigs_in_sappe[OF _ B]] i1 by simp
  have s2: \<open>shyg s\<^sub>2 X\<close> by (rule uni_shyg[OF un _ tsigs_ann_ty[OF ta]]) (use i1 in simp)
  show ?case using shyg_scomp[OF _ s2] tsigs_sapp[OF s2] tsigs_sub_pend[OF s2] i1 se by simp
next
  case (infer_EFn uf B A pd ps b n s e' \<tau> pd' n')
  from infer_EFn.prems have B: \<open>sigs_in B X\<close> and P: \<open>tsigs_pend pd \<subseteq> X\<close> by blast+
  from infer_EFn.prems obtain ls where ol: \<open>open_labels [fn_pat ps] = Some ls\<close>
    by (auto split: option.split_asm)
  show ?case
  proof (cases ls)
    case Nil
    with ol have ol': \<open>open_labels [fn_pat ps] = Some []\<close> by simp
    from infer_EFn.prems obtain sp \<tau>s \<Gamma> n\<^sub>1 s\<^sub>2 b'' \<tau>\<^sub>b ps\<^sub>x where
      d1: \<open>infer_pats uf B ps n = Some (sp, ps\<^sub>x, \<tau>s, \<Gamma>, n\<^sub>1)\<close> and
      d2: \<open>infer uf (mono_env sid \<Gamma> @ sappe sp B) (RV n\<^sub>1) (sub_pend sp pd) b (Suc n\<^sub>1)
        = Some (s\<^sub>2, b'', \<tau>\<^sub>b, pd', n')\<close> and
      se: \<open>s = s\<^sub>2 \<odot> sp\<close> \<open>\<tau> = TFn (sapp s\<^sub>2 (fn_ty \<tau>s)) (sappr s\<^sub>2 (RV n\<^sub>1)) \<tau>\<^sub>b\<close>
      by (auto simp: ol' Let_def split: Option.bind_split_asm prod.split_asm if_split_asm)
    have p: \<open>shyg sp X \<and> (\<forall>\<tau> \<in> set \<tau>s. tsigs \<tau> \<subseteq> X) \<and> tsigs_bs \<Gamma> \<subseteq> X\<close>
      by (rule infer_pat_sigs(4)[OF d1 B])
    have B': \<open>sigs_in (mono_env sid \<Gamma> @ sappe sp B) X\<close>
      using sigs_in_mono_env[OF shyg_sid] sigs_in_sappe[OF _ B] p by simp
    have i: \<open>shyg s\<^sub>2 X \<and> tsigs \<tau>\<^sub>b \<subseteq> X \<and> tsigs_pend pd' \<subseteq> X\<close>
      using ol' d1 d2 B' tsigs_sub_pend[OF conjunct1[OF p] P]
      by - (rule infer_EFn.IH; (rule refl | assumption)+)
    have f: \<open>tsigs (fn_ty \<tau>s) \<subseteq> X\<close> using p by (auto simp: tsigs_fn_ty)
    show ?thesis
      using shyg_scomp[OF _ conjunct1[OF i]] tsigs_sapp[OF conjunct1[OF i] f] i p se by simp
  next
    case (Cons l ls')
    with ol have ol': \<open>open_labels [fn_pat ps] = Some (l # ls')\<close> by simp
    from infer_EFn.prems obtain so evs \<tau>\<^sub>t pdo n\<^sub>1 sp p'' \<tau>\<^sub>p \<Gamma> n\<^sub>2 s\<^sub>1 n\<^sub>3 s\<^sub>2 b'' \<tau>\<^sub>b where
      os: \<open>open_scrut uf (TV n) pd (l # ls') (Suc n) = Some (so, evs, \<tau>\<^sub>t, pdo, n\<^sub>1)\<close> and
      dp: \<open>infer_pat uf (sappe so B) (open_arm (l # ls') (fn_pat ps)) n\<^sub>1
        = Some (sp, p'', \<tau>\<^sub>p, \<Gamma>, n\<^sub>2)\<close> and
      u1: \<open>uni uf (sapp sp \<tau>\<^sub>t) \<tau>\<^sub>p n\<^sub>2 = Some (s\<^sub>1, n\<^sub>3)\<close> and
      d2: \<open>infer uf (mono_env s\<^sub>1 \<Gamma> @ sappe (s\<^sub>1 \<odot> sp \<odot> so) B) (RV n\<^sub>3) (sub_pend (s\<^sub>1 \<odot> sp) pdo) b
             (Suc n\<^sub>3) = Some (s\<^sub>2, b'', \<tau>\<^sub>b, pd', n')\<close> and
      se: \<open>s = s\<^sub>2 \<odot> (s\<^sub>1 \<odot> sp \<odot> so)\<close>
          \<open>\<tau> = TFn (sapp (s\<^sub>2 \<odot> (s\<^sub>1 \<odot> sp \<odot> so)) (TV n)) (sappr s\<^sub>2 (RV n\<^sub>3)) \<tau>\<^sub>b\<close>
      by (auto simp: ol' Let_def split: Option.bind_split_asm prod.split_asm if_split_asm
            simp del: sapp.simps sappe.simps sappr.simps sapps.simps)
    have o: \<open>shyg so X \<and> tsigs \<tau>\<^sub>t \<subseteq> X \<and> tsigs_pend pdo \<subseteq> X\<close>
      by (rule open_scrut_sigs[OF os _ P]) simp
    have p: \<open>shyg sp X \<and> tsigs \<tau>\<^sub>p \<subseteq> X \<and> tsigs_bs \<Gamma> \<subseteq> X\<close>
      by (rule infer_pat_sigs(1)[OF dp sigs_in_sappe[OF conjunct1[OF o] B]])
    have s1: \<open>shyg s\<^sub>1 X\<close> by (rule uni_shyg[OF u1]) (use o p tsigs_sapp in simp_all)
    have s: \<open>shyg (s\<^sub>1 \<odot> sp \<odot> so) X\<close> using o p s1 by (simp add: shyg_scomp)
    have B': \<open>sigs_in (mono_env s\<^sub>1 \<Gamma> @ sappe (s\<^sub>1 \<odot> sp \<odot> so) B) X\<close>
      using sigs_in_mono_env[OF s1] sigs_in_sappe[OF s B] p by simp
    have P': \<open>tsigs_pend (sub_pend (s\<^sub>1 \<odot> sp) pdo) \<subseteq> X\<close>
      using tsigs_sub_pend[of \<open>s\<^sub>1 \<odot> sp\<close> X pdo] o p s1 by (simp add: shyg_scomp)
    have i: \<open>shyg s\<^sub>2 X \<and> tsigs \<tau>\<^sub>b \<subseteq> X \<and> tsigs_pend pd' \<subseteq> X\<close>
      using ol' os dp u1 d2 B' P'
      by - (rule infer_EFn.IH; (rule refl | assumption)+)
    show ?thesis
      using shyg_scomp[OF s conjunct1[OF i]] tsigs_sapp[of \<open>s\<^sub>2 \<odot> (s\<^sub>1 \<odot> sp \<odot> so)\<close> X \<open>TV n\<close>] i se
      by simp
  qed
next
  case (infer_EFnMod uf B A pd b e n s e' \<tau> pd' n')
  from infer_EFnMod.prems have B: \<open>sigs_in B X\<close> and P: \<open>tsigs_pend pd \<subseteq> X\<close> by blast+
  from infer_EFnMod.prems obtain T E\<^sub>0 n\<^sub>1 K E\<^sub>K n\<^sub>2 s\<^sub>b e'' \<tau>\<^sub>b pd\<^sub>1 n\<^sub>3 pd'' where
    ss: \<open>sig_stat B n (mbind_sig b) = Some ((T, E\<^sub>0), n\<^sub>1)\<close> and
    de: \<open>dep_env B n (mbind_sig b) (length T) = Some (K, E\<^sub>K, n\<^sub>2)\<close> and
    ib: \<open>infer uf
               ((mbind_nm b, if is_imp b then TEinst (param_env E\<^sub>K) else TEstr (param_env E\<^sub>K)) # B)
               (RV (n\<^sub>2)) pd e (Suc (n\<^sub>2)) = Some (s\<^sub>b, e'', \<tau>\<^sub>b, pd\<^sub>1, n\<^sub>3)\<close> and
    ri: \<open>resolve_inner K pd\<^sub>1 = Some pd''\<close> and
    rs: \<open>s = sproj (Suc (n\<^sub>2)) s\<^sub>b\<close>
      \<open>\<tau> = TDep (is_imp b) (mbind_sig b) (length T) (sappr s\<^sub>b (RV n\<^sub>2)) (kclose K \<tau>\<^sub>b)\<close>
      \<open>pd' = pd''\<close>
    by (auto simp: Let_def bind_eq_Some_conv split: prod.split_asm if_split_asm)
  have EK: \<open>sigs_in (param_env E\<^sub>K) X\<close> by (rule sigs_in_param_env[OF dep_env_sigs[OF de B]])
  have B': \<open>sigs_in
      ((mbind_nm b, if is_imp b then TEinst (param_env E\<^sub>K) else TEstr (param_env E\<^sub>K)) # B) X\<close>
    using EK B by (auto simp: sigs_in_def)
  have i: \<open>shyg s\<^sub>b X \<and> tsigs \<tau>\<^sub>b \<subseteq> X \<and> tsigs_pend pd\<^sub>1 \<subseteq> X\<close>
    by (rule infer_EFnMod.IH[OF ss refl refl de refl refl ib B' P])
  have k: \<open>sig_key (mbind_sig b) \<subseteq> X\<close> by (rule sig_stat_key[OF ss B])
  show ?case using i k rs shyg_sproj tsigs_resolve_inner[OF ri] by simp
next
  case (infer_ELet uf B A pd p e b n s e\<^sub>x \<tau> pd' n')
  from infer_ELet.prems have B: \<open>sigs_in B X\<close> and P: \<open>tsigs_pend pd \<subseteq> X\<close> by blast+
  obtain s\<^sub>1 e'' \<tau>\<^sub>e pd\<^sub>1 n\<^sub>1 where d1: \<open>infer uf B A pd e n = Some (s\<^sub>1, e'', \<tau>\<^sub>e, pd\<^sub>1, n\<^sub>1)\<close>
  proof (cases \<open>infer uf B A pd e n\<close>)
    case None then show ?thesis using infer_ELet.prems by simp
  next
    case (Some r) then show ?thesis using that by (cases r) auto
  qed
  from infer_ELet.prems obtain ls where ol: \<open>open_labels [p] = Some ls\<close>
    by (auto simp: d1 split: option.split_asm)
  have i1: \<open>shyg s\<^sub>1 X \<and> tsigs \<tau>\<^sub>e \<subseteq> X \<and> tsigs_pend pd\<^sub>1 \<subseteq> X\<close>
    using d1 B P by (rule infer_ELet.IH)
  show ?case
  proof (cases ls)
    case Nil
    with ol have ol': \<open>open_labels [p] = Some []\<close> by simp
    obtain sp p\<^sub>x \<tau>\<^sub>p \<Gamma> n\<^sub>2 where dp: \<open>infer_pat uf (sappe s\<^sub>1 B) p n\<^sub>1 = Some (sp, p\<^sub>x, \<tau>\<^sub>p, \<Gamma>, n\<^sub>2)\<close>
    proof (cases \<open>infer_pat uf (sappe s\<^sub>1 B) p n\<^sub>1\<close>)
      case None then show ?thesis using infer_ELet.prems
        by (simp add: d1 ol' del: sapp.simps sappe.simps sappr.simps sapps.simps)
    next
      case (Some r) then show ?thesis using that by (cases r) auto
    qed
    obtain s\<^sub>2 n\<^sub>3 where u1: \<open>uni uf (sapp sp \<tau>\<^sub>e) \<tau>\<^sub>p n\<^sub>2 = Some (s\<^sub>2, n\<^sub>3)\<close>
    proof (cases \<open>uni uf (sapp sp \<tau>\<^sub>e) \<tau>\<^sub>p n\<^sub>2\<close>)
      case None then show ?thesis using infer_ELet.prems
        by (simp add: d1 ol' dp del: sapp.simps sappe.simps sappr.simps sapps.simps)
    next
      case (Some r) then show ?thesis using that by (cases r) auto
    qed
    obtain asx rsx reqs pdr where asrs: \<open>(asx, rsx, reqs, pdr) =
      (if val_exp B e'' then (if var_pat p \<and> length \<Gamma> = 1
          then gen_off (sappe (s\<^sub>2 \<odot> sp \<odot> s\<^sub>1) B) (sappr (s\<^sub>2 \<odot> sp \<odot> s\<^sub>1) A) (sub_pend (s\<^sub>2 \<odot> sp) pd\<^sub>1) n
                 (sapp s\<^sub>2 \<tau>\<^sub>p)
          else (case gen_p (sappe (s\<^sub>2 \<odot> sp \<odot> s\<^sub>1) B) (sappr (s\<^sub>2 \<odot> sp \<odot> s\<^sub>1) A)
                       (sub_pend (s\<^sub>2 \<odot> sp) pd\<^sub>1) n
                       (sapp s\<^sub>2 \<tau>\<^sub>p)
                of (as, rs) \<Rightarrow> (as, rs, [], sub_pend (s\<^sub>2 \<odot> sp) pd\<^sub>1)))
       else ({}, {}, [], sub_pend (s\<^sub>2 \<odot> sp) pd\<^sub>1))\<close>
      by (metis prod_cases4)
    have covb: \<open>covers (sappe (s\<^sub>2 \<odot> sp \<odot> s\<^sub>1) B) (sapp s\<^sub>2 \<tau>\<^sub>p) [p] \<and>
                btv_list (sapp s\<^sub>2 \<tau>\<^sub>p) = [] \<and> brv_list (sapp s\<^sub>2 \<tau>\<^sub>p) = []\<close>
      using infer_ELet.prems by (simp add: d1 ol' dp u1 asrs[symmetric] Let_def
            split: if_split_asm del: sapp.simps sappe.simps sappr.simps sapps.simps)
    obtain s\<^sub>3 b'' pd\<^sub>3 where d3: \<open>infer uf (gen_env_s s\<^sub>2 asx rsx reqs \<Gamma> @ sappe (s\<^sub>2 \<odot> sp \<odot> s\<^sub>1) B)
      (sappr (s\<^sub>2 \<odot> sp \<odot> s\<^sub>1) A) pdr b n\<^sub>3 = Some (s\<^sub>3, b'', \<tau>, pd\<^sub>3, n')\<close>
      and se: \<open>s = s\<^sub>3 \<odot> (s\<^sub>2 \<odot> sp \<odot> s\<^sub>1)\<close> \<open>pd' = pd\<^sub>3\<close>
    proof (cases \<open>infer uf (gen_env_s s\<^sub>2 asx rsx reqs \<Gamma> @ sappe (s\<^sub>2 \<odot> sp \<odot> s\<^sub>1) B)
      (sappr (s\<^sub>2 \<odot> sp \<odot> s\<^sub>1) A) pdr b n\<^sub>3\<close>)
      case None then show ?thesis using infer_ELet.prems
        by (simp add: d1 ol' dp u1 asrs[symmetric] covb gen_env_s_def Let_def
              del: sapp.simps sappe.simps sappr.simps sapps.simps)
    next
      case (Some r) then show ?thesis using that infer_ELet.prems
        by (cases r) (auto simp: d1 ol' dp u1 asrs[symmetric] covb gen_env_s_def Let_def
              simp del: sapp.simps sappe.simps sappr.simps sapps.simps)
    qed
    have p: \<open>shyg sp X \<and> tsigs \<tau>\<^sub>p \<subseteq> X \<and> tsigs_bs \<Gamma> \<subseteq> X\<close>
      by (rule infer_pat_sigs(1)[OF dp sigs_in_sappe[OF conjunct1[OF i1] B]])
    have s2: \<open>shyg s\<^sub>2 X\<close> by (rule uni_shyg[OF u1]) (use i1 p tsigs_sapp in simp_all)
    have s: \<open>shyg (s\<^sub>2 \<odot> sp \<odot> s\<^sub>1) X\<close> using i1 p s2 by (simp add: shyg_scomp)
    have P3: \<open>tsigs_pend (sub_pend (s\<^sub>2 \<odot> sp) pd\<^sub>1) \<subseteq> X\<close>
      using tsigs_sub_pend[of \<open>s\<^sub>2 \<odot> sp\<close> X pd\<^sub>1] p s2 i1 by (simp add: shyg_scomp)
    have gs: \<open>tsigs_pend pdr \<subseteq> X \<and> (\<forall>\<tau>. tsigs \<tau> \<subseteq> X \<longrightarrow> tsigs (offs reqs \<tau>) \<subseteq> X)\<close>
    proof (cases \<open>val_exp B e'' \<and> var_pat p \<and> length \<Gamma> = 1\<close>)
      case True
      then have \<open>gen_off (sappe (s\<^sub>2 \<odot> sp \<odot> s\<^sub>1) B) (sappr (s\<^sub>2 \<odot> sp \<odot> s\<^sub>1) A)
                   (sub_pend (s\<^sub>2 \<odot> sp) pd\<^sub>1) n
                   (sapp s\<^sub>2 \<tau>\<^sub>p) = (asx, rsx, reqs, pdr)\<close>
        using asrs by simp
      from gen_off_sigs[OF this P3] show ?thesis by blast
    next
      case False
      then have \<open>reqs = [] \<and> pdr = sub_pend (s\<^sub>2 \<odot> sp) pd\<^sub>1\<close>
        using asrs by (auto split: if_split_asm prod.split_asm)
      then show ?thesis using P3 by simp
    qed
    have G: \<open>sigs_in (gen_env_s s\<^sub>2 asx rsx reqs \<Gamma>) X\<close>
      using p gs by (intro sigs_in_gen_env_s[OF s2]) blast+
    have B3: \<open>sigs_in (gen_env_s s\<^sub>2 asx rsx reqs \<Gamma> @ sappe (s\<^sub>2 \<odot> sp \<odot> s\<^sub>1) B) X\<close>
      using G sigs_in_sappe[OF s B] by simp
    have i3: \<open>shyg s\<^sub>3 X \<and> tsigs \<tau> \<subseteq> X \<and> tsigs_pend pd\<^sub>3 \<subseteq> X\<close>
      using d1 refl refl refl refl ol' refl dp refl refl refl refl u1 refl refl refl refl refl refl
        refl asrs refl refl gen_env_s_def covb d3 B3 conjunct1[OF gs]
      by (rule infer_ELet.IH)
    show ?thesis using s i3 se by (simp add: shyg_scomp)
  next
    case (Cons l ls')
    with ol have ol': \<open>open_labels [p] = Some (l # ls')\<close> by simp
    from infer_ELet.prems obtain so evs \<tau>\<^sub>t pdo n\<^sub>2 where
      os: \<open>open_scrut uf \<tau>\<^sub>e pd\<^sub>1 (l # ls') n\<^sub>1 = Some (so, evs, \<tau>\<^sub>t, pdo, n\<^sub>2)\<close>
      by (auto simp: d1 ol' split: Option.bind_split_asm prod.split_asm
            simp del: sapp.simps sappe.simps sappr.simps sapps.simps)
    from infer_ELet.prems obtain sp p\<^sub>x \<tau>\<^sub>p \<Gamma> n\<^sub>3 where
      dp: \<open>infer_pat uf (sappe (so \<odot> s\<^sub>1) B) (open_arm (l # ls') p) n\<^sub>2 = Some (sp, p\<^sub>x, \<tau>\<^sub>p, \<Gamma>, n\<^sub>3)\<close>
      by (auto simp: d1 ol' os split: Option.bind_split_asm prod.split_asm
            simp del: sapp.simps sappe.simps sappr.simps sapps.simps)
    from infer_ELet.prems obtain s\<^sub>2 n\<^sub>4 where u1: \<open>uni uf (sapp sp \<tau>\<^sub>t) \<tau>\<^sub>p n\<^sub>3 = Some (s\<^sub>2, n\<^sub>4)\<close>
      by (auto simp: d1 ol' os dp split: Option.bind_split_asm prod.split_asm
            simp del: sapp.simps sappe.simps sappr.simps sapps.simps)
    let ?s = \<open>s\<^sub>2 \<odot> sp \<odot> so \<odot> s\<^sub>1\<close>
    let ?pd = \<open>sub_pend (s\<^sub>2 \<odot> sp) pdo\<close>
    obtain asx rsx where asrs: \<open>(asx, rsx) =
      (if val_exp B e'' then gen_p (sappe ?s B) (sappr ?s A) ?pd n (sapp s\<^sub>2 \<tau>\<^sub>p) else ({}, {}))\<close>
      by (metis prod.collapse)
    let ?\<Gamma>' = \<open>map (\<lambda>(x, \<tau>). (x, TEval (close_sch asx rsx (sapp s\<^sub>2 \<tau>)))) \<Gamma>\<close>
    from infer_ELet.prems obtain s\<^sub>3 b'' pd\<^sub>3 where
      covb: \<open>covers (sappe ?s B) (sapp s\<^sub>2 \<tau>\<^sub>p) [open_arm (l # ls') p] \<and>
             btv_list (sapp s\<^sub>2 \<tau>\<^sub>p) = [] \<and> brv_list (sapp s\<^sub>2 \<tau>\<^sub>p) = []\<close> and
      d3: \<open>infer uf (?\<Gamma>' @ sappe ?s B) (sappr ?s A) ?pd b n\<^sub>4 = Some (s\<^sub>3, b'', \<tau>, pd\<^sub>3, n')\<close> and
      se: \<open>s = s\<^sub>3 \<odot> ?s\<close> \<open>pd' = pd\<^sub>3\<close>
      by (auto simp: d1 ol' os dp u1 asrs[symmetric] Let_def
            split: Option.bind_split_asm prod.split_asm if_split_asm
            simp del: sapp.simps sappe.simps sappr.simps sapps.simps)
    have o: \<open>shyg so X \<and> tsigs \<tau>\<^sub>t \<subseteq> X \<and> tsigs_pend pdo \<subseteq> X\<close>
      by (rule open_scrut_sigs[OF os]) (use i1 in simp_all)
    have s0: \<open>shyg (so \<odot> s\<^sub>1) X\<close> using i1 o by (simp add: shyg_scomp)
    have p: \<open>shyg sp X \<and> tsigs \<tau>\<^sub>p \<subseteq> X \<and> tsigs_bs \<Gamma> \<subseteq> X\<close>
      by (rule infer_pat_sigs(1)[OF dp sigs_in_sappe[OF s0 B]])
    have s2: \<open>shyg s\<^sub>2 X\<close> by (rule uni_shyg[OF u1]) (use o p tsigs_sapp in simp_all)
    have s: \<open>shyg ?s X\<close> using i1 o p s2 by (simp add: shyg_scomp)
    have P3: \<open>tsigs_pend ?pd \<subseteq> X\<close>
      using tsigs_sub_pend[of \<open>s\<^sub>2 \<odot> sp\<close> X pdo] o p s2 by (simp add: shyg_scomp)
    have G: \<open>sigs_in ?\<Gamma>' X\<close>
      using sigs_in_gen_env_s[OF s2 conjunct2[OF conjunct2[OF p]], where reqs = \<open>[]\<close>]
      by (simp add: gen_env_s_def)
    have B3: \<open>sigs_in (?\<Gamma>' @ sappe ?s B) X\<close> using G sigs_in_sappe[OF s B] by simp
    have i3: \<open>shyg s\<^sub>3 X \<and> tsigs \<tau> \<subseteq> X \<and> tsigs_pend pd\<^sub>3 \<subseteq> X\<close>
      using d1 ol' os dp u1 asrs covb d3 B3 P3
      by - (rule infer_ELet.IH; (rule refl | assumption)+)
    show ?thesis using s i3 se by (simp add: shyg_scomp)
  qed
next
  case (infer_ELetFun uf B A pd f mbs cls b n s e' \<tau> pd' n')
  note IH = infer_ELetFun.IH
  from infer_ELetFun.prems have B: \<open>sigs_in B X\<close> and P: \<open>tsigs_pend pd \<subseteq> X\<close> by blast+
  have ok: \<open>\<not> (cls = [] \<or> \<not> is_fn (foldr EFnMod mbs (dfun_rhs cls)) \<or> \<not> nm_ok (n_txt f))\<close>
    using infer_ELetFun.prems by (auto simp: Let_def split: if_split_asm)
  obtain s\<^sub>1 r' \<tau>' pd\<^sub>1 n\<^sub>1 where
    d1: \<open>infer uf ((n_txt f, TEval (kmono (TV n))) # B) A pd (foldr EFnMod mbs (dfun_rhs cls)) (Suc n)
         = Some (s\<^sub>1, r', \<tau>', pd\<^sub>1, n\<^sub>1)\<close>
  proof (cases \<open>infer uf ((n_txt f, TEval (kmono (TV n))) # B) A pd (foldr EFnMod mbs (dfun_rhs cls)) (Suc n)\<close>)
    case None then show ?thesis using infer_ELetFun.prems ok
      by (simp add: Let_def del: sapp.simps sappe.simps sappr.simps sapps.simps)
  next
    case (Some r) then show ?thesis using that by (cases r) auto
  qed
  obtain s\<^sub>2 n\<^sub>2 where u1: \<open>uni uf (sapp s\<^sub>1 (TV n)) \<tau>' n\<^sub>1 = Some (s\<^sub>2, n\<^sub>2)\<close>
  proof (cases \<open>uni uf (sapp s\<^sub>1 (TV n)) \<tau>' n\<^sub>1\<close>)
    case None then show ?thesis using infer_ELetFun.prems ok
      by (simp add: d1 Let_def del: sapp.simps sappe.simps sappr.simps sapps.simps)
  next
    case (Some r) then show ?thesis using that by (cases r) auto
  qed
  obtain as rs reqs pdr where asrs: \<open>(as, rs, reqs, pdr) = gen_off (sappe (s\<^sub>2 \<odot> s\<^sub>1) B)
      (sappr (s\<^sub>2 \<odot> s\<^sub>1) A) (sub_pend s\<^sub>2 pd\<^sub>1) n (sapp s\<^sub>2 \<tau>')\<close>
    by (metis prod_cases4)
  have bt: \<open>btv_list (sapp s\<^sub>2 \<tau>') = [] \<and> brv_list (sapp s\<^sub>2 \<tau>') = []\<close>
    using infer_ELetFun.prems ok by (simp add: d1 u1 asrs[symmetric] Let_def
          split: if_split_asm del: sapp.simps sappe.simps sappr.simps sapps.simps)
  obtain s\<^sub>3 b' pd\<^sub>3 where
    d3: \<open>infer uf ((n_txt f, TEval (close_sch as rs (offs reqs (sapp s\<^sub>2 \<tau>')))) # sappe (s\<^sub>2 \<odot> s\<^sub>1) B)
          (sappr (s\<^sub>2 \<odot> s\<^sub>1) A) pdr b n\<^sub>2 = Some (s\<^sub>3, b', \<tau>, pd\<^sub>3, n')\<close>
    and se: \<open>s = s\<^sub>3 \<odot> (s\<^sub>2 \<odot> s\<^sub>1)\<close> \<open>pd' = pd\<^sub>3\<close>
  proof (cases \<open>infer uf ((n_txt f, TEval (close_sch as rs (offs reqs (sapp s\<^sub>2 \<tau>')))) # sappe (s\<^sub>2 \<odot> s\<^sub>1) B)
          (sappr (s\<^sub>2 \<odot> s\<^sub>1) A) pdr b n\<^sub>2\<close>)
    case None then show ?thesis using infer_ELetFun.prems ok
      by (simp add: d1 u1 asrs[symmetric] bt Let_def del: sapp.simps sappe.simps sappr.simps sapps.simps)
  next
    case (Some r) then show ?thesis using that infer_ELetFun.prems ok
      by (cases r) (auto simp: d1 u1 asrs[symmetric] bt Let_def
            simp del: sapp.simps sappe.simps sappr.simps sapps.simps)
  qed
  have B1: \<open>sigs_in ((n_txt f, TEval (kmono (TV n))) # B) X\<close> using B by (simp add: sigs_in_def)
  have i1: \<open>shyg s\<^sub>1 X \<and> tsigs \<tau>' \<subseteq> X \<and> tsigs_pend pd\<^sub>1 \<subseteq> X\<close>
    using ok d1 B1 P by (rule IH(1)[OF refl])
  have s2: \<open>shyg s\<^sub>2 X\<close> by (rule uni_shyg[OF u1]) (use i1 tsigs_sapp in \<open>simp_all add: sigs_in_def\<close>)
  have s: \<open>shyg (s\<^sub>2 \<odot> s\<^sub>1) X\<close> using i1 s2 by (simp add: shyg_scomp)
  have P3: \<open>tsigs_pend (sub_pend s\<^sub>2 pd\<^sub>1) \<subseteq> X\<close>
    using tsigs_sub_pend[of s\<^sub>2 X pd\<^sub>1] s2 i1 by simp
  have gs: \<open>tsigs_pend pdr \<subseteq> X\<close> \<open>tsigs (offs reqs (sapp s\<^sub>2 \<tau>')) \<subseteq> X\<close>
    using gen_off_sigs[OF asrs[symmetric] P3] tsigs_sapp[OF s2] i1 by blast+
  have B3: \<open>sigs_in ((n_txt f, TEval (close_sch as rs (offs reqs (sapp s\<^sub>2 \<tau>')))) # sappe (s\<^sub>2 \<odot> s\<^sub>1) B) X\<close>
    using sigs_in_sappe[OF s B] gs(2) by simp
  have i3: \<open>shyg s\<^sub>3 X \<and> tsigs \<tau> \<subseteq> X \<and> tsigs_pend pd\<^sub>3 \<subseteq> X\<close>
    using refl ok d1 refl refl refl refl u1 refl refl refl refl refl refl refl asrs refl refl bt d3 B3 gs(1)
    by (rule IH(2))
  show ?case using s i3 se by (simp add: shyg_scomp)
next
  case (infer_EGuards_Cons uf B A pd gs e alts n s e' \<tau> pd' n')
  note IH = infer_EGuards_Cons.IH
  from infer_EGuards_Cons.prems have B: \<open>sigs_in B X\<close> and P: \<open>tsigs_pend pd \<subseteq> X\<close> by blast+
  obtain s\<^sub>1 gs' \<tau>s pd\<^sub>1 n\<^sub>1 where d1: \<open>infer_exps uf B A pd gs n = Some (s\<^sub>1, gs', \<tau>s, pd\<^sub>1, n\<^sub>1)\<close>
  proof (cases \<open>infer_exps uf B A pd gs n\<close>)
    case None then show ?thesis using infer_EGuards_Cons.prems
      by (simp del: sapp.simps sappe.simps sappr.simps sapps.simps)
  next
    case (Some r) then show ?thesis using that by (cases r) auto
  qed
  obtain s\<^sub>2 n\<^sub>2 where u1: \<open>unis uf (map (\<lambda>\<tau>. (\<tau>, TC bool_ty [])) \<tau>s) n\<^sub>1 = Some (s\<^sub>2, n\<^sub>2)\<close>
  proof (cases \<open>unis uf (map (\<lambda>\<tau>. (\<tau>, TC bool_ty [])) \<tau>s) n\<^sub>1\<close>)
    case None then show ?thesis using infer_EGuards_Cons.prems
      by (simp add: d1 del: sapp.simps sappe.simps sappr.simps sapps.simps)
  next
    case (Some r) then show ?thesis using that by (cases r) auto
  qed
  obtain s\<^sub>3 e'' \<tau>\<^sub>e pd\<^sub>3 n\<^sub>3 where d2: \<open>infer uf (sappe (s\<^sub>2 \<odot> s\<^sub>1) B) (sappr (s\<^sub>2 \<odot> s\<^sub>1) A)
      (sub_pend s\<^sub>2 pd\<^sub>1) e n\<^sub>2 = Some (s\<^sub>3, e'', \<tau>\<^sub>e, pd\<^sub>3, n\<^sub>3)\<close>
  proof (cases \<open>infer uf (sappe (s\<^sub>2 \<odot> s\<^sub>1) B) (sappr (s\<^sub>2 \<odot> s\<^sub>1) A) (sub_pend s\<^sub>2 pd\<^sub>1) e n\<^sub>2\<close>)
    case None then show ?thesis using infer_EGuards_Cons.prems
      by (simp add: d1 u1 Let_def del: sapp.simps sappe.simps sappr.simps sapps.simps)
  next
    case (Some r) then show ?thesis using that by (cases r) auto
  qed
  have i1: \<open>shyg s\<^sub>1 X \<and> (\<forall>\<tau>\<in>set \<tau>s. tsigs \<tau> \<subseteq> X) \<and> tsigs_pend pd\<^sub>1 \<subseteq> X\<close>
    using d1 B P by (rule IH(1))
  have s2: \<open>shyg s\<^sub>2 X\<close> by (rule unis_shyg[OF u1]) (use i1 in \<open>auto simp: tsigs_cs_def\<close>)
  have s: \<open>shyg (s\<^sub>2 \<odot> s\<^sub>1) X\<close> using i1 s2 by (simp add: shyg_scomp)
  have B2: \<open>sigs_in (sappe (s\<^sub>2 \<odot> s\<^sub>1) B) X\<close> by (rule sigs_in_sappe[OF s B])
  have P2: \<open>tsigs_pend (sub_pend s\<^sub>2 pd\<^sub>1) \<subseteq> X\<close> using tsigs_sub_pend[OF s2] i1 by simp
  have i2: \<open>shyg s\<^sub>3 X \<and> tsigs \<tau>\<^sub>e \<subseteq> X \<and> tsigs_pend pd\<^sub>3 \<subseteq> X\<close>
    using d1 refl refl refl refl u1 refl refl d2 B2 P2 by (rule IH(2))
  have s': \<open>shyg (s\<^sub>3 \<odot> (s\<^sub>2 \<odot> s\<^sub>1)) X\<close> using s i2 by (simp add: shyg_scomp)
  show ?case
  proof (cases \<open>alts = []\<close>)
    case True
    then show ?thesis using infer_EGuards_Cons.prems s' i2
      by (auto simp: d1 u1 d2 Let_def simp del: sapp.simps sappe.simps sappr.simps sapps.simps)
  next
    case False
    obtain s\<^sub>4 g' \<tau>\<^sub>g pd\<^sub>4 n\<^sub>4 where d3: \<open>infer uf (sappe (s\<^sub>3 \<odot> (s\<^sub>2 \<odot> s\<^sub>1)) B)
        (sappr (s\<^sub>3 \<odot> (s\<^sub>2 \<odot> s\<^sub>1)) A) pd\<^sub>3 (EGuards alts) n\<^sub>3 = Some (s\<^sub>4, g', \<tau>\<^sub>g, pd\<^sub>4, n\<^sub>4)\<close>
    proof (cases \<open>infer uf (sappe (s\<^sub>3 \<odot> (s\<^sub>2 \<odot> s\<^sub>1)) B) (sappr (s\<^sub>3 \<odot> (s\<^sub>2 \<odot> s\<^sub>1)) A) pd\<^sub>3
        (EGuards alts) n\<^sub>3\<close>)
      case None then show ?thesis using infer_EGuards_Cons.prems False
        by (simp add: d1 u1 d2 Let_def del: sapp.simps sappe.simps sappr.simps sapps.simps)
    next
      case (Some r) then show ?thesis using that by (cases r) auto
    qed
    obtain s\<^sub>5 n\<^sub>5 where u2: \<open>uni uf \<tau>\<^sub>g (sapp s\<^sub>4 \<tau>\<^sub>e) n\<^sub>4 = Some (s\<^sub>5, n\<^sub>5)\<close>
    proof (cases \<open>uni uf \<tau>\<^sub>g (sapp s\<^sub>4 \<tau>\<^sub>e) n\<^sub>4\<close>)
      case None then show ?thesis using infer_EGuards_Cons.prems False
        by (simp add: d1 u1 d2 d3 Let_def del: sapp.simps sappe.simps sappr.simps sapps.simps)
    next
      case (Some r) then show ?thesis using that by (cases r) auto
    qed
    have B3: \<open>sigs_in (sappe (s\<^sub>3 \<odot> (s\<^sub>2 \<odot> s\<^sub>1)) B) X\<close> by (rule sigs_in_sappe[OF s' B])
    have i3: \<open>shyg s\<^sub>4 X \<and> tsigs \<tau>\<^sub>g \<subseteq> X \<and> tsigs_pend pd\<^sub>4 \<subseteq> X\<close>
      using d1 refl refl refl refl u1 refl refl d2 refl refl refl refl False refl d3 B3 conjunct2[OF conjunct2[OF i2]]
      by (rule IH(3))
    have s5: \<open>shyg s\<^sub>5 X\<close>
      by (rule uni_shyg[OF u2]) (use i3 i2 tsigs_sapp in simp_all)
    have \<open>s = s\<^sub>5 \<odot> s\<^sub>4 \<odot> (s\<^sub>3 \<odot> (s\<^sub>2 \<odot> s\<^sub>1))\<close> \<open>\<tau> = sapp s\<^sub>5 \<tau>\<^sub>g\<close> \<open>pd' = sub_pend s\<^sub>5 pd\<^sub>4\<close>
      using infer_EGuards_Cons.prems False
      by (auto simp: d1 u1 d2 d3 u2 Let_def simp del: sapp.simps sappe.simps sappr.simps sapps.simps)
    then show ?thesis
      using s' i3 s5 tsigs_sapp[OF s5] tsigs_sub_pend[OF s5] by (simp add: shyg_scomp)
  qed
next
  case (infer_ESeq uf B A pd e\<^sub>1 e\<^sub>2 n s e' \<tau> pd' n')
  from infer_ESeq.prems have B: \<open>sigs_in B X\<close> and P: \<open>tsigs_pend pd \<subseteq> X\<close> by blast+
  from infer_ESeq.prems obtain s\<^sub>1 e\<^sub>1' \<tau>\<^sub>1 pd\<^sub>1 n\<^sub>1 s\<^sub>2 e\<^sub>2' pd\<^sub>2 where
    d1: \<open>infer uf B A pd e\<^sub>1 n = Some (s\<^sub>1, e\<^sub>1', \<tau>\<^sub>1, pd\<^sub>1, n\<^sub>1)\<close> and
    d2: \<open>infer uf (sappe s\<^sub>1 B) (sappr s\<^sub>1 A) pd\<^sub>1 e\<^sub>2 n\<^sub>1 = Some (s\<^sub>2, e\<^sub>2', \<tau>, pd\<^sub>2, n')\<close> and
    se: \<open>s = s\<^sub>2 \<odot> s\<^sub>1\<close> \<open>pd' = pd\<^sub>2\<close>
    by (auto split: Option.bind_split_asm prod.split_asm)
  have i1: \<open>shyg s\<^sub>1 X \<and> tsigs \<tau>\<^sub>1 \<subseteq> X \<and> tsigs_pend pd\<^sub>1 \<subseteq> X\<close>
    using d1 B P by (rule infer_ESeq.IH)
  have i2: \<open>shyg s\<^sub>2 X \<and> tsigs \<tau> \<subseteq> X \<and> tsigs_pend pd\<^sub>2 \<subseteq> X\<close>
    using d1 refl refl refl refl d2 sigs_in_sappe[OF conjunct1[OF i1] B]
      by (rule infer_ESeq.IH) (use i1 in simp_all)
  show ?case using i1 i2 se by (simp add: shyg_scomp)
next
  case (infer_EIf_Some uf B A pd c t e n s ex \<tau> pd' n')
  from infer_EIf_Some.prems have B: \<open>sigs_in B X\<close> and P: \<open>tsigs_pend pd \<subseteq> X\<close> by blast+
  from infer_EIf_Some.prems obtain s\<^sub>1 c'' \<tau>c pd\<^sub>1 n\<^sub>1 s\<^sub>2 n\<^sub>2 s\<^sub>3 t'' \<tau>t pd\<^sub>3 n\<^sub>3 s\<^sub>4 e'' \<tau>e pd\<^sub>4 n\<^sub>4 s\<^sub>5 where
    d1: \<open>infer uf B A pd c n = Some (s\<^sub>1, c'', \<tau>c, pd\<^sub>1, n\<^sub>1)\<close> and
    u1: \<open>uni uf \<tau>c (TC bool_ty []) n\<^sub>1 = Some (s\<^sub>2, n\<^sub>2)\<close> and
    d3: \<open>infer uf (sappe (s\<^sub>2 \<odot> s\<^sub>1) B) (sappr (s\<^sub>2 \<odot> s\<^sub>1) A) (sub_pend s\<^sub>2 pd\<^sub>1) t n\<^sub>2
           = Some (s\<^sub>3, t'', \<tau>t, pd\<^sub>3, n\<^sub>3)\<close> and
    d4: \<open>infer uf (sappe (s\<^sub>3 \<odot> (s\<^sub>2 \<odot> s\<^sub>1)) B) (sappr (s\<^sub>3 \<odot> (s\<^sub>2 \<odot> s\<^sub>1)) A) pd\<^sub>3 e n\<^sub>3
           = Some (s\<^sub>4, e'', \<tau>e, pd\<^sub>4, n\<^sub>4)\<close> and
    u2: \<open>uni uf \<tau>e (sapp s\<^sub>4 \<tau>t) n\<^sub>4 = Some (s\<^sub>5, n')\<close> and
    se: \<open>s = s\<^sub>5 \<odot> s\<^sub>4 \<odot> (s\<^sub>3 \<odot> (s\<^sub>2 \<odot> s\<^sub>1))\<close> \<open>\<tau> = sapp s\<^sub>5 (sapp s\<^sub>4 \<tau>t)\<close>
      \<open>pd' = sub_pend s\<^sub>5 pd\<^sub>4\<close>
    by (auto simp: Let_def bind_eq_Some_conv)
  have i1: \<open>shyg s\<^sub>1 X \<and> tsigs \<tau>c \<subseteq> X \<and> tsigs_pend pd\<^sub>1 \<subseteq> X\<close>
    using d1 B P by (rule infer_EIf_Some.IH)
  have s2: \<open>shyg s\<^sub>2 X\<close> by (rule uni_shyg[OF u1]) (use i1 in simp_all)
  have s21: \<open>shyg (s\<^sub>2 \<odot> s\<^sub>1) X\<close> using i1 s2 by (simp add: shyg_scomp)
  have i3: \<open>shyg s\<^sub>3 X \<and> tsigs \<tau>t \<subseteq> X \<and> tsigs_pend pd\<^sub>3 \<subseteq> X\<close>
    using d1 refl refl refl refl u1 refl refl d3 sigs_in_sappe[OF s21 B] by (rule infer_EIf_Some.IH)
       (use tsigs_sub_pend[OF s2] i1 in simp)
  have s321: \<open>shyg (s\<^sub>3 \<odot> (s\<^sub>2 \<odot> s\<^sub>1)) X\<close> using s21 i3 by (simp add: shyg_scomp)
  have i4: \<open>shyg s\<^sub>4 X \<and> tsigs \<tau>e \<subseteq> X \<and> tsigs_pend pd\<^sub>4 \<subseteq> X\<close>
    using d1 refl refl refl refl u1 refl refl d3 refl refl refl refl refl d4
      sigs_in_sappe[OF s321 B] by (rule infer_EIf_Some.IH)
       (use i3 in simp)
  have s5: \<open>shyg s\<^sub>5 X\<close> by (rule uni_shyg[OF u2]) (use i4 i3 tsigs_sapp in simp_all)
  show ?case using se s321 s5 i4 tsigs_sapp[OF s5 tsigs_sapp[OF conjunct1[OF i4]]]
    tsigs_sub_pend[OF s5] i3
    by (simp add: shyg_scomp)
next
  case (infer_EIf_None uf B A pd c t n s e' \<tau> pd' n')
  from infer_EIf_None.prems have B: \<open>sigs_in B X\<close> and P: \<open>tsigs_pend pd \<subseteq> X\<close> by blast+
  from infer_EIf_None.prems obtain s\<^sub>1 c'' \<tau>c pd\<^sub>1 n\<^sub>1 s\<^sub>2 n\<^sub>2 s\<^sub>3 t'' \<tau>t pd\<^sub>3 n\<^sub>3 s\<^sub>4 where
    d1: \<open>infer uf B A pd c n = Some (s\<^sub>1, c'', \<tau>c, pd\<^sub>1, n\<^sub>1)\<close> and
    u1: \<open>uni uf \<tau>c (TC bool_ty []) n\<^sub>1 = Some (s\<^sub>2, n\<^sub>2)\<close> and
    d3: \<open>infer uf (sappe (s\<^sub>2 \<odot> s\<^sub>1) B) (sappr (s\<^sub>2 \<odot> s\<^sub>1) A) (sub_pend s\<^sub>2 pd\<^sub>1) t n\<^sub>2
           = Some (s\<^sub>3, t'', \<tau>t, pd\<^sub>3, n\<^sub>3)\<close> and
    u2: \<open>uni uf \<tau>t unit_ty n\<^sub>3 = Some (s\<^sub>4, n')\<close> and
    se: \<open>s = s\<^sub>4 \<odot> s\<^sub>3 \<odot> (s\<^sub>2 \<odot> s\<^sub>1)\<close> \<open>\<tau> = unit_ty\<close> \<open>pd' = sub_pend s\<^sub>4 pd\<^sub>3\<close>
    by (auto simp: Let_def bind_eq_Some_conv)
  have i1: \<open>shyg s\<^sub>1 X \<and> tsigs \<tau>c \<subseteq> X \<and> tsigs_pend pd\<^sub>1 \<subseteq> X\<close>
    using d1 B P by (rule infer_EIf_None.IH)
  have s2: \<open>shyg s\<^sub>2 X\<close> by (rule uni_shyg[OF u1]) (use i1 in simp_all)
  have s21: \<open>shyg (s\<^sub>2 \<odot> s\<^sub>1) X\<close> using i1 s2 by (simp add: shyg_scomp)
  have i3: \<open>shyg s\<^sub>3 X \<and> tsigs \<tau>t \<subseteq> X \<and> tsigs_pend pd\<^sub>3 \<subseteq> X\<close>
    using d1 refl refl refl refl u1 refl refl d3 sigs_in_sappe[OF s21 B] by (rule infer_EIf_None.IH)
       (use tsigs_sub_pend[OF s2] i1 in simp)
  have s4: \<open>shyg s\<^sub>4 X\<close> by (rule uni_shyg[OF u2]) (use i3 in simp_all)
  show ?case using se s21 s4 i3 tsigs_sub_pend[OF s4] by (simp add: shyg_scomp)
next
  case (infer_EMatch uf B A pd e arms n s e' \<tau> pd' n')
  from infer_EMatch.prems have B: \<open>sigs_in B X\<close> and P: \<open>tsigs_pend pd \<subseteq> X\<close> by blast+
  from infer_EMatch.prems obtain s\<^sub>1 e'' \<tau>\<^sub>0 pd\<^sub>1 n\<^sub>1 ls where
    d1: \<open>infer uf B A pd e n = Some (s\<^sub>1, e'', \<tau>\<^sub>0, pd\<^sub>1, n\<^sub>1)\<close> and
    ol: \<open>open_labels (map fst arms) = Some ls\<close>
    by (auto split: Option.bind_split_asm prod.split_asm option.split_asm)
  have i1: \<open>shyg s\<^sub>1 X \<and> tsigs \<tau>\<^sub>0 \<subseteq> X \<and> tsigs_pend pd\<^sub>1 \<subseteq> X\<close>
    using d1 B P by (rule infer_EMatch.IH)
  show ?case
  proof (cases ls)
    case Nil
    with ol have ol': \<open>open_labels (map fst arms) = Some []\<close> by simp
    from infer_EMatch.prems obtain s\<^sub>2 arms'' where
      d2: \<open>infer_arms uf (sappe s\<^sub>1 B) (sappr s\<^sub>1 A) pd\<^sub>1 \<tau>\<^sub>0 (TV n\<^sub>1) arms (Suc n\<^sub>1)
        = Some (s\<^sub>2, arms'', pd', n')\<close> and
      se: \<open>s = s\<^sub>2 \<odot> s\<^sub>1\<close> \<open>\<tau> = sapp s\<^sub>2 (TV n\<^sub>1)\<close>
      by (auto simp: d1 ol' split: Option.bind_split_asm prod.split_asm if_split_asm)
    have i2: \<open>shyg s\<^sub>2 X \<and> tsigs_pend pd' \<subseteq> X\<close>
      using d1 refl refl refl refl ol' refl d2 sigs_in_sappe[OF conjunct1[OF i1] B]
      by (rule infer_EMatch.IH) (use i1 in simp_all)
    show ?thesis using shyg_scomp i1 i2 se tsigs_sapp[of s\<^sub>2 X \<open>TV n\<^sub>1\<close>] by auto
  next
    case (Cons l ls')
    with ol have ol': \<open>open_labels (map fst arms) = Some (l # ls')\<close> by simp
    from infer_EMatch.prems obtain so evs \<tau>\<^sub>t pdo n\<^sub>2 s\<^sub>2 arms'' where
      os: \<open>open_scrut uf \<tau>\<^sub>0 pd\<^sub>1 (l # ls') n\<^sub>1 = Some (so, evs, \<tau>\<^sub>t, pdo, n\<^sub>2)\<close> and
      d2: \<open>infer_arms uf (sappe (so \<odot> s\<^sub>1) B) (sappr (so \<odot> s\<^sub>1) A) pdo \<tau>\<^sub>t (TV n\<^sub>2)
             (open_arms (l # ls') arms) (Suc n\<^sub>2) = Some (s\<^sub>2, arms'', pd', n')\<close> and
      se: \<open>s = s\<^sub>2 \<odot> (so \<odot> s\<^sub>1)\<close> \<open>\<tau> = sapp s\<^sub>2 (TV n\<^sub>2)\<close>
      by (auto simp: d1 ol' Let_def split: Option.bind_split_asm prod.split_asm if_split_asm)
    have o: \<open>shyg so X \<and> tsigs \<tau>\<^sub>t \<subseteq> X \<and> tsigs_pend pdo \<subseteq> X\<close>
      by (rule open_scrut_sigs[OF os]) (use i1 in simp_all)
    have s: \<open>shyg (so \<odot> s\<^sub>1) X\<close> using i1 o by (simp add: shyg_scomp)
    have i2: \<open>shyg s\<^sub>2 X \<and> tsigs_pend pd' \<subseteq> X\<close>
      using d1 refl refl refl refl ol' refl os refl refl refl refl refl d2 sigs_in_sappe[OF s B]
      by (rule infer_EMatch.IH) (use o in simp_all)
    show ?thesis using shyg_scomp[OF s conjunct1[OF i2]] i2 se tsigs_sapp[of s\<^sub>2 X \<open>TV n\<^sub>2\<close>]
      by auto
  qed
next
  case (infer_EHandle uf B A pd e cls n s e' \<tau> pd' n')
  from infer_EHandle.prems have B: \<open>sigs_in B X\<close> and P: \<open>tsigs_pend pd \<subseteq> X\<close> by blast+
  from infer_EHandle.prems obtain s\<^sub>1 e'' \<tau>\<^sub>0 pd\<^sub>1 n\<^sub>1 s\<^sub>2 cls'' where
    pe: \<open>list_all (plain_eff B) (hlabels B cls)\<close> and
    d1: \<open>infer uf B (canon_row (rext (hlabels B cls) A)) pd e n = Some (s\<^sub>1, e'', \<tau>\<^sub>0, pd\<^sub>1, n\<^sub>1)\<close> and
    d2: \<open>infer_cls uf (sappe s\<^sub>1 B) (sappr s\<^sub>1 A) pd\<^sub>1 False \<tau>\<^sub>0 (tuple []) cls n\<^sub>1
      = Some (s\<^sub>2, cls'', \<tau>, pd', n')\<close> and
    se: \<open>s = s\<^sub>2 \<odot> s\<^sub>1\<close>
    by (auto split: Option.bind_split_asm prod.split_asm if_split_asm)
  have i1: \<open>shyg s\<^sub>1 X \<and> tsigs \<tau>\<^sub>0 \<subseteq> X \<and> tsigs_pend pd\<^sub>1 \<subseteq> X\<close>
    using pe d1 B P by (rule infer_EHandle.IH)
  have i2: \<open>shyg s\<^sub>2 X \<and> tsigs \<tau> \<subseteq> X \<and> tsigs_pend pd' \<subseteq> X\<close>
    using pe d1 refl refl refl refl d2 sigs_in_sappe[OF conjunct1[OF i1] B]
    by (rule infer_EHandle.IH) (use i1 in simp_all)
  show ?case using i1 i2 se by (simp add: shyg_scomp)
next
  case (infer_EHandler uf B A pd cls n s e' \<tau> pd' n')
  from infer_EHandler.prems have B: \<open>sigs_in B X\<close> and P: \<open>tsigs_pend pd \<subseteq> X\<close> by blast+
  from infer_EHandler.prems obtain cls'' \<tau>c where
    pe: \<open>list_all (plain_eff B) (hlabels B cls)\<close> and
    d: \<open>infer_cls uf B (RV n) pd False (TV (Suc n)) (tuple []) cls (Suc (Suc n))
      = Some (s, cls'', \<tau>c, pd', n')\<close> and
    te: \<open>\<tau> = TFn (TFn unit_ty (sappr s (canon_row (rext (hlabels B cls) (RV n))))
      (sapp s (TV (Suc n)))) (sappr s (RV n)) \<tau>c\<close>
    by (auto simp: bind_eq_Some_conv split: if_split_asm)
  have i: \<open>shyg s X \<and> tsigs \<tau>c \<subseteq> X \<and> tsigs_pend pd' \<subseteq> X\<close>
    by (rule infer_EHandler.IH) (use pe d B P in auto)
  show ?case using i te tsigs_sapp[of s X \<open>TV (Suc n)\<close>] by simp
next
  case (infer_EMask uf B A pd l e n s e' \<tau> pd' n')
  from infer_EMask.prems have B: \<open>sigs_in B X\<close> and P: \<open>tsigs_pend pd \<subseteq> X\<close> by blast+
  from infer_EMask.prems obtain lbl ps \<tau>\<^sub>1 \<tau>\<^sub>2 s\<^sub>1 n\<^sub>1 s\<^sub>2 e'' where
    lk: \<open>tlookup B [n_txt l] = Some (TEop lbl ps \<tau>\<^sub>1 \<tau>\<^sub>2)\<close> and
    ur: \<open>uni_row A (canon_row (RCons lbl (RV n))) (Suc n) = Some (s\<^sub>1, n\<^sub>1)\<close> and
    d2: \<open>infer uf (sappe s\<^sub>1 B) (sappr s\<^sub>1 (RV n)) (sub_pend s\<^sub>1 pd) e n\<^sub>1
      = Some (s\<^sub>2, e'', \<tau>, pd', n')\<close> and
    se: \<open>s = s\<^sub>2 \<odot> s\<^sub>1\<close>
    by (auto split: option.split_asm tentry.split_asm Option.bind_split_asm prod.split_asm)
  have s1: \<open>shyg s\<^sub>1 X\<close> by (rule uni_row_shyg[OF ur])
  have i: \<open>shyg s\<^sub>2 X \<and> tsigs \<tau> \<subseteq> X \<and> tsigs_pend pd' \<subseteq> X\<close>
    by (rule infer_EMask.IH[OF lk refl ur refl d2 sigs_in_sappe[OF s1 B] tsigs_sub_pend[OF s1 P]])
  show ?case using shyg_scomp[OF s1] i se by simp
next
  case infer_head_AMod
  from infer_head_AMod.prems[unfolded infer_head.simps] show ?case by (rule infer_head_AMod.IH)
next
  case (infer_atom_AParen_Cons_Nil uf B A pd e n s a' \<tau> pd' n')
  from infer_atom_AParen_Cons_Nil.prems have B: \<open>sigs_in B X\<close> and P: \<open>tsigs_pend pd \<subseteq> X\<close> by blast+
  from infer_atom_AParen_Cons_Nil.prems obtain e''
    where d: \<open>infer uf B A pd e n = Some (s, e'', \<tau>, pd', n')\<close>
    by (auto split: Option.bind_split_asm prod.split_asm)
  show ?case by (rule infer_atom_AParen_Cons_Nil.IH[OF d B P])
next
  case (infer_atom_AParen_Cons_Cons uf B A pd v w va n s a' \<tau> pd' n')
  from infer_atom_AParen_Cons_Cons.prems have B: \<open>sigs_in B X\<close> and P: \<open>tsigs_pend pd \<subseteq> X\<close> by blast+
  from infer_atom_AParen_Cons_Cons.prems obtain es'' \<tau>s where
    d: \<open>infer_exps uf B A pd (v # w # va) n = Some (s, es'', \<tau>s, pd', n')\<close> and te: \<open>\<tau> = tuple \<tau>s\<close>
    by (auto split: Option.bind_split_asm prod.split_asm)
  show ?case using infer_atom_AParen_Cons_Cons.IH[OF d B P] te by auto
next
  case (infer_atom_AList uf B A pd es n s a' \<tau> pd' n')
  from infer_atom_AList.prems have B: \<open>sigs_in B X\<close> and P: \<open>tsigs_pend pd \<subseteq> X\<close> by blast+
  from infer_atom_AList.prems obtain s\<^sub>1 es'' \<tau>s pd\<^sub>1 n\<^sub>1 s\<^sub>2 where
    d1: \<open>infer_exps uf B A pd es n = Some (s\<^sub>1, es'', \<tau>s, pd\<^sub>1, n\<^sub>1)\<close> and
    un: \<open>unis uf (map (\<lambda>\<tau>. (\<tau>, TV n\<^sub>1)) \<tau>s) (Suc n\<^sub>1) = Some (s\<^sub>2, n')\<close> and
    se: \<open>s = s\<^sub>2 \<odot> s\<^sub>1\<close> \<open>\<tau> = TC list_ty [sapp s\<^sub>2 (TV n\<^sub>1)]\<close> \<open>pd' = sub_pend s\<^sub>2 pd\<^sub>1\<close>
    by (auto simp: bind_eq_Some_conv)
  have i: \<open>shyg s\<^sub>1 X \<and> (\<forall>\<tau> \<in> set \<tau>s. tsigs \<tau> \<subseteq> X) \<and> tsigs_pend pd\<^sub>1 \<subseteq> X\<close>
    by (rule infer_atom_AList.IH[OF d1 B P])
  have cs: \<open>tsigs_cs (map (\<lambda>\<tau>. (\<tau>, TV n\<^sub>1)) \<tau>s) \<subseteq> X\<close> using i by (auto simp: tsigs_cs_def)
  have s2: \<open>shyg s\<^sub>2 X\<close> by (rule unis_shyg[OF un cs])
  show ?case using se shyg_scomp[OF conjunct1[OF i] s2] tsigs_sapp[of s\<^sub>2 X \<open>TV n\<^sub>1\<close>] s2
    tsigs_sub_pend[OF s2] i by simp
next
  case (infer_args uf B A pd d \<tau>\<^sub>0 as n s as' \<tau> pd' n')
  from infer_args.prems have E: \<open>infer_args uf B A pd d \<tau>\<^sub>0 as n = Some (s, as', \<tau>, pd', n')\<close>
    and B: \<open>sigs_in B X\<close>
    and P: \<open>tsigs_pend pd \<subseteq> X\<close>
    and T0: \<open>tsigs \<tau>\<^sub>0 \<subseteq> X\<close> by blast+
  show ?case
  proof (cases \<tau>\<^sub>0)
    case (TV x)
    show ?thesis
    proof (rule infer_args_step_sigs[OF infer_args.prems], goal_cases nd ih1 ih2)
      case ih1 from TV ih1 show ?case by (rule infer_args.IH)
    next
      case ih2 from TV show ?case by (rule infer_args.IH) (use ih2 in auto)
    qed (simp add: TV)

  next
    case (TB x)
    show ?thesis
    proof (rule infer_args_step_sigs[OF infer_args.prems], goal_cases nd ih1 ih2)
      case ih1 from TB ih1 show ?case by (rule infer_args.IH)
    next
      case ih2 from TB show ?case by (rule infer_args.IH) (use ih2 in auto)
    qed (simp add: TB)

  next
    case (TK x)
    show ?thesis
    proof (rule infer_args_step_sigs[OF infer_args.prems], goal_cases nd ih1 ih2)
      case ih1 from TK ih1 show ?case by (rule infer_args.IH)
    next
      case ih2 from TK show ?case by (rule infer_args.IH) (use ih2 in auto)
    qed (simp add: TK)

  next
    case (TA d' j)
    show ?thesis
    proof (rule infer_args_step_sigs[OF infer_args.prems], goal_cases nd ih1 ih2)
      case ih1 from TA ih1 show ?case by (rule infer_args.IH)
    next
      case ih2 from TA show ?case by (rule infer_args.IH) (use ih2 in auto)
    qed (simp add: TA)

  next
    case (TC c ts)
    show ?thesis
    proof (rule infer_args_step_sigs[OF infer_args.prems], goal_cases nd ih1 ih2)
      case ih1 from TC ih1 show ?case by (rule infer_args.IH)
    next
      case ih2 from TC show ?case by (rule infer_args.IH) (use ih2 in auto)
    qed (simp add: TC)

  next
    case (TApp t\<^sub>1 t\<^sub>2)
    show ?thesis
    proof (rule infer_args_step_sigs[OF infer_args.prems], goal_cases nd ih1 ih2)
      case ih1 from TApp ih1 show ?case by (rule infer_args.IH)
    next
      case ih2 from TApp show ?case by (rule infer_args.IH) (use ih2 in auto)
    qed (simp add: TApp)

  next
    case (TFn t\<^sub>1 e t\<^sub>2)
    show ?thesis
    proof (rule infer_args_step_sigs[OF infer_args.prems], goal_cases nd ih1 ih2)
      case ih1 from TFn ih1 show ?case by (rule infer_args.IH)
    next
      case ih2 from TFn show ?case by (rule infer_args.IH) (use ih2 in auto)
    qed (simp add: TFn)
  next
    case (TDep i sg m e t')
    have t': \<open>tsigs t' \<subseteq> X\<close> using T0 TDep by simp
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
      have s1: \<open>shyg s\<^sub>1 X\<close> by (rule uni_row_shyg[OF ur])
      have ph: \<open>tsigs (tsp K (zip K (map TV [n\<^sub>1 ..< n\<^sub>1 + m])) j) \<subseteq> X\<close> for j
        by (rule tsigs_tsp) (auto dest!: set_zip_rightD)
      have t0: \<open>tsigs (sapp s\<^sub>1 (kopen (tsp K (zip K (map TV [n\<^sub>1 ..< n\<^sub>1 + m]))) t')) \<subseteq> X\<close>
        by (rule tsigs_sapp[OF s1 tsigs_kopen_at[OF ph t']])
      have pd1: \<open>tsigs_pend
          ((imp_name n\<^sub>3, PImp K (map (apsnd (sapp s\<^sub>1)) (zip K (map TV [n\<^sub>1 ..< n\<^sub>1 + m])))
            E\<^sub>K (cands B) None) # sub_pend s\<^sub>1 pd) \<subseteq> X\<close>
        using tsigs_sub_pend[OF s1 P] tsigs_sapp[OF s1, of \<open>TV _\<close>]
        by (auto dest!: set_zip_rightD) blast
      have w2: \<open>shyg s\<^sub>2 X \<and> tsigs \<tau> \<subseteq> X \<and> tsigs_pend pd' \<subseteq> X\<close>
        using TDep True[THEN eqTrueI] d0 de refl refl not_not[THEN iffD2, OF kd] refl refl refl ur
          refl refl refl
          rec sigs_in_sappe[OF s1 B] pd1 t0
        by (rule infer_args.IH)
      show ?thesis using se shyg_scomp[OF s1 conjunct1[OF w2]] w2 by simp
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
          have s1: \<open>shyg s\<^sub>1 X\<close> by (rule uni_row_shyg[OF ur])
          have EP: \<open>tsigs_env E_P \<subseteq> X\<close>
            using sigs_in_tlookup[OF B tle] ec by (cases ent) auto
          have ph: \<open>tsigs (tsp K \<phi> j) \<subseteq> X\<close> for j by (rule tsigs_tsp[OF match_dep_tsigs[OF md EP]])
          have t0: \<open>tsigs (sapp s\<^sub>1 (kopen (tsp K \<phi>) t')) \<subseteq> X\<close>
            by (rule tsigs_sapp[OF s1 tsigs_kopen_at[OF ph t']])
          have w2: \<open>shyg s\<^sub>2 X \<and> tsigs \<tau> \<subseteq> X \<and> tsigs_pend pd' \<subseteq> X\<close>
            using TDep eq_False[THEN iffD2, OF False] Cons APath nr tle ec de refl refl
              not_not[THEN iffD2, OF kd] md enr ur
              refl rec sigs_in_sappe[OF s1 B] tsigs_sub_pend[OF s1 P] t0
            by (rule infer_args.IH)
          show ?thesis using se shyg_scomp[OF s1 conjunct1[OF w2]] w2 by simp
        qed (use E TDep False Cons in simp_all)
      qed
    qed
  next
    case (TOff x r t')
    from E TOff obtain as'' where
      rec: \<open>infer_args uf B A ((imp_name n, POff x r) # pd) d t' as (Suc n) = Some (s, as'', \<tau>, pd', n')\<close>
      by (auto simp del: infer_args.simps simp: infer_args_TOff Let_def bind_eq_Some_conv)
    have pd1: \<open>tsigs_pend ((imp_name n, POff x r) # pd) \<subseteq> X\<close> using P T0 TOff by simp
    have t': \<open>tsigs t' \<subseteq> X\<close> using T0 TOff by simp
    show ?thesis using TOff refl rec B pd1 t' by (rule infer_args.IH)
  next
    case (TEv l w ts)
    show ?thesis
    proof (rule infer_args_step_sigs[OF infer_args.prems], goal_cases nd ih1 ih2)
      case ih1 from TEv ih1 show ?case by (rule infer_args.IH)
    next
      case ih2 from TEv show ?case by (rule infer_args.IH) (use ih2 in auto)
    qed (simp add: TEv)

  next
    case (TAct lt K e t)
    show ?thesis
    proof (rule infer_args_step_sigs[OF infer_args.prems], goal_cases nd ih1 ih2)
      case ih1 from TAct ih1 show ?case by (rule infer_args.IH)
    next
      case ih2 from TAct show ?case by (rule infer_args.IH) (use ih2 in auto)
    qed (simp add: TAct)
  next
    case TRNil
    show ?thesis
    proof (rule infer_args_step_sigs[OF infer_args.prems], goal_cases nd ih1 ih2)
      case ih1 from TRNil ih1 show ?case by (rule infer_args.IH)
    next
      case ih2 from TRNil show ?case by (rule infer_args.IH) (use ih2 in auto)
    qed (simp add: TRNil)
  next
    case (TRCons lb t r)
    show ?thesis
    proof (rule infer_args_step_sigs[OF infer_args.prems], goal_cases nd ih1 ih2)
      case ih1 from TRCons ih1 show ?case by (rule infer_args.IH)
    next
      case ih2 from TRCons show ?case by (rule infer_args.IH) (use ih2 in auto)
    qed (simp add: TRCons)
  qed
next
  case (infer_exps_Cons uf B A pd e es n s es' \<tau>s pd' n')
  from infer_exps_Cons.prems have B: \<open>sigs_in B X\<close> and P: \<open>tsigs_pend pd \<subseteq> X\<close> by blast+
  from infer_exps_Cons.prems obtain s\<^sub>1 e'' \<tau> pd\<^sub>1 n\<^sub>1 s\<^sub>2 es'' \<tau>s' where
    d1: \<open>infer uf B A pd e n = Some (s\<^sub>1, e'', \<tau>, pd\<^sub>1, n\<^sub>1)\<close> and
    d2: \<open>infer_exps uf (sappe s\<^sub>1 B) (sappr s\<^sub>1 A) pd\<^sub>1 es n\<^sub>1 = Some (s\<^sub>2, es'', \<tau>s', pd', n')\<close> and
    se: \<open>s = s\<^sub>2 \<odot> s\<^sub>1\<close> \<open>\<tau>s = sapp s\<^sub>2 \<tau> # \<tau>s'\<close>
    by (auto split: Option.bind_split_asm prod.split_asm)
  have i1: \<open>shyg s\<^sub>1 X \<and> tsigs \<tau> \<subseteq> X \<and> tsigs_pend pd\<^sub>1 \<subseteq> X\<close>
    using d1 B P by (rule infer_exps_Cons.IH)
  have i2: \<open>shyg s\<^sub>2 X \<and> (\<forall>\<tau> \<in> set \<tau>s'. tsigs \<tau> \<subseteq> X) \<and> tsigs_pend pd' \<subseteq> X\<close>
    using d1 refl refl refl refl d2 sigs_in_sappe[OF conjunct1[OF i1] B]
      by (rule infer_exps_Cons.IH) (use i1 in simp_all)
  show ?case using shyg_scomp[OF conjunct1[OF i1] conjunct1[OF i2]] tsigs_sapp[OF conjunct1[OF i2]]
    i1 i2 se by simp
next
  case (infer_chain_EOp_Cons uf B A pd a as opr e n s e'x oprs \<tau>s pd' n')
  from infer_chain_EOp_Cons.prems have B: \<open>sigs_in B X\<close> and P: \<open>tsigs_pend pd \<subseteq> X\<close> by blast+
  from infer_chain_EOp_Cons.prems obtain s\<^sub>1 a'' \<tau>\<^sub>0 pd\<^sub>1 n\<^sub>1 s\<^sub>2 as'' \<tau> pd\<^sub>2 n\<^sub>2 where
    d1: \<open>infer_head uf B A pd a n = Some (s\<^sub>1, a'', \<tau>\<^sub>0, pd\<^sub>1, n\<^sub>1)\<close> and
    d2: \<open>infer_args uf (sappe s\<^sub>1 B) (sappr s\<^sub>1 A) pd\<^sub>1 uf \<tau>\<^sub>0 as n\<^sub>1 = Some (s\<^sub>2, as'', \<tau>, pd\<^sub>2, n\<^sub>2)\<close> and
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
  have w1: \<open>shyg s\<^sub>1 X \<and> tsigs \<tau>\<^sub>0 \<subseteq> X \<and> tsigs_pend pd\<^sub>1 \<subseteq> X\<close>
    using d1 B P by (rule infer_chain_EOp_Cons.IH)
  have w2: \<open>shyg s\<^sub>2 X \<and> tsigs \<tau> \<subseteq> X \<and> tsigs_pend pd\<^sub>2 \<subseteq> X\<close>
    using d1 refl refl refl refl d2 sigs_in_sappe[OF _ B]
      by (rule infer_chain_EOp_Cons.IH) (use w1 in simp_all)
  have s21: \<open>shyg (s\<^sub>2 \<odot> s\<^sub>1) X\<close> using w1 w2 by (simp add: shyg_scomp)
  show ?case
  proof (cases \<open>is_eop e\<close>)
    case True
    from R True obtain s\<^sub>3 e' oprs' \<tau>s' pd\<^sub>3 n\<^sub>3 where
      d3: \<open>infer_chain uf (sappe (s\<^sub>2 \<odot> s\<^sub>1) B) (sappr (s\<^sub>2 \<odot> s\<^sub>1) A) pd\<^sub>2 e n\<^sub>2
        = Some (s\<^sub>3, e', oprs', \<tau>s', pd\<^sub>3, n\<^sub>3)\<close> and
      se: \<open>s = s\<^sub>3 \<odot> (s\<^sub>2 \<odot> s\<^sub>1)\<close> \<open>\<tau>s = sapp s\<^sub>3 \<tau> # \<tau>s'\<close> \<open>pd' = pd\<^sub>3\<close>
      by (auto simp: bind_eq_Some_conv)
    have w3: \<open>shyg s\<^sub>3 X \<and> (\<forall>\<tau> \<in> set \<tau>s'. tsigs \<tau> \<subseteq> X) \<and> tsigs_pend pd\<^sub>3 \<subseteq> X\<close>
      using d1 refl refl refl refl d2 refl refl refl refl refl True d3 sigs_in_sappe[OF s21 B]
        by (rule infer_chain_EOp_Cons.IH)
         (use w2 in simp)
    show ?thesis using se shyg_scomp[OF s21 conjunct1[OF w3]] tsigs_sapp[OF conjunct1[OF w3]] w2 w3
      by simp
  next
    case False
    from R False obtain s\<^sub>3 e' \<tau>\<^sub>l pd\<^sub>3 n\<^sub>3 where
      d3: \<open>infer uf (sappe (s\<^sub>2 \<odot> s\<^sub>1) B) (sappr (s\<^sub>2 \<odot> s\<^sub>1) A) pd\<^sub>2 e n\<^sub>2
        = Some (s\<^sub>3, e', \<tau>\<^sub>l, pd\<^sub>3, n\<^sub>3)\<close> and
      se: \<open>s = s\<^sub>3 \<odot> (s\<^sub>2 \<odot> s\<^sub>1)\<close> \<open>\<tau>s = [sapp s\<^sub>3 \<tau>, \<tau>\<^sub>l]\<close> \<open>pd' = pd\<^sub>3\<close>
      by (auto simp: bind_eq_Some_conv)
    have w3: \<open>shyg s\<^sub>3 X \<and> tsigs \<tau>\<^sub>l \<subseteq> X \<and> tsigs_pend pd\<^sub>3 \<subseteq> X\<close>
      using d1 refl refl refl refl d2 refl refl refl refl refl False d3 sigs_in_sappe[OF s21 B]
        by (rule infer_chain_EOp_Cons.IH)
         (use w2 in simp)
    show ?thesis using se shyg_scomp[OF s21 conjunct1[OF w3]] tsigs_sapp[OF conjunct1[OF w3]] w2 w3
      by simp
  qed
next
  case (infer_arms_Cons uf B A pd \<tau>\<^sub>0 \<tau>\<^sub>r p b arms n s arms'x pd' n')
  from infer_arms_Cons.prems have B: \<open>sigs_in B X\<close>
    and P: \<open>tsigs_pend pd \<subseteq> X\<close>
    and T0: \<open>tsigs \<tau>\<^sub>0 \<subseteq> X\<close>
    and Tr: \<open>tsigs \<tau>\<^sub>r \<subseteq> X\<close> by blast+
  from infer_arms_Cons.prems obtain sp \<tau>\<^sub>p \<Gamma> n\<^sub>1 s\<^sub>1 n\<^sub>2 s\<^sub>2 b'' \<tau>\<^sub>b pd\<^sub>2 n\<^sub>3
    s\<^sub>3 n\<^sub>4 s\<^sub>4 arms'' p\<^sub>x where
    dp: \<open>infer_pat uf B p n = Some (sp, p\<^sub>x, \<tau>\<^sub>p, \<Gamma>, n\<^sub>1)\<close> and
    u1: \<open>uni uf (sapp sp \<tau>\<^sub>0) \<tau>\<^sub>p n\<^sub>1 = Some (s\<^sub>1, n\<^sub>2)\<close> and
    db: \<open>infer uf (mono_env s\<^sub>1 \<Gamma> @ sappe (s\<^sub>1 \<odot> sp) B) (sappr (s\<^sub>1 \<odot> sp) A)
           (sub_pend (s\<^sub>1 \<odot> sp) pd) b n\<^sub>2 = Some (s\<^sub>2, b'', \<tau>\<^sub>b, pd\<^sub>2, n\<^sub>3)\<close> and
    u2: \<open>uni uf \<tau>\<^sub>b (sapp (s\<^sub>2 \<odot> (s\<^sub>1 \<odot> sp)) \<tau>\<^sub>r) n\<^sub>3 = Some (s\<^sub>3, n\<^sub>4)\<close> and
    da: \<open>infer_arms uf (sappe (s\<^sub>3 \<odot> s\<^sub>2 \<odot> (s\<^sub>1 \<odot> sp)) B) (sappr (s\<^sub>3 \<odot> s\<^sub>2 \<odot> (s\<^sub>1 \<odot> sp)) A)
           (sub_pend s\<^sub>3 pd\<^sub>2) (sapp (s\<^sub>3 \<odot> s\<^sub>2 \<odot> (s\<^sub>1 \<odot> sp)) \<tau>\<^sub>0) (sapp (s\<^sub>3 \<odot> s\<^sub>2 \<odot> (s\<^sub>1 \<odot> sp)) \<tau>\<^sub>r)
           arms n\<^sub>4 = Some (s\<^sub>4, arms'', pd', n')\<close> and
    se: \<open>s = s\<^sub>4 \<odot> (s\<^sub>3 \<odot> s\<^sub>2 \<odot> (s\<^sub>1 \<odot> sp))\<close>
    by (auto simp: Let_def bind_eq_Some_conv)
  have p: \<open>shyg sp X \<and> tsigs \<tau>\<^sub>p \<subseteq> X \<and> tsigs_bs \<Gamma> \<subseteq> X\<close> by (rule infer_pat_sigs(1)[OF dp B])
  have s1: \<open>shyg s\<^sub>1 X\<close> by (rule uni_shyg[OF u1]) (use p tsigs_sapp[OF _ T0] in simp_all)
  have s1p: \<open>shyg (s\<^sub>1 \<odot> sp) X\<close> using p s1 by (simp add: shyg_scomp)
  have ib: \<open>sigs_in (mono_env s\<^sub>1 \<Gamma> @ sappe (s\<^sub>1 \<odot> sp) B) X\<close>
    using sigs_in_mono_env[OF s1] sigs_in_sappe[OF s1p B] p by simp
  have wb: \<open>shyg s\<^sub>2 X \<and> tsigs \<tau>\<^sub>b \<subseteq> X \<and> tsigs_pend pd\<^sub>2 \<subseteq> X\<close>
    using dp refl refl refl refl u1 refl refl db ib
      by (rule infer_arms_Cons.IH) (use tsigs_sub_pend[OF s1p P] in simp)
  have s21: \<open>shyg (s\<^sub>2 \<odot> (s\<^sub>1 \<odot> sp)) X\<close> using s1p wb by (simp add: shyg_scomp)
  have s3: \<open>shyg s\<^sub>3 X\<close> by (rule uni_shyg[OF u2]) (use wb tsigs_sapp[OF s21 Tr] in simp_all)
  have s321: \<open>shyg (s\<^sub>3 \<odot> s\<^sub>2 \<odot> (s\<^sub>1 \<odot> sp)) X\<close> using s1p wb s3 by (simp add: shyg_scomp)
  have wa: \<open>shyg s\<^sub>4 X \<and> tsigs_pend pd' \<subseteq> X\<close>
    using dp refl refl refl refl u1 refl refl db refl refl refl refl u2 refl refl da
      sigs_in_sappe[OF s321 B]
    by (rule infer_arms_Cons.IH)
      (use tsigs_sub_pend[OF s3] wb tsigs_sapp[OF s321 T0] tsigs_sapp[OF s321 Tr] in simp_all)
  show ?case using se shyg_scomp[OF s321 conjunct1[OF wa]] wa by simp
next
  case (infer_cls_Cons_HOp uf B A pd nm \<tau>\<^sub>0 targs opn ps k b cls n s cls'x \<tau> pd' n')
  from infer_cls_Cons_HOp.prems have B: \<open>sigs_in B X\<close>
    and P: \<open>tsigs_pend pd \<subseteq> X\<close>
    and T0: \<open>tsigs \<tau>\<^sub>0 \<subseteq> X\<close>
    and Targs: \<open>tsigs targs \<subseteq> X\<close> by blast+
  define eps where \<open>eps sq = (if nm then sappr sq A else canon_row
    (rext (hlabels B cls) (sappr sq A)))\<close> for sq
  have \<open>\<exists>l ps\<^sub>e \<tau>\<^sub>1\<^sub>0 \<tau>\<^sub>2\<^sub>0 args. tlookup B [n_txt opn] = Some (TEop l ps\<^sub>e \<tau>\<^sub>1\<^sub>0 \<tau>\<^sub>2\<^sub>0) \<and>
          untuple targs = Some args \<and> length args = length ps\<^sub>e\<close>
    using infer_cls_Cons_HOp.prems
    by (cases \<open>tlookup B [n_txt opn]\<close>; cases \<open>untuple targs\<close>;
        simp split: tentry.split_asm if_split_asm)
  then obtain l ps\<^sub>e \<tau>\<^sub>1\<^sub>0 \<tau>\<^sub>2\<^sub>0 args where lk: \<open>tlookup B [n_txt opn] = Some (TEop l ps\<^sub>e \<tau>\<^sub>1\<^sub>0 \<tau>\<^sub>2\<^sub>0)\<close>
    and ta: \<open>untuple targs = Some args\<close> and lc: \<open>length args = length ps\<^sub>e\<close>
      by blast
  have ta': \<open>targs = tuple args\<close> using ta by simp
  define \<tau>\<^sub>1 where \<open>\<tau>\<^sub>1 = op_inst ps\<^sub>e args \<tau>\<^sub>1\<^sub>0\<close>
  define \<tau>\<^sub>2 where \<open>\<tau>\<^sub>2 = op_inst ps\<^sub>e args \<tau>\<^sub>2\<^sub>0\<close>
  have lkm: \<open>map_of B (n_txt opn) = Some (TEop l ps\<^sub>e \<tau>\<^sub>1\<^sub>0 \<tau>\<^sub>2\<^sub>0)\<close> using lk by simp
  from infer_cls_Cons_HOp.prems obtain sp \<tau>s \<Gamma> n\<^sub>1 s\<^sub>1 n\<^sub>2 s\<^sub>2 b'' \<tau>\<^sub>b pd\<^sub>2 n\<^sub>3
    s\<^sub>3 n\<^sub>4 s\<^sub>4 cls'' ps\<^sub>x where
    dps: \<open>infer_pats uf B ps n = Some (sp, ps\<^sub>x, \<tau>s, \<Gamma>, n\<^sub>1)\<close> and
    u1: \<open>uni uf (fn_ty \<tau>s) (sapp sp \<tau>\<^sub>1) n\<^sub>1 = Some (s\<^sub>1, n\<^sub>2)\<close> and
    db: \<open>infer uf ((case k of None \<Rightarrow> mono_env s\<^sub>1 \<Gamma>
            | Some kn \<Rightarrow> (n_txt kn, TEval (kmono (TFn (sapp (s\<^sub>1 \<odot> sp) \<tau>\<^sub>2) (eps (s\<^sub>1 \<odot> sp))
                            (sapp (s\<^sub>1 \<odot> sp) \<tau>\<^sub>0)))) # mono_env s\<^sub>1 \<Gamma>) @ sappe (s\<^sub>1 \<odot> sp) B)
            (eps (s\<^sub>1 \<odot> sp)) (sub_pend (s\<^sub>1 \<odot> sp) pd) b n\<^sub>2 = Some (s\<^sub>2, b'', \<tau>\<^sub>b, pd\<^sub>2, n\<^sub>3)\<close> and
    u2: \<open>uni uf \<tau>\<^sub>b (case k of None \<Rightarrow> sapp (s\<^sub>2 \<odot> (s\<^sub>1 \<odot> sp)) \<tau>\<^sub>2
            | Some _ \<Rightarrow> sapp s\<^sub>2 (sapp (s\<^sub>1 \<odot> sp) \<tau>\<^sub>0)) n\<^sub>3 = Some (s\<^sub>3, n\<^sub>4)\<close> and
    dc: \<open>infer_cls uf (sappe (s\<^sub>3 \<odot> s\<^sub>2 \<odot> (s\<^sub>1 \<odot> sp)) B) (sappr (s\<^sub>3 \<odot> s\<^sub>2 \<odot> (s\<^sub>1 \<odot> sp)) A)
            (sub_pend s\<^sub>3 pd\<^sub>2) nm (sapp (s\<^sub>3 \<odot> s\<^sub>2 \<odot> (s\<^sub>1 \<odot> sp)) \<tau>\<^sub>0) (sapp (s\<^sub>3 \<odot> s\<^sub>2 \<odot> (s\<^sub>1 \<odot> sp)) targs)
              cls n\<^sub>4
            = Some (s\<^sub>4, cls'', \<tau>, pd', n')\<close> and
    se: \<open>s = s\<^sub>4 \<odot> (s\<^sub>3 \<odot> s\<^sub>2 \<odot> (s\<^sub>1 \<odot> sp))\<close>
    by (auto simp: lkm ta ta' lc eps_def[symmetric] \<tau>\<^sub>1_def[symmetric] \<tau>\<^sub>2_def[symmetric] Let_def
                   bind_eq_Some_conv split: if_split_asm)
  have covk: \<open>covers (sappe (s\<^sub>1 \<odot> sp) B) (sapp s\<^sub>1 (fn_ty \<tau>s)) [fn_pat ps]
    \<and> (case k of None \<Rightarrow> True | Some kn \<Rightarrow> n_txt kn \<notin> set (map fst \<Gamma>) \<and> nm_ok (n_txt kn))\<close>
    using infer_cls_Cons_HOp.prems
    by (simp add: lkm ta ta' lc dps u1 \<tau>\<^sub>1_def[symmetric] \<tau>\<^sub>2_def[symmetric] Let_def
             split: if_split_asm)
  have ar: \<open>\<forall>t \<in> set args. tsigs t \<subseteq> X\<close> using Targs ta' by auto
  have o: \<open>tsigs \<tau>\<^sub>1 \<subseteq> X\<close> \<open>tsigs \<tau>\<^sub>2 \<subseteq> X\<close>
    using sigs_in_tlookup[OF B lk] ar by (simp_all add: \<tau>\<^sub>1_def \<tau>\<^sub>2_def tsigs_op_inst)
  have p: \<open>shyg sp X \<and> (\<forall>\<tau> \<in> set \<tau>s. tsigs \<tau> \<subseteq> X) \<and> tsigs_bs \<Gamma> \<subseteq> X\<close>
    by (rule infer_pat_sigs(4)[OF dps B])
  have s1: \<open>shyg s\<^sub>1 X\<close> by (rule uni_shyg[OF u1])
    (use p tsigs_sapp[OF _ o(1)] in \<open>auto simp: tsigs_fn_ty\<close>)
  have s1p: \<open>shyg (s\<^sub>1 \<odot> sp) X\<close> using p s1 by (simp add: shyg_scomp)
  have G: \<open>sigs_in (case k of None \<Rightarrow> mono_env s\<^sub>1 \<Gamma>
            | Some kn \<Rightarrow> (n_txt kn, TEval (kmono (TFn (sapp (s\<^sub>1 \<odot> sp) \<tau>\<^sub>2) (eps (s\<^sub>1 \<odot> sp))
                            (sapp (s\<^sub>1 \<odot> sp) \<tau>\<^sub>0)))) # mono_env s\<^sub>1 \<Gamma>) X\<close>
    using sigs_in_mono_env[OF s1] p tsigs_sapp[OF s1p o(2)] tsigs_sapp[OF s1p T0]
    by (cases k) simp_all
  have ib: \<open>sigs_in ((case k of None \<Rightarrow> mono_env s\<^sub>1 \<Gamma>
            | Some kn \<Rightarrow> (n_txt kn, TEval (kmono (TFn (sapp (s\<^sub>1 \<odot> sp) \<tau>\<^sub>2) (eps (s\<^sub>1 \<odot> sp))
                            (sapp (s\<^sub>1 \<odot> sp) \<tau>\<^sub>0)))) # mono_env s\<^sub>1 \<Gamma>) @ sappe (s\<^sub>1 \<odot> sp) B) X\<close>
    using G sigs_in_sappe[OF s1p B] by simp
  have wb: \<open>shyg s\<^sub>2 X \<and> tsigs \<tau>\<^sub>b \<subseteq> X \<and> tsigs_pend pd\<^sub>2 \<subseteq> X\<close>
    using refl lk refl ta lc \<tau>\<^sub>1_def \<tau>\<^sub>2_def dps refl refl refl refl u1 refl refl refl eps_def
      refl refl covk db ib
    by (rule infer_cls_Cons_HOp.IH) (use tsigs_sub_pend[OF s1p P] in simp)
  have s21: \<open>shyg (s\<^sub>2 \<odot> (s\<^sub>1 \<odot> sp)) X\<close> using s1p wb by (simp add: shyg_scomp)
  have s3: \<open>shyg s\<^sub>3 X\<close>
    by (rule uni_shyg[OF u2]) (use wb tsigs_sapp[OF s21 o(2)]
      tsigs_sapp[OF conjunct1[OF wb] tsigs_sapp[OF s1p T0]] in \<open>simp_all split: option.split\<close>)
  have s321: \<open>shyg (s\<^sub>3 \<odot> s\<^sub>2 \<odot> (s\<^sub>1 \<odot> sp)) X\<close> using s1p wb s3 by (simp add: shyg_scomp)
  have wc: \<open>shyg s\<^sub>4 X \<and> tsigs \<tau> \<subseteq> X \<and> tsigs_pend pd' \<subseteq> X\<close>
    using refl lk refl ta lc \<tau>\<^sub>1_def \<tau>\<^sub>2_def dps refl refl refl refl u1 refl refl refl eps_def
      refl refl covk db refl refl refl refl u2 refl refl dc sigs_in_sappe[OF s321 B]
    by (rule infer_cls_Cons_HOp.IH)
      (use tsigs_sub_pend[OF s3] wb tsigs_sapp[OF s321 T0] tsigs_sapp[OF s321 Targs] in simp_all)
  show ?case using se s321 wc by (simp add: shyg_scomp)
next
  case (infer_cls_Cons_HFin uf B A pd nm \<tau>\<^sub>0 targs b cls n s cls'x \<tau> pd' n')
  from infer_cls_Cons_HFin.prems have B: \<open>sigs_in B X\<close>
    and P: \<open>tsigs_pend pd \<subseteq> X\<close>
    and T0: \<open>tsigs \<tau>\<^sub>0 \<subseteq> X\<close>
    and Targs: \<open>tsigs targs \<subseteq> X\<close> by blast+
  from infer_cls_Cons_HFin.prems obtain s\<^sub>1 b'' \<tau>\<^sub>f pd\<^sub>1 n\<^sub>1 s\<^sub>2 n\<^sub>2 s\<^sub>3 cls'' where
    d1: \<open>infer uf B A pd b n = Some (s\<^sub>1, b'', \<tau>\<^sub>f, pd\<^sub>1, n\<^sub>1)\<close> and
    u1: \<open>uni uf \<tau>\<^sub>f unit_ty n\<^sub>1 = Some (s\<^sub>2, n\<^sub>2)\<close> and
    dc: \<open>infer_cls uf (sappe (s\<^sub>2 \<odot> s\<^sub>1) B) (sappr (s\<^sub>2 \<odot> s\<^sub>1) A) (sub_pend s\<^sub>2 pd\<^sub>1) nm
           (sapp (s\<^sub>2 \<odot> s\<^sub>1) \<tau>\<^sub>0) (sapp (s\<^sub>2 \<odot> s\<^sub>1) targs) cls n\<^sub>2
           = Some (s\<^sub>3, cls'', \<tau>, pd', n')\<close> and
    se: \<open>s = s\<^sub>3 \<odot> (s\<^sub>2 \<odot> s\<^sub>1)\<close>
    by (auto simp: Let_def bind_eq_Some_conv)
  have i1: \<open>shyg s\<^sub>1 X \<and> tsigs \<tau>\<^sub>f \<subseteq> X \<and> tsigs_pend pd\<^sub>1 \<subseteq> X\<close>
    using d1 B P by (rule infer_cls_Cons_HFin.IH)
  have s2: \<open>shyg s\<^sub>2 X\<close> by (rule uni_shyg[OF u1]) (use i1 in simp_all)
  have s21: \<open>shyg (s\<^sub>2 \<odot> s\<^sub>1) X\<close> using i1 s2 by (simp add: shyg_scomp)
  have wc: \<open>shyg s\<^sub>3 X \<and> tsigs \<tau> \<subseteq> X \<and> tsigs_pend pd' \<subseteq> X\<close>
    using d1 refl refl refl refl u1 refl refl dc sigs_in_sappe[OF s21 B]
    by (rule infer_cls_Cons_HFin.IH)
       (use tsigs_sub_pend[OF s2] i1 tsigs_sapp[OF s21 T0] tsigs_sapp[OF s21 Targs] in simp_all)
  show ?case using se s21 wc by (simp add: shyg_scomp)
next
  case (infer_cls_Cons_HRet uf B A pd nm \<tau>\<^sub>0 targs p b cls n s cls'x \<tau> pd' n')
  from infer_cls_Cons_HRet.prems have B: \<open>sigs_in B X\<close>
    and P: \<open>tsigs_pend pd \<subseteq> X\<close>
    and T0: \<open>tsigs \<tau>\<^sub>0 \<subseteq> X\<close>
    and Targs: \<open>tsigs targs \<subseteq> X\<close> by blast+
  define eps where \<open>eps sq = (if nm then sappr sq A else canon_row
    (rext (hlabels B cls) (sappr sq A)))\<close> for sq
  from infer_cls_Cons_HRet.prems obtain sp \<tau>\<^sub>p \<Gamma> n\<^sub>1 s\<^sub>1 n\<^sub>2 s\<^sub>2 b'' \<tau>' pd\<^sub>2 n\<^sub>3 s\<^sub>3 cls'' p\<^sub>x where
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
    using infer_cls_Cons_HRet.prems by (simp add: dp u1 Let_def split: if_split_asm del: sapp.simps
      sappe.simps sappr.simps sapps.simps)
  have pp: \<open>shyg sp X \<and> tsigs \<tau>\<^sub>p \<subseteq> X \<and> tsigs_bs \<Gamma> \<subseteq> X\<close> by (rule infer_pat_sigs(1)[OF dp B])
  have s1: \<open>shyg s\<^sub>1 X\<close> by (rule uni_shyg[OF u1]) (use pp tsigs_sapp[OF _ T0] in simp_all)
  have s1p: \<open>shyg (s\<^sub>1 \<odot> sp) X\<close> using pp s1 by (simp add: shyg_scomp)
  have ib: \<open>sigs_in (mono_env s\<^sub>1 \<Gamma> @ sappe (s\<^sub>1 \<odot> sp) B) X\<close>
    using sigs_in_mono_env[OF s1] sigs_in_sappe[OF s1p B] pp by simp
  have wb: \<open>shyg s\<^sub>2 X \<and> tsigs \<tau>' \<subseteq> X \<and> tsigs_pend pd\<^sub>2 \<subseteq> X\<close>
    using dp refl refl refl refl u1 refl refl refl eps_def covn db ib
    by (rule infer_cls_Cons_HRet.IH) (use tsigs_sub_pend[OF s1p P] in simp)
  have s21: \<open>shyg (s\<^sub>2 \<odot> (s\<^sub>1 \<odot> sp)) X\<close> using s1p wb by (simp add: shyg_scomp)
  have wc: \<open>shyg s\<^sub>3 X \<and> tsigs \<tau> \<subseteq> X \<and> tsigs_pend pd' \<subseteq> X\<close>
    using dp refl refl refl refl u1 refl refl refl eps_def covn db refl refl refl refl refl dc
      sigs_in_sappe[OF s21 B]
    by (rule infer_cls_Cons_HRet.IH) (use wb tsigs_sapp[OF s21 Targs] in simp_all)
  show ?case using se s21 wc by (simp add: shyg_scomp)
next
  case (infer_EWith uf B A pd x h e n s e' \<tau> pd' n')
  from infer_EWith.prems have B: \<open>sigs_in B X\<close> and P: \<open>tsigs_pend pd \<subseteq> X\<close> by blast+
  from infer_EWith.prems obtain s\<^sub>1 h' \<tau>\<^sub>h pd\<^sub>1 n\<^sub>1 s\<^sub>2 \<tau>\<^sub>a pd\<^sub>2 n\<^sub>3
      s\<^sub>b e'' \<tau>\<^sub>b pd\<^sub>b n\<^sub>b s\<^sub>4 n\<^sub>5 where
    d1: \<open>infer uf B A pd h n = Some (s\<^sub>1, h', \<tau>\<^sub>h, pd\<^sub>1, n\<^sub>1)\<close> and
    kn: \<open>n\<^sub>1 \<notin> ktv_env (sappe s\<^sub>1 B)\<close> and nm: \<open>nm_ok (n_txt x)\<close> and
    ap: \<open>app_arg uf (sappe s\<^sub>1 B) (sappr s\<^sub>1 A) pd\<^sub>1 \<tau>\<^sub>h
           (TAct (TV (Suc n\<^sub>1)) [n\<^sub>1] (RV (Suc (Suc (Suc n\<^sub>1)))) (TV (Suc (Suc (Suc (Suc n\<^sub>1))))))
           (Suc (Suc (Suc (Suc (Suc n\<^sub>1))))) = Some (s\<^sub>2, \<tau>\<^sub>a, pd\<^sub>2, n\<^sub>3)\<close> and
    ib: \<open>infer uf (name_env (sappe s\<^sub>2 (sappe s\<^sub>1 B)) (n_txt x) (sapp s\<^sub>2 (TV (Suc n\<^sub>1))) @
           (n_txt x, TEval (kmono (TEv (sapp s\<^sub>2 (TV (Suc n\<^sub>1))) (TK n\<^sub>1)
             (sapp s\<^sub>2 (TV (Suc (Suc n\<^sub>1))))))) # sappe s\<^sub>2 (sappe s\<^sub>1 B))
           (sappr s\<^sub>2 (RV (Suc (Suc (Suc n\<^sub>1))))) pd\<^sub>2 e n\<^sub>3 = Some (s\<^sub>b, e'', \<tau>\<^sub>b, pd\<^sub>b, n\<^sub>b)\<close> and
    un: \<open>uni uf (sapp (s\<^sub>b \<odot> s\<^sub>2) (TV (Suc (Suc (Suc (Suc n\<^sub>1)))))) \<tau>\<^sub>b n\<^sub>b = Some (s\<^sub>4, n\<^sub>5)\<close> and
    se: \<open>s = sproj n\<^sub>3 (s\<^sub>4 \<odot> s\<^sub>b) \<odot> s\<^sub>2 \<odot> s\<^sub>1\<close> and
    te: \<open>\<tau> = sapp (sproj n\<^sub>3 (s\<^sub>4 \<odot> s\<^sub>b)) \<tau>\<^sub>a\<close> and pe: \<open>pd' = sub_pend s\<^sub>4 pd\<^sub>b\<close>
    by (auto simp: Let_def bind_eq_Some_conv split: prod.split_asm if_split_asm)
  have w1: \<open>shyg s\<^sub>1 X \<and> tsigs \<tau>\<^sub>h \<subseteq> X \<and> tsigs_pend pd\<^sub>1 \<subseteq> X\<close>
    using d1 B P by (rule infer_EWith.IH)
  have s1: \<open>shyg s\<^sub>1 X\<close> using w1 by blast
  have w2: \<open>shyg s\<^sub>2 X \<and> tsigs \<tau>\<^sub>a \<subseteq> X \<and> tsigs_pend pd\<^sub>2 \<subseteq> X\<close>
    by (rule app_arg_sigs[OF ap]) (use w1 in auto)
  have s2: \<open>shyg s\<^sub>2 X\<close> using w2 by blast
  have B2: \<open>sigs_in (name_env (sappe s\<^sub>2 (sappe s\<^sub>1 B)) (n_txt x) (sapp s\<^sub>2 (TV (Suc n\<^sub>1))) @
      (n_txt x, TEval (kmono (TEv (sapp s\<^sub>2 (TV (Suc n\<^sub>1))) (TK n\<^sub>1)
        (sapp s\<^sub>2 (TV (Suc (Suc n\<^sub>1))))))) # sappe s\<^sub>2 (sappe s\<^sub>1 B)) X\<close>
    using sigs_in_sappe[OF s2 sigs_in_sappe[OF s1 B]] tsigs_sapp[OF s2]
    by (cases rule: name_env_cases[of \<open>sappe s\<^sub>2 (sappe s\<^sub>1 B)\<close> \<open>n_txt x\<close>
        \<open>sapp s\<^sub>2 (TV (Suc n\<^sub>1))\<close>]) simp_all
  have wb: \<open>shyg s\<^sub>b X \<and> tsigs \<tau>\<^sub>b \<subseteq> X \<and> tsigs_pend pd\<^sub>b \<subseteq> X\<close>
    by (rule infer_EWith.IH) (use d1 kn nm ap ib B2 w1 w2 in auto)
  have s4: \<open>shyg s\<^sub>4 X\<close>
    by (rule uni_shyg[OF un]) (use wb s2 tsigs_sapp in \<open>simp_all add: shyg_scomp\<close>)
  have sp: \<open>shyg (sproj n\<^sub>3 (s\<^sub>4 \<odot> s\<^sub>b)) X\<close> using s4 wb by (simp add: shyg_sproj shyg_scomp)
  show ?case
    using se te pe sp s1 s2 w2 tsigs_sapp[OF sp] tsigs_sub_pend[OF s4] wb s4
    by (simp add: shyg_scomp)
next
  case (infer_EHandlerN uf B A pd cls n s e' \<tau> pd' n')
  from infer_EHandlerN.prems have B: \<open>sigs_in B X\<close> and P: \<open>tsigs_pend pd \<subseteq> X\<close> by blast+
  from infer_EHandlerN.prems obtain lbl rest l ls ar cls'' \<tau>c where
    hl: \<open>hlabels B cls = lbl # rest\<close> and eo: \<open>eff_of_op B lbl = Some (l, ls, ar)\<close> and
    cd: \<open>set (hlabels B cls) = set (map (mangle l) ls)\<close> and
    kn: \<open>n + ar \<notin> ktv_env B\<close> and
    dc: \<open>infer_cls uf B (RV (Suc (n + ar))) pd True (TV (Suc (Suc (n + ar))))
      (tuple (map TV [n ..< n + ar])) cls
           (Suc (Suc (Suc (n + ar)))) = Some (s, cls'', \<tau>c, pd', n')\<close> and
    te: \<open>\<tau> = TFn (TAct (eff_ty l (map (sapp s) (map TV [n ..< n + ar]))) [n + ar]
             (canon_row (rext (map (nlbl \<circ> mangle l) ls) (sappr s (RV (Suc (n + ar))))))
               (sapp s (TV (Suc (Suc (n + ar))))))
             (sappr s (RV (Suc (n + ar)))) \<tau>c\<close>
    by (auto simp: Let_def bind_eq_Some_conv split: list.split_asm option.split_asm if_split_asm
      prod.split_asm)
  have i: \<open>shyg s X \<and> tsigs \<tau>c \<subseteq> X \<and> tsigs_pend pd' \<subseteq> X\<close>
    by (rule infer_EHandlerN.IH) (use hl eo cd kn dc B P in auto)
  have a: \<open>\<forall>t \<in> set (map (sapp s) (map TV [n ..< n + ar])). tsigs t \<subseteq> X\<close>
    using tsigs_sapp[OF conjunct1[OF i]] by auto
  show ?case using i te a tsigs_sapp[of s X \<open>TV (Suc (Suc (n + ar)))\<close>] by auto
next
  case infer_head_APath
  show ?case by (rule hpath_sigs) (use infer_head_APath.prems in simp_all)
next
  case infer_atom_APath
  from infer_atom_APath.prems show ?case by (rule apath_sigs)
next
  case (infer_atom_ARec uf B A pd fs n s a' \<tau> pd' n')
  from infer_atom_ARec.prems have B: \<open>sigs_in B X\<close> and P: \<open>tsigs_pend pd \<subseteq> X\<close> by blast+
  from infer_atom_ARec.prems obtain es'' \<tau>s where
    d: \<open>infer_exps uf B A pd (map snd fs) n = Some (s, es'', \<tau>s, pd', n')\<close> and
    te: \<open>\<tau> = rec_of (zip (map (n_txt \<circ> fst) fs) \<tau>s) TRNil\<close>
    by (auto split: Option.bind_split_asm prod.split_asm if_split_asm)
  have i: \<open>shyg s X \<and> (\<forall>\<tau> \<in> set \<tau>s. tsigs \<tau> \<subseteq> X) \<and> tsigs_pend pd' \<subseteq> X\<close>
    by (rule infer_atom_ARec.IH[OF _ d B P])
      (use infer_atom_ARec.prems in \<open>auto split: if_split_asm\<close>)
  show ?case using i te by (fastforce simp: tsigs_rec_of dest: set_zip_rightD)
next
  case (infer_atom_ADot uf B A pd a x n s a' \<tau> pd' n')
  from infer_atom_ADot.prems have B: \<open>sigs_in B X\<close> and P: \<open>tsigs_pend pd \<subseteq> X\<close> by blast+
  from infer_atom_ADot.prems obtain s\<^sub>1 a'' \<tau>\<^sub>a pd\<^sub>1 n\<^sub>1 s\<^sub>2 n\<^sub>2 where
    d1: \<open>infer_atom uf B A pd a n = Some (s\<^sub>1, a'', \<tau>\<^sub>a, pd\<^sub>1, n\<^sub>1)\<close> and
    un: \<open>uni uf \<tau>\<^sub>a (TRCons (n_txt x) (TV n\<^sub>1) (TV (Suc n\<^sub>1))) (n\<^sub>1 + 2) = Some (s\<^sub>2, n\<^sub>2)\<close> and
    se: \<open>s = s\<^sub>2 \<odot> s\<^sub>1\<close> \<open>\<tau> = sapp s\<^sub>2 (TV n\<^sub>1)\<close> and
    pe: \<open>pd' = (imp_name n\<^sub>2, POff (n_txt x) (sapp s\<^sub>2 (TRCons (n_txt x) (TV n\<^sub>1) (TV (Suc n\<^sub>1)))))
        # sub_pend s\<^sub>2 pd\<^sub>1\<close>
    by (auto simp: bind_eq_Some_conv Let_def)
  have i: \<open>shyg s\<^sub>1 X \<and> tsigs \<tau>\<^sub>a \<subseteq> X \<and> tsigs_pend pd\<^sub>1 \<subseteq> X\<close>
    by (rule infer_atom_ADot.IH[OF d1 B P])
  have s2: \<open>shyg s\<^sub>2 X\<close> by (rule uni_shyg[OF un]) (use i in auto)
  have r: \<open>tsigs (sapp s\<^sub>2 (TRCons (n_txt x) (TV n\<^sub>1) (TV (Suc n\<^sub>1)))) \<subseteq> X\<close>
    by (rule tsigs_sapp[OF s2]) simp
  show ?case using se pe shyg_scomp[OF conjunct1[OF i] s2] tsigs_sapp[of s\<^sub>2 X \<open>TV n\<^sub>1\<close>] s2 r
    tsigs_sub_pend[OF s2] i by simp
qed (auto split: Option.bind_split_asm prod.split_asm if_split_asm)


end
