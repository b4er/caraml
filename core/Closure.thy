theory Closure
  imports Bigstep
begin

section \<open>Closure conversion: a closure needs only its free variables\<close>

text \<open>The evaluator captures the \<^emph>\<open>entire\<close> ambient environment at every
  \<^const>\<open>Clam\<close> and \<^const>\<open>Cletrec\<close>, closure conversion trims that
  capture to the body's free variables.

  Trimming changes closure values, so results are compared up to \<^emph>\<open>closure agreement\<close>:
  two closures agree when their captured environments agree, recursively, on the free
  variables their bodies read.\<close>

subsection \<open>Free variables and pattern binders\<close>

fun pvars :: \<open>cpat \<Rightarrow> name set\<close>
and pvars_list :: \<open>cpat list \<Rightarrow> name set\<close> where
  \<open>pvars CPany = {}\<close>
| \<open>pvars (CPvar x) = {x}\<close>
| \<open>pvars (CPlit _) = {}\<close>
| \<open>pvars (CPcon c ps) = pvars_list ps\<close>
| \<open>pvars (CPas x p) = insert x (pvars p)\<close>
| \<open>pvars_list [] = {}\<close>
| \<open>pvars_list (p # ps) = pvars p \<union> pvars_list ps\<close>

fun fv :: \<open>cexp \<Rightarrow> name set\<close>
and fv_list :: \<open>cexp list \<Rightarrow> name set\<close>
and fv_arms :: \<open>(cpat \<times> cexp) list \<Rightarrow> name set\<close> where
  \<open>fv (Cvar x) = {x}\<close>
| \<open>fv (Clit _) = {}\<close>
| \<open>fv (Clam x b) = fv b - {x}\<close>
| \<open>fv (Capp f a) = fv f \<union> fv a\<close>
| \<open>fv (Clet x e b) = fv e \<union> (fv b - {x})\<close>
| \<open>fv (Cletrec f x e b) = (fv e - {f, x}) \<union> (fv b - {f})\<close>
| \<open>fv (Ccon c es) = fv_list es\<close>
| \<open>fv (Cmatch e cls) = fv e \<union> fv_arms cls\<close>
| \<open>fv (Cperform l a) = fv a\<close>
| \<open>fv (Chandle l h b) = fv h \<union> fv b\<close>
| \<open>fv (Cmask l e) = fv e\<close>
| \<open>fv (Cperformn x op a) = fv x \<union> fv a\<close>
| \<open>fv (Chandlen l h \<phi> b) = fv h \<union> fv b\<close>
| \<open>fv_list [] = {}\<close>
| \<open>fv_list (e # es) = fv e \<union> fv_list es\<close>
| \<open>fv_arms [] = {}\<close>
| \<open>fv_arms ((p, e) # cls) = (fv e - pvars p) \<union> fv_arms cls\<close>

text \<open>The binders a successful pattern match introduces are exactly
  \<^const>\<open>pvars\<close>:\<close>

lemma cpmatch_dom: \<open>cpmatch p v = Some bs \<Longrightarrow> set (map fst bs) = pvars p\<close>
  and cpmatch_list_dom:
    \<open>cpmatch_list ps vs = Some bss \<Longrightarrow> set (map fst bss) = pvars_list ps\<close>
  by (induction p v and ps vs arbitrary: bs and bss rule: cpmatch_induct)
     (clarsimp simp: image_Un split: if_split_asm option.split_asm)+

subsection \<open>Closure agreement\<close>

text \<open>Two values agree, \<^text>\<open>\<approx>\<^sub>v\<close>, when they are structurally equal
  except that captured environments need only agree, recursively, on the free
  variables the captured code reads. Frames agree similarly,
  \<^text>\<open>\<approx>\<^sub>f\<close> (continuations carry frames, frames carry values).\<close>

inductive
      cveq :: \<open>cval \<Rightarrow> cval \<Rightarrow> bool\<close>  (infix \<open>\<approx>\<^sub>v\<close> 50)
  and cfeq :: \<open>cframe \<Rightarrow> cframe \<Rightarrow> bool\<close>  (infix \<open>\<approx>\<^sub>f\<close> 50)
where
  QLit: \<open>Vlit l \<approx>\<^sub>v Vlit l\<close>
| QCon: \<open>list_all2 (\<approx>\<^sub>v) vs vs' \<Longrightarrow> Vcon c vs \<approx>\<^sub>v Vcon c vs'\<close>
| QClos: \<open>(\<forall>y \<in> fv b - {x}. rel_option (\<approx>\<^sub>v) (map_of e\<^sub>1 y) (map_of e\<^sub>2 y)) \<Longrightarrow>
          Vclos e\<^sub>1 x b \<approx>\<^sub>v Vclos e\<^sub>2 x b\<close>
| QClosrec: \<open>(\<forall>y \<in> fv b - {x, g}. rel_option (\<approx>\<^sub>v) (map_of e\<^sub>1 y) (map_of e\<^sub>2 y)) \<Longrightarrow>
             Vclosrec e\<^sub>1 g x b \<approx>\<^sub>v Vclosrec e\<^sub>2 g x b\<close>
| QCont: \<open>list_all2 (\<approx>\<^sub>f) fs fs' \<Longrightarrow> VCont fs \<approx>\<^sub>v VCont fs'\<close>
| QName: \<open>Vname i \<approx>\<^sub>v Vname i\<close>

| FApp1: \<open>(\<forall>y \<in> fv a. rel_option (\<approx>\<^sub>v) (map_of e\<^sub>1 y) (map_of e\<^sub>2 y)) \<Longrightarrow>
          CFapp1 e\<^sub>1 a \<approx>\<^sub>f CFapp1 e\<^sub>2 a\<close>
| FApp2: \<open>fv\<^sub>1 \<approx>\<^sub>v fv\<^sub>2 \<Longrightarrow> CFapp2 fv\<^sub>1 \<approx>\<^sub>f CFapp2 fv\<^sub>2\<close>
| FLet: \<open>(\<forall>y \<in> fv b - {x}. rel_option (\<approx>\<^sub>v) (map_of e\<^sub>1 y) (map_of e\<^sub>2 y)) \<Longrightarrow>
         CFlet x e\<^sub>1 b \<approx>\<^sub>f CFlet x e\<^sub>2 b\<close>
| FCon: \<open>list_all2 (\<approx>\<^sub>v) vs vs' \<Longrightarrow>
         (\<forall>y \<in> fv_list es. rel_option (\<approx>\<^sub>v) (map_of e\<^sub>1 y) (map_of e\<^sub>2 y)) \<Longrightarrow>
         CFcon c vs e\<^sub>1 es \<approx>\<^sub>f CFcon c vs' e\<^sub>2 es\<close>
| FMatch: \<open>(\<forall>y \<in> fv_arms cls. rel_option (\<approx>\<^sub>v) (map_of e\<^sub>1 y) (map_of e\<^sub>2 y)) \<Longrightarrow>
           CFmatch e\<^sub>1 cls \<approx>\<^sub>f CFmatch e\<^sub>2 cls\<close>
| FPerf: \<open>CFperf l \<approx>\<^sub>f CFperf l\<close>
| FPerfn1: \<open>(\<forall>y \<in> fv a. rel_option (\<approx>\<^sub>v) (map_of e\<^sub>1 y) (map_of e\<^sub>2 y)) \<Longrightarrow>
            CFperfn1 e\<^sub>1 op a \<approx>\<^sub>f CFperfn1 e\<^sub>2 op a\<close>
| FPerfn2: \<open>xv\<^sub>1 \<approx>\<^sub>v xv\<^sub>2 \<Longrightarrow> CFperfn2 xv\<^sub>1 op \<approx>\<^sub>f CFperfn2 xv\<^sub>2 op\<close>
| FHandle: \<open>hv\<^sub>1 \<approx>\<^sub>v hv\<^sub>2 \<Longrightarrow> CFhandle l hv\<^sub>1 \<approx>\<^sub>f CFhandle l hv\<^sub>2\<close>
| FHandlen: \<open>hv\<^sub>1 \<approx>\<^sub>v hv\<^sub>2 \<Longrightarrow> CFhandlen l i hv\<^sub>1 \<phi> \<approx>\<^sub>f CFhandlen l i hv\<^sub>2 \<phi>\<close>
| FMask: \<open>CFmask l \<approx>\<^sub>f CFmask l\<close>

text \<open>Environment agreement on a set of names is pointwise on the lookups, so
  a closure trimmed to the free variables of its body still agrees with the
  original. Result agreement:\<close>

definition aenv :: \<open>name set \<Rightarrow> (name \<times> cval) list \<Rightarrow> (name \<times> cval) list \<Rightarrow> bool\<close> where
  \<open>aenv S e\<^sub>1 e\<^sub>2 \<longleftrightarrow> (\<forall>y \<in> S. rel_option (\<approx>\<^sub>v) (map_of e\<^sub>1 y) (map_of e\<^sub>2 y))\<close>

fun hreq :: \<open>hres \<Rightarrow> hres \<Rightarrow> bool\<close> where
  \<open>hreq (HRval v) (HRval v') \<longleftrightarrow> v \<approx>\<^sub>v v'\<close>
| \<open>hreq HRtimeout HRtimeout \<longleftrightarrow> True\<close>
| \<open>hreq HRerr HRerr \<longleftrightarrow> True\<close>
| \<open>hreq (HRop l m w fr) (HRop l' m' w' fr') \<longleftrightarrow>
     l = l' \<and> m = m' \<and> w \<approx>\<^sub>v w' \<and> list_all2 (\<approx>\<^sub>f) fr fr'\<close>
| \<open>hreq (HRopn i op w fr) (HRopn i' op' w' fr') \<longleftrightarrow>
     i = i' \<and> op = op' \<and> w \<approx>\<^sub>v w' \<and> list_all2 (\<approx>\<^sub>f) fr fr'\<close>
| \<open>hreq _ _ \<longleftrightarrow> False\<close>

subsection \<open>Basic properties of agreement\<close>

text \<open>Agreement is reflexive:\<close>

lemma rel_option_self: \<open>(\<And>a. z = Some a \<Longrightarrow> Q a a) \<Longrightarrow> rel_option Q z z\<close>
  by (cases z) auto

lemma cveq_cfeq_refl: \<open>v \<approx>\<^sub>v v \<and> f \<approx>\<^sub>f f\<close>
  by (induction rule: cval_cframe.induct)
    (auto intro!: cveq_cfeq.intros rel_option_self simp: list_all2_same dest!: map_of_SomeD)

lemmas cveq_refl = cveq_cfeq_refl[THEN conjunct1]

lemma aenv_refl[simp, intro!]: \<open>aenv S e e\<close>
  by (auto simp: aenv_def rel_option_iff cveq_refl split: option.split)

lemma list_all2_cveq_refl[simp, intro!]: \<open>list_all2 (\<approx>\<^sub>v) vs vs\<close>
  by (simp add: list_all2_same cveq_refl)

text \<open>Inversion: agreement fixes the outer constructor, and for literals,
  names and constructors an equal literal, name or tag with agreeing
  arguments.\<close>

inductive_simps cveq_shape:
  \<open>Vlit l \<approx>\<^sub>v v\<close>
  \<open>Vcon c vs \<approx>\<^sub>v v\<close>
  \<open>Vclos e x b \<approx>\<^sub>v v\<close>
  \<open>Vclosrec e g x b \<approx>\<^sub>v v\<close>
  \<open>VCont fs \<approx>\<^sub>v v\<close>
  \<open>Vname i \<approx>\<^sub>v v\<close>

subsection \<open>Pattern matching respects agreement\<close>

text \<open>Matching a pattern against agreeing values yields the same shape of
  result, with equal binder names carrying agreeing values:\<close>

abbreviation beq :: \<open>(name \<times> cval) list \<Rightarrow> (name \<times> cval) list \<Rightarrow> bool\<close> where
  \<open>beq \<equiv> list_all2 (rel_prod (=) (\<approx>\<^sub>v))\<close>

lemma cpmatch_cong: \<open>v\<^sub>1 \<approx>\<^sub>v v\<^sub>2 \<Longrightarrow> rel_option beq (cpmatch p v\<^sub>1) (cpmatch p v\<^sub>2)\<close>
  and cpmatch_list_cong: \<open>list_all2 (\<approx>\<^sub>v) vs\<^sub>1 vs\<^sub>2 \<Longrightarrow>
    rel_option beq (cpmatch_list ps vs\<^sub>1) (cpmatch_list ps vs\<^sub>2)\<close>
proof (induction p v\<^sub>1 and ps vs\<^sub>1 arbitrary: v\<^sub>2 and vs\<^sub>2 rule: cpmatch_induct)
  case (cpmatch_CPcon c ps c' vs v\<^sub>2)
  from cpmatch_CPcon.prems obtain vs\<^sub>2 where \<open>v\<^sub>2 = Vcon c' vs\<^sub>2\<close>
    and \<open>list_all2 (\<approx>\<^sub>v) vs vs\<^sub>2\<close> \<open>length vs = length vs\<^sub>2\<close>
    by (auto dest: list_all2_lengthD simp: cveq_shape)
  with cpmatch_CPcon.IH show ?case by simp
next
  case cpmatch_CPas
  from cpmatch_CPas.IH[OF cpmatch_CPas.prems] cpmatch_CPas.prems show ?case
    by (auto split: option.splits simp: rel_option_iff)
next
  case (cpmatch_list_Cons p ps v vs vs\<^sub>2)
  from cpmatch_list_Cons.prems obtain z zs where
    vs\<^sub>2: \<open>vs\<^sub>2 = z # zs\<close> and vz: \<open>v \<approx>\<^sub>v z\<close> and r: \<open>list_all2 (\<approx>\<^sub>v) vs zs\<close>
    by (auto simp: list_all2_Cons1)
  have m: \<open>rel_option beq (cpmatch p v) (cpmatch p z)\<close>
    using cpmatch_list_Cons.IH vz by blast
  have \<open>rel_option beq (cpmatch_list ps vs) (cpmatch_list ps zs)\<close>
    if \<open>cpmatch p v = Some b\<close> for b
    using cpmatch_list_Cons.IH r that by blast
  with m show ?case
    by (auto split: option.splits simp: vs\<^sub>2 rel_option_iff intro: list_all2_appendI)
qed (auto split: option.splits simp: list_all2_Cons1 cveq_shape)

subsection \<open>Environment manipulation under agreement\<close>

text \<open>Looking up an in-scope name in agreeing environments yields agreeing
  values, and extending both with a shared binder or with agreeing binding
  blocks preserves agreement:\<close>

lemma aenv_lookup:
  \<open>aenv S e\<^sub>1 e\<^sub>2 \<Longrightarrow> x \<in> S \<Longrightarrow> map_of e\<^sub>1 x = Some v \<Longrightarrow>
   \<exists>v'. map_of e\<^sub>2 x = Some v' \<and> v \<approx>\<^sub>v v'\<close>
  by (fastforce simp: aenv_def rel_option_iff split: option.splits)

lemma aenv_cons:
  \<open>v\<^sub>1 \<approx>\<^sub>v v\<^sub>2 \<Longrightarrow> aenv (S - {x}) e\<^sub>1 e\<^sub>2 \<Longrightarrow> aenv S ((x, v\<^sub>1) # e\<^sub>1) ((x, v\<^sub>2) # e\<^sub>2)\<close>
  by (auto simp: aenv_def)

lemma beq_fst: \<open>beq bs\<^sub>1 bs\<^sub>2 \<Longrightarrow> map fst bs\<^sub>1 = map fst bs\<^sub>2\<close>
  by (induction bs\<^sub>1 bs\<^sub>2 rule: list_all2_induct) auto

lemma beq_rel_map_of:
  \<open>beq bs\<^sub>1 bs\<^sub>2 \<Longrightarrow> rel_option (\<approx>\<^sub>v) (map_of bs\<^sub>1 y) (map_of bs\<^sub>2 y)\<close>
  by (induction bs\<^sub>1 bs\<^sub>2 rule: list_all2_induct) (auto split: if_splits)

lemma aenv_append_beq:
  assumes b: \<open>beq bs\<^sub>1 bs\<^sub>2\<close> and rest: \<open>aenv (S - set (map fst bs\<^sub>1)) e\<^sub>1 e\<^sub>2\<close>
  shows \<open>aenv S (bs\<^sub>1 @ e\<^sub>1) (bs\<^sub>2 @ e\<^sub>2)\<close>
  unfolding aenv_def
proof (intro ballI)
  fix y assume y: \<open>y \<in> S\<close>
  show \<open>rel_option (\<approx>\<^sub>v) (map_of (bs\<^sub>1 @ e\<^sub>1) y) (map_of (bs\<^sub>2 @ e\<^sub>2) y)\<close>
  proof (cases \<open>y \<in> set (map fst bs\<^sub>1)\<close>)
    case True
    hence \<open>map_of bs\<^sub>1 y \<noteq> None\<close> by (simp add: map_of_eq_None_iff)
    moreover from True have \<open>map_of bs\<^sub>2 y \<noteq> None\<close>
      by (simp add: beq_fst[OF b] map_of_eq_None_iff)
    ultimately show ?thesis
      using beq_rel_map_of[OF b, of y] by (auto simp: map_add_def split: option.splits)
  next
    case False
    hence \<open>map_of bs\<^sub>1 y = None\<close> by (simp add: map_of_eq_None_iff)
    moreover from False have \<open>map_of bs\<^sub>2 y = None\<close>
      by (simp add: beq_fst[OF b] map_of_eq_None_iff)
    ultimately show ?thesis
      using rest y False by (auto simp: aenv_def map_add_def)
  qed
qed

text \<open>Introduction forms phrased with \<^const>\<open>aenv\<close>:\<close>

lemma cveq_closI: \<open>aenv (fv b - {x}) e\<^sub>1 e\<^sub>2 \<Longrightarrow> Vclos e\<^sub>1 x b \<approx>\<^sub>v Vclos e\<^sub>2 x b\<close>
  by (auto simp: aenv_def intro: QClos)

lemma cveq_closrecI: \<open>aenv (fv b - {x, g}) e\<^sub>1 e\<^sub>2 \<Longrightarrow> Vclosrec e\<^sub>1 g x b \<approx>\<^sub>v Vclosrec e\<^sub>2 g x b\<close>
  by (auto simp: aenv_def intro: QClosrec)

lemma cfeq_app1I: \<open>aenv (fv a) e\<^sub>1 e\<^sub>2 \<Longrightarrow> CFapp1 e\<^sub>1 a \<approx>\<^sub>f CFapp1 e\<^sub>2 a\<close>
  by (auto simp: aenv_def intro: FApp1)

lemma cfeq_letI: \<open>aenv (fv b - {x}) e\<^sub>1 e\<^sub>2 \<Longrightarrow> CFlet x e\<^sub>1 b \<approx>\<^sub>f CFlet x e\<^sub>2 b\<close>
  by (auto simp: aenv_def intro: FLet)

lemma cfeq_conI:
  \<open>list_all2 (\<approx>\<^sub>v) vs vs' \<Longrightarrow> aenv (fv_list es) e\<^sub>1 e\<^sub>2 \<Longrightarrow> CFcon c vs e\<^sub>1 es \<approx>\<^sub>f CFcon c vs' e\<^sub>2 es\<close>
  by (auto simp: aenv_def intro: FCon)

lemma cfeq_matchI: \<open>aenv (fv_arms cls) e\<^sub>1 e\<^sub>2 \<Longrightarrow> CFmatch e\<^sub>1 cls \<approx>\<^sub>f CFmatch e\<^sub>2 cls\<close>
  by (auto simp: aenv_def intro: FMatch)

lemma cfeq_perfn1I: \<open>aenv (fv a) e\<^sub>1 e\<^sub>2 \<Longrightarrow> CFperfn1 e\<^sub>1 op a \<approx>\<^sub>f CFperfn1 e\<^sub>2 op a\<close>
  by (auto simp: aenv_def intro: FPerfn1)

text \<open>Result agreement, inverted on the left result's shape:\<close>

lemma hreq_valL[simp]: \<open>hreq (HRval v) r \<longleftrightarrow> (\<exists>v'. r = HRval v' \<and> v \<approx>\<^sub>v v')\<close>
  by (cases r) auto

lemma hreq_opL[simp]:
  \<open>hreq (HRop l m w fr) r \<longleftrightarrow>
   (\<exists>w' fr'. r = HRop l m w' fr' \<and> w \<approx>\<^sub>v w' \<and> list_all2 (\<approx>\<^sub>f) fr fr')\<close>
  by (cases r) auto

lemma hreq_opnL[simp]:
  \<open>hreq (HRopn i op w fr) r \<longleftrightarrow>
   (\<exists>w' fr'. r = HRopn i op w' fr' \<and> w \<approx>\<^sub>v w' \<and> list_all2 (\<approx>\<^sub>f) fr fr')\<close>
  by (cases r) auto

lemma hreq_errL[simp]: \<open>hreq HRerr r \<longleftrightarrow> r = HRerr\<close>
  by (cases r) auto

lemma hreq_timeoutL[simp]: \<open>hreq HRtimeout r \<longleftrightarrow> r = HRtimeout\<close>
  by (cases r) auto

text \<open>Agreeing results are bubbles together, and pushing agreeing frames
  onto agreeing bubbles, or masking them, keeps them agreeing:\<close>

lemma hreq_bubble: \<open>hreq r r' \<Longrightarrow> bubble r' = bubble r\<close>
  by (cases r) auto

lemma hreq_push: \<open>hreq r r' \<Longrightarrow> f \<approx>\<^sub>f g \<Longrightarrow> hreq (push f r) (push g r')\<close>
  by (cases r) (auto intro: list_all2_appendI)

lemma hreq_maskr: \<open>hreq r r' \<Longrightarrow> hreq (maskr l r) (maskr l r')\<close>
  by (cases r) (auto intro!: list_all2_appendI FMask)

text \<open>Frame inversion, and that agreement preserves the plain-versus-handler
  classification of a frame:\<close>

inductive_simps cfeq_shape:
  \<open>CFapp1 e a \<approx>\<^sub>f g\<close>
  \<open>CFapp2 v \<approx>\<^sub>f g\<close>
  \<open>CFlet x e b \<approx>\<^sub>f g\<close>
  \<open>CFcon c vs e es \<approx>\<^sub>f g\<close>
  \<open>CFmatch e cls \<approx>\<^sub>f g\<close>
  \<open>CFperf l \<approx>\<^sub>f g\<close>
  \<open>CFperfn1 e op a \<approx>\<^sub>f g\<close>
  \<open>CFperfn2 v op \<approx>\<^sub>f g\<close>
  \<open>CFhandle l hv \<approx>\<^sub>f g\<close>
  \<open>CFhandlen l i hv \<phi> \<approx>\<^sub>f g\<close>
  \<open>CFmask l \<approx>\<^sub>f g\<close>

lemma cfeq_plain: \<open>f \<approx>\<^sub>f g \<Longrightarrow> plain_frame g = plain_frame f\<close>
  by (cases f) (auto simp: cfeq_shape)

lemma cfeq_plainn: \<open>f \<approx>\<^sub>f g \<Longrightarrow> plainn_frame g = plainn_frame f\<close>
  by (cases f) (auto simp: cfeq_shape)

subsection \<open>Coincidence: evaluation depends only on the free variables\<close>

text \<open>From agreeing inputs, each judgment yields an agreeing result, with the
  same supply out:\<close>

lemma coincide: \<open>env\<^sub>1 \<turnstile> e,ns \<Down> r\<^sub>1,ns' \<Longrightarrow> aenv (fv e) env\<^sub>1 env\<^sub>2 \<Longrightarrow>
    \<exists>r\<^sub>2. env\<^sub>2 \<turnstile> e,ns \<Down> r\<^sub>2,ns' \<and> hreq r\<^sub>1 r\<^sub>2\<close>
  and coincide_con: \<open>env\<^sub>1 \<turnstile> c \<langle>vs\<^sub>1;es\<rangle>,ns \<Down> r\<^sub>1,ns' \<Longrightarrow> aenv (fv_list es) env\<^sub>1 env\<^sub>2 \<Longrightarrow>
    list_all2 (\<approx>\<^sub>v) vs\<^sub>1 vs\<^sub>2 \<Longrightarrow>
    \<exists>r\<^sub>2. env\<^sub>2 \<turnstile> c \<langle>vs\<^sub>2;es\<rangle>,ns \<Down> r\<^sub>2,ns' \<and> hreq r\<^sub>1 r\<^sub>2\<close>
  and coincide_match: \<open>env\<^sub>1 \<turnstile> u\<^sub>1 \<Zrres> cls,ns \<Down> r\<^sub>1,ns' \<Longrightarrow> aenv (fv_arms cls) env\<^sub>1 env\<^sub>2 \<Longrightarrow>
    u\<^sub>1 \<approx>\<^sub>v u\<^sub>2 \<Longrightarrow> \<exists>r\<^sub>2. env\<^sub>2 \<turnstile> u\<^sub>2 \<Zrres> cls,ns \<Down> r\<^sub>2,ns' \<and> hreq r\<^sub>1 r\<^sub>2\<close>
  and coincide_apply: \<open>fw\<^sub>1 \<sqdot> av\<^sub>1,ns \<Down> r\<^sub>1,ns' \<Longrightarrow> fw\<^sub>1 \<approx>\<^sub>v fw\<^sub>2 \<Longrightarrow> av\<^sub>1 \<approx>\<^sub>v av\<^sub>2 \<Longrightarrow>
    \<exists>r\<^sub>2. fw\<^sub>2 \<sqdot> av\<^sub>2,ns \<Down> r\<^sub>2,ns' \<and> hreq r\<^sub>1 r\<^sub>2\<close>
  and coincide_step: \<open>u\<^sub>1 \<Zdres> fr\<^sub>1,ns \<Down> r\<^sub>1,ns' \<Longrightarrow> u\<^sub>1 \<approx>\<^sub>v u\<^sub>2 \<Longrightarrow> fr\<^sub>1 \<approx>\<^sub>f fr\<^sub>2 \<Longrightarrow>
    \<exists>r\<^sub>2. u\<^sub>2 \<Zdres> fr\<^sub>2,ns \<Down> r\<^sub>2,ns' \<and> hreq r\<^sub>1 r\<^sub>2\<close>
  and coincide_unwind: \<open>u\<^sub>1 \<leadsto> fs\<^sub>1,ns \<Down> r\<^sub>1,ns' \<Longrightarrow> u\<^sub>1 \<approx>\<^sub>v u\<^sub>2 \<Longrightarrow> list_all2 (\<approx>\<^sub>f) fs\<^sub>1 fs\<^sub>2 \<Longrightarrow>
    \<exists>r\<^sub>2. u\<^sub>2 \<leadsto> fs\<^sub>2,ns \<Down> r\<^sub>2,ns' \<and> hreq r\<^sub>1 r\<^sub>2\<close>
  and coincide_resume: \<open>resume q\<^sub>1 fs\<^sub>1,ns \<Down> r\<^sub>1,ns' \<Longrightarrow> hreq q\<^sub>1 q\<^sub>2 \<Longrightarrow> list_all2 (\<approx>\<^sub>f) fs\<^sub>1 fs\<^sub>2 \<Longrightarrow>
    \<exists>r\<^sub>2. resume q\<^sub>2 fs\<^sub>2,ns \<Down> r\<^sub>2,ns' \<and> hreq r\<^sub>1 r\<^sub>2\<close>
  and coincide_throw: \<open>throw l \<^bold>@ m  w\<^sub>1 \<parallel> gr\<^sub>1 \<parallel> gs\<^sub>1,ns \<Down> r\<^sub>1,ns' \<Longrightarrow> w\<^sub>1 \<approx>\<^sub>v w\<^sub>2 \<Longrightarrow>
    list_all2 (\<approx>\<^sub>f) gr\<^sub>1 gr\<^sub>2 \<Longrightarrow> list_all2 (\<approx>\<^sub>f) gs\<^sub>1 gs\<^sub>2 \<Longrightarrow>
    \<exists>r\<^sub>2. throw l \<^bold>@ m  w\<^sub>2 \<parallel> gr\<^sub>2 \<parallel> gs\<^sub>2,ns \<Down> r\<^sub>2,ns' \<and> hreq r\<^sub>1 r\<^sub>2\<close>
  and coincide_thrown: \<open>thrown i op  w\<^sub>1 \<parallel> gr\<^sub>1 \<parallel> gs\<^sub>1,ns \<Down> r\<^sub>1,ns' \<Longrightarrow> w\<^sub>1 \<approx>\<^sub>v w\<^sub>2 \<Longrightarrow>
    list_all2 (\<approx>\<^sub>f) gr\<^sub>1 gr\<^sub>2 \<Longrightarrow> list_all2 (\<approx>\<^sub>f) gs\<^sub>1 gs\<^sub>2 \<Longrightarrow>
    \<exists>r\<^sub>2. thrown i op  w\<^sub>2 \<parallel> gr\<^sub>2 \<parallel> gs\<^sub>2,ns \<Down> r\<^sub>2,ns' \<and> hreq r\<^sub>1 r\<^sub>2\<close>
proof (induction
       arbitrary: env\<^sub>2 and env\<^sub>2 vs\<^sub>2 and env\<^sub>2 u\<^sub>2 and fw\<^sub>2 av\<^sub>2 and u\<^sub>2 fr\<^sub>2
                  and u\<^sub>2 fs\<^sub>2 and q\<^sub>2 fs\<^sub>2 and w\<^sub>2 gr\<^sub>2 gs\<^sub>2 and w\<^sub>2 gr\<^sub>2 gs\<^sub>2
       rule: Dinducts)
  case (EvVar env x v ns env\<^sub>2)
  from EvVar.prems EvVar.hyps obtain v' where \<open>map_of env\<^sub>2 x = Some v'\<close> and \<open>v \<approx>\<^sub>v v'\<close>
    by (auto dest: aenv_lookup)
  then show ?case by (auto intro: Dintros)
next
  case (EvLam env x b ns env\<^sub>2)
  have \<open>env\<^sub>2 \<turnstile> Clam x b,ns \<Down> HRval (Vclos env\<^sub>2 x b),ns\<close> by (rule Bigstep.EvLam)
  moreover have \<open>hreq (HRval (Vclos env x b)) (HRval (Vclos env\<^sub>2 x b))\<close>
    using cveq_closI[of b x env env\<^sub>2] EvLam.prems by simp
  ultimately show ?case by blast
next
  case (EvApp env f ns fw ns\<^sub>1 a av ns\<^sub>2 r ns\<^sub>3 env\<^sub>2)
  from EvApp.prems have af: \<open>aenv (fv f) env env\<^sub>2\<close> and aa: \<open>aenv (fv a) env env\<^sub>2\<close>
    by (auto simp: aenv_def)
  from af obtain fw' where f\<^sub>2: \<open>env\<^sub>2 \<turnstile> f,ns \<Down> (HRval fw'),ns\<^sub>1\<close> and efw: \<open>fw \<approx>\<^sub>v fw'\<close>
    by (blast dest: EvApp.IH hreq_valL[THEN iffD1])
  from aa obtain av' where a\<^sub>2: \<open>env\<^sub>2 \<turnstile> a,ns\<^sub>1 \<Down> (HRval av'),ns\<^sub>2\<close> and eav: \<open>av \<approx>\<^sub>v av'\<close>
    by (blast dest: EvApp.IH hreq_valL[THEN iffD1])
  from efw eav obtain r\<^sub>2 where ap\<^sub>2: \<open>fw' \<sqdot> av',ns\<^sub>2 \<Down> r\<^sub>2,ns\<^sub>3\<close> and hr: \<open>hreq r r\<^sub>2\<close>
    by (auto dest: EvApp.IH)
  show ?case using f\<^sub>2 a\<^sub>2 ap\<^sub>2 hr by (auto intro: Dintros)
next
  case (EvAppBub2 env f ns fw ns\<^sub>1 a r ns\<^sub>2 r' env\<^sub>2)
  from EvAppBub2.prems have af: \<open>aenv (fv f) env env\<^sub>2\<close> and aa: \<open>aenv (fv a) env env\<^sub>2\<close>
    by (auto simp: aenv_def)
  from af obtain fw' where f\<^sub>2: \<open>env\<^sub>2 \<turnstile> f,ns \<Down> (HRval fw'),ns\<^sub>1\<close> and efw: \<open>fw \<approx>\<^sub>v fw'\<close>
    by (blast dest: EvAppBub2.IH hreq_valL[THEN iffD1])
  from aa obtain r\<^sub>2 where a\<^sub>2: \<open>env\<^sub>2 \<turnstile> a,ns\<^sub>1 \<Down> r\<^sub>2,ns\<^sub>2\<close> and hr: \<open>hreq r r\<^sub>2\<close>
    by (auto dest: EvAppBub2.IH)
  show ?case
    using Bigstep.EvAppBub2[OF f\<^sub>2 a\<^sub>2] hreq_bubble[OF hr] EvAppBub2.hyps
          hreq_push[OF hr FApp2[OF efw]]
    by blast
next
  case (EvAppBub1 env f ns r ns\<^sub>1 r' a env\<^sub>2)
  from EvAppBub1.prems have af: \<open>aenv (fv f) env env\<^sub>2\<close> and aa: \<open>aenv (fv a) env env\<^sub>2\<close>
    by (auto simp: aenv_def)
  from EvAppBub1.IH[OF af] obtain r\<^sub>2 where f\<^sub>2: \<open>env\<^sub>2 \<turnstile> f,ns \<Down> r\<^sub>2,ns\<^sub>1\<close> and hr: \<open>hreq r r\<^sub>2\<close>
    by auto
  show ?case
    using Bigstep.EvAppBub1[OF f\<^sub>2] hreq_bubble[OF hr] EvAppBub1.hyps
          hreq_push[OF hr cfeq_app1I[OF aa]]
    by blast
next
  case (EvLet env e ns v ns\<^sub>1 x b r ns\<^sub>2 env\<^sub>2)
  from EvLet.prems have ae: \<open>aenv (fv e) env env\<^sub>2\<close> and ab: \<open>aenv (fv b - {x}) env env\<^sub>2\<close>
    by (auto simp: aenv_def)
  from ae obtain v' where e\<^sub>2: \<open>env\<^sub>2 \<turnstile> e,ns \<Down> (HRval v'),ns\<^sub>1\<close> and ev: \<open>v \<approx>\<^sub>v v'\<close>
    by (blast dest: EvLet.IH hreq_valL[THEN iffD1])
  from aenv_cons[OF ev ab] obtain r\<^sub>2
    where b\<^sub>2: \<open>((x, v') # env\<^sub>2) \<turnstile> b,ns\<^sub>1 \<Down> r\<^sub>2,ns\<^sub>2\<close> and hr: \<open>hreq r r\<^sub>2\<close> by (auto dest: EvLet.IH)
  show ?case using e\<^sub>2 b\<^sub>2 hr by (auto intro: Dintros)
next
  case (EvLetBub env e ns r ns\<^sub>1 r' x b env\<^sub>2)
  from EvLetBub.prems have ae: \<open>aenv (fv e) env env\<^sub>2\<close> and ab: \<open>aenv (fv b - {x}) env env\<^sub>2\<close>
    by (auto simp: aenv_def)
  from EvLetBub.IH[OF ae] obtain r\<^sub>2 where e\<^sub>2: \<open>env\<^sub>2 \<turnstile> e,ns \<Down> r\<^sub>2,ns\<^sub>1\<close> and hr: \<open>hreq r r\<^sub>2\<close>
    by auto
  show ?case
    using Bigstep.EvLetBub[OF e\<^sub>2] hreq_bubble[OF hr] EvLetBub.hyps
          hreq_push[OF hr cfeq_letI[OF ab]]
    by blast
next
  case (EvLetrec f env x e b ns r ns' env\<^sub>2)
  from EvLetrec.prems have ae: \<open>aenv (fv e - {f, x}) env env\<^sub>2\<close>
    and ab: \<open>aenv (fv b - {f}) env env\<^sub>2\<close>
    by (auto simp: aenv_def)
  have ae': \<open>aenv (fv e - {x, f}) env env\<^sub>2\<close> using ae by (simp add: insert_commute)
  have rec: \<open>Vclosrec env f x e \<approx>\<^sub>v Vclosrec env\<^sub>2 f x e\<close> using ae' by (rule cveq_closrecI)
  from EvLetrec.IH[OF aenv_cons[OF rec ab]] obtain r\<^sub>2
    where b\<^sub>2: \<open>((f, Vclosrec env\<^sub>2 f x e) # env\<^sub>2) \<turnstile> b,ns \<Down> r\<^sub>2,ns'\<close> and hr: \<open>hreq r r\<^sub>2\<close> by auto
  show ?case using b\<^sub>2 hr by (auto intro: Dintros)
next
  case (EvCon env c es ns r ns' env\<^sub>2)
  from EvCon.prems have aes: \<open>aenv (fv_list es) env env\<^sub>2\<close> by simp
  from EvCon.IH[OF aes, of \<open>[]\<close>] obtain r\<^sub>2
    where c\<^sub>2: \<open>env\<^sub>2 \<turnstile> c \<langle>[];es\<rangle>,ns \<Down> r\<^sub>2,ns'\<close> and hr: \<open>hreq r r\<^sub>2\<close>
    by auto
  show ?case using c\<^sub>2 hr by (auto intro: Dintros)
next
  case (EvMatch env e ns v ns\<^sub>1 cls r ns\<^sub>2 env\<^sub>2)
  from EvMatch.prems have ae: \<open>aenv (fv e) env env\<^sub>2\<close> and acls: \<open>aenv (fv_arms cls) env env\<^sub>2\<close>
    by (auto simp: aenv_def)
  from ae obtain v' where e\<^sub>2: \<open>env\<^sub>2 \<turnstile> e,ns \<Down> (HRval v'),ns\<^sub>1\<close> and ev: \<open>v \<approx>\<^sub>v v'\<close>
    by (blast dest: EvMatch.IH hreq_valL[THEN iffD1])
  from acls ev obtain r\<^sub>2 where m\<^sub>2: \<open>env\<^sub>2 \<turnstile> v' \<Zrres> cls,ns\<^sub>1 \<Down> r\<^sub>2,ns\<^sub>2\<close> and hr: \<open>hreq r r\<^sub>2\<close>
    by (auto dest: EvMatch.IH)
  show ?case using e\<^sub>2 m\<^sub>2 hr by (auto intro: Dintros)
next
  case (EvMatchBub env e ns r ns\<^sub>1 r' cls env\<^sub>2)
  from EvMatchBub.prems have ae: \<open>aenv (fv e) env env\<^sub>2\<close> and acls: \<open>aenv (fv_arms cls) env env\<^sub>2\<close>
    by (auto simp: aenv_def)
  from EvMatchBub.IH[OF ae] obtain r\<^sub>2 where e\<^sub>2: \<open>env\<^sub>2 \<turnstile> e,ns \<Down> r\<^sub>2,ns\<^sub>1\<close> and hr: \<open>hreq r r\<^sub>2\<close>
    by auto
  show ?case
    using Bigstep.EvMatchBub[OF e\<^sub>2] hreq_bubble[OF hr] EvMatchBub.hyps
          hreq_push[OF hr cfeq_matchI[OF acls]]
    by blast
next
  case (EvPerform env a ns av ns\<^sub>1 l env\<^sub>2)
  from EvPerform.prems have aa: \<open>aenv (fv a) env env\<^sub>2\<close> by simp
  from EvPerform.IH[OF aa] obtain av'
    where a\<^sub>2: \<open>env\<^sub>2 \<turnstile> a,ns \<Down> (HRval av'),ns\<^sub>1\<close> and ev: \<open>av \<approx>\<^sub>v av'\<close>
    by auto
  show ?case using a\<^sub>2 ev by (auto intro: Dintros)
next
  case (EvPerformBub env a ns r ns\<^sub>1 r' l env\<^sub>2)
  from EvPerformBub.prems have aa: \<open>aenv (fv a) env env\<^sub>2\<close> by simp
  from EvPerformBub.IH[OF aa] obtain r\<^sub>2 where a\<^sub>2: \<open>env\<^sub>2 \<turnstile> a,ns \<Down> r\<^sub>2,ns\<^sub>1\<close> and hr: \<open>hreq r r\<^sub>2\<close>
    by auto
  show ?case
    using Bigstep.EvPerformBub[OF a\<^sub>2] hreq_bubble[OF hr] EvPerformBub.hyps hreq_push[OF hr FPerf]
    by blast
next
  case (EvHandle env h ns hv ns\<^sub>1 b r ns\<^sub>2 l r' ns\<^sub>3 env\<^sub>2)
  from EvHandle.prems have ah: \<open>aenv (fv h) env env\<^sub>2\<close> and ab: \<open>aenv (fv b) env env\<^sub>2\<close>
    by (auto simp: aenv_def)
  from ah obtain hv' where h\<^sub>2: \<open>env\<^sub>2 \<turnstile> h,ns \<Down> (HRval hv'),ns\<^sub>1\<close> and ehv: \<open>hv \<approx>\<^sub>v hv'\<close>
    by (blast dest: EvHandle.IH hreq_valL[THEN iffD1])
  from ab obtain r\<^sub>2 where b\<^sub>2: \<open>env\<^sub>2 \<turnstile> b,ns\<^sub>1 \<Down> r\<^sub>2,ns\<^sub>2\<close> and hr: \<open>hreq r r\<^sub>2\<close>
    by (auto dest: EvHandle.IH)
  have gs: \<open>list_all2 (\<approx>\<^sub>f) [CFhandle l hv] [CFhandle l hv']\<close> using ehv by (auto intro: FHandle)
  from hr gs obtain r\<^sub>2'
    where t\<^sub>2: \<open>resume r\<^sub>2 [CFhandle l hv'],ns\<^sub>2 \<Down> r\<^sub>2',ns\<^sub>3\<close>
      and hr': \<open>hreq r' r\<^sub>2'\<close> by (auto dest: EvHandle.IH)
  show ?case using h\<^sub>2 b\<^sub>2 t\<^sub>2 hr' by (auto intro: Dintros)
next
  case (EvMask env e ns v ns\<^sub>1 l env\<^sub>2)
  from EvMask.prems have ae: \<open>aenv (fv e) env env\<^sub>2\<close> by simp
  from EvMask.IH[OF ae] obtain v' where e\<^sub>2: \<open>env\<^sub>2 \<turnstile> e,ns \<Down> (HRval v'),ns\<^sub>1\<close> and ev: \<open>v \<approx>\<^sub>v v'\<close>
    by auto
  show ?case using e\<^sub>2 ev by (auto intro: Dintros)
next
  case (EvMaskBub env e ns r ns\<^sub>1 r' l env\<^sub>2)
  from EvMaskBub.prems have ae: \<open>aenv (fv e) env env\<^sub>2\<close> by simp
  from EvMaskBub.IH[OF ae] obtain r\<^sub>2 where e\<^sub>2: \<open>env\<^sub>2 \<turnstile> e,ns \<Down> r\<^sub>2,ns\<^sub>1\<close> and hr: \<open>hreq r r\<^sub>2\<close>
    by auto
  show ?case
    using Bigstep.EvMaskBub[OF e\<^sub>2] hreq_bubble[OF hr] EvMaskBub.hyps hreq_maskr[OF hr, of l]
    by blast
next
  case (EvPerformn env x ns i ns\<^sub>1 a av ns\<^sub>2 op env\<^sub>2)
  from EvPerformn.prems have ax: \<open>aenv (fv x) env env\<^sub>2\<close> and aa: \<open>aenv (fv a) env env\<^sub>2\<close>
    by (auto simp: aenv_def)
  from ax have x\<^sub>2: \<open>env\<^sub>2 \<turnstile> x,ns \<Down> (HRval (Vname i)),ns\<^sub>1\<close>
    by (auto dest: EvPerformn.IH simp: cveq_shape)
  from aa obtain av' where a\<^sub>2: \<open>env\<^sub>2 \<turnstile> a,ns\<^sub>1 \<Down> (HRval av'),ns\<^sub>2\<close> and ev: \<open>av \<approx>\<^sub>v av'\<close>
    by (blast dest: EvPerformn.IH hreq_valL[THEN iffD1])
  show ?case using x\<^sub>2 a\<^sub>2 ev by (auto intro: Dintros)
next
  case (EvPerformnBub2 env x ns xv ns\<^sub>1 a r ns\<^sub>2 r' op env\<^sub>2)
  from EvPerformnBub2.prems have ax: \<open>aenv (fv x) env env\<^sub>2\<close> and aa: \<open>aenv (fv a) env env\<^sub>2\<close>
    by (auto simp: aenv_def)
  from ax obtain xv' where x\<^sub>2: \<open>env\<^sub>2 \<turnstile> x,ns \<Down> (HRval xv'),ns\<^sub>1\<close> and exv: \<open>xv \<approx>\<^sub>v xv'\<close>
    by (blast dest: EvPerformnBub2.IH hreq_valL[THEN iffD1])
  from aa obtain r\<^sub>2 where a\<^sub>2: \<open>env\<^sub>2 \<turnstile> a,ns\<^sub>1 \<Down> r\<^sub>2,ns\<^sub>2\<close> and hr: \<open>hreq r r\<^sub>2\<close>
    by (auto dest: EvPerformnBub2.IH)
  show ?case
    using Bigstep.EvPerformnBub2[OF x\<^sub>2 a\<^sub>2] hreq_bubble[OF hr] EvPerformnBub2.hyps
          hreq_push[OF hr FPerfn2[OF exv]]
    by blast
next
  case (EvPerformnBub1 env x ns r ns\<^sub>1 r' op a env\<^sub>2)
  from EvPerformnBub1.prems have ax: \<open>aenv (fv x) env env\<^sub>2\<close> and aa: \<open>aenv (fv a) env env\<^sub>2\<close>
    by (auto simp: aenv_def)
  from EvPerformnBub1.IH[OF ax] obtain r\<^sub>2 where x\<^sub>2: \<open>env\<^sub>2 \<turnstile> x,ns \<Down> r\<^sub>2,ns\<^sub>1\<close> and hr: \<open>hreq r r\<^sub>2\<close>
    by auto
  show ?case
    using Bigstep.EvPerformnBub1[OF x\<^sub>2] hreq_bubble[OF hr] EvPerformnBub1.hyps
          hreq_push[OF hr cfeq_perfn1I[OF aa]]
    by blast
next
  case (EvHandlen env h ns hv ns\<^sub>1 b bv ns\<^sub>2 r ns\<^sub>3 l \<phi> r' ns\<^sub>4 env\<^sub>2)
  from EvHandlen.prems have ah: \<open>aenv (fv h) env env\<^sub>2\<close> and ab: \<open>aenv (fv b) env env\<^sub>2\<close>
    by (auto simp: aenv_def)
  from ah obtain hv' where h\<^sub>2: \<open>env\<^sub>2 \<turnstile> h,ns \<Down> (HRval hv'),ns\<^sub>1\<close> and ehv: \<open>hv \<approx>\<^sub>v hv'\<close>
    by (blast dest: EvHandlen.IH hreq_valL[THEN iffD1])
  from ab obtain bv' where b\<^sub>2: \<open>env\<^sub>2 \<turnstile> b,ns\<^sub>1 \<Down> (HRval bv'),ns\<^sub>2\<close> and ebv: \<open>bv \<approx>\<^sub>v bv'\<close>
    by (blast dest: EvHandlen.IH hreq_valL[THEN iffD1])
  from ebv obtain r\<^sub>2
    where ap\<^sub>2: \<open>bv' \<sqdot> (Vname ns\<^sub>2),(Suc ns\<^sub>2) \<Down> r\<^sub>2,ns\<^sub>3\<close> and hr: \<open>hreq r r\<^sub>2\<close>
    by (blast dest: EvHandlen.IH intro: QName)
  have gs: \<open>list_all2 (\<approx>\<^sub>f) [CFhandlen l ns\<^sub>2 hv \<phi>] [CFhandlen l ns\<^sub>2 hv' \<phi>]\<close>
    using ehv by (auto intro: FHandlen)
  from hr gs obtain r\<^sub>2'
    where t\<^sub>2: \<open>resume r\<^sub>2 [CFhandlen l ns\<^sub>2 hv' \<phi>],ns\<^sub>3 \<Down> r\<^sub>2',ns\<^sub>4\<close>
      and hr': \<open>hreq r' r\<^sub>2'\<close> by (auto dest: EvHandlen.IH)
  show ?case using h\<^sub>2 b\<^sub>2 ap\<^sub>2 t\<^sub>2 hr' by (auto intro: Dintros)
next
  case (EcCons env e ns v ns\<^sub>1 c vs es r ns\<^sub>2 env\<^sub>2 vs\<^sub>2)
  from EcCons.prems have ae: \<open>aenv (fv e) env env\<^sub>2\<close> and aes: \<open>aenv (fv_list es) env env\<^sub>2\<close>
    and lav: \<open>list_all2 (\<approx>\<^sub>v) vs vs\<^sub>2\<close> by (auto simp: aenv_def)
  from ae obtain v' where e\<^sub>2: \<open>env\<^sub>2 \<turnstile> e,ns \<Down> (HRval v'),ns\<^sub>1\<close> and ev: \<open>v \<approx>\<^sub>v v'\<close>
    by (blast dest: EcCons.IH hreq_valL[THEN iffD1])
  have \<open>list_all2 (\<approx>\<^sub>v) (v # vs) (v' # vs\<^sub>2)\<close> using ev lav by simp
  from aes this obtain r\<^sub>2
    where c\<^sub>2: \<open>env\<^sub>2 \<turnstile> c \<langle>(v' # vs\<^sub>2);es\<rangle>,ns\<^sub>1 \<Down> r\<^sub>2,ns\<^sub>2\<close>
      and hr: \<open>hreq r r\<^sub>2\<close> by (auto dest: EcCons.IH)
  show ?case using e\<^sub>2 c\<^sub>2 hr by (auto intro: Dintros)
next
  case (EcConsBub env e ns r ns\<^sub>1 r' c vs es env\<^sub>2 vs\<^sub>2)
  from EcConsBub.prems have ae: \<open>aenv (fv e) env env\<^sub>2\<close> and aes: \<open>aenv (fv_list es) env env\<^sub>2\<close>
    and lav: \<open>list_all2 (\<approx>\<^sub>v) vs vs\<^sub>2\<close> by (auto simp: aenv_def)
  from EcConsBub.IH[OF ae] obtain r\<^sub>2 where e\<^sub>2: \<open>env\<^sub>2 \<turnstile> e,ns \<Down> r\<^sub>2,ns\<^sub>1\<close> and hr: \<open>hreq r r\<^sub>2\<close>
    by auto
  show ?case
    using Bigstep.EcConsBub[OF e\<^sub>2] hreq_bubble[OF hr] EcConsBub.hyps
          hreq_push[OF hr cfeq_conI[OF lav aes]]
    by blast
next
  case (EmHit p v bs env e ns r ns' cls env\<^sub>2 u\<^sub>2)
  from EmHit.prems have ae: \<open>aenv (fv e - pvars p) env env\<^sub>2\<close> and vu: \<open>v \<approx>\<^sub>v u\<^sub>2\<close>
    by (auto simp: aenv_def)
  from cpmatch_cong[OF vu, of p] EmHit.hyps obtain bs\<^sub>2
    where m\<^sub>2: \<open>cpmatch p u\<^sub>2 = Some bs\<^sub>2\<close> and eb: \<open>beq bs bs\<^sub>2\<close>
    by (auto simp: rel_option_iff split: option.splits)
  have dom: \<open>set (map fst bs) = pvars p\<close> using EmHit.hyps cpmatch_dom by blast
  have ae\<^sub>2: \<open>aenv (fv e - set (map fst bs)) env env\<^sub>2\<close> unfolding dom by (rule ae)
  have \<open>aenv (fv e) (bs @ env) (bs\<^sub>2 @ env\<^sub>2)\<close> by (rule aenv_append_beq[OF eb ae\<^sub>2])
  from EmHit.IH[OF this] obtain r\<^sub>2
    where e\<^sub>2: \<open>(bs\<^sub>2 @ env\<^sub>2) \<turnstile> e,ns \<Down> r\<^sub>2,ns'\<close> and hr: \<open>hreq r r\<^sub>2\<close>
    by auto
  show ?case using m\<^sub>2 e\<^sub>2 hr by (auto intro: Dintros)
next
  case (EmMiss p v env cls ns r ns' e env\<^sub>2 u\<^sub>2)
  from EmMiss.prems have acls: \<open>aenv (fv_arms cls) env env\<^sub>2\<close> and vu: \<open>v \<approx>\<^sub>v u\<^sub>2\<close>
    by (auto simp: aenv_def)
  have m\<^sub>2: \<open>cpmatch p u\<^sub>2 = None\<close>
    using cpmatch_cong[OF vu, of p] EmMiss.hyps
    by (auto simp: rel_option_iff split: option.splits)
  from EmMiss.IH[OF acls vu] obtain r\<^sub>2
    where c\<^sub>2: \<open>env\<^sub>2 \<turnstile> u\<^sub>2 \<Zrres> cls,ns \<Down> r\<^sub>2,ns'\<close> and hr: \<open>hreq r r\<^sub>2\<close>
    by auto
  show ?case using m\<^sub>2 c\<^sub>2 hr by (auto intro: Dintros)
next
  case (ApClos x av cenv b ns r ns' fw\<^sub>2 av\<^sub>2)
  from ApClos.prems obtain cenv\<^sub>2 where fw\<^sub>2: \<open>fw\<^sub>2 = Vclos cenv\<^sub>2 x b\<close>
    and acenv: \<open>aenv (fv b - {x}) cenv cenv\<^sub>2\<close> and eav: \<open>av \<approx>\<^sub>v av\<^sub>2\<close>
    by (auto simp: aenv_def cveq_shape)
  from ApClos.IH[OF aenv_cons[OF eav acenv]] obtain r\<^sub>2
    where b\<^sub>2: \<open>((x, av\<^sub>2) # cenv\<^sub>2) \<turnstile> b,ns \<Down> r\<^sub>2,ns'\<close> and hr: \<open>hreq r r\<^sub>2\<close> by auto
  show ?case unfolding fw\<^sub>2 using b\<^sub>2 hr by (auto intro: Dintros)
next
  case (ApClosrec x av g cenv b ns r ns' fw\<^sub>2 av\<^sub>2)
  from ApClosrec.prems obtain cenv\<^sub>2 where fw\<^sub>2: \<open>fw\<^sub>2 = Vclosrec cenv\<^sub>2 g x b\<close>
    and acenv: \<open>aenv (fv b - {x, g}) cenv cenv\<^sub>2\<close> and eav: \<open>av \<approx>\<^sub>v av\<^sub>2\<close>
    by (auto simp: aenv_def cveq_shape)
  have rec: \<open>Vclosrec cenv g x b \<approx>\<^sub>v Vclosrec cenv\<^sub>2 g x b\<close> using acenv by (rule cveq_closrecI)
  have acenv': \<open>aenv (fv b - {x} - {g}) cenv cenv\<^sub>2\<close> using acenv by (auto simp: aenv_def)
  have inner: \<open>aenv (fv b - {x}) ((g, Vclosrec cenv g x b) # cenv)
                                 ((g, Vclosrec cenv\<^sub>2 g x b) # cenv\<^sub>2)\<close>
    by (rule aenv_cons[OF rec acenv'])
  from ApClosrec.IH[OF aenv_cons[OF eav inner]] obtain r\<^sub>2
    where b\<^sub>2: \<open>((x, av\<^sub>2) # (g, Vclosrec cenv\<^sub>2 g x b) # cenv\<^sub>2) \<turnstile> b,ns \<Down> r\<^sub>2,ns'\<close>
      and hr: \<open>hreq r r\<^sub>2\<close>
    by auto
  show ?case unfolding fw\<^sub>2 using b\<^sub>2 hr by (auto intro: Dintros)
next
  case (ApCont av fs ns r ns' fw\<^sub>2 av\<^sub>2)
  from ApCont.prems obtain fs\<^sub>2 where fw\<^sub>2: \<open>fw\<^sub>2 = VCont fs\<^sub>2\<close> and lfs: \<open>list_all2 (\<approx>\<^sub>f) fs fs\<^sub>2\<close>
    and eav: \<open>av \<approx>\<^sub>v av\<^sub>2\<close> by (auto simp: cveq_shape)
  from ApCont.IH[OF eav lfs] obtain r\<^sub>2 where u\<^sub>2: \<open>av\<^sub>2 \<leadsto> fs\<^sub>2,ns \<Down> r\<^sub>2,ns'\<close> and hr: \<open>hreq r r\<^sub>2\<close>
    by auto
  show ?case unfolding fw\<^sub>2 using u\<^sub>2 hr by (auto intro: Dintros)
next
  case (StApp1 env a ns av ns\<^sub>1 v r ns\<^sub>2 u\<^sub>2 fr\<^sub>2)
  from StApp1.prems obtain env\<^sub>2 where fr\<^sub>2: \<open>fr\<^sub>2 = CFapp1 env\<^sub>2 a\<close> and aa: \<open>aenv (fv a) env env\<^sub>2\<close>
    and vu: \<open>v \<approx>\<^sub>v u\<^sub>2\<close> by (auto simp: aenv_def cfeq_shape)
  from aa obtain av' where a\<^sub>2: \<open>env\<^sub>2 \<turnstile> a,ns \<Down> (HRval av'),ns\<^sub>1\<close> and ea: \<open>av \<approx>\<^sub>v av'\<close>
    by (blast dest: StApp1.IH hreq_valL[THEN iffD1])
  from vu ea obtain r\<^sub>2 where ap\<^sub>2: \<open>u\<^sub>2 \<sqdot> av',ns\<^sub>1 \<Down> r\<^sub>2,ns\<^sub>2\<close> and hr: \<open>hreq r r\<^sub>2\<close>
    by (auto dest: StApp1.IH)
  show ?case unfolding fr\<^sub>2 using a\<^sub>2 ap\<^sub>2 hr by (auto intro: Dintros)
next
  case (StApp1Bub env a ns r ns\<^sub>1 r' v u\<^sub>2 fr\<^sub>2)
  from StApp1Bub.prems obtain env\<^sub>2
    where fr\<^sub>2: \<open>fr\<^sub>2 = CFapp1 env\<^sub>2 a\<close> and aa: \<open>aenv (fv a) env env\<^sub>2\<close>
    and vu: \<open>v \<approx>\<^sub>v u\<^sub>2\<close> by (auto simp: aenv_def cfeq_shape)
  from StApp1Bub.IH[OF aa] obtain r\<^sub>2 where a\<^sub>2: \<open>env\<^sub>2 \<turnstile> a,ns \<Down> r\<^sub>2,ns\<^sub>1\<close> and hr: \<open>hreq r r\<^sub>2\<close>
    by auto
  show ?case unfolding fr\<^sub>2
    using Bigstep.StApp1Bub[OF a\<^sub>2] hreq_bubble[OF hr] StApp1Bub.hyps hreq_push[OF hr FApp2[OF vu]]
    by blast
next
  case (StApp2 fw v ns r ns' u\<^sub>2 fr\<^sub>2)
  from StApp2.prems obtain fw'
    where fr\<^sub>2: \<open>fr\<^sub>2 = CFapp2 fw'\<close> and efw: \<open>fw \<approx>\<^sub>v fw'\<close> and vu: \<open>v \<approx>\<^sub>v u\<^sub>2\<close>
    by (auto simp: cfeq_shape)
  from StApp2.IH[OF efw vu] obtain r\<^sub>2 where ap\<^sub>2: \<open>fw' \<sqdot> u\<^sub>2,ns \<Down> r\<^sub>2,ns'\<close> and hr: \<open>hreq r r\<^sub>2\<close>
    by auto
  show ?case unfolding fr\<^sub>2 using ap\<^sub>2 hr by (auto intro: Dintros)
next
  case (StLet x v env b ns r ns' u\<^sub>2 fr\<^sub>2)
  from StLet.prems obtain env\<^sub>2
    where fr\<^sub>2: \<open>fr\<^sub>2 = CFlet x env\<^sub>2 b\<close> and ab: \<open>aenv (fv b - {x}) env env\<^sub>2\<close>
    and vu: \<open>v \<approx>\<^sub>v u\<^sub>2\<close> by (auto simp: aenv_def cfeq_shape)
  from StLet.IH[OF aenv_cons[OF vu ab]] obtain r\<^sub>2
    where b\<^sub>2: \<open>((x, u\<^sub>2) # env\<^sub>2) \<turnstile> b,ns \<Down> r\<^sub>2,ns'\<close> and hr: \<open>hreq r r\<^sub>2\<close> by auto
  show ?case unfolding fr\<^sub>2 using b\<^sub>2 hr by (auto intro: Dintros)
next
  case (StCon env c v vs es ns r ns' u\<^sub>2 fr\<^sub>2)
  from StCon.prems obtain vs\<^sub>2 env\<^sub>2 where fr\<^sub>2: \<open>fr\<^sub>2 = CFcon c vs\<^sub>2 env\<^sub>2 es\<close>
    and lvs: \<open>list_all2 (\<approx>\<^sub>v) vs vs\<^sub>2\<close> and aes: \<open>aenv (fv_list es) env env\<^sub>2\<close> and vu: \<open>v \<approx>\<^sub>v u\<^sub>2\<close>
    by (auto simp: aenv_def cfeq_shape)
  have \<open>list_all2 (\<approx>\<^sub>v) (v # vs) (u\<^sub>2 # vs\<^sub>2)\<close> using vu lvs by simp
  from StCon.IH[OF aes this] obtain r\<^sub>2
    where c\<^sub>2: \<open>env\<^sub>2 \<turnstile> c \<langle>(u\<^sub>2 # vs\<^sub>2);es\<rangle>,ns \<Down> r\<^sub>2,ns'\<close> and hr: \<open>hreq r r\<^sub>2\<close>
    by auto
  show ?case unfolding fr\<^sub>2 using c\<^sub>2 hr by (auto intro: Dintros)
next
  case (StMatch env v cls ns r ns' u\<^sub>2 fr\<^sub>2)
  from StMatch.prems obtain env\<^sub>2 where fr\<^sub>2: \<open>fr\<^sub>2 = CFmatch env\<^sub>2 cls\<close>
    and acls: \<open>aenv (fv_arms cls) env env\<^sub>2\<close> and vu: \<open>v \<approx>\<^sub>v u\<^sub>2\<close> by (auto simp: aenv_def cfeq_shape)
  from StMatch.IH[OF acls vu] obtain r\<^sub>2
    where m\<^sub>2: \<open>env\<^sub>2 \<turnstile> u\<^sub>2 \<Zrres> cls,ns \<Down> r\<^sub>2,ns'\<close> and hr: \<open>hreq r r\<^sub>2\<close>
    by auto
  show ?case unfolding fr\<^sub>2 using m\<^sub>2 hr by (auto intro: Dintros)
next
  case (StPerfn1 env a ns av ns\<^sub>1 i op u\<^sub>2 fr\<^sub>2)
  from StPerfn1.prems obtain env\<^sub>2
    where fr\<^sub>2: \<open>fr\<^sub>2 = CFperfn1 env\<^sub>2 op a\<close> and aa: \<open>aenv (fv a) env env\<^sub>2\<close>
    and vu: \<open>u\<^sub>2 = Vname i\<close> by (auto simp: aenv_def cfeq_shape cveq_shape)
  from StPerfn1.IH[OF aa] obtain av'
    where a\<^sub>2: \<open>env\<^sub>2 \<turnstile> a,ns \<Down> (HRval av'),ns\<^sub>1\<close> and ea: \<open>av \<approx>\<^sub>v av'\<close>
    by auto
  show ?case unfolding fr\<^sub>2 vu using a\<^sub>2 ea by (auto intro: Dintros)
next
  case (StPerfn1Bub env a ns r ns\<^sub>1 r' v op u\<^sub>2 fr\<^sub>2)
  from StPerfn1Bub.prems obtain env\<^sub>2
    where fr\<^sub>2: \<open>fr\<^sub>2 = CFperfn1 env\<^sub>2 op a\<close> and aa: \<open>aenv (fv a) env env\<^sub>2\<close>
    and vu: \<open>v \<approx>\<^sub>v u\<^sub>2\<close> by (auto simp: aenv_def cfeq_shape)
  from StPerfn1Bub.IH[OF aa] obtain r\<^sub>2 where a\<^sub>2: \<open>env\<^sub>2 \<turnstile> a,ns \<Down> r\<^sub>2,ns\<^sub>1\<close> and hr: \<open>hreq r r\<^sub>2\<close>
    by auto
  show ?case unfolding fr\<^sub>2
    using Bigstep.StPerfn1Bub[OF a\<^sub>2] hreq_bubble[OF hr] StPerfn1Bub.hyps
          hreq_push[OF hr FPerfn2[OF vu]]
    by blast
next
  case (StPerfn2 v i op ns u\<^sub>2 fr\<^sub>2)
  from StPerfn2.prems have fr\<^sub>2: \<open>fr\<^sub>2 = CFperfn2 (Vname i) op\<close>
    by (auto simp: cfeq_shape cveq_shape)
  show ?case unfolding fr\<^sub>2 using StPerfn2.prems by (auto intro: Dintros)
next
  case (UwCons v f ns r ns\<^sub>1 fs r' ns\<^sub>2 u\<^sub>2 fs\<^sub>2)
  from UwCons.prems obtain g gs where fs\<^sub>2: \<open>fs\<^sub>2 = g # gs\<close> and fg: \<open>f \<approx>\<^sub>f g\<close>
    and lgs: \<open>list_all2 (\<approx>\<^sub>f) fs gs\<close> and vu: \<open>v \<approx>\<^sub>v u\<^sub>2\<close> by (auto simp: list_all2_Cons1)
  from vu fg obtain r\<^sub>2 where s\<^sub>2: \<open>u\<^sub>2 \<Zdres> g,ns \<Down> r\<^sub>2,ns\<^sub>1\<close> and hr: \<open>hreq r r\<^sub>2\<close>
    by (auto dest: UwCons.IH)
  from hr lgs obtain r\<^sub>2' where u2c: \<open>resume r\<^sub>2 gs,ns\<^sub>1 \<Down> r\<^sub>2',ns\<^sub>2\<close> and hr': \<open>hreq r' r\<^sub>2'\<close>
    by (auto dest: UwCons.IH)
  show ?case unfolding fs\<^sub>2 using s\<^sub>2 u2c hr' by (auto intro: Dintros)
next
  case (RsVal v fs ns r ns' q\<^sub>2 fs\<^sub>2)
  from RsVal.prems obtain v' where q\<^sub>2: \<open>q\<^sub>2 = HRval v'\<close> and ev: \<open>v \<approx>\<^sub>v v'\<close>
    and lfs: \<open>list_all2 (\<approx>\<^sub>f) fs fs\<^sub>2\<close> by auto
  from RsVal.IH[OF ev lfs] obtain r\<^sub>2 where u\<^sub>2: \<open>v' \<leadsto> fs\<^sub>2,ns \<Down> r\<^sub>2,ns'\<close> and hr: \<open>hreq r r\<^sub>2\<close>
    by auto
  show ?case unfolding q\<^sub>2 using u\<^sub>2 hr by (auto intro: Dintros)
next
  case (RsOp l m w fr fs ns r ns' q\<^sub>2 fs\<^sub>2)
  from RsOp.prems obtain w' fr' where q\<^sub>2: \<open>q\<^sub>2 = HRop l m w' fr'\<close> and ew: \<open>w \<approx>\<^sub>v w'\<close>
    and efr: \<open>list_all2 (\<approx>\<^sub>f) fr fr'\<close> and lfs: \<open>list_all2 (\<approx>\<^sub>f) fs fs\<^sub>2\<close> by auto
  from RsOp.IH[OF ew efr lfs] obtain r\<^sub>2
    where t\<^sub>2: \<open>throw l \<^bold>@ m  w' \<parallel> fr' \<parallel> fs\<^sub>2,ns \<Down> r\<^sub>2,ns'\<close> and hr: \<open>hreq r r\<^sub>2\<close> by auto
  show ?case unfolding q\<^sub>2 using t\<^sub>2 hr by (auto intro: Dintros)
next
  case (RsOpn i op w fr fs ns r ns' q\<^sub>2 fs\<^sub>2)
  from RsOpn.prems obtain w' fr' where q\<^sub>2: \<open>q\<^sub>2 = HRopn i op w' fr'\<close> and ew: \<open>w \<approx>\<^sub>v w'\<close>
    and efr: \<open>list_all2 (\<approx>\<^sub>f) fr fr'\<close> and lfs: \<open>list_all2 (\<approx>\<^sub>f) fs fs\<^sub>2\<close> by auto
  from RsOpn.IH[OF ew efr lfs] obtain r\<^sub>2
    where t\<^sub>2: \<open>thrown i op  w' \<parallel> fr' \<parallel> fs\<^sub>2,ns \<Down> r\<^sub>2,ns'\<close> and hr: \<open>hreq r r\<^sub>2\<close> by auto
  show ?case unfolding q\<^sub>2 using t\<^sub>2 hr by (auto intro: Dintros)
next
  case (ThCatch hv w fr l ns r ns\<^sub>1 fs r' ns\<^sub>2 w\<^sub>2 gr\<^sub>2 gs\<^sub>2)
  from ThCatch.prems have ew: \<open>w \<approx>\<^sub>v w\<^sub>2\<close> and egr: \<open>list_all2 (\<approx>\<^sub>f) fr gr\<^sub>2\<close>
    and lg: \<open>list_all2 (\<approx>\<^sub>f) (CFhandle l hv # fs) gs\<^sub>2\<close> by auto
  from lg obtain hv\<^sub>2 gs' where gs\<^sub>2: \<open>gs\<^sub>2 = CFhandle l hv\<^sub>2 # gs'\<close>
    and ehv: \<open>hv \<approx>\<^sub>v hv\<^sub>2\<close> and lgs: \<open>list_all2 (\<approx>\<^sub>f) fs gs'\<close>
    by (auto simp: list_all2_Cons1 cfeq_shape)
  have argeq: \<open>Vcon (tuple_con 2) [w, VCont (fr @ [CFhandle l hv])]
               \<approx>\<^sub>v Vcon (tuple_con 2) [w\<^sub>2, VCont (gr\<^sub>2 @ [CFhandle l hv\<^sub>2])]\<close>
    using ew egr ehv by (auto intro: QCon QCont list_all2_appendI FHandle)
  from ehv argeq obtain r\<^sub>2 where
    a\<^sub>2: \<open>hv\<^sub>2 \<sqdot> (Vcon (tuple_con 2) [w\<^sub>2, VCont (gr\<^sub>2 @ [CFhandle l hv\<^sub>2])]),ns \<Down> r\<^sub>2,ns\<^sub>1\<close>
    and hr: \<open>hreq r r\<^sub>2\<close> by (auto dest: ThCatch.IH)
  from hr lgs obtain r\<^sub>2' where u\<^sub>2: \<open>resume r\<^sub>2 gs',ns\<^sub>1 \<Down> r\<^sub>2',ns\<^sub>2\<close> and hr': \<open>hreq r' r\<^sub>2'\<close>
    by (auto dest: ThCatch.IH)
  show ?case unfolding gs\<^sub>2 using a\<^sub>2 u\<^sub>2 hr' by (auto intro: Dintros)
next
  case (ThSkip l m w fr hv fs ns r ns' w\<^sub>2 gr\<^sub>2 gs\<^sub>2)
  from ThSkip.prems have ew: \<open>w \<approx>\<^sub>v w\<^sub>2\<close> and egr: \<open>list_all2 (\<approx>\<^sub>f) fr gr\<^sub>2\<close>
    and lg: \<open>list_all2 (\<approx>\<^sub>f) (CFhandle l hv # fs) gs\<^sub>2\<close> by auto
  from lg obtain hv\<^sub>2 gs' where gs\<^sub>2: \<open>gs\<^sub>2 = CFhandle l hv\<^sub>2 # gs'\<close>
    and ehv: \<open>hv \<approx>\<^sub>v hv\<^sub>2\<close> and lgs: \<open>list_all2 (\<approx>\<^sub>f) fs gs'\<close>
    by (auto simp: list_all2_Cons1 cfeq_shape)
  have \<open>list_all2 (\<approx>\<^sub>f) (fr @ [CFhandle l hv]) (gr\<^sub>2 @ [CFhandle l hv\<^sub>2])\<close>
    using egr ehv by (auto intro: list_all2_appendI FHandle)
  from ThSkip.IH[OF ew this lgs] obtain r\<^sub>2
    where t\<^sub>2: \<open>throw l \<^bold>@ m  w\<^sub>2 \<parallel> (gr\<^sub>2 @ [CFhandle l hv\<^sub>2]) \<parallel> gs',ns \<Down> r\<^sub>2,ns'\<close>
      and hr: \<open>hreq r r\<^sub>2\<close> by auto
  show ?case unfolding gs\<^sub>2 using t\<^sub>2 hr by (auto intro: Dintros)
next
  case (ThOther l' l m w fr hv fs ns r ns' w\<^sub>2 gr\<^sub>2 gs\<^sub>2)
  from ThOther.prems have ew: \<open>w \<approx>\<^sub>v w\<^sub>2\<close> and egr: \<open>list_all2 (\<approx>\<^sub>f) fr gr\<^sub>2\<close>
    and lg: \<open>list_all2 (\<approx>\<^sub>f) (CFhandle l' hv # fs) gs\<^sub>2\<close> by auto
  from lg obtain hv\<^sub>2 gs' where gs\<^sub>2: \<open>gs\<^sub>2 = CFhandle l' hv\<^sub>2 # gs'\<close>
    and ehv: \<open>hv \<approx>\<^sub>v hv\<^sub>2\<close> and lgs: \<open>list_all2 (\<approx>\<^sub>f) fs gs'\<close>
    by (auto simp: list_all2_Cons1 cfeq_shape)
  have \<open>list_all2 (\<approx>\<^sub>f) (fr @ [CFhandle l' hv]) (gr\<^sub>2 @ [CFhandle l' hv\<^sub>2])\<close>
    using egr ehv by (auto intro: list_all2_appendI FHandle)
  from ThOther.IH[OF ew this lgs] obtain r\<^sub>2
    where t\<^sub>2: \<open>throw l \<^bold>@ m  w\<^sub>2 \<parallel> (gr\<^sub>2 @ [CFhandle l' hv\<^sub>2]) \<parallel> gs',ns \<Down> r\<^sub>2,ns'\<close>
      and hr: \<open>hreq r r\<^sub>2\<close> by auto
  show ?case unfolding gs\<^sub>2 using t\<^sub>2 hr ThOther.hyps by (auto intro: Dintros)
next
  case (ThMaskEq l m w fr fs ns r ns' w\<^sub>2 gr\<^sub>2 gs\<^sub>2)
  from ThMaskEq.prems have ew: \<open>w \<approx>\<^sub>v w\<^sub>2\<close> and egr: \<open>list_all2 (\<approx>\<^sub>f) fr gr\<^sub>2\<close>
    and lg: \<open>list_all2 (\<approx>\<^sub>f) (CFmask l # fs) gs\<^sub>2\<close> by auto
  from lg obtain gs' where gs\<^sub>2: \<open>gs\<^sub>2 = CFmask l # gs'\<close> and lgs: \<open>list_all2 (\<approx>\<^sub>f) fs gs'\<close>
    by (auto simp: list_all2_Cons1 cfeq_shape)
  have \<open>list_all2 (\<approx>\<^sub>f) (fr @ [CFmask l]) (gr\<^sub>2 @ [CFmask l])\<close>
    using egr by (auto intro: list_all2_appendI FMask)
  from ThMaskEq.IH[OF ew this lgs] obtain r\<^sub>2
    where t\<^sub>2: \<open>throw l \<^bold>@ (Suc m)  w\<^sub>2 \<parallel> (gr\<^sub>2 @ [CFmask l]) \<parallel> gs',ns \<Down> r\<^sub>2,ns'\<close>
      and hr: \<open>hreq r r\<^sub>2\<close> by auto
  show ?case unfolding gs\<^sub>2 using t\<^sub>2 hr by (auto intro: Dintros)
next
  case (ThMaskNeq l' l m w fr fs ns r ns' w\<^sub>2 gr\<^sub>2 gs\<^sub>2)
  from ThMaskNeq.prems have ew: \<open>w \<approx>\<^sub>v w\<^sub>2\<close> and egr: \<open>list_all2 (\<approx>\<^sub>f) fr gr\<^sub>2\<close>
    and lg: \<open>list_all2 (\<approx>\<^sub>f) (CFmask l' # fs) gs\<^sub>2\<close> by auto
  from lg obtain gs' where gs\<^sub>2: \<open>gs\<^sub>2 = CFmask l' # gs'\<close> and lgs: \<open>list_all2 (\<approx>\<^sub>f) fs gs'\<close>
    by (auto simp: list_all2_Cons1 cfeq_shape)
  have \<open>list_all2 (\<approx>\<^sub>f) (fr @ [CFmask l']) (gr\<^sub>2 @ [CFmask l'])\<close>
    using egr by (auto intro: list_all2_appendI FMask)
  from ThMaskNeq.IH[OF ew this lgs] obtain r\<^sub>2
    where t\<^sub>2: \<open>throw l \<^bold>@ m  w\<^sub>2 \<parallel> (gr\<^sub>2 @ [CFmask l']) \<parallel> gs',ns \<Down> r\<^sub>2,ns'\<close>
      and hr: \<open>hreq r r\<^sub>2\<close> by auto
  show ?case unfolding gs\<^sub>2 using t\<^sub>2 hr ThMaskNeq.hyps by (auto intro: Dintros)
next
  case (ThPlain f l m w fr fs ns r ns' w\<^sub>2 gr\<^sub>2 gs\<^sub>2)
  from ThPlain.prems have ew: \<open>w \<approx>\<^sub>v w\<^sub>2\<close> and egr: \<open>list_all2 (\<approx>\<^sub>f) fr gr\<^sub>2\<close>
    and lg: \<open>list_all2 (\<approx>\<^sub>f) (f # fs) gs\<^sub>2\<close> by auto
  from lg obtain g gs' where gs\<^sub>2: \<open>gs\<^sub>2 = g # gs'\<close> and fg: \<open>f \<approx>\<^sub>f g\<close>
    and lgs: \<open>list_all2 (\<approx>\<^sub>f) fs gs'\<close> by (auto simp: list_all2_Cons1)
  have plg: \<open>plain_frame g\<close> using fg ThPlain.hyps by (simp add: cfeq_plain)
  have \<open>list_all2 (\<approx>\<^sub>f) (fr @ [f]) (gr\<^sub>2 @ [g])\<close>
    using egr fg by (auto intro: list_all2_appendI)
  from ThPlain.IH[OF ew this lgs] obtain r\<^sub>2
    where t\<^sub>2: \<open>throw l \<^bold>@ m  w\<^sub>2 \<parallel> (gr\<^sub>2 @ [g]) \<parallel> gs',ns \<Down> r\<^sub>2,ns'\<close> and hr: \<open>hreq r r\<^sub>2\<close> by auto
  show ?case unfolding gs\<^sub>2 using t\<^sub>2 hr plg by (auto intro: Dintros)
next
  case (TnCatch op \<phi> \<phi>' hv w fr l i ns r ns\<^sub>1 fs r' ns\<^sub>2 w\<^sub>2 gr\<^sub>2 gs\<^sub>2)
  from TnCatch.prems have ew: \<open>w \<approx>\<^sub>v w\<^sub>2\<close> and egr: \<open>list_all2 (\<approx>\<^sub>f) fr gr\<^sub>2\<close>
    and lg: \<open>list_all2 (\<approx>\<^sub>f) (CFhandlen l i hv \<phi> # fs) gs\<^sub>2\<close> by auto
  from lg obtain hv\<^sub>2 gs' where gs\<^sub>2: \<open>gs\<^sub>2 = CFhandlen l i hv\<^sub>2 \<phi> # gs'\<close>
    and ehv: \<open>hv \<approx>\<^sub>v hv\<^sub>2\<close> and lgs: \<open>list_all2 (\<approx>\<^sub>f) fs gs'\<close>
    by (auto simp: list_all2_Cons1 cfeq_shape)
  have argeq: \<open>Vcon (tuple_con 3) [Vlit (LStr op), w, VCont (fr @ [CFhandlen l i hv \<phi>'])]
               \<approx>\<^sub>v Vcon (tuple_con 3) [Vlit (LStr op), w\<^sub>2, VCont (gr\<^sub>2 @ [CFhandlen l i hv\<^sub>2 \<phi>'])]\<close>
    using ew egr ehv by (auto intro: QCon QCont QLit list_all2_appendI FHandlen)
  from ehv argeq obtain r\<^sub>2 where
    a\<^sub>2: \<open>hv\<^sub>2 \<sqdot> (Vcon (tuple_con 3)
            [Vlit (LStr op), w\<^sub>2, VCont (gr\<^sub>2 @ [CFhandlen l i hv\<^sub>2 \<phi>'])]),ns \<Down> r\<^sub>2,ns\<^sub>1\<close>
    and hr: \<open>hreq r r\<^sub>2\<close> by (auto dest: TnCatch.IH)
  from hr lgs obtain r\<^sub>2' where u\<^sub>2: \<open>resume r\<^sub>2 gs',ns\<^sub>1 \<Down> r\<^sub>2',ns\<^sub>2\<close> and hr': \<open>hreq r' r\<^sub>2'\<close>
    by (auto dest: TnCatch.IH)
  show ?case unfolding gs\<^sub>2 using a\<^sub>2 u\<^sub>2 hr' TnCatch.hyps by (auto intro: Dintros)
next
  case (TnOther j i op w fr l hv \<phi> fs ns r ns' w\<^sub>2 gr\<^sub>2 gs\<^sub>2)
  from TnOther.prems have ew: \<open>w \<approx>\<^sub>v w\<^sub>2\<close> and egr: \<open>list_all2 (\<approx>\<^sub>f) fr gr\<^sub>2\<close>
    and lg: \<open>list_all2 (\<approx>\<^sub>f) (CFhandlen l j hv \<phi> # fs) gs\<^sub>2\<close> by auto
  from lg obtain hv\<^sub>2 gs' where gs\<^sub>2: \<open>gs\<^sub>2 = CFhandlen l j hv\<^sub>2 \<phi> # gs'\<close>
    and ehv: \<open>hv \<approx>\<^sub>v hv\<^sub>2\<close> and lgs: \<open>list_all2 (\<approx>\<^sub>f) fs gs'\<close>
    by (auto simp: list_all2_Cons1 cfeq_shape)
  have \<open>list_all2 (\<approx>\<^sub>f) (fr @ [CFhandlen l j hv \<phi>]) (gr\<^sub>2 @ [CFhandlen l j hv\<^sub>2 \<phi>])\<close>
    using egr ehv by (auto intro: list_all2_appendI FHandlen)
  from TnOther.IH[OF ew this lgs] obtain r\<^sub>2
    where t\<^sub>2: \<open>thrown i op  w\<^sub>2 \<parallel> (gr\<^sub>2 @ [CFhandlen l j hv\<^sub>2 \<phi>]) \<parallel> gs',ns \<Down> r\<^sub>2,ns'\<close>
      and hr: \<open>hreq r r\<^sub>2\<close> by auto
  show ?case unfolding gs\<^sub>2 using t\<^sub>2 hr TnOther.hyps by (auto intro: Dintros)
next
  case (TnPlain f i op w fr fs ns r ns' w\<^sub>2 gr\<^sub>2 gs\<^sub>2)
  from TnPlain.prems have ew: \<open>w \<approx>\<^sub>v w\<^sub>2\<close> and egr: \<open>list_all2 (\<approx>\<^sub>f) fr gr\<^sub>2\<close>
    and lg: \<open>list_all2 (\<approx>\<^sub>f) (f # fs) gs\<^sub>2\<close> by auto
  from lg obtain g gs' where gs\<^sub>2: \<open>gs\<^sub>2 = g # gs'\<close> and fg: \<open>f \<approx>\<^sub>f g\<close>
    and lgs: \<open>list_all2 (\<approx>\<^sub>f) fs gs'\<close> by (auto simp: list_all2_Cons1)
  have plg: \<open>plainn_frame g\<close> using fg TnPlain.hyps by (simp add: cfeq_plainn)
  have \<open>list_all2 (\<approx>\<^sub>f) (fr @ [f]) (gr\<^sub>2 @ [g])\<close>
    using egr fg by (auto intro: list_all2_appendI)
  from TnPlain.IH[OF ew this lgs] obtain r\<^sub>2
    where t\<^sub>2: \<open>thrown i op  w\<^sub>2 \<parallel> (gr\<^sub>2 @ [g]) \<parallel> gs',ns \<Down> r\<^sub>2,ns'\<close> and hr: \<open>hreq r r\<^sub>2\<close> by auto
  show ?case unfolding gs\<^sub>2 using t\<^sub>2 hr plg by (auto intro: Dintros)
qed (auto simp: cfeq_shape cveq_shape intro: Dintros cveq_closI cveq_cfeq.intros)

end
