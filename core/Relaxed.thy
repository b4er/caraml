theory Relaxed
  imports Core
begin

section \<open>The relaxed evaluator: protocol violations as a marker\<close>

text \<open>Three error sites of the evaluator are protocol violations, not type
  errors: a named operation its handler's protocol residual forbids
  (\<^const>\<open>cthrown\<close>, \<^const>\<open>step_prot\<close>), an action returning at a residual that
  is not nullable (\<^const>\<open>cstep\<close> at \<^const>\<open>CFhandlen\<close>, \<^const>\<open>exit_prot\<close>),
  and a named operation escaping a top-level binding (\<^const>\<open>crun\<close> at
  \<^const>\<open>HRopn\<close>). The protocol grades govern them, not the value typing.

  The relaxed mode of the evaluator makes those sites raise a marker, which
  the program level reports as a host event on the marker label.
  \<^text>\<open>centry_agr\<close>: the two modes agree clock for clock, except where the
  relaxed one reports a marker and the strict one is stuck. So type soundness
  (the relaxed evaluator is never stuck) and the protocol argument (no marker)
  together give safety of the strict one.\<close>

abbreviation \<open>cevalR \<equiv> mceval True\<close>
abbreviation \<open>cevconR \<equiv> mcevcon True\<close>
abbreviation \<open>cevalmR \<equiv> mcevalm True\<close>
abbreviation \<open>capplyR \<equiv> mcapply True\<close>
abbreviation \<open>cstepR \<equiv> mcstep True\<close>
abbreviation \<open>cunwindR \<equiv> mcunwind True\<close>
abbreviation \<open>cresumeR \<equiv> mcresume True\<close>
abbreviation \<open>cthrowR \<equiv> mcthrow True\<close>
abbreviation \<open>cthrownR \<equiv> mcthrown True\<close>
abbreviation \<open>crunR \<equiv> mcrun True\<close>
abbreviation \<open>ceval_progR \<equiv> mceval_prog True\<close>
abbreviation \<open>centryR \<equiv> mcentry True\<close>

abbreviation csemR :: \<open>ffi \<Rightarrow> cprog \<Rightarrow> nat \<Rightarrow> cval cres \<times> ffi_ev list\<close> where
  \<open>csemR \<equiv> centryR (str ''main'')\<close>

subsection \<open>Agreement of the two modes\<close>

text \<open>The two modes agree on a pair of results when they are equal, or the
  strict one is stuck where the relaxed one reports a marker, with the same
  supply.\<close>

definition agr :: \<open>hres \<times> nat \<Rightarrow> hres \<times> nat \<Rightarrow> bool\<close> where
  \<open>agr p p' \<longleftrightarrow> snd p' = snd p \<and> (fst p' = fst p \<or> (fst p = HRerr \<and> viol (fst p')))\<close>

lemma agr_refl[simp, intro!]: \<open>agr p p\<close>
  by (simp add: agr_def)

lemma agr_viol[simp]: \<open>viol r \<Longrightarrow> agr (HRerr, ns) (r, ns)\<close>
  by (simp add: agr_def)

lemma agr_val[simp]: \<open>agr p (HRval v, ns) \<longleftrightarrow> p = (HRval v, ns)\<close>
  \<open>agr (HRval v, ns) p' \<longleftrightarrow> p' = (HRval v, ns)\<close>
  by (cases p; cases p'; auto simp: agr_def)+

text \<open>The strict mode produces no marker unless the program performs,
  handles or masks the reserved label (no elaborated program does).\<close>

fun vfree :: \<open>cexp \<Rightarrow> bool\<close> and vfree_es :: \<open>cexp list \<Rightarrow> bool\<close>
and vfree_cls :: \<open>(cpat \<times> cexp) list \<Rightarrow> bool\<close> where
  \<open>vfree (Cvar x) = True\<close>
| \<open>vfree (Clit l) = True\<close>
| \<open>vfree (Clam x b) = vfree b\<close>
| \<open>vfree (Capp f a) = (vfree f \<and> vfree a)\<close>
| \<open>vfree (Clet x e b) = (vfree e \<and> vfree b)\<close>
| \<open>vfree (Cletrec f x e b) = (vfree e \<and> vfree b)\<close>
| \<open>vfree (Ccon c es) = vfree_es es\<close>
| \<open>vfree (Cmatch e cls) = (vfree e \<and> vfree_cls cls)\<close>
| \<open>vfree (Cperform l a) = (l \<noteq> viol_lbl \<and> vfree a)\<close>
| \<open>vfree (Chandle l h b) = (l \<noteq> viol_lbl \<and> vfree h \<and> vfree b)\<close>
| \<open>vfree (Cmask l e) = (l \<noteq> viol_lbl \<and> vfree e)\<close>
| \<open>vfree (Cperformn x op a) = (vfree x \<and> vfree a)\<close>
| \<open>vfree (Chandlen l h \<phi> b) = (vfree h \<and> vfree b)\<close>
| \<open>vfree_es [] = True\<close>
| \<open>vfree_es (e # es) = (vfree e \<and> vfree_es es)\<close>
| \<open>vfree_cls [] = True\<close>
| \<open>vfree_cls ((p, e) # cls) = (vfree e \<and> vfree_cls cls)\<close>

fun vfree_v :: \<open>cval \<Rightarrow> bool\<close> and vfree_vs :: \<open>cval list \<Rightarrow> bool\<close>
and vfree_env :: \<open>(name \<times> cval) list \<Rightarrow> bool\<close>
and vfree_f :: \<open>cframe \<Rightarrow> bool\<close> and vfree_fs :: \<open>cframe list \<Rightarrow> bool\<close> where
  \<open>vfree_v (Vlit l) = True\<close>
| \<open>vfree_v (Vclos env x b) = (vfree_env env \<and> vfree b)\<close>
| \<open>vfree_v (Vclosrec env f x b) = (vfree_env env \<and> vfree b)\<close>
| \<open>vfree_v (Vcon c vs) = vfree_vs vs\<close>
| \<open>vfree_v (VCont fs) = vfree_fs fs\<close>
| \<open>vfree_v (Vname i) = True\<close>
| \<open>vfree_vs [] = True\<close>
| \<open>vfree_vs (v # vs) = (vfree_v v \<and> vfree_vs vs)\<close>
| \<open>vfree_env [] = True\<close>
| \<open>vfree_env ((x, v) # env) = (vfree_v v \<and> vfree_env env)\<close>
| \<open>vfree_f (CFapp1 env a) = (vfree_env env \<and> vfree a)\<close>
| \<open>vfree_f (CFapp2 v) = vfree_v v\<close>
| \<open>vfree_f (CFlet x env b) = (vfree_env env \<and> vfree b)\<close>
| \<open>vfree_f (CFcon c vs env es) = (vfree_vs vs \<and> vfree_env env \<and> vfree_es es)\<close>
| \<open>vfree_f (CFmatch env cls) = (vfree_env env \<and> vfree_cls cls)\<close>
| \<open>vfree_f (CFperf l) = (l \<noteq> viol_lbl)\<close>
| \<open>vfree_f (CFperfn1 env op a) = (vfree_env env \<and> vfree a)\<close>
| \<open>vfree_f (CFperfn2 v op) = vfree_v v\<close>
| \<open>vfree_f (CFhandle l hv) = (l \<noteq> viol_lbl \<and> vfree_v hv)\<close>
| \<open>vfree_f (CFhandlen l i hv \<phi>) = vfree_v hv\<close>
| \<open>vfree_f (CFmask l) = (l \<noteq> viol_lbl)\<close>
| \<open>vfree_fs [] = True\<close>
| \<open>vfree_fs (f # fs) = (vfree_f f \<and> vfree_fs fs)\<close>

fun vfree_r :: \<open>hres \<Rightarrow> bool\<close> where
  \<open>vfree_r (HRval v) = vfree_v v\<close>
| \<open>vfree_r (HRop l m w fr) = (l \<noteq> viol_lbl \<and> vfree_v w \<and> vfree_fs fr)\<close>
| \<open>vfree_r (HRopn i op w fr) = (vfree_v w \<and> vfree_fs fr)\<close>
| \<open>vfree_r r = True\<close>

lemma vfree_env_append[simp]: \<open>vfree_env (a @ b) \<longleftrightarrow> vfree_env a \<and> vfree_env b\<close>
  by (induction a) auto

lemma vfree_fs_append[simp]: \<open>vfree_fs (a @ b) \<longleftrightarrow> vfree_fs a \<and> vfree_fs b\<close>
  by (induction a) auto

lemma vfree_vs_append[simp]: \<open>vfree_vs (a @ b) \<longleftrightarrow> vfree_vs a \<and> vfree_vs b\<close>
  by (induction a) auto

lemma vfree_vs_rev[simp]: \<open>vfree_vs (rev vs) \<longleftrightarrow> vfree_vs vs\<close>
  by (induction vs) auto

lemma vfree_env_map_of: \<open>vfree_env env \<Longrightarrow> map_of env x = Some v \<Longrightarrow> vfree_v v\<close>
  by (induction env) (auto split: if_split_asm)

lemma cpmatch_vfree: \<open>cpmatch p v = Some bs \<Longrightarrow> vfree_v v \<Longrightarrow> vfree_env bs\<close>
  and cpmatch_list_vfree: \<open>cpmatch_list ps vs = Some bs \<Longrightarrow> vfree_vs vs \<Longrightarrow> vfree_env bs\<close>
  by (induction p v and ps vs arbitrary: bs and bs rule: cpmatch_induct)
     (auto split: if_split_asm option.split_asm)

lemma vfree_r_push[simp]:
  \<open>vfree_r (push f r) \<longleftrightarrow>
   vfree_r r \<and> (vfree_f f \<or> (\<forall>l m w fr. r \<noteq> HRop l m w fr) \<and> (\<forall>i op w fr. r \<noteq> HRopn i op w fr))\<close>
  by (cases r) auto

lemma vfree_r_bindr:
  \<open>vfree_r (fst p) \<Longrightarrow> vfree_f f \<Longrightarrow> (\<And>v ns. p = (HRval v, ns) \<Longrightarrow> vfree_r (fst (g v ns))) \<Longrightarrow>
   vfree_r (fst (bindr p f g))\<close>
  by (cases p) (auto simp: bindr_def split: hres.split)

lemma vfree_r_guardr:
  \<open>vfree_r (fst p) \<Longrightarrow> (\<And>v ns. p = (HRval v, ns) \<Longrightarrow> vfree_r (fst (g v ns))) \<Longrightarrow>
   vfree_r (fst (guardr p g))\<close>
  by (cases p) (auto simp: guardr_def split: hres.split)

lemma vfree_r_thenr:
  \<open>vfree_r (fst p) \<Longrightarrow> (\<And>r ns. p = (r, ns) \<Longrightarrow> vfree_r r \<Longrightarrow> vfree_r (fst (g r ns))) \<Longrightarrow>
   vfree_r (fst (thenr p g))\<close>
  by (cases p) (auto simp: thenr_def)

lemma vfree_r_performn[simp]: \<open>vfree_v av \<Longrightarrow> vfree_r (fst (performn xv op av ns))\<close>
  by (cases xv) auto

lemma vfree_r_maskr: \<open>vfree_r r \<Longrightarrow> l \<noteq> viol_lbl \<Longrightarrow> vfree_r (maskr l r)\<close>
  by (cases r) auto

lemma ceval_vfree: \<open>vfree_env env \<Longrightarrow> vfree e \<Longrightarrow> vfree_r (fst (ceval k env e ns))\<close>
  and cevcon_vfree: \<open>vfree_env env \<Longrightarrow> vfree_vs vs \<Longrightarrow> vfree_es es \<Longrightarrow>
    vfree_r (fst (cevcon k env c vs es ns))\<close>
  and cevalm_vfree: \<open>vfree_env env \<Longrightarrow> vfree_v u \<Longrightarrow> vfree_cls cls \<Longrightarrow>
    vfree_r (fst (cevalm k env u cls ns))\<close>
  and capply_vfree: \<open>vfree_v fv \<Longrightarrow> vfree_v av \<Longrightarrow> vfree_r (fst (capply k fv av ns))\<close>
  and cstep_vfree: \<open>vfree_v u \<Longrightarrow> vfree_f f \<Longrightarrow> vfree_r (fst (cstep k u f ns))\<close>
  and cunwind_vfree: \<open>vfree_v u \<Longrightarrow> vfree_fs fs \<Longrightarrow> vfree_r (fst (cunwind k u fs ns))\<close>
  and cresume_vfree: \<open>vfree_r r \<Longrightarrow> vfree_fs fs \<Longrightarrow> vfree_r (fst (cresume k r fs ns))\<close>
  and cthrow_vfree: \<open>l \<noteq> viol_lbl \<Longrightarrow> vfree_v w \<Longrightarrow> vfree_fs fr \<Longrightarrow> vfree_fs fs \<Longrightarrow>
    vfree_r (fst (cthrow k l m w fr fs ns))\<close>
  and cthrown_vfree: \<open>vfree_v w \<Longrightarrow> vfree_fs fr \<Longrightarrow> vfree_fs fs \<Longrightarrow>
    vfree_r (fst (cthrown k i op w fr fs ns))\<close>
proof (induction k env e ns and k env c vs es ns and k env u cls ns and k fv av ns
      and k u f ns and k u fs ns and k r fs ns and k l m w fr fs ns and k i op w fr fs ns
      rule: ceval_induct)
  case ceval_Cvar
  then show ?case by (auto split: option.split dest: vfree_env_map_of)
next
  case cevalm_Cons
  then show ?case by (auto split: option.split dest: cpmatch_vfree)
qed (auto intro!: vfree_r_bindr vfree_r_guardr vfree_r_thenr vfree_r_maskr split: option.split)

text \<open>Agreement, combinator by combinator: a marker on the relaxed side is
  passed along where the strict one passes stuckness along.\<close>

lemma bindr_agr:
  \<open>agr p p' \<Longrightarrow> (\<And>v ns. p = (HRval v, ns) \<Longrightarrow> p' = (HRval v, ns) \<Longrightarrow> agr (g v ns) (g' v ns)) \<Longrightarrow>
   agr (bindr p f g) (bindr p' f g')\<close>
  by (cases p; cases p') (auto simp: agr_def bindr_def viol_def split: hres.split)

lemma guardr_agr:
  \<open>agr p p' \<Longrightarrow> (\<And>v ns. p = (HRval v, ns) \<Longrightarrow> p' = (HRval v, ns) \<Longrightarrow> agr (g v ns) (g' v ns)) \<Longrightarrow>
   agr (guardr p g) (mguardr True p' g')\<close>
  by (cases p; cases p') (auto simp: agr_def guardr_def mguardr_def viol_def split: hres.split)

lemma thenr_agr:
  \<open>agr p p' \<Longrightarrow> (\<And>r ns. p = (r, ns) \<Longrightarrow> agr (g r ns) (g' r ns)) \<Longrightarrow>
   (\<And>r' ns. viol r' \<Longrightarrow> agr (g HRerr ns) (g' r' ns)) \<Longrightarrow>
   agr (thenr p g) (thenr p' g')\<close>
  by (cases p; cases p') (auto simp: agr_def thenr_def)

lemma maskr_agr: \<open>viol r' \<Longrightarrow> agr (maskr l HRerr, ns) (maskr l r', ns)\<close>
  by (auto simp: viol_def agr_def)

lemma cresumeR_viol: \<open>viol r' \<Longrightarrow> agr (cresume k HRerr fs ns) (cresumeR k r' fs ns)\<close>
  by (cases k) (auto simp: viol_def agr_def)

lemma vfree_val:
  \<open>ceval k env e ns = (r, ns') \<Longrightarrow> vfree_env env \<Longrightarrow> vfree e \<Longrightarrow> vfree_r r\<close>
  \<open>capply k fv av ns = (r, ns') \<Longrightarrow> vfree_v fv \<Longrightarrow> vfree_v av \<Longrightarrow> vfree_r r\<close>
  \<open>cstep k u f ns = (r, ns') \<Longrightarrow> vfree_v u \<Longrightarrow> vfree_f f \<Longrightarrow> vfree_r r\<close>
  \<open>ceval k env e ns = (HRval v, ns') \<Longrightarrow> vfree_env env \<Longrightarrow> vfree e \<Longrightarrow> vfree_v v\<close>
  using ceval_vfree[of env e k ns] capply_vfree[of fv av k ns] cstep_vfree[of u f k ns]
  by auto

text \<open>On marker-free inputs the two modes agree, clock for clock and
  supply for supply:\<close>

lemma ceval_agr: \<open>vfree_env env \<Longrightarrow> vfree e \<Longrightarrow> agr (ceval k env e ns) (cevalR k env e ns)\<close>
  and cevcon_agr: \<open>vfree_env env \<Longrightarrow> vfree_vs vs \<Longrightarrow> vfree_es es \<Longrightarrow>
    agr (cevcon k env c vs es ns) (cevconR k env c vs es ns)\<close>
  and cevalm_agr: \<open>vfree_env env \<Longrightarrow> vfree_v u \<Longrightarrow> vfree_cls cls \<Longrightarrow>
    agr (cevalm k env u cls ns) (cevalmR k env u cls ns)\<close>
  and capply_agr: \<open>vfree_v fv \<Longrightarrow> vfree_v av \<Longrightarrow> agr (capply k fv av ns) (capplyR k fv av ns)\<close>
  and cstep_agr: \<open>vfree_v u \<Longrightarrow> vfree_f f \<Longrightarrow> agr (cstep k u f ns) (cstepR k u f ns)\<close>
  and cunwind_agr: \<open>vfree_v u \<Longrightarrow> vfree_fs fs \<Longrightarrow> agr (cunwind k u fs ns) (cunwindR k u fs ns)\<close>
  and cresume_agr: \<open>vfree_r r \<Longrightarrow> vfree_fs fs \<Longrightarrow> agr (cresume k r fs ns) (cresumeR k r fs ns)\<close>
  and cthrow_agr: \<open>l \<noteq> viol_lbl \<Longrightarrow> vfree_v w \<Longrightarrow> vfree_fs fr \<Longrightarrow> vfree_fs fs \<Longrightarrow>
    agr (cthrow k l m w fr fs ns) (cthrowR k l m w fr fs ns)\<close>
  and cthrown_agr: \<open>vfree_v w \<Longrightarrow> vfree_fs fr \<Longrightarrow> vfree_fs fs \<Longrightarrow>
    agr (cthrown k i op w fr fs ns) (cthrownR k i op w fr fs ns)\<close>
proof (induction k env e ns and k env c vs es ns and k env u cls ns and k fv av ns
      and k u f ns and k u fs ns and k r fs ns and k l m w fr fs ns and k i op w fr fs ns
      rule: ceval_induct)
  case cevalm_Cons
  then show ?case by (auto split: option.split dest: cpmatch_vfree)
qed (auto intro!: bindr_agr guardr_agr thenr_agr maskr_agr cresumeR_viol
          simp: vfree_val split: option.split)

subsection \<open>Agreement at the program level\<close>

text \<open>At the program level a marker, or an escaped named operation, is the
  host event on the reserved label where the strict one is stuck. A host that
  returns marker-free values (every first-order value is one) keeps the
  correspondence through the foreign calls.\<close>

definition host_vfree :: \<open>ffi \<Rightarrow> bool\<close> where
  \<open>host_vfree ffi \<longleftrightarrow> (\<forall>s evs v r. ffi s evs v = Some (FRet r) \<longrightarrow> vfree_v r)\<close>

definition agrc :: \<open>'a cres \<times> ffi_ev list \<Rightarrow> 'a cres \<times> ffi_ev list \<Rightarrow> bool\<close> where
  \<open>agrc q q' \<longleftrightarrow>
     snd q' = snd q \<and> (fst q' = fst q \<or> (fst q = Rerr \<and> (\<exists>w. fst q' = Rhost (viol_ev w))))\<close>

lemma agrc_refl[simp, intro!]: \<open>agrc q q\<close>
  by (simp add: agrc_def)

lemma crun_vfree:
  assumes host: \<open>host_vfree ffi\<close>
  shows \<open>vfree_r (fst p) \<Longrightarrow> fst (crun k ffi evs p) = Rval (v, ns') \<Longrightarrow> vfree_v v\<close>
proof (induction k arbitrary: evs p)
  case 0
  then show ?case by (cases p; cases \<open>fst p\<close>) auto
next
  case (Suc k)
  show ?case
  proof (cases \<open>fst p\<close>)
    case (HRop l m w fr)
    then obtain ns where p: \<open>p = (HRop l m w fr, ns)\<close> by (cases p) auto
    from Suc.prems p obtain sy u where \<open>ffi sy evs w = Some (FRet u)\<close>
      and rec: \<open>fst (crun k ffi (evs @ [FFIev sy w (FRet u)]) (cunwind k u fr ns)) = Rval (v, ns')\<close>
      by (auto split: option.split_asm ffi_res.split_asm)
    with host have \<open>vfree_v u\<close> unfolding host_vfree_def by blast
    with Suc.prems p show ?thesis by (intro Suc.IH[OF _ rec, OF cunwind_vfree]) auto
  qed (use Suc.prems in \<open>(cases p; auto)+\<close>)
qed

lemma crun_agr:
  assumes host: \<open>host_vfree ffi\<close>
  shows \<open>vfree_r (fst p) \<Longrightarrow> agr p p' \<Longrightarrow> agrc (crun k ffi evs p) (crunR k ffi evs p')\<close>
proof (induction k arbitrary: evs p p')
  case 0
  obtain a b where p: \<open>p = (a, b)\<close> by (cases p)
  obtain a' b' where p': \<open>p' = (a', b')\<close> by (cases p')
  show ?case using 0 p p' by (cases a; cases a') (auto simp: agr_def agrc_def viol_def)
next
  case (Suc k)
  show ?case
  proof (cases \<open>p' = p\<close>)
    case True
    show ?thesis
    proof (cases \<open>fst p\<close>)
      case (HRop l m w fr)
      then obtain ns where p: \<open>p = (HRop l m w fr, ns)\<close> by (cases p) auto
      have lv: \<open>l \<noteq> viol_lbl\<close> using Suc.prems p by simp
      have hv: \<open>ffi sy evs w = Some (FRet u) \<Longrightarrow> vfree_v u\<close> for sy u
        using host unfolding host_vfree_def by blast
      have IH: \<open>agrc (crun k ffi (evs @ [FFIev sy w (FRet u)]) (cunwind k u fr ns))
                     (crunR k ffi (evs @ [FFIev sy w (FRet u)]) (cunwindR k u fr ns))\<close>
        if \<open>ffi sy evs w = Some (FRet u)\<close> for sy u
        using Suc.prems p hv[OF that] by (intro Suc.IH[OF cunwind_vfree cunwind_agr]) auto
      show ?thesis using IH p lv True by (auto split: option.split ffi_res.split)
    qed (use Suc.prems True in \<open>(cases p; auto simp: agrc_def)+\<close>)
  next
    case False
    with Suc.prems obtain ns m' w' fr'
      where \<open>p = (HRerr, ns)\<close> \<open>p' = (HRop viol_lbl m' w' fr', ns)\<close>
      by (cases p; cases p') (auto simp: agr_def viol_def)
    then show ?thesis by (simp add: agrc_def)
  qed
qed

lemma ceval_prog_agr:
  assumes host: \<open>host_vfree ffi\<close>
  shows \<open>vfree_env env \<Longrightarrow> (\<And>x e. (x, e) \<in> set p \<Longrightarrow> vfree e) \<Longrightarrow>
    agrc (ceval_prog k ffi env ns evs p) (ceval_progR k ffi env ns evs p)\<close>
proof (induction p arbitrary: env ns evs)
  case (Cons d p)
  obtain x e where d: \<open>d = (x, e)\<close> by (cases d)
  from Cons.prems have venv: \<open>vfree_env env\<close> and ve: \<open>vfree e\<close>
    and vp: \<open>\<And>x' e'. (x', e') \<in> set p \<Longrightarrow> vfree e'\<close>
    by (auto simp: d)
  have c: \<open>agrc (crun k ffi evs (ceval k env e ns)) (crunR k ffi evs (cevalR k env e ns))\<close>
    using venv ve by (intro crun_agr[OF host] ceval_agr ceval_vfree) auto
  show ?case
  proof (cases \<open>fst (crun k ffi evs (ceval k env e ns))\<close>)
    case (Rval vn)
    obtain v ns' where vn: \<open>vn = (v, ns')\<close> by (cases vn)
    obtain evs' where cr: \<open>crun k ffi evs (ceval k env e ns) = (Rval (v, ns'), evs')\<close>
      using Rval vn by (cases \<open>crun k ffi evs (ceval k env e ns)\<close>) auto
    have \<open>vfree_v v\<close>
      using venv ve by (intro crun_vfree[OF host _ Rval[unfolded vn]] ceval_vfree)
    with venv have venv': \<open>vfree_env ((x, v) # env)\<close> by simp
    have eq: \<open>crunR k ffi evs (cevalR k env e ns) = (Rval (v, ns'), evs')\<close>
      using c cr by (auto simp: agrc_def prod_eq_iff)
    show ?thesis using Cons.IH[OF venv' vp] by (simp add: d cr eq)
  qed (use c in \<open>(cases \<open>crun k ffi evs (ceval k env e ns)\<close>;
                  cases \<open>crunR k ffi evs (cevalR k env e ns)\<close>; auto simp: d agrc_def)+\<close>)
qed simp

lemma centry_agr:
  assumes host: \<open>host_vfree ffi\<close> and vp: \<open>\<And>x e. (x, e) \<in> set p \<Longrightarrow> vfree e\<close>
  shows \<open>agrc (centry x ffi p k) (centryR x ffi p k)\<close>
proof -
  have \<open>agrc (ceval_prog k ffi [] 0 [] p) (ceval_progR k ffi [] 0 [] p)\<close>
    by (rule ceval_prog_agr[OF host _ vp]) simp
  then show ?thesis unfolding mcentry_def
    by (cases \<open>ceval_prog k ffi [] 0 [] p\<close>; cases \<open>ceval_progR k ffi [] 0 [] p\<close>)
       (auto simp: agrc_def split: cres.split option.split)
qed

end
