theory Bigstep
  imports Core
begin

section \<open>Clock-free big-step semantics\<close>

text \<open>The evaluator as a relation. A judgment derives only the
  \<^emph>\<open>displayed\<close> outcomes, a value or a rising bubble: a derivation is its
  own termination witness, and stuckness is the absence of one.
  \<^text>\<open>cevalD_adequate\<close>: derivable iff the evaluator computes the same
  outcome at some clock, \<^text>\<open>crunD_adequate\<close> and \<^text>\<open>cevalpD_adequate\<close>
  say the same of the program level.\<close>

fun plain_frame :: \<open>cframe \<Rightarrow> bool\<close> where
  \<open>plain_frame (CFhandle l hv) = False\<close>
| \<open>plain_frame (CFmask l) = False\<close>
| \<open>plain_frame f = True\<close>

fun plainn_frame :: \<open>cframe \<Rightarrow> bool\<close> where
  \<open>plainn_frame (CFhandlen l i hv \<phi>) = False\<close>
| \<open>plainn_frame f = True\<close>

fun bubble :: \<open>hres \<Rightarrow> bool\<close> where
  \<open>bubble (HRop l m w fr) = True\<close>
| \<open>bubble (HRopn i op w fr) = True\<close>
| \<open>bubble r = False\<close>

fun displayable :: \<open>hres \<Rightarrow> bool\<close> where
  \<open>displayable (HRval v) = True\<close>
| \<open>displayable r = bubble r\<close>

lemma bubble_push[simp]: \<open>bubble (push f r) = bubble r\<close>
  by (cases r) simp_all

lemma displayable_push[simp]: \<open>displayable (push f r) = displayable r\<close>
  by (cases r) simp_all

lemma bindr_bubble[simp]: \<open>bubble r \<Longrightarrow> bindr (r, ns) f g = (push f r, ns)\<close>
  by (cases r) simp_all

lemma maskr_bubble[simp]: \<open>bubble (maskr l r) = bubble r\<close>
  by (cases r) simp_all

lemma bubble_displayable[simp]: \<open>bubble r \<Longrightarrow> displayable r\<close>
  by (cases r) simp_all

inductive
      cevalD  :: \<open>(name \<times> cval) list \<Rightarrow> cexp \<Rightarrow> nat \<Rightarrow> hres \<Rightarrow> nat \<Rightarrow> bool\<close>
      (\<open>_ \<turnstile> _,_ \<Down> _,_\<close> [51, 51, 51, 51, 51] 50)
  and cevconD ::
      \<open>(name \<times> cval) list \<Rightarrow> name \<Rightarrow> cval list \<Rightarrow> cexp list \<Rightarrow> nat \<Rightarrow> hres \<Rightarrow> nat \<Rightarrow> bool\<close>
      (\<open>_ \<turnstile> _ \<langle>_;_\<rangle>,_ \<Down> _,_\<close> [51, 51, 51, 51, 51, 51, 51] 50)
  and cevalmD ::
      \<open>(name \<times> cval) list \<Rightarrow> cval \<Rightarrow> (cpat \<times> cexp) list \<Rightarrow> nat \<Rightarrow> hres \<Rightarrow> nat \<Rightarrow> bool\<close>
      (\<open>_ \<turnstile> _ \<Zrres> _,_ \<Down> _,_\<close> [51, 51, 51, 51, 51, 51] 50)
  and capplyD :: \<open>cval \<Rightarrow> cval \<Rightarrow> nat \<Rightarrow> hres \<Rightarrow> nat \<Rightarrow> bool\<close>
      (\<open>_ \<sqdot> _,_ \<Down> _,_\<close> [51, 51, 51, 51, 51] 50)
  and cstepD :: \<open>cval \<Rightarrow> cframe \<Rightarrow> nat \<Rightarrow> hres \<Rightarrow> nat \<Rightarrow> bool\<close>
      (\<open>_ \<Zdres> _,_ \<Down> _,_\<close> [51, 51, 51, 51, 51] 50)
  and cunwindD :: \<open>cval \<Rightarrow> cframe list \<Rightarrow> nat \<Rightarrow> hres \<Rightarrow> nat \<Rightarrow> bool\<close>
      (\<open>_ \<leadsto> _,_ \<Down> _,_\<close> [51, 51, 51, 51, 51] 50)
  and cresumeD :: \<open>hres \<Rightarrow> cframe list \<Rightarrow> nat \<Rightarrow> hres \<Rightarrow> nat \<Rightarrow> bool\<close>
      (\<open>resume _ _,_ \<Down> _,_\<close> [51, 51, 51, 51, 51] 50)
  and cthrowD ::
      \<open>name \<Rightarrow> nat \<Rightarrow> cval \<Rightarrow> cframe list \<Rightarrow> cframe list \<Rightarrow> nat \<Rightarrow> hres \<Rightarrow> nat \<Rightarrow> bool\<close>
      (\<open>throw _ \<^bold>@ _  _ \<parallel> _ \<parallel> _,_ \<Down> _,_\<close> [51, 51, 51, 51, 51, 51, 51, 51] 50)
  and cthrownD ::
      \<open>nat \<Rightarrow> name \<Rightarrow> cval \<Rightarrow> cframe list \<Rightarrow> cframe list \<Rightarrow> nat \<Rightarrow> hres \<Rightarrow> nat \<Rightarrow> bool\<close>
      (\<open>thrown _ _  _ \<parallel> _ \<parallel> _,_ \<Down> _,_\<close> [51, 51, 51, 51, 51, 51, 51, 51] 50)
where
  EvVar: \<open>map_of env x = Some v \<Longrightarrow> env \<turnstile> (Cvar x),ns \<Down> (HRval v),ns\<close>
| EvLit: \<open>env \<turnstile> (Clit l),ns \<Down> (HRval (Vlit l)),ns\<close>
| EvLam: \<open>env \<turnstile> (Clam x b),ns \<Down> (HRval (Vclos env x b)),ns\<close>

| EvApp: \<open>env \<turnstile> f,ns \<Down> (HRval fv),ns\<^sub>1 \<Longrightarrow> env \<turnstile> a,ns\<^sub>1 \<Down> (HRval av),ns\<^sub>2 \<Longrightarrow>
          fv \<sqdot> av,ns\<^sub>2 \<Down> r,ns\<^sub>3 \<Longrightarrow> env \<turnstile> (Capp f a),ns \<Down> r,ns\<^sub>3\<close>
| EvAppBub2: \<open>env \<turnstile> f,ns \<Down> (HRval fv),ns\<^sub>1 \<Longrightarrow> env \<turnstile> a,ns\<^sub>1 \<Down> r,ns\<^sub>2 \<Longrightarrow> bubble r \<Longrightarrow>
              r' = push (CFapp2 fv) r \<Longrightarrow> env \<turnstile> (Capp f a),ns \<Down> r',ns\<^sub>2\<close>
| EvAppBub1: \<open>env \<turnstile> f,ns \<Down> r,ns\<^sub>1 \<Longrightarrow> bubble r \<Longrightarrow> r' = push (CFapp1 env a) r \<Longrightarrow>
              env \<turnstile> (Capp f a),ns \<Down> r',ns\<^sub>1\<close>

| EvLet: \<open>env \<turnstile> e,ns \<Down> (HRval v),ns\<^sub>1 \<Longrightarrow> ((x, v) # env) \<turnstile> b,ns\<^sub>1 \<Down> r,ns\<^sub>2 \<Longrightarrow>
          env \<turnstile> (Clet x e b),ns \<Down> r,ns\<^sub>2\<close>
| EvLetBub: \<open>env \<turnstile> e,ns \<Down> r,ns\<^sub>1 \<Longrightarrow> bubble r \<Longrightarrow> r' = push (CFlet x env b) r \<Longrightarrow>
             env \<turnstile> (Clet x e b),ns \<Down> r',ns\<^sub>1\<close>

| EvLetrec: \<open>((f, Vclosrec env f x e) # env) \<turnstile> b,ns \<Down> r,ns' \<Longrightarrow>
             env \<turnstile> (Cletrec f x e b),ns \<Down> r,ns'\<close>

| EvCon: \<open>env \<turnstile> c \<langle>[];es\<rangle>,ns \<Down> r,ns' \<Longrightarrow> env \<turnstile> (Ccon c es),ns \<Down> r,ns'\<close>

| EvMatch: \<open>env \<turnstile> e,ns \<Down> (HRval v),ns\<^sub>1 \<Longrightarrow> env \<turnstile> v \<Zrres> cls,ns\<^sub>1 \<Down> r,ns\<^sub>2 \<Longrightarrow>
            env \<turnstile> (Cmatch e cls),ns \<Down> r,ns\<^sub>2\<close>
| EvMatchBub: \<open>env \<turnstile> e,ns \<Down> r,ns\<^sub>1 \<Longrightarrow> bubble r \<Longrightarrow> r' = push (CFmatch env cls) r \<Longrightarrow>
               env \<turnstile> (Cmatch e cls),ns \<Down> r',ns\<^sub>1\<close>

| EvPerform: \<open>env \<turnstile> a,ns \<Down> (HRval av),ns\<^sub>1 \<Longrightarrow>
              env \<turnstile> (Cperform l a),ns \<Down> (HRop l 0 av []),ns\<^sub>1\<close>
| EvPerformBub: \<open>env \<turnstile> a,ns \<Down> r,ns\<^sub>1 \<Longrightarrow> bubble r \<Longrightarrow> r' = push (CFperf l) r \<Longrightarrow>
                 env \<turnstile> (Cperform l a),ns \<Down> r',ns\<^sub>1\<close>

| EvHandle: \<open>env \<turnstile> h,ns \<Down> (HRval hv),ns\<^sub>1 \<Longrightarrow> env \<turnstile> b,ns\<^sub>1 \<Down> r,ns\<^sub>2 \<Longrightarrow>
             resume r [CFhandle l hv],ns\<^sub>2 \<Down> r',ns\<^sub>3 \<Longrightarrow>
             env \<turnstile> (Chandle l h b),ns \<Down> r',ns\<^sub>3\<close>

| EvMask: \<open>env \<turnstile> e,ns \<Down> (HRval v),ns\<^sub>1 \<Longrightarrow> env \<turnstile> (Cmask l e),ns \<Down> (HRval v),ns\<^sub>1\<close>
| EvMaskBub: \<open>env \<turnstile> e,ns \<Down> r,ns\<^sub>1 \<Longrightarrow> bubble r \<Longrightarrow> r' = maskr l r \<Longrightarrow>
              env \<turnstile> (Cmask l e),ns \<Down> r',ns\<^sub>1\<close>

| EvPerformn: \<open>env \<turnstile> x,ns \<Down> (HRval (Vname i)),ns\<^sub>1 \<Longrightarrow>
               env \<turnstile> a,ns\<^sub>1 \<Down> (HRval av),ns\<^sub>2 \<Longrightarrow>
               env \<turnstile> (Cperformn x op a),ns \<Down> (HRopn i op av []),ns\<^sub>2\<close>
| EvPerformnBub2: \<open>env \<turnstile> x,ns \<Down> (HRval xv),ns\<^sub>1 \<Longrightarrow>
                   env \<turnstile> a,ns\<^sub>1 \<Down> r,ns\<^sub>2 \<Longrightarrow> bubble r \<Longrightarrow>
                   r' = push (CFperfn2 xv op) r \<Longrightarrow> env \<turnstile> (Cperformn x op a),ns \<Down> r',ns\<^sub>2\<close>
| EvPerformnBub1: \<open>env \<turnstile> x,ns \<Down> r,ns\<^sub>1 \<Longrightarrow> bubble r \<Longrightarrow>
                   r' = push (CFperfn1 env op a) r \<Longrightarrow>
                   env \<turnstile> (Cperformn x op a),ns \<Down> r',ns\<^sub>1\<close>

| EvHandlen: \<open>env \<turnstile> h,ns \<Down> (HRval hv),ns\<^sub>1 \<Longrightarrow> env \<turnstile> b,ns\<^sub>1 \<Down> (HRval bv),ns\<^sub>2 \<Longrightarrow>
              bv \<sqdot> (Vname ns\<^sub>2),(Suc ns\<^sub>2) \<Down> r,ns\<^sub>3 \<Longrightarrow>
              resume r [CFhandlen l ns\<^sub>2 hv \<phi>],ns\<^sub>3 \<Down> r',ns\<^sub>4 \<Longrightarrow>
              env \<turnstile> (Chandlen l h \<phi> b),ns \<Down> r',ns\<^sub>4\<close>

| EcNil: \<open>env \<turnstile> c \<langle>vs;[]\<rangle>,ns \<Down> (HRval (Vcon c (rev vs))),ns\<close>
| EcCons: \<open>env \<turnstile> e,ns \<Down> (HRval v),ns\<^sub>1 \<Longrightarrow> env \<turnstile> c \<langle>(v # vs);es\<rangle>,ns\<^sub>1 \<Down> r,ns\<^sub>2 \<Longrightarrow>
           env \<turnstile> c \<langle>vs;(e # es)\<rangle>,ns \<Down> r,ns\<^sub>2\<close>
| EcConsBub: \<open>env \<turnstile> e,ns \<Down> r,ns\<^sub>1 \<Longrightarrow> bubble r \<Longrightarrow> r' = push (CFcon c vs env es) r \<Longrightarrow>
              env \<turnstile> c \<langle>vs;(e # es)\<rangle>,ns \<Down> r',ns\<^sub>1\<close>

| EmHit: \<open>cpmatch p v = Some bs \<Longrightarrow> (bs @ env) \<turnstile> e,ns \<Down> r,ns' \<Longrightarrow>
          env \<turnstile> v \<Zrres> ((p, e) # cls),ns \<Down> r,ns'\<close>
| EmMiss: \<open>cpmatch p v = None \<Longrightarrow> env \<turnstile> v \<Zrres> cls,ns \<Down> r,ns' \<Longrightarrow>
           env \<turnstile> v \<Zrres> ((p, e) # cls),ns \<Down> r,ns'\<close>

| ApClos: \<open>((x, av) # cenv) \<turnstile> b,ns \<Down> r,ns' \<Longrightarrow> (Vclos cenv x b) \<sqdot> av,ns \<Down> r,ns'\<close>
| ApClosrec: \<open>((x, av) # (g, Vclosrec cenv g x b) # cenv) \<turnstile> b,ns \<Down> r,ns' \<Longrightarrow>
              (Vclosrec cenv g x b) \<sqdot> av,ns \<Down> r,ns'\<close>
| ApCont: \<open>av \<leadsto> fs,ns \<Down> r,ns' \<Longrightarrow> (VCont fs) \<sqdot> av,ns \<Down> r,ns'\<close>

| StApp1: \<open>env \<turnstile> a,ns \<Down> (HRval av),ns\<^sub>1 \<Longrightarrow> v \<sqdot> av,ns\<^sub>1 \<Down> r,ns\<^sub>2 \<Longrightarrow>
           v \<Zdres> (CFapp1 env a),ns \<Down> r,ns\<^sub>2\<close>
| StApp1Bub: \<open>env \<turnstile> a,ns \<Down> r,ns\<^sub>1 \<Longrightarrow> bubble r \<Longrightarrow> r' = push (CFapp2 v) r \<Longrightarrow>
              v \<Zdres> (CFapp1 env a),ns \<Down> r',ns\<^sub>1\<close>
| StApp2: \<open>fv \<sqdot> v,ns \<Down> r,ns' \<Longrightarrow> v \<Zdres> (CFapp2 fv),ns \<Down> r,ns'\<close>
| StLet: \<open>((x, v) # env) \<turnstile> b,ns \<Down> r,ns' \<Longrightarrow> v \<Zdres> (CFlet x env b),ns \<Down> r,ns'\<close>
| StCon: \<open>env \<turnstile> c \<langle>(v # vs);es\<rangle>,ns \<Down> r,ns' \<Longrightarrow> v \<Zdres> (CFcon c vs env es),ns \<Down> r,ns'\<close>
| StMatch: \<open>env \<turnstile> v \<Zrres> cls,ns \<Down> r,ns' \<Longrightarrow> v \<Zdres> (CFmatch env cls),ns \<Down> r,ns'\<close>
| StPerf: \<open>v \<Zdres> (CFperf l),ns \<Down> (HRop l 0 v []),ns\<close>
| StPerfn1: \<open>env \<turnstile> a,ns \<Down> (HRval av),ns\<^sub>1 \<Longrightarrow>
             (Vname i) \<Zdres> (CFperfn1 env op a),ns \<Down> (HRopn i op av []),ns\<^sub>1\<close>
| StPerfn1Bub: \<open>env \<turnstile> a,ns \<Down> r,ns\<^sub>1 \<Longrightarrow> bubble r \<Longrightarrow>
                r' = push (CFperfn2 v op) r \<Longrightarrow>
                v \<Zdres> (CFperfn1 env op a),ns \<Down> r',ns\<^sub>1\<close>
| StPerfn2: \<open>v \<Zdres> (CFperfn2 (Vname i) op),ns \<Down> (HRopn i op v []),ns\<close>
| StHandle: \<open>v \<Zdres> (CFhandle l hv),ns \<Down> (HRval v),ns\<close>
| StHandlen: \<open>exit_prot \<phi> \<Longrightarrow> v \<Zdres> (CFhandlen l i hv \<phi>),ns \<Down> (HRval v),ns\<close>
| StMask: \<open>v \<Zdres> (CFmask l),ns \<Down> (HRval v),ns\<close>

| UwNil: \<open>v \<leadsto> [],ns \<Down> (HRval v),ns\<close>
| UwCons: \<open>v \<Zdres> f,ns \<Down> r,ns\<^sub>1 \<Longrightarrow> resume r fs,ns\<^sub>1 \<Down> r',ns\<^sub>2 \<Longrightarrow>
           v \<leadsto> (f # fs),ns \<Down> r',ns\<^sub>2\<close>

| RsVal: \<open>v \<leadsto> fs,ns \<Down> r,ns' \<Longrightarrow> resume (HRval v) fs,ns \<Down> r,ns'\<close>
| RsOp: \<open>throw l \<^bold>@ m  w \<parallel> fr \<parallel> fs,ns \<Down> r,ns' \<Longrightarrow> resume (HRop l m w fr) fs,ns \<Down> r,ns'\<close>
| RsOpn: \<open>thrown i op  w \<parallel> fr \<parallel> fs,ns \<Down> r,ns' \<Longrightarrow> resume (HRopn i op w fr) fs,ns \<Down> r,ns'\<close>

| ThNil: \<open>throw l \<^bold>@ m  w \<parallel> fr \<parallel> [],ns \<Down> (HRop l m w fr),ns\<close>
| ThCatch: \<open>hv \<sqdot> (Vcon (tuple_con 2) [w, VCont (fr @ [CFhandle l hv])]),ns \<Down> r,ns\<^sub>1 \<Longrightarrow>
            resume r fs,ns\<^sub>1 \<Down> r',ns\<^sub>2 \<Longrightarrow>
            throw l \<^bold>@ 0  w \<parallel> fr \<parallel> (CFhandle l hv # fs),ns \<Down> r',ns\<^sub>2\<close>
| ThSkip: \<open>throw l \<^bold>@ m  w \<parallel> (fr @ [CFhandle l hv]) \<parallel> fs,ns \<Down> r,ns' \<Longrightarrow>
           throw l \<^bold>@ (Suc m)  w \<parallel> fr \<parallel> (CFhandle l hv # fs),ns \<Down> r,ns'\<close>
| ThOther: \<open>l' \<noteq> l \<Longrightarrow> throw l \<^bold>@ m  w \<parallel> (fr @ [CFhandle l' hv]) \<parallel> fs,ns \<Down> r,ns' \<Longrightarrow>
            throw l \<^bold>@ m  w \<parallel> fr \<parallel> (CFhandle l' hv # fs),ns \<Down> r,ns'\<close>
| ThMaskEq: \<open>throw l \<^bold>@ (Suc m)  w \<parallel> (fr @ [CFmask l]) \<parallel> fs,ns \<Down> r,ns' \<Longrightarrow>
             throw l \<^bold>@ m  w \<parallel> fr \<parallel> (CFmask l # fs),ns \<Down> r,ns'\<close>
| ThMaskNeq: \<open>l' \<noteq> l \<Longrightarrow> throw l \<^bold>@ m  w \<parallel> (fr @ [CFmask l']) \<parallel> fs,ns \<Down> r,ns' \<Longrightarrow>
              throw l \<^bold>@ m  w \<parallel> fr \<parallel> (CFmask l' # fs),ns \<Down> r,ns'\<close>
| ThPlain: \<open>plain_frame f \<Longrightarrow> throw l \<^bold>@ m  w \<parallel> (fr @ [f]) \<parallel> fs,ns \<Down> r,ns' \<Longrightarrow>
            throw l \<^bold>@ m  w \<parallel> fr \<parallel> (f # fs),ns \<Down> r,ns'\<close>

| TnNil: \<open>thrown i op  w \<parallel> fr \<parallel> [],ns \<Down> (HRopn i op w fr),ns\<close>
| TnCatch: \<open>step_prot op \<phi> = Some \<phi>' \<Longrightarrow>
            hv \<sqdot> (Vcon (tuple_con 3) [Vlit (LStr op), w, VCont (fr @ [CFhandlen l i hv \<phi>'])]),ns
              \<Down> r,ns\<^sub>1 \<Longrightarrow>
            resume r fs,ns\<^sub>1 \<Down> r',ns\<^sub>2 \<Longrightarrow>
            thrown i op  w \<parallel> fr \<parallel> (CFhandlen l i hv \<phi> # fs),ns \<Down> r',ns\<^sub>2\<close>
| TnOther: \<open>j \<noteq> i \<Longrightarrow> thrown i op  w \<parallel> (fr @ [CFhandlen l j hv \<phi>]) \<parallel> fs,ns \<Down> r,ns' \<Longrightarrow>
            thrown i op  w \<parallel> fr \<parallel> (CFhandlen l j hv \<phi> # fs),ns \<Down> r,ns'\<close>
| TnPlain: \<open>plainn_frame f \<Longrightarrow> thrown i op  w \<parallel> (fr @ [f]) \<parallel> fs,ns \<Down> r,ns' \<Longrightarrow>
            thrown i op  w \<parallel> fr \<parallel> (f # fs),ns \<Down> r,ns'\<close>

lemmas Dintros =
  cevalD_cevconD_cevalmD_capplyD_cstepD_cunwindD_cresumeD_cthrowD_cthrownD.intros
lemmas Dinducts =
  cevalD_cevconD_cevalmD_capplyD_cstepD_cunwindD_cresumeD_cthrowD_cthrownD.inducts

text \<open>Every derived outcome is displayed:\<close>

lemma cevalD_displayable: \<open>env \<turnstile> e,ns \<Down> r,ns' \<Longrightarrow> displayable r\<close>
  and cevconD_displayable: \<open>env \<turnstile> c \<langle>vs;es\<rangle>,ns \<Down> rc,ns' \<Longrightarrow> displayable rc\<close>
  and cevalmD_displayable: \<open>env \<turnstile> v \<Zrres> cls,ns \<Down> rm,ns' \<Longrightarrow> displayable rm\<close>
  and capplyD_displayable: \<open>fv \<sqdot> av,ns \<Down> ra,ns' \<Longrightarrow> displayable ra\<close>
  and cstepD_displayable: \<open>v \<Zdres> f,ns \<Down> rs,ns' \<Longrightarrow> displayable rs\<close>
  and cunwindD_displayable: \<open>v \<leadsto> fs,ns \<Down> ru,ns' \<Longrightarrow> displayable ru\<close>
  and cresumeD_displayable: \<open>resume r\<^sub>0 fs,ns \<Down> rr,ns' \<Longrightarrow> displayable rr\<close>
  and cthrowD_displayable: \<open>throw l \<^bold>@ m  w \<parallel> fr \<parallel> fs,ns \<Down> rt,ns' \<Longrightarrow> displayable rt\<close>
  and cthrownD_displayable: \<open>thrown i op  w \<parallel> fr \<parallel> fs,ns \<Down> rn,ns' \<Longrightarrow> displayable rn\<close>
  by (induction rule: Dinducts) auto

lemmas D_displayable = cevalD_displayable cevconD_displayable cevalmD_displayable
  capplyD_displayable cstepD_displayable cunwindD_displayable cresumeD_displayable
  cthrowD_displayable cthrownD_displayable

text \<open>Non-timeout results of the fueled evaluator are stable under a longer
  clock:\<close>

lemma ceval_ne_mono:
  \<open>ceval k env e ns = (r, ns') \<Longrightarrow> r \<noteq> HRtimeout \<Longrightarrow> k \<le> k' \<Longrightarrow>
   ceval k' env e ns = (r, ns')\<close>
  using ceval_le[of k k' env e ns] by (auto simp: hres_le_def)

lemma cevcon_ne_mono:
  \<open>cevcon k env c vs es ns = (r, ns') \<Longrightarrow> r \<noteq> HRtimeout \<Longrightarrow> k \<le> k' \<Longrightarrow>
   cevcon k' env c vs es ns = (r, ns')\<close>
  using cevcon_le[of k k' env c vs es ns] by (auto simp: hres_le_def)

lemma cevalm_ne_mono:
  \<open>cevalm k env v cls ns = (r, ns') \<Longrightarrow> r \<noteq> HRtimeout \<Longrightarrow> k \<le> k' \<Longrightarrow>
   cevalm k' env v cls ns = (r, ns')\<close>
  using cevalm_le[of k k' env v cls ns] by (auto simp: hres_le_def)

lemma capply_ne_mono:
  \<open>capply k fv av ns = (r, ns') \<Longrightarrow> r \<noteq> HRtimeout \<Longrightarrow> k \<le> k' \<Longrightarrow>
   capply k' fv av ns = (r, ns')\<close>
  using capply_le[of k k' fv av ns] by (auto simp: hres_le_def)

lemma cstep_ne_mono:
  \<open>cstep k v f ns = (r, ns') \<Longrightarrow> r \<noteq> HRtimeout \<Longrightarrow> k \<le> k' \<Longrightarrow>
   cstep k' v f ns = (r, ns')\<close>
  using cstep_le[of k k' v f ns] by (auto simp: hres_le_def)

lemma cunwind_ne_mono:
  \<open>cunwind k v fs ns = (r, ns') \<Longrightarrow> r \<noteq> HRtimeout \<Longrightarrow> k \<le> k' \<Longrightarrow>
   cunwind k' v fs ns = (r, ns')\<close>
  using cunwind_le[of k k' v fs ns] by (auto simp: hres_le_def)

lemma cresume_ne_mono:
  \<open>cresume k r\<^sub>0 fs ns = (r, ns') \<Longrightarrow> r \<noteq> HRtimeout \<Longrightarrow> k \<le> k' \<Longrightarrow>
   cresume k' r\<^sub>0 fs ns = (r, ns')\<close>
  using cresume_le[of k k' r\<^sub>0 fs ns] by (auto simp: hres_le_def)

text \<open>Completeness: whatever displayed outcome the fueled evaluator computes
  is derivable. The combinators are taken apart by elimination rules that keep
  a bubble abstract:\<close>

lemma bindr_displayable_cases:
  assumes \<open>bindr p f g = (r, ns')\<close> \<open>displayable r\<close>
  obtains v ns where \<open>p = (HRval v, ns)\<close> \<open>g v ns = (r, ns')\<close>
        | r\<^sub>0 where \<open>p = (r\<^sub>0, ns')\<close> \<open>bubble r\<^sub>0\<close> \<open>r = push f r\<^sub>0\<close>
  using assms by (cases p) (auto simp: bindr_def split: hres.split_asm)

lemma guardr_displayable_cases:
  assumes \<open>guardr p g = (r, ns')\<close> \<open>displayable r\<close>
  obtains v ns where \<open>p = (HRval v, ns)\<close> \<open>g v ns = (r, ns')\<close>
  using assms by (cases p) (auto simp: guardr_def split: hres.split_asm)

lemma thenr_cases:
  assumes \<open>thenr p g = (r, ns')\<close>
  obtains r\<^sub>0 ns where \<open>p = (r\<^sub>0, ns)\<close> \<open>g r\<^sub>0 ns = (r, ns')\<close>
  using assms by (cases p) (auto simp: thenr_def)

lemma displayable_cases:
  assumes \<open>displayable r\<close>
  obtains v where \<open>r = HRval v\<close> | \<open>bubble r\<close>
  using assms by (cases r) auto

lemma performn_displayable_cases:
  assumes \<open>performn v op av ns = (r, ns')\<close> \<open>displayable r\<close>
  obtains i where \<open>v = Vname i\<close> \<open>r = HRopn i op av []\<close> \<open>ns' = ns\<close>
  using assms by (cases v) auto

lemma cresume_displayable: \<open>cresume k r\<^sub>0 fs ns = (r, ns') \<Longrightarrow> displayable r \<Longrightarrow> displayable r\<^sub>0\<close>
  by (cases k; cases r\<^sub>0) auto

lemma displayable_maskr[simp]: \<open>displayable (maskr l r) = displayable r\<close>
  by (cases r) auto

lemma ceval_imp_D:
    \<open>ceval k env e ns = (r, ns') \<Longrightarrow> displayable r \<Longrightarrow> env \<turnstile> e,ns \<Down> r,ns'\<close>
  and cevcon_imp_D: \<open>cevcon k env c vs es ns = (rc, ns') \<Longrightarrow> displayable rc \<Longrightarrow>
    env \<turnstile> c \<langle>vs;es\<rangle>,ns \<Down> rc,ns'\<close>
  and cevalm_imp_D: \<open>cevalm k env v cls ns = (rm, ns') \<Longrightarrow> displayable rm \<Longrightarrow>
    env \<turnstile> v \<Zrres> cls,ns \<Down> rm,ns'\<close>
  and capply_imp_D: \<open>capply k fv av ns = (ra, ns') \<Longrightarrow> displayable ra \<Longrightarrow> fv \<sqdot> av,ns \<Down> ra,ns'\<close>
  and cstep_imp_D: \<open>cstep k v f ns = (rs, ns') \<Longrightarrow> displayable rs \<Longrightarrow> v \<Zdres> f,ns \<Down> rs,ns'\<close>
  and cunwind_imp_D: \<open>cunwind k v fs ns = (ru, ns') \<Longrightarrow> displayable ru \<Longrightarrow> v \<leadsto> fs,ns \<Down> ru,ns'\<close>
  and cresume_imp_D: \<open>cresume k r\<^sub>0 fs ns = (rr, ns') \<Longrightarrow> displayable rr \<Longrightarrow>
    resume r\<^sub>0 fs,ns \<Down> rr,ns'\<close>
  and cthrow_imp_D: \<open>cthrow k l m w fr fs ns = (rt, ns') \<Longrightarrow> displayable rt \<Longrightarrow>
    throw l \<^bold>@ m  w \<parallel> fr \<parallel> fs,ns \<Down> rt,ns'\<close>
  and cthrown_imp_D: \<open>cthrown k i op w fr fs ns = (rn, ns') \<Longrightarrow> displayable rn \<Longrightarrow>
    thrown i op  w \<parallel> fr \<parallel> fs,ns \<Down> rn,ns'\<close>
proof (induction k env e ns and k env c vs es ns and k env v cls ns and k fv av ns and k v f ns
    and k v fs ns and k r\<^sub>0 fs ns and k l m w fr fs ns and k i op w fr fs ns
    arbitrary: r ns' and rc ns' and rm ns' and ra ns' and rs ns' and ru ns' and rr ns'
      and rt ns' and rn ns'
    rule: ceval_induct)
  case ceval_Capp
  then show ?case
    by (fastforce intro: EvApp EvAppBub2 EvAppBub1 elim!: bindr_displayable_cases displayable_cases)
next
  case ceval_Clet
  then show ?case
    by (fastforce intro: EvLet EvLetBub elim!: bindr_displayable_cases displayable_cases)
next
  case ceval_Cmatch
  then show ?case
    by (fastforce intro: EvMatch EvMatchBub elim!: bindr_displayable_cases displayable_cases)
next
  case ceval_Cperform
  then show ?case
    by (fastforce intro: EvPerform EvPerformBub elim!: bindr_displayable_cases displayable_cases)
next
  case ceval_Chandle
  then show ?case
    by (fastforce intro: EvHandle elim!: guardr_displayable_cases thenr_cases
                  dest: cresume_displayable)
next
  case (ceval_Cmask k env l e ns r ns')
  from ceval_Cmask.prems obtain r\<^sub>0 where e: \<open>ceval k env e ns = (r\<^sub>0, ns')\<close>
    and r: \<open>r = maskr l r\<^sub>0\<close> and d: \<open>displayable r\<^sub>0\<close>
    by (auto elim!: thenr_cases)
  show ?case using ceval_Cmask.IH[OF e d] d by (cases r\<^sub>0) (auto simp: r intro: EvMask EvMaskBub)
next
  case ceval_Cperformn
  then show ?case
    by (fastforce intro: EvPerformn EvPerformnBub2 EvPerformnBub1
                  elim!: bindr_displayable_cases displayable_cases performn_displayable_cases)
next
  case ceval_Chandlen
  then show ?case
    by (fastforce intro: EvHandlen elim!: guardr_displayable_cases thenr_cases
                  dest: cresume_displayable)
next
  case cevcon_Cons
  then show ?case
    by (fastforce intro: EcCons EcConsBub elim!: bindr_displayable_cases displayable_cases)
next
  case cstep_CFapp1
  then show ?case
    by (fastforce intro: StApp1 StApp1Bub elim!: bindr_displayable_cases displayable_cases)
next
  case cstep_CFperfn1
  then show ?case
    by (fastforce intro: StPerfn1 StPerfn1Bub
                  elim!: bindr_displayable_cases displayable_cases performn_displayable_cases)
next
  case cunwind_Cons
  then show ?case
    by (fastforce intro: UwCons elim!: thenr_cases dest: cresume_displayable)
next
  case cthrow_Cons_CFhandle
  then show ?case
    by (fastforce intro: ThCatch ThSkip ThOther elim!: thenr_cases dest: cresume_displayable
                  simp: gr0_conv_Suc split: if_split_asm)
next
  case cthrown_Cons_CFhandlen
  then show ?case
    by (fastforce intro: TnCatch TnOther elim!: thenr_cases dest: cresume_displayable
                  split: option.split_asm if_split_asm)
qed (auto intro: Dintros elim!: performn_displayable_cases
    simp: gr0_conv_Suc split: option.split_asm if_split_asm)

text \<open>Soundness: every derivation is computed by the fueled evaluator at some
  clock, the sub-derivation clocks combined by monotonicity.\<close>

lemma displayable_ne: \<open>displayable r \<Longrightarrow> r \<noteq> HRtimeout\<close>
  by (cases r) auto

lemma bubble_ne: \<open>bubble r \<Longrightarrow> r \<noteq> HRtimeout\<close>
  by (cases r) auto

lemmas D_ne = D_displayable[THEN displayable_ne]

lemma D_imp_ceval: \<open>env \<turnstile> e,ns \<Down> r,ns' \<Longrightarrow> \<exists>k. ceval k env e ns = (r, ns')\<close>
  and D_imp_cevcon: \<open>env \<turnstile> c \<langle>vs;es\<rangle>,ns \<Down> rc,ns' \<Longrightarrow> \<exists>k. cevcon k env c vs es ns = (rc, ns')\<close>
  and D_imp_cevalm: \<open>env \<turnstile> v \<Zrres> cls,ns \<Down> rm,ns' \<Longrightarrow> \<exists>k. cevalm k env v cls ns = (rm, ns')\<close>
  and D_imp_capply: \<open>fv \<sqdot> av,ns \<Down> ra,ns' \<Longrightarrow> \<exists>k. capply k fv av ns = (ra, ns')\<close>
  and D_imp_cstep: \<open>v \<Zdres> f,ns \<Down> rs,ns' \<Longrightarrow> \<exists>k. cstep k v f ns = (rs, ns')\<close>
  and D_imp_cunwind: \<open>v \<leadsto> fs,ns \<Down> ru,ns' \<Longrightarrow> \<exists>k. cunwind k v fs ns = (ru, ns')\<close>
  and D_imp_cresume: \<open>resume r\<^sub>0 fs,ns \<Down> rr,ns' \<Longrightarrow> \<exists>k. cresume k r\<^sub>0 fs ns = (rr, ns')\<close>
  and D_imp_cthrow: \<open>throw l \<^bold>@ m  w \<parallel> fr \<parallel> fs,ns \<Down> rt,ns' \<Longrightarrow>
    \<exists>k. cthrow k l m w fr fs ns = (rt, ns')\<close>
  and D_imp_cthrown: \<open>thrown i op  w \<parallel> fr \<parallel> fs,ns \<Down> rn,ns' \<Longrightarrow>
    \<exists>k. cthrown k i op w fr fs ns = (rn, ns')\<close>
proof (induction rule: Dinducts)
  case (EvApp env f ns fv ns\<^sub>1 a av ns\<^sub>2 r ns\<^sub>3)
  from EvApp.IH obtain k\<^sub>1 k\<^sub>2 k\<^sub>3 where
    h\<^sub>1: \<open>ceval k\<^sub>1 env f ns = (HRval fv, ns\<^sub>1)\<close> and
    h\<^sub>2: \<open>ceval k\<^sub>2 env a ns\<^sub>1 = (HRval av, ns\<^sub>2)\<close> and
    h\<^sub>3: \<open>capply k\<^sub>3 fv av ns\<^sub>2 = (r, ns\<^sub>3)\<close> by blast
  define K where \<open>K = max k\<^sub>1 (max k\<^sub>2 k\<^sub>3)\<close>
  have le: \<open>k\<^sub>1 \<le> K\<close> \<open>k\<^sub>2 \<le> K\<close> \<open>k\<^sub>3 \<le> K\<close> by (simp_all add: K_def)
  have \<open>ceval (Suc K) env (Capp f a) ns = (r, ns\<^sub>3)\<close>
    using EvApp.hyps D_ne
    by (simp add: ceval_ne_mono[OF h\<^sub>1] ceval_ne_mono[OF h\<^sub>2] capply_ne_mono[OF h\<^sub>3] le)
  then show ?case by blast
next
  case (EvAppBub2 env f ns fv ns\<^sub>1 a r ns\<^sub>2 r')
  from EvAppBub2.IH obtain k\<^sub>1 k\<^sub>2 where
    h\<^sub>1: \<open>ceval k\<^sub>1 env f ns = (HRval fv, ns\<^sub>1)\<close> and
    h\<^sub>2: \<open>ceval k\<^sub>2 env a ns\<^sub>1 = (r, ns\<^sub>2)\<close> by blast
  have \<open>ceval (Suc (max k\<^sub>1 k\<^sub>2)) env (Capp f a) ns = (r', ns\<^sub>2)\<close>
    using EvAppBub2.hyps bubble_ne
    by (simp add: ceval_ne_mono[OF h\<^sub>1 _ max.cobounded1] ceval_ne_mono[OF h\<^sub>2 _ max.cobounded2])
  then show ?case by blast
next
  case (EvAppBub1 env f ns r ns\<^sub>1 r' a)
  then obtain k where \<open>ceval k env f ns = (r, ns\<^sub>1)\<close> by blast
  then show ?case using EvAppBub1.hyps by (intro exI[of _ \<open>Suc k\<close>]) simp
next
  case (EvLet env e ns v ns\<^sub>1 x b r ns\<^sub>2)
  from EvLet.IH obtain k\<^sub>1 k\<^sub>2 where
    h\<^sub>1: \<open>ceval k\<^sub>1 env e ns = (HRval v, ns\<^sub>1)\<close> and
    h\<^sub>2: \<open>ceval k\<^sub>2 ((x, v) # env) b ns\<^sub>1 = (r, ns\<^sub>2)\<close> by blast
  have \<open>ceval (Suc (max k\<^sub>1 k\<^sub>2)) env (Clet x e b) ns = (r, ns\<^sub>2)\<close>
    using EvLet.hyps D_ne
    by (simp add: ceval_ne_mono[OF h\<^sub>1 _ max.cobounded1] ceval_ne_mono[OF h\<^sub>2 _ max.cobounded2])
  then show ?case by blast
next
  case (EvLetBub env e ns r ns\<^sub>1 r' x b)
  then obtain k where \<open>ceval k env e ns = (r, ns\<^sub>1)\<close> by blast
  then show ?case using EvLetBub.hyps by (intro exI[of _ \<open>Suc k\<close>]) simp
next
  case (EvLetrec f env x e b ns r ns')
  then obtain k where \<open>ceval k ((f, Vclosrec env f x e) # env) b ns = (r, ns')\<close> by blast
  then show ?case by (intro exI[of _ \<open>Suc k\<close>]) simp
next
  case (EvCon env c es ns r ns')
  then obtain k where \<open>cevcon k env c [] es ns = (r, ns')\<close> by blast
  then show ?case by (intro exI[of _ \<open>Suc k\<close>]) simp
next
  case (EvMatch env e ns v ns\<^sub>1 cls r ns\<^sub>2)
  from EvMatch.IH obtain k\<^sub>1 k\<^sub>2 where
    h\<^sub>1: \<open>ceval k\<^sub>1 env e ns = (HRval v, ns\<^sub>1)\<close> and
    h\<^sub>2: \<open>cevalm k\<^sub>2 env v cls ns\<^sub>1 = (r, ns\<^sub>2)\<close> by blast
  have \<open>ceval (Suc (max k\<^sub>1 k\<^sub>2)) env (Cmatch e cls) ns = (r, ns\<^sub>2)\<close>
    using EvMatch.hyps D_ne
    by (simp add: ceval_ne_mono[OF h\<^sub>1 _ max.cobounded1] cevalm_ne_mono[OF h\<^sub>2 _ max.cobounded2])
  then show ?case by blast
next
  case (EvMatchBub env e ns r ns\<^sub>1 r' cls)
  then obtain k where \<open>ceval k env e ns = (r, ns\<^sub>1)\<close> by blast
  then show ?case using EvMatchBub.hyps by (intro exI[of _ \<open>Suc k\<close>]) simp
next
  case (EvPerform env a ns av ns\<^sub>1 l)
  then obtain k where \<open>ceval k env a ns = (HRval av, ns\<^sub>1)\<close> by blast
  then show ?case by (intro exI[of _ \<open>Suc k\<close>]) simp
next
  case (EvPerformBub env a ns r ns\<^sub>1 r' l)
  then obtain k where \<open>ceval k env a ns = (r, ns\<^sub>1)\<close> by blast
  then show ?case using EvPerformBub.hyps by (intro exI[of _ \<open>Suc k\<close>]) simp
next
  case (EvHandle env h ns hv ns\<^sub>1 b r ns\<^sub>2 l r' ns\<^sub>3)
  from EvHandle.IH obtain k\<^sub>1 k\<^sub>2 k\<^sub>3 where
    h\<^sub>1: \<open>ceval k\<^sub>1 env h ns = (HRval hv, ns\<^sub>1)\<close> and
    h\<^sub>2: \<open>ceval k\<^sub>2 env b ns\<^sub>1 = (r, ns\<^sub>2)\<close> and
    h\<^sub>3: \<open>cresume k\<^sub>3 r [CFhandle l hv] ns\<^sub>2 = (r', ns\<^sub>3)\<close> by blast
  define K where \<open>K = max k\<^sub>1 (max k\<^sub>2 k\<^sub>3)\<close>
  have le: \<open>k\<^sub>1 \<le> K\<close> \<open>k\<^sub>2 \<le> K\<close> \<open>k\<^sub>3 \<le> K\<close> by (simp_all add: K_def)
  have \<open>ceval (Suc K) env (Chandle l h b) ns = (r', ns\<^sub>3)\<close>
    using EvHandle.hyps D_ne
    by (simp add: ceval_ne_mono[OF h\<^sub>1] ceval_ne_mono[OF h\<^sub>2] cresume_ne_mono[OF h\<^sub>3] le)
  then show ?case by blast
next
  case (EvMask env e ns v ns\<^sub>1 l)
  then obtain k where \<open>ceval k env e ns = (HRval v, ns\<^sub>1)\<close> by blast
  then show ?case by (intro exI[of _ \<open>Suc k\<close>]) simp
next
  case (EvMaskBub env e ns r ns\<^sub>1 r' l)
  then obtain k where \<open>ceval k env e ns = (r, ns\<^sub>1)\<close> by blast
  then show ?case using EvMaskBub.hyps by (intro exI[of _ \<open>Suc k\<close>]) simp
next
  case (EvPerformn env x ns i ns\<^sub>1 a av ns\<^sub>2 op)
  from EvPerformn.IH obtain k\<^sub>1 k\<^sub>2 where
    h\<^sub>1: \<open>ceval k\<^sub>1 env x ns = (HRval (Vname i), ns\<^sub>1)\<close> and
    h\<^sub>2: \<open>ceval k\<^sub>2 env a ns\<^sub>1 = (HRval av, ns\<^sub>2)\<close> by blast
  have \<open>ceval (Suc (max k\<^sub>1 k\<^sub>2)) env (Cperformn x op a) ns = (HRopn i op av [], ns\<^sub>2)\<close>
    by (simp add: ceval_ne_mono[OF h\<^sub>1 _ max.cobounded1] ceval_ne_mono[OF h\<^sub>2 _ max.cobounded2])
  then show ?case by blast
next
  case (EvPerformnBub2 env x ns xv ns\<^sub>1 a r ns\<^sub>2 r' op)
  from EvPerformnBub2.IH obtain k\<^sub>1 k\<^sub>2 where
    h\<^sub>1: \<open>ceval k\<^sub>1 env x ns = (HRval xv, ns\<^sub>1)\<close> and
    h\<^sub>2: \<open>ceval k\<^sub>2 env a ns\<^sub>1 = (r, ns\<^sub>2)\<close> by blast
  have \<open>ceval (Suc (max k\<^sub>1 k\<^sub>2)) env (Cperformn x op a) ns = (r', ns\<^sub>2)\<close>
    using EvPerformnBub2.hyps bubble_ne
    by (simp add: ceval_ne_mono[OF h\<^sub>1 _ max.cobounded1] ceval_ne_mono[OF h\<^sub>2 _ max.cobounded2])
  then show ?case by blast
next
  case (EvPerformnBub1 env x ns r ns\<^sub>1 r' op a)
  then obtain k where \<open>ceval k env x ns = (r, ns\<^sub>1)\<close> by blast
  then show ?case using EvPerformnBub1.hyps by (intro exI[of _ \<open>Suc k\<close>]) simp
next
  case (EvHandlen env h ns hv ns\<^sub>1 b bv ns\<^sub>2 r ns\<^sub>3 l \<phi> r' ns\<^sub>4)
  from EvHandlen.IH obtain k\<^sub>1 k\<^sub>2 k\<^sub>3 k\<^sub>4 where
    h\<^sub>1: \<open>ceval k\<^sub>1 env h ns = (HRval hv, ns\<^sub>1)\<close> and
    h\<^sub>2: \<open>ceval k\<^sub>2 env b ns\<^sub>1 = (HRval bv, ns\<^sub>2)\<close> and
    h\<^sub>3: \<open>capply k\<^sub>3 bv (Vname ns\<^sub>2) (Suc ns\<^sub>2) = (r, ns\<^sub>3)\<close> and
    h\<^sub>4: \<open>cresume k\<^sub>4 r [CFhandlen l ns\<^sub>2 hv \<phi>] ns\<^sub>3 = (r', ns\<^sub>4)\<close> by blast
  define K where \<open>K = max k\<^sub>1 (max k\<^sub>2 (max k\<^sub>3 k\<^sub>4))\<close>
  have le: \<open>k\<^sub>1 \<le> K\<close> \<open>k\<^sub>2 \<le> K\<close> \<open>k\<^sub>3 \<le> K\<close> \<open>k\<^sub>4 \<le> K\<close> by (simp_all add: K_def)
  have \<open>ceval (Suc K) env (Chandlen l h \<phi> b) ns = (r', ns\<^sub>4)\<close>
    using EvHandlen.hyps D_ne
    by (simp add: ceval_ne_mono[OF h\<^sub>1] ceval_ne_mono[OF h\<^sub>2] capply_ne_mono[OF h\<^sub>3]
                  cresume_ne_mono[OF h\<^sub>4] le)
  then show ?case by blast
next
  case (EcCons env e ns v ns\<^sub>1 c vs es r ns\<^sub>2)
  from EcCons.IH obtain k\<^sub>1 k\<^sub>2 where
    h\<^sub>1: \<open>ceval k\<^sub>1 env e ns = (HRval v, ns\<^sub>1)\<close> and
    h\<^sub>2: \<open>cevcon k\<^sub>2 env c (v # vs) es ns\<^sub>1 = (r, ns\<^sub>2)\<close> by blast
  have \<open>cevcon (Suc (max k\<^sub>1 k\<^sub>2)) env c vs (e # es) ns = (r, ns\<^sub>2)\<close>
    using EcCons.hyps D_ne
    by (simp add: ceval_ne_mono[OF h\<^sub>1 _ max.cobounded1] cevcon_ne_mono[OF h\<^sub>2 _ max.cobounded2])
  then show ?case by blast
next
  case (EcConsBub env e ns r ns\<^sub>1 r' c vs es)
  then obtain k where \<open>ceval k env e ns = (r, ns\<^sub>1)\<close> by blast
  then show ?case using EcConsBub.hyps by (intro exI[of _ \<open>Suc k\<close>]) simp
next
  case (EmHit p v bs env e ns r ns' cls)
  then obtain k where \<open>ceval k (bs @ env) e ns = (r, ns')\<close> by blast
  then show ?case using EmHit.hyps by (intro exI[of _ \<open>Suc k\<close>]) simp
next
  case (EmMiss p v env cls ns r ns' e)
  then obtain k where \<open>cevalm k env v cls ns = (r, ns')\<close> by blast
  then show ?case using EmMiss.hyps by (intro exI[of _ \<open>Suc k\<close>]) simp
next
  case (ApClos x av cenv b ns r ns')
  then obtain k where \<open>ceval k ((x, av) # cenv) b ns = (r, ns')\<close> by blast
  then show ?case by (intro exI[of _ \<open>Suc k\<close>]) simp
next
  case (ApClosrec x av g cenv b ns r ns')
  then obtain k where \<open>ceval k ((x, av) # (g, Vclosrec cenv g x b) # cenv) b ns = (r, ns')\<close> by blast
  then show ?case by (intro exI[of _ \<open>Suc k\<close>]) simp
next
  case (ApCont av fs ns r ns')
  then obtain k where \<open>cunwind k av fs ns = (r, ns')\<close> by blast
  then show ?case by (intro exI[of _ \<open>Suc k\<close>]) simp
next
  case (StApp1 env a ns av ns\<^sub>1 v r ns\<^sub>2)
  from StApp1.IH obtain k\<^sub>1 k\<^sub>2 where
    h\<^sub>1: \<open>ceval k\<^sub>1 env a ns = (HRval av, ns\<^sub>1)\<close> and
    h\<^sub>2: \<open>capply k\<^sub>2 v av ns\<^sub>1 = (r, ns\<^sub>2)\<close> by blast
  have \<open>cstep (Suc (max k\<^sub>1 k\<^sub>2)) v (CFapp1 env a) ns = (r, ns\<^sub>2)\<close>
    using StApp1.hyps D_ne
    by (simp add: ceval_ne_mono[OF h\<^sub>1 _ max.cobounded1] capply_ne_mono[OF h\<^sub>2 _ max.cobounded2])
  then show ?case by blast
next
  case (StApp1Bub env a ns r ns\<^sub>1 r' v)
  then obtain k where \<open>ceval k env a ns = (r, ns\<^sub>1)\<close> by blast
  then show ?case using StApp1Bub.hyps by (intro exI[of _ \<open>Suc k\<close>]) simp
next
  case (StApp2 fv v ns r ns')
  then obtain k where \<open>capply k fv v ns = (r, ns')\<close> by blast
  then show ?case by (intro exI[of _ \<open>Suc k\<close>]) simp
next
  case (StLet x v env b ns r ns')
  then obtain k where \<open>ceval k ((x, v) # env) b ns = (r, ns')\<close> by blast
  then show ?case by (intro exI[of _ \<open>Suc k\<close>]) simp
next
  case (StCon env c v vs es ns r ns')
  then obtain k where \<open>cevcon k env c (v # vs) es ns = (r, ns')\<close> by blast
  then show ?case by (intro exI[of _ \<open>Suc k\<close>]) simp
next
  case (StMatch env v cls ns r ns')
  then obtain k where \<open>cevalm k env v cls ns = (r, ns')\<close> by blast
  then show ?case by (intro exI[of _ \<open>Suc k\<close>]) simp
next
  case (StPerfn1 env a ns av ns\<^sub>1 i op)
  then obtain k where \<open>ceval k env a ns = (HRval av, ns\<^sub>1)\<close> by blast
  then show ?case by (intro exI[of _ \<open>Suc k\<close>]) simp
next
  case (StPerfn1Bub env a ns r ns\<^sub>1 r' v op)
  then obtain k where \<open>ceval k env a ns = (r, ns\<^sub>1)\<close> by blast
  then show ?case using StPerfn1Bub.hyps by (intro exI[of _ \<open>Suc k\<close>]) simp
next
  case (UwCons v f ns r ns\<^sub>1 fs r' ns\<^sub>2)
  from UwCons.IH obtain k\<^sub>1 k\<^sub>2 where
    h\<^sub>1: \<open>cstep k\<^sub>1 v f ns = (r, ns\<^sub>1)\<close> and
    h\<^sub>2: \<open>cresume k\<^sub>2 r fs ns\<^sub>1 = (r', ns\<^sub>2)\<close> by blast
  have \<open>cunwind (Suc (max k\<^sub>1 k\<^sub>2)) v (f # fs) ns = (r', ns\<^sub>2)\<close>
    using UwCons.hyps D_ne
    by (simp add: cstep_ne_mono[OF h\<^sub>1 _ max.cobounded1] cresume_ne_mono[OF h\<^sub>2 _ max.cobounded2])
  then show ?case by blast
next
  case (RsVal v fs ns r ns')
  then obtain k where \<open>cunwind k v fs ns = (r, ns')\<close> by blast
  then show ?case by (intro exI[of _ \<open>Suc k\<close>]) simp
next
  case (RsOp l m w fr fs ns r ns')
  then obtain k where \<open>cthrow k l m w fr fs ns = (r, ns')\<close> by blast
  then show ?case by (intro exI[of _ \<open>Suc k\<close>]) simp
next
  case (RsOpn i op w fr fs ns r ns')
  then obtain k where \<open>cthrown k i op w fr fs ns = (r, ns')\<close> by blast
  then show ?case by (intro exI[of _ \<open>Suc k\<close>]) simp
next
  case (ThCatch hv w fr l ns r ns\<^sub>1 fs r' ns\<^sub>2)
  from ThCatch.IH obtain k\<^sub>1 k\<^sub>2 where
    h\<^sub>1: \<open>capply k\<^sub>1 hv (Vcon (tuple_con 2) [w, VCont (fr @ [CFhandle l hv])]) ns = (r, ns\<^sub>1)\<close>
    and h\<^sub>2: \<open>cresume k\<^sub>2 r fs ns\<^sub>1 = (r', ns\<^sub>2)\<close> by blast
  have \<open>cthrow (Suc (max k\<^sub>1 k\<^sub>2)) l 0 w fr (CFhandle l hv # fs) ns = (r', ns\<^sub>2)\<close>
    using ThCatch.hyps D_ne
    by (simp add: capply_ne_mono[OF h\<^sub>1 _ max.cobounded1] cresume_ne_mono[OF h\<^sub>2 _ max.cobounded2])
  then show ?case by blast
next
  case (ThSkip l m w fr hv fs ns r ns')
  then obtain k where \<open>cthrow k l m w (fr @ [CFhandle l hv]) fs ns = (r, ns')\<close> by blast
  then show ?case by (intro exI[of _ \<open>Suc k\<close>]) simp
next
  case (ThOther l' l m w fr hv fs ns r ns')
  then obtain k where \<open>cthrow k l m w (fr @ [CFhandle l' hv]) fs ns = (r, ns')\<close> by blast
  then show ?case using ThOther.hyps by (intro exI[of _ \<open>Suc k\<close>]) simp
next
  case (ThMaskEq l m w fr fs ns r ns')
  then obtain k where \<open>cthrow k l (Suc m) w (fr @ [CFmask l]) fs ns = (r, ns')\<close> by blast
  then show ?case by (intro exI[of _ \<open>Suc k\<close>]) simp
next
  case (ThMaskNeq l' l m w fr fs ns r ns')
  then obtain k where \<open>cthrow k l m w (fr @ [CFmask l']) fs ns = (r, ns')\<close> by blast
  then show ?case using ThMaskNeq.hyps by (intro exI[of _ \<open>Suc k\<close>]) simp
next
  case (ThPlain f l m w fr fs ns r ns')
  then obtain k where h: \<open>cthrow k l m w (fr @ [f]) fs ns = (r, ns')\<close> by blast
  show ?case
  proof (intro exI[of _ \<open>Suc k\<close>])
    show \<open>cthrow (Suc k) l m w fr (f # fs) ns = (r, ns')\<close>
      using ThPlain.hyps h by (cases f) simp_all
  qed
next
  case (TnCatch op \<phi> \<phi>' hv w fr l i ns r ns\<^sub>1 fs r' ns\<^sub>2)
  from TnCatch.IH obtain k\<^sub>1 k\<^sub>2 where
    h\<^sub>1: \<open>capply k\<^sub>1 hv (Vcon (tuple_con 3) [Vlit (LStr op), w, VCont (fr @ [CFhandlen l i hv \<phi>'])])
      ns = (r, ns\<^sub>1)\<close>
    and h\<^sub>2: \<open>cresume k\<^sub>2 r fs ns\<^sub>1 = (r', ns\<^sub>2)\<close> by blast
  have \<open>cthrown (Suc (max k\<^sub>1 k\<^sub>2)) i op w fr (CFhandlen l i hv \<phi> # fs) ns = (r', ns\<^sub>2)\<close>
    using TnCatch.hyps D_ne
    by (simp add: capply_ne_mono[OF h\<^sub>1 _ max.cobounded1] cresume_ne_mono[OF h\<^sub>2 _ max.cobounded2])
  then show ?case by blast
next
  case (TnOther j i op w fr l hv \<phi> fs ns r ns')
  then obtain k where \<open>cthrown k i op w (fr @ [CFhandlen l j hv \<phi>]) fs ns = (r, ns')\<close> by blast
  then show ?case using TnOther.hyps by (intro exI[of _ \<open>Suc k\<close>]) simp
next
  case (TnPlain f i op w fr fs ns r ns')
  then obtain k where h: \<open>cthrown k i op w (fr @ [f]) fs ns = (r, ns')\<close> by blast
  show ?case
  proof (intro exI[of _ \<open>Suc k\<close>])
    show \<open>cthrown (Suc k) i op w fr (f # fs) ns = (r, ns')\<close>
      using TnPlain.hyps h by (cases f) simp_all
  qed
qed (auto intro: exI[of _ \<open>Suc 0\<close>])

subsection \<open>Adequacy\<close>

theorem cevalD_adequate:
  \<open>env \<turnstile> e,ns \<Down> r,ns' \<longleftrightarrow> displayable r \<and> (\<exists>k. ceval k env e ns = (r, ns'))\<close>
  using ceval_imp_D D_imp_ceval cevalD_displayable by blast

subsection \<open>Relational program evaluation\<close>

text \<open>Top-level bindings, clock-free, with the host in the loop: \<open>crunD\<close>
  is \<^const>\<open>crun\<close> as a judgment, servicing the operations that escape a
  binding and resuming their continuations through \<^const>\<open>cunwindD\<close>, and
  \<open>cevalpD\<close> is \<^const>\<open>ceval_prog\<close>. Both are the bridge to the module-level
  judgments. As with expressions, a derivation is a termination witness:
  only successful runs are derivable, the trace recorded along.\<close>

inductive crunD ::
  \<open>ffi \<Rightarrow> ffi_ev list \<Rightarrow> hres \<times> nat \<Rightarrow> cval \<times> nat \<Rightarrow> ffi_ev list \<Rightarrow> bool\<close>
where
  CrVal: \<open>crunD ffi evs (HRval v, ns) (v, ns) evs\<close>
| CrHost: \<open>ffi_sym l = Some sy \<Longrightarrow> ffi sy evs w = Some (FRet v) \<Longrightarrow>
           v \<leadsto> fr,ns \<Down> r,ns' \<Longrightarrow>
           crunD ffi (evs @ [FFIev sy w (FRet v)]) (r, ns') vn evs' \<Longrightarrow>
           crunD ffi evs (HRop l m w fr, ns) vn evs'\<close>

inductive cevalpD :: \<open>ffi \<Rightarrow> (name \<times> cval) list \<Rightarrow> nat \<Rightarrow> ffi_ev list \<Rightarrow> cprog
                      \<Rightarrow> (name \<times> cval) list \<times> nat \<Rightarrow> ffi_ev list \<Rightarrow> bool\<close> where
  EpNil: \<open>cevalpD ffi env ns evs [] (env, ns) evs\<close>
| EpCons: \<open>env \<turnstile> e,ns \<Down> r,ns\<^sub>1 \<Longrightarrow> crunD ffi evs (r, ns\<^sub>1) (v, ns\<^sub>2) evs\<^sub>1 \<Longrightarrow>
           cevalpD ffi ((x, v) # env) ns\<^sub>2 evs\<^sub>1 ds env' evs' \<Longrightarrow>
           cevalpD ffi env ns evs ((x, e) # ds) env' evs'\<close>

lemma crun_Rval_mono:
  \<open>crun k ffi evs p = (Rval v, evs') \<Longrightarrow> k \<le> k' \<Longrightarrow> crun k' ffi evs p = (Rval v, evs')\<close>
  using crun_le[of k k' p p ffi evs] by simp

lemma ceval_prog_Rval_mono:
  \<open>ceval_prog k ffi env ns evs p = (Rval v, evs') \<Longrightarrow> k \<le> k' \<Longrightarrow>
   ceval_prog k' ffi env ns evs p = (Rval v, evs')\<close>
  using ceval_prog_le[of k k' ffi env ns evs p] by simp

lemma crun_Rval_displayable: \<open>crun k ffi evs (r, ns) = (Rval v, evs') \<Longrightarrow> displayable r\<close>
  by (cases r; cases k) auto

lemma crunD_adequate:
  \<open>crunD ffi evs (r, ns) v evs' \<longleftrightarrow> (\<exists>k. crun k ffi evs (r, ns) = (Rval v, evs'))\<close>
proof
  assume \<open>crunD ffi evs (r, ns) v evs'\<close>
  then show \<open>\<exists>k. crun k ffi evs (r, ns) = (Rval v, evs')\<close>
  proof induction
    case (CrVal ffi evs v ns)
    show ?case by (intro exI[of _ 0]) simp
  next
    case (CrHost l sy ffi evs w v fr ns r ns' v' evs' m)
    from CrHost.hyps obtain k\<^sub>1 where h\<^sub>1: \<open>cunwind k\<^sub>1 v fr ns = (r, ns')\<close>
      by (auto dest: D_imp_cunwind)
    from CrHost.IH obtain k\<^sub>2 where
      h\<^sub>2: \<open>crun k\<^sub>2 ffi (evs @ [FFIev sy w (FRet v)]) (r, ns') = (Rval v', evs')\<close> by blast
    have \<open>crun (Suc (max k\<^sub>1 k\<^sub>2)) ffi evs (HRop l m w fr, ns) = (Rval v', evs')\<close>
      using CrHost.hyps D_ne
      by (simp add: cunwind_ne_mono[OF h\<^sub>1 _ max.cobounded1]
                    crun_Rval_mono[OF h\<^sub>2 max.cobounded2])
    then show ?case by blast
  qed
next
  assume \<open>\<exists>k. crun k ffi evs (r, ns) = (Rval v, evs')\<close>
  then obtain k where \<open>crun k ffi evs (r, ns) = (Rval v, evs')\<close> by blast
  then show \<open>crunD ffi evs (r, ns) v evs'\<close>
  proof (induction k ffi evs \<open>(r, ns)\<close> arbitrary: r ns rule: crun_induct)
    case (Suc k ffi evs l m w fr ns)
    from Suc.prems obtain sy v\<^sub>0 where
      sy: \<open>ffi_sym l = Some sy\<close> and host: \<open>ffi sy evs w = Some (FRet v\<^sub>0)\<close> and
      rest: \<open>crun k ffi (evs @ [FFIev sy w (FRet v\<^sub>0)]) (cunwind k v\<^sub>0 fr ns) = (Rval v, evs')\<close>
      by (auto split: option.split_asm ffi_res.split_asm)
    obtain r\<^sub>1 ns\<^sub>1 where u: \<open>cunwind k v\<^sub>0 fr ns = (r\<^sub>1, ns\<^sub>1)\<close>
      by (cases \<open>cunwind k v\<^sub>0 fr ns\<close>) blast
    show ?case
      by (rule CrHost[OF sy host cunwind_imp_D[OF u crun_Rval_displayable[OF rest[unfolded u]]]
                         Suc.hyps[OF sy host refl _ rest[unfolded u]]]) (simp add: u)
  qed (auto intro: CrVal)
qed

lemma cevalpD_adequate:
  \<open>cevalpD ffi env ns evs p env' evs' \<longleftrightarrow>
   (\<exists>k. ceval_prog k ffi env ns evs p = (Rval env', evs'))\<close>
proof
  assume \<open>cevalpD ffi env ns evs p env' evs'\<close>
  then show \<open>\<exists>k. ceval_prog k ffi env ns evs p = (Rval env', evs')\<close>
  proof induction
    case (EpNil ffi env ns evs)
    show ?case by (intro exI[of _ 0]) simp
  next
    case (EpCons env e ns r ns\<^sub>1 ffi evs v ns\<^sub>2 evs\<^sub>1 x ds env' evs')
    from EpCons.hyps obtain k\<^sub>1 where h\<^sub>1: \<open>ceval k\<^sub>1 env e ns = (r, ns\<^sub>1)\<close>
      by (auto dest: D_imp_ceval)
    from EpCons.hyps obtain k\<^sub>2 where h\<^sub>2: \<open>crun k\<^sub>2 ffi evs (r, ns\<^sub>1) = (Rval (v, ns\<^sub>2), evs\<^sub>1)\<close>
      by (auto simp: crunD_adequate)
    from EpCons.IH obtain k\<^sub>3 where
      h\<^sub>3: \<open>ceval_prog k\<^sub>3 ffi ((x, v) # env) ns\<^sub>2 evs\<^sub>1 ds = (Rval env', evs')\<close> by blast
    define K where \<open>K = max k\<^sub>1 (max k\<^sub>2 k\<^sub>3)\<close>
    have le: \<open>k\<^sub>1 \<le> K\<close> \<open>k\<^sub>2 \<le> K\<close> \<open>k\<^sub>3 \<le> K\<close> by (simp_all add: K_def)
    have \<open>ceval_prog K ffi env ns evs ((x, e) # ds) = (Rval env', evs')\<close>
      using EpCons.hyps D_ne
      by (simp add: ceval_ne_mono[OF h\<^sub>1] crun_Rval_mono[OF h\<^sub>2] ceval_prog_Rval_mono[OF h\<^sub>3] le)
    then show ?case by blast
  qed
next
  assume \<open>\<exists>k. ceval_prog k ffi env ns evs p = (Rval env', evs')\<close>
  then obtain k where \<open>ceval_prog k ffi env ns evs p = (Rval env', evs')\<close> by blast
  then show \<open>cevalpD ffi env ns evs p env' evs'\<close>
  proof (induction p arbitrary: env ns evs)
    case Nil
    then show ?case by (auto intro: EpNil)
  next
    case (Cons d ds)
    obtain x e where d: \<open>d = (x, e)\<close> by (cases d) auto
    obtain r ns\<^sub>1 where ce: \<open>ceval k env e ns = (r, ns\<^sub>1)\<close> by (cases \<open>ceval k env e ns\<close>) blast
    from Cons.prems obtain v ns\<^sub>2 evs\<^sub>1 where
      hv: \<open>crun k ffi evs (r, ns\<^sub>1) = (Rval (v, ns\<^sub>2), evs\<^sub>1)\<close> and
      rest: \<open>ceval_prog k ffi ((x, v) # env) ns\<^sub>2 evs\<^sub>1 ds = (Rval env', evs')\<close>
      unfolding d by (auto simp: sbind_def ce split: prod.split_asm cres.split_asm)
    have ev: \<open>env \<turnstile> e,ns \<Down> r,ns\<^sub>1\<close>
      by (rule ceval_imp_D[OF ce crun_Rval_displayable[OF hv]])
    have \<open>crunD ffi evs (r, ns\<^sub>1) (v, ns\<^sub>2) evs\<^sub>1\<close>
      using hv by (auto simp: crunD_adequate)
    then show ?case
      unfolding d by (rule EpCons[OF ev _ Cons.IH[OF rest]])
  qed
qed

lemma crun_imp_D:
  \<open>crun k ffi evs (r, ns) = (Rval v, evs') \<Longrightarrow> crunD ffi evs (r, ns) v evs'\<close>
  using crunD_adequate by blast

lemma ceval_prog_imp_D:
  \<open>ceval_prog k ffi env ns evs p = (Rval env', evs') \<Longrightarrow> cevalpD ffi env ns evs p env' evs'\<close>
  using cevalpD_adequate by blast

end
