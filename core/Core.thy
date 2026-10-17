theory Core
  imports CaraML_Prelude.Named_Cases CaraML_Syntax.Names CaraML_Syntax.Protocol
begin

section \<open>The module-free core language and its semantics\<close>

text \<open>The target of static interpretation: a module-free core with functions,
  recursive let, saturated constructors, nested matches, effect handlers and a
  foreign interface. Names are the flat codepoint strings of
  \<^theory>\<open>CaraML_Syntax.Names\<close>. Tuples are \<^text>\<open>Ccon\<close> applications of the
  constructor names \<^const>\<open>tuple_con\<close>.

  An unnamed handler \<^text>\<open>Chandle l h b\<close> catches the operations of label
  \<open>l\<close> performed in \<open>b\<close>. A named handler \<^text>\<open>Chandlen l h \<phi> b\<close>
  \<^cite>\<open>\<open>Sect. 2.3\<close> in xie2021names\<close> mints a fresh handler name, applies the
  action \<open>b\<close> to it, and catches the operations performed on that name
  (\<^text>\<open>Cperformn x op a\<close>), its frame keeps the residual of the effect's
  protocol \<open>\<phi>\<close>.\<close>

datatype lit = LNat nat | LStr name | LChr nat

datatype cpat =
    CPany
  | CPvar name
  | CPlit lit
  | CPcon name \<open>cpat list\<close>
  | CPas name cpat                \<comment> \<open>\<open>p as x\<close>\<close>

datatype cexp =
    Cvar name
  | Clit lit
  | Clam name cexp
  | Capp cexp cexp
  | Clet name cexp cexp
  | Cletrec name name cexp cexp   \<comment> \<open>\<open>letrec f x = e in b\<close>\<close>
  | Ccon name \<open>cexp list\<close>
  | Cmatch cexp \<open>(cpat \<times> cexp) list\<close>
  | Cperform name cexp            \<comment> \<open>invoke effect operation (label, argument)\<close>
  | Chandle name cexp cexp        \<comment> \<open>\<open>handle l with h in b\<close>: delimit \<open>b\<close> with
                                      handler \<open>h\<close> for label \<open>l\<close>\<close>
  | Cmask name cexp               \<comment> \<open>skip the innermost \<open>l\<close>-handler\<close>
  | Cperformn cexp name cexp      \<comment> \<open>\<open>x.op a\<close>: invoke \<open>op\<close> on the handler named by \<open>x\<close>\<close>
  | Chandlen name cexp \<open>name ltlf option\<close> cexp
                                  \<comment> \<open>\<open>handle l with h under \<phi> applied to b\<close>: a fresh
                                      name for the action \<open>b\<close>, its operations caught
                                      by \<open>h\<close>, its trace checked against \<open>\<phi>\<close>\<close>

text \<open>A captured continuation is a list of evaluation-context frames (innermost
  first). Continuations apply like functions, so handlers have full control,
  multi-shot resumption included.\<close>

datatype cval =
    Vlit lit
  | Vclos \<open>(name \<times> cval) list\<close> name cexp
  | Vclosrec \<open>(name \<times> cval) list\<close> name name cexp
  | Vcon name \<open>cval list\<close>
  | VCont \<open>cframe list\<close>                       \<comment> \<open>captured continuation\<close>
  | Vname nat                                 \<comment> \<open>a handler name\<close>
and cframe =
    CFapp1 \<open>(name \<times> cval) list\<close> cexp          \<comment> \<open>function done, argument pending\<close>
  | CFapp2 cval                               \<comment> \<open>argument done, apply to this function\<close>
  | CFlet name \<open>(name \<times> cval) list\<close> cexp
  | CFcon name \<open>cval list\<close> \<open>(name \<times> cval) list\<close> \<open>cexp list\<close>
  | CFmatch \<open>(name \<times> cval) list\<close> \<open>(cpat \<times> cexp) list\<close>
  | CFperf name                               \<comment> \<open>operation argument pending\<close>
  | CFperfn1 \<open>(name \<times> cval) list\<close> name cexp   \<comment> \<open>name pending, then the argument\<close>
  | CFperfn2 cval name                        \<comment> \<open>name done, argument pending\<close>
  | CFhandle name cval                        \<comment> \<open>re-entering this handler's scope\<close>
  | CFhandlen name nat cval \<open>name ltlf option\<close>
                                              \<comment> \<open>named handler: label, name, handler, residual\<close>
  | CFmask name

text \<open>The name supply a value needs: one above every handler name it holds.\<close>

fun vsup :: \<open>cval \<Rightarrow> nat\<close> and vsups :: \<open>cval list \<Rightarrow> nat\<close>
and esup :: \<open>(name \<times> cval) list \<Rightarrow> nat\<close>
and fsup :: \<open>cframe \<Rightarrow> nat\<close> and fssup :: \<open>cframe list \<Rightarrow> nat\<close> where
  \<open>vsup (Vlit l) = 0\<close>
| \<open>vsup (Vclos env x b) = esup env\<close>
| \<open>vsup (Vclosrec env f x b) = esup env\<close>
| \<open>vsup (Vcon c vs) = vsups vs\<close>
| \<open>vsup (VCont fs) = fssup fs\<close>
| \<open>vsup (Vname i) = Suc i\<close>
| \<open>vsups [] = 0\<close>
| \<open>vsups (v # vs) = max (vsup v) (vsups vs)\<close>
| \<open>esup [] = 0\<close>
| \<open>esup ((x, v) # env) = max (vsup v) (esup env)\<close>
| \<open>fsup (CFapp1 env a) = esup env\<close>
| \<open>fsup (CFapp2 v) = vsup v\<close>
| \<open>fsup (CFlet x env b) = esup env\<close>
| \<open>fsup (CFcon c vs env es) = max (vsups vs) (esup env)\<close>
| \<open>fsup (CFmatch env cls) = esup env\<close>
| \<open>fsup (CFperf l) = 0\<close>
| \<open>fsup (CFperfn1 env op a) = esup env\<close>
| \<open>fsup (CFperfn2 v op) = vsup v\<close>
| \<open>fsup (CFhandle l hv) = vsup hv\<close>
| \<open>fsup (CFhandlen l i hv \<phi>) = max (Suc i) (vsup hv)\<close>
| \<open>fsup (CFmask l) = 0\<close>
| \<open>fssup [] = 0\<close>
| \<open>fssup (f # fs) = max (fsup f) (fssup fs)\<close>

subsection \<open>The foreign interface\<close>

text \<open>A foreign call is an effect operation that no handler answers: it
  escapes to the top level, where the host answers it (\<open>crun\<close> below).
  Externs perform on labels \<open>%ffi.sym\<close>, which no source label can spell, so
  no \<open>handle\<close> or \<open>mask\<close> meets one. The host is an oracle from the symbol, the
  history of earlier calls and the argument to an answer, or to \<^const>\<open>None\<close>
  when it rejects the call: stuckness, which \<^text>\<open>ffi_ok\<close> rules out. Values
  cross the boundary as core values, a backend fixes the marshalling. The
  oracle has the shape of CakeML's \<^cite>\<open>\<open>Sect. 2\<close> in kumar2014\<close>, with the
  history in place of the host state.\<close>

datatype ffi_res = FRet cval | FErr         \<comment> \<open>an answer, or the host ends the run\<close>
datatype ffi_ev = FFIev name cval ffi_res   \<comment> \<open>symbol, argument, answer: one trace event\<close>
type_synonym ffi = \<open>name \<Rightarrow> ffi_ev list \<Rightarrow> cval \<Rightarrow> ffi_res option\<close>

definition ffi_label :: \<open>name \<Rightarrow> name\<close> where
  \<open>ffi_label sy = str ''%ffi.'' @ sy\<close>

definition ffi_sym :: \<open>name \<Rightarrow> name option\<close> where
  \<open>ffi_sym l = (if take 5 l = str ''%ffi.'' then Some (drop 5 l) else None)\<close>

lemma ffi_sym_label[simp]: \<open>ffi_sym (ffi_label sy) = Some sy\<close>
  by (simp add: ffi_sym_def ffi_label_def)

subsection \<open>Results\<close>

text \<open>Results distinguish success, clock exhaustion, stuckness, and the host
  ending the run. A program diverges iff it times out at every clock.\<close>

datatype 'a cres = Rval 'a | Rtimeout | Rerr | Rhost ffi_ev

text \<open>The evaluator's results have two more alternatives, the \<^emph>\<open>bubbles\<close>:
  \<open>HRop l m v k\<close> is an operation of label \<open>l\<close> with payload \<open>v\<close> rising towards
  its handler with the captured continuation \<open>k\<close>, \<open>m\<close> counting the
  \<open>l\<close>-handlers still to skip. \<open>HRopn i op v k\<close> is operation \<open>op\<close> performed
  on the handler named \<open>i\<close>, which only that handler's frame catches.\<close>

datatype hres =
    HRval cval
  | HRtimeout
  | HRerr
  | HRop name nat cval \<open>cframe list\<close>
  | HRopn nat name cval \<open>cframe list\<close>

fun cpmatch :: \<open>cpat \<Rightarrow> cval \<Rightarrow> (name \<times> cval) list option\<close> and
  cpmatch_list :: \<open>cpat list \<Rightarrow> cval list \<Rightarrow> (name \<times> cval) list option\<close>
where
  \<open>cpmatch CPany v = Some []\<close>
| \<open>cpmatch (CPvar x) v = Some [(x, v)]\<close>
| \<open>cpmatch (CPlit l) (Vlit l') = (if l = l' then Some [] else None)\<close>
| \<open>cpmatch (CPlit l) _ = None\<close>
| \<open>cpmatch (CPcon c ps) (Vcon c' vs) =
     (if c = c' \<and> length ps = length vs then cpmatch_list ps vs else None)\<close>
| \<open>cpmatch (CPcon c ps) _ = None\<close>
| \<open>cpmatch (CPas x p) v =
     (case cpmatch p v of None \<Rightarrow> None | Some bs \<Rightarrow> Some ((x, v) # bs))\<close>
| \<open>cpmatch_list [] [] = Some []\<close>
| \<open>cpmatch_list (p # ps) (v # vs) =
     (case cpmatch p v of
        None \<Rightarrow> None
      | Some b \<Rightarrow> (case cpmatch_list ps vs of None \<Rightarrow> None | Some bs \<Rightarrow> Some (b @ bs)))\<close>
| \<open>cpmatch_list ps vs = None\<close>

lemmas cpmatch_induct = cpmatch_cpmatch_list.induct[named_cases cpmatch]

subsection \<open>The evaluator\<close>

text \<open>\<^const>\<open>Cperform\<close> yields a bubble that rises through the evaluation
  contexts, each appending its frame to the captured continuation.
  \<^const>\<open>Chandle\<close> catches the bubbles of its label and applies the handler to
  \<open>(payload, resume)\<close>; \<open>resume\<close> ends with the handler's frame, so handlers are
  deep. \<^const>\<open>Cmask\<close> increments the bubble's skip count, so one enclosing
  \<open>l\<close>-handler lets it pass.

  Names are generative \<^cite>\<open>\<open>Sect. 4\<close> in milner1997\<close>
  \<^cite>\<open>\<open>Sect. 2.3\<close> in xie2021names\<close>: a supply \<open>ns\<close> is threaded through the
  evaluator, and \<^const>\<open>Chandlen\<close> takes the next number. Its frame
  \<^const>\<open>CFhandlen\<close> carries the protocol residual. A named bubble caught by
  the frame with its number steps the residual by \<^const>\<open>nfderiv\<close>, and is
  stuck when that is \<open>Ff\<close>; the handler receives the operation's name with the
  payload and the resumption, since one handler value serves every operation
  of the effect. Leaving the frame normally is stuck unless the residual is
  nullable. A handler that discards its continuation drops the frame without
  leaving it, so an abort is not checked. Unnamed bubbles pass named frames;
  named bubbles pass unnamed frames and masks.\<close>

fun push :: \<open>cframe \<Rightarrow> hres \<Rightarrow> hres\<close> where
  \<open>push f (HRop l m w fr) = HRop l m w (fr @ [f])\<close>
| \<open>push f (HRopn i op w fr) = HRopn i op w (fr @ [f])\<close>
| \<open>push f r = r\<close>

text \<open>The bind of the evaluator: continue with a value, or let anything else
  rise, a bubble taking the frame along (\<^const>\<open>push\<close>).\<close>

definition bindr ::
  \<open>hres \<times> nat \<Rightarrow> cframe \<Rightarrow> (cval \<Rightarrow> nat \<Rightarrow> hres \<times> nat) \<Rightarrow> hres \<times> nat\<close> where
  \<open>bindr p f g = (case p of (HRval v, ns) \<Rightarrow> g v ns | (r, ns) \<Rightarrow> (push f r, ns))\<close>

lemma bindr_simps[simp]:
  \<open>bindr (HRval v, ns) f g = g v ns\<close>
  \<open>bindr (HRtimeout, ns) f g = (HRtimeout, ns)\<close>
  \<open>bindr (HRerr, ns) f g = (HRerr, ns)\<close>
  \<open>bindr (HRop l m w fr, ns) f g = (HRop l m w (fr @ [f]), ns)\<close>
  \<open>bindr (HRopn i op w fr, ns) f g = (HRopn i op w (fr @ [f]), ns)\<close>
  by (simp_all add: bindr_def)

lemma bindr_cong[fundef_cong]:
  \<open>p = p' \<Longrightarrow> f = f' \<Longrightarrow> (\<And>v ns. p' = (HRval v, ns) \<Longrightarrow> g v ns = g' v ns) \<Longrightarrow>
   bindr p f g = bindr p' f' g'\<close>
  by (auto simp: bindr_def split: prod.split hres.split)

text \<open>The handler position of \<^const>\<open>Chandle\<close>, and the handler and action
  positions of \<^const>\<open>Chandlen\<close>, must evaluate to a value: a bubble there is
  stuckness.\<close>

definition guardr :: \<open>hres \<times> nat \<Rightarrow> (cval \<Rightarrow> nat \<Rightarrow> hres \<times> nat) \<Rightarrow> hres \<times> nat\<close> where
  \<open>guardr p g =
     (case p of
        (HRval v, ns) \<Rightarrow> g v ns
      | (HRtimeout, ns) \<Rightarrow> (HRtimeout, ns)
      | (_, ns) \<Rightarrow> (HRerr, ns))\<close>

lemma guardr_simps[simp]:
  \<open>guardr (HRval v, ns) g = g v ns\<close>
  \<open>guardr (HRtimeout, ns) g = (HRtimeout, ns)\<close>
  \<open>guardr (HRerr, ns) g = (HRerr, ns)\<close>
  \<open>guardr (HRop l m w fr, ns) g = (HRerr, ns)\<close>
  \<open>guardr (HRopn i op w fr, ns) g = (HRerr, ns)\<close>
  by (simp_all add: guardr_def)

lemma guardr_cong[fundef_cong]:
  \<open>p = p' \<Longrightarrow> (\<And>v ns. p' = (HRval v, ns) \<Longrightarrow> g v ns = g' v ns) \<Longrightarrow>
   guardr p g = guardr p' g'\<close>
  by (auto simp: guardr_def split: prod.split hres.split)

definition thenr :: \<open>hres \<times> nat \<Rightarrow> (hres \<Rightarrow> nat \<Rightarrow> hres \<times> nat) \<Rightarrow> hres \<times> nat\<close> where
  \<open>thenr p g = (case p of (r, ns) \<Rightarrow> g r ns)\<close>

lemma thenr_simps[simp]: \<open>thenr (r, ns) g = g r ns\<close>
  by (simp add: thenr_def)

lemma thenr_cong[fundef_cong]:
  \<open>p = p' \<Longrightarrow> (\<And>r ns. p' = (r, ns) \<Longrightarrow> g r ns = g' r ns) \<Longrightarrow> thenr p g = thenr p' g'\<close>
  by (auto simp: thenr_def split: prod.split)

text \<open>Masking: an unnamed bubble of the label skips one more handler; any
  other bubble records the frame.\<close>

fun maskr :: \<open>name \<Rightarrow> hres \<Rightarrow> hres\<close> where
  \<open>maskr l (HRop l' m w fr) = HRop l' (if l' = l then Suc m else m) w (fr @ [CFmask l])\<close>
| \<open>maskr l r = push (CFmask l) r\<close>

text \<open>The protocol residual: stepping by an operation, and the exit test.\<close>

definition step_prot :: \<open>name \<Rightarrow> name ltlf option \<Rightarrow> name ltlf option option\<close> where
  \<open>step_prot op \<phi> =
     (case \<phi> of None \<Rightarrow> Some None
      | Some \<psi> \<Rightarrow> (let \<psi>' = nfderiv op \<psi> in if \<psi>' = Ff then None else Some (Some \<psi>')))\<close>

fun exit_prot :: \<open>name ltlf option \<Rightarrow> bool\<close> where
  \<open>exit_prot None = True\<close>
| \<open>exit_prot (Some \<psi>) = fnull \<psi>\<close>

fun performn :: \<open>cval \<Rightarrow> name \<Rightarrow> cval \<Rightarrow> nat \<Rightarrow> hres \<times> nat\<close> where
  \<open>performn (Vname i) op av ns = (HRopn i op av [], ns)\<close>
| \<open>performn _ op av ns = (HRerr, ns)\<close>

text \<open>The evaluator has a strict and a relaxed mode. Where the strict mode is
  stuck at a protocol violation, the relaxed one raises a \<^emph>\<open>marker\<close>: a
  bubble on the reserved label \<open>%viol\<close>, which no handler catches
  (theory \<open>Relaxed\<close>).\<close>

definition viol_lbl :: name where
  \<open>viol_lbl = str ''%viol''\<close>

abbreviation viol_ev :: \<open>cval \<Rightarrow> ffi_ev\<close> where
  \<open>viol_ev w \<equiv> FFIev viol_lbl w FErr\<close>

lemma ffi_sym_viol[simp]: \<open>ffi_sym viol_lbl = None\<close>
  by (simp add: ffi_sym_def viol_lbl_def)

lemma viol_not_ffi[simp]: \<open>viol_lbl \<noteq> ffi_label sy\<close> \<open>ffi_label sy \<noteq> viol_lbl\<close>
  by (simp_all add: ffi_label_def viol_lbl_def)

definition viol :: \<open>hres \<Rightarrow> bool\<close> where
  \<open>viol r \<longleftrightarrow> (\<exists>m w fr. r = HRop viol_lbl m w fr)\<close>

lemma viol_simps[simp]:
  \<open>\<not> viol (HRval v)\<close> \<open>\<not> viol HRtimeout\<close> \<open>\<not> viol HRerr\<close> \<open>\<not> viol (HRopn i op w fr)\<close>
  \<open>viol (HRop l m w fr) \<longleftrightarrow> l = viol_lbl\<close>
  by (simp_all add: viol_def)

text \<open>The relaxed mode lets a marker through a guarded position (a violation
  inside a handler position stays a violation).\<close>

definition mguardr :: \<open>bool \<Rightarrow> hres \<times> nat \<Rightarrow> (cval \<Rightarrow> nat \<Rightarrow> hres \<times> nat) \<Rightarrow> hres \<times> nat\<close>
where
  \<open>mguardr rx p g = (if rx \<and> viol (fst p) then p else guardr p g)\<close>

lemma mguardr_simps[simp]:
  \<open>mguardr False p g = guardr p g\<close>
  \<open>mguardr rx (HRval v, ns) g = g v ns\<close>
  \<open>mguardr rx (HRtimeout, ns) g = (HRtimeout, ns)\<close>
  \<open>mguardr rx (HRerr, ns) g = (HRerr, ns)\<close>
  \<open>mguardr rx (HRop l m w fr, ns) g =
     (if rx \<and> l = viol_lbl then (HRop l m w fr, ns) else (HRerr, ns))\<close>
  \<open>mguardr rx (HRopn i op w fr, ns) g = (HRerr, ns)\<close>
  by (simp_all add: mguardr_def)

lemma mguardr_cong[fundef_cong]:
  \<open>p = p' \<Longrightarrow> (\<And>v ns. p' = (HRval v, ns) \<Longrightarrow> g v ns = g' v ns) \<Longrightarrow>
   mguardr rx p g = mguardr rx p' g'\<close>
  by (auto simp: mguardr_def intro: guardr_cong)

context
  fixes rx :: bool
begin

function (sequential) mceval :: \<open>nat \<Rightarrow> (name \<times> cval) list \<Rightarrow> cexp \<Rightarrow> nat \<Rightarrow> hres \<times> nat\<close> and
  mcevcon :: \<open>nat \<Rightarrow> (name \<times> cval) list \<Rightarrow> name \<Rightarrow> cval list \<Rightarrow> cexp list \<Rightarrow> nat \<Rightarrow> hres \<times> nat\<close> and
  mcevalm :: \<open>nat \<Rightarrow> (name \<times> cval) list \<Rightarrow> cval \<Rightarrow> (cpat \<times> cexp) list \<Rightarrow> nat \<Rightarrow> hres \<times> nat\<close> and
  mcapply :: \<open>nat \<Rightarrow> cval \<Rightarrow> cval \<Rightarrow> nat \<Rightarrow> hres \<times> nat\<close> and
  mcstep :: \<open>nat \<Rightarrow> cval \<Rightarrow> cframe \<Rightarrow> nat \<Rightarrow> hres \<times> nat\<close> and
  mcunwind :: \<open>nat \<Rightarrow> cval \<Rightarrow> cframe list \<Rightarrow> nat \<Rightarrow> hres \<times> nat\<close> and
  mcresume :: \<open>nat \<Rightarrow> hres \<Rightarrow> cframe list \<Rightarrow> nat \<Rightarrow> hres \<times> nat\<close> and
  mcthrow :: \<open>nat \<Rightarrow> name \<Rightarrow> nat \<Rightarrow> cval \<Rightarrow> cframe list \<Rightarrow> cframe list \<Rightarrow> nat \<Rightarrow> hres \<times> nat\<close> and
  mcthrown :: \<open>nat \<Rightarrow> nat \<Rightarrow> name \<Rightarrow> cval \<Rightarrow> cframe list \<Rightarrow> cframe list \<Rightarrow> nat \<Rightarrow> hres \<times> nat\<close>
where
  \<open>mceval 0 env e ns = (HRtimeout, ns)\<close>
| \<open>mceval (Suc k) env (Cvar x) ns =
     (case map_of env x of Some v \<Rightarrow> (HRval v, ns) | None \<Rightarrow> (HRerr, ns))\<close>
| \<open>mceval (Suc k) env (Clit l) ns = (HRval (Vlit l), ns)\<close>
| \<open>mceval (Suc k) env (Clam x b) ns = (HRval (Vclos env x b), ns)\<close>
| \<open>mceval (Suc k) env (Capp f a) ns =
     bindr (mceval k env f ns) (CFapp1 env a) (\<lambda>fv ns\<^sub>1.
       bindr (mceval k env a ns\<^sub>1) (CFapp2 fv) (\<lambda>av ns\<^sub>2. mcapply k fv av ns\<^sub>2))\<close>
| \<open>mceval (Suc k) env (Clet x e b) ns =
     bindr (mceval k env e ns) (CFlet x env b) (\<lambda>v ns\<^sub>1. mceval k ((x, v) # env) b ns\<^sub>1)\<close>
| \<open>mceval (Suc k) env (Cletrec f x e b) ns =
     mceval k ((f, Vclosrec env f x e) # env) b ns\<close>
| \<open>mceval (Suc k) env (Ccon c es) ns = mcevcon k env c [] es ns\<close>
| \<open>mceval (Suc k) env (Cmatch e cls) ns =
     bindr (mceval k env e ns) (CFmatch env cls) (\<lambda>v ns\<^sub>1. mcevalm k env v cls ns\<^sub>1)\<close>
| \<open>mceval (Suc k) env (Cperform l a) ns =
     bindr (mceval k env a ns) (CFperf l) (\<lambda>av ns\<^sub>1. (HRop l 0 av [], ns\<^sub>1))\<close>
| \<open>mceval (Suc k) env (Chandle l h b) ns =
     mguardr rx (mceval k env h ns) (\<lambda>hv ns\<^sub>1.
       thenr (mceval k env b ns\<^sub>1) (\<lambda>r ns\<^sub>2. mcresume k r [CFhandle l hv] ns\<^sub>2))\<close>
| \<open>mceval (Suc k) env (Cmask l e) ns = thenr (mceval k env e ns) (\<lambda>r ns\<^sub>1. (maskr l r, ns\<^sub>1))\<close>
| \<open>mceval (Suc k) env (Cperformn x op a) ns =
     bindr (mceval k env x ns) (CFperfn1 env op a) (\<lambda>xv ns\<^sub>1.
       bindr (mceval k env a ns\<^sub>1) (CFperfn2 xv op) (\<lambda>av ns\<^sub>2. performn xv op av ns\<^sub>2))\<close>
| \<open>mceval (Suc k) env (Chandlen l h \<phi> b) ns =
     mguardr rx (mceval k env h ns) (\<lambda>hv ns\<^sub>1.
       mguardr rx (mceval k env b ns\<^sub>1) (\<lambda>bv ns\<^sub>2.
         thenr (mcapply k bv (Vname ns\<^sub>2) (Suc ns\<^sub>2))
               (\<lambda>r ns\<^sub>3. mcresume k r [CFhandlen l ns\<^sub>2 hv \<phi>] ns\<^sub>3)))\<close>

| \<open>mcevcon 0 env c vs es ns = (HRtimeout, ns)\<close>
| \<open>mcevcon (Suc k) env c vs [] ns = (HRval (Vcon c (rev vs)), ns)\<close>
| \<open>mcevcon (Suc k) env c vs (e # es) ns =
     bindr (mceval k env e ns) (CFcon c vs env es) (\<lambda>v ns\<^sub>1. mcevcon k env c (v # vs) es ns\<^sub>1)\<close>

| \<open>mcevalm 0 env v cls ns = (HRtimeout, ns)\<close>
| \<open>mcevalm (Suc k) env v [] ns = (HRerr, ns)\<close>
| \<open>mcevalm (Suc k) env v ((p, e) # cls) ns =
     (case cpmatch p v of
        Some bs \<Rightarrow> mceval k (bs @ env) e ns
      | None \<Rightarrow> mcevalm k env v cls ns)\<close>

| \<open>mcapply 0 fv av ns = (HRtimeout, ns)\<close>
| \<open>mcapply (Suc k) (Vclos cenv x b) av ns = mceval k ((x, av) # cenv) b ns\<close>
| \<open>mcapply (Suc k) (Vclosrec cenv g x b) av ns =
     mceval k ((x, av) # (g, Vclosrec cenv g x b) # cenv) b ns\<close>
| \<open>mcapply (Suc k) (VCont fs) av ns = mcunwind k av fs ns\<close>
| \<open>mcapply (Suc k) fv av ns = (HRerr, ns)\<close>

| \<open>mcstep 0 v f ns = (HRtimeout, ns)\<close>
| \<open>mcstep (Suc k) v (CFapp1 env a) ns =
     bindr (mceval k env a ns) (CFapp2 v) (\<lambda>av ns\<^sub>1. mcapply k v av ns\<^sub>1)\<close>
| \<open>mcstep (Suc k) v (CFapp2 fv) ns = mcapply k fv v ns\<close>
| \<open>mcstep (Suc k) v (CFlet x env b) ns = mceval k ((x, v) # env) b ns\<close>
| \<open>mcstep (Suc k) v (CFcon c vs env es) ns = mcevcon k env c (v # vs) es ns\<close>
| \<open>mcstep (Suc k) v (CFmatch env cls) ns = mcevalm k env v cls ns\<close>
| \<open>mcstep (Suc k) v (CFperf l) ns = (HRop l 0 v [], ns)\<close>
| \<open>mcstep (Suc k) v (CFperfn1 env op a) ns =
     bindr (mceval k env a ns) (CFperfn2 v op) (\<lambda>av ns\<^sub>1. performn v op av ns\<^sub>1)\<close>
| \<open>mcstep (Suc k) v (CFperfn2 xv op) ns = performn xv op v ns\<close>
| \<open>mcstep (Suc k) v (CFhandle l hv) ns = (HRval v, ns)\<close>
| \<open>mcstep (Suc k) v (CFhandlen l i hv \<phi>) ns =
     (if exit_prot \<phi> then (HRval v, ns)
      else (if rx then HRop viol_lbl 0 v [] else HRerr, ns))\<close>
| \<open>mcstep (Suc k) v (CFmask l) ns = (HRval v, ns)\<close>

| \<open>mcunwind 0 v fs ns = (HRtimeout, ns)\<close>
| \<open>mcunwind (Suc k) v [] ns = (HRval v, ns)\<close>
| \<open>mcunwind (Suc k) v (f # fs) ns = thenr (mcstep k v f ns) (\<lambda>r ns\<^sub>1. mcresume k r fs ns\<^sub>1)\<close>

| \<open>mcresume 0 r fs ns = (HRtimeout, ns)\<close>
| \<open>mcresume (Suc k) (HRval v) fs ns = mcunwind k v fs ns\<close>
| \<open>mcresume (Suc k) (HRop l m w fr) fs ns =
     (if rx \<and> l = viol_lbl then (HRop l m w fr, ns) else mcthrow k l m w fr fs ns)\<close>
| \<open>mcresume (Suc k) (HRopn i op w fr) fs ns = mcthrown k i op w fr fs ns\<close>
| \<open>mcresume (Suc k) r fs ns = (r, ns)\<close>

| \<open>mcthrow 0 l m w fr fs ns = (HRtimeout, ns)\<close>
| \<open>mcthrow (Suc k) l m w fr [] ns = (HRop l m w fr, ns)\<close>
| \<open>mcthrow (Suc k) l m w fr (CFhandle l' hv # fs) ns =
     (if l' = l then
        (if m = 0 then
           thenr (mcapply k hv (Vcon (tuple_con 2) [w, VCont (fr @ [CFhandle l' hv])]) ns)
                 (\<lambda>r ns\<^sub>1. mcresume k r fs ns\<^sub>1)
         else mcthrow k l (m - 1) w (fr @ [CFhandle l' hv]) fs ns)
      else mcthrow k l m w (fr @ [CFhandle l' hv]) fs ns)\<close>
| \<open>mcthrow (Suc k) l m w fr (CFmask l' # fs) ns =
     (if l' = l then mcthrow k l (Suc m) w (fr @ [CFmask l']) fs ns
      else mcthrow k l m w (fr @ [CFmask l']) fs ns)\<close>
| \<open>mcthrow (Suc k) l m w fr (f # fs) ns = mcthrow k l m w (fr @ [f]) fs ns\<close>

| \<open>mcthrown 0 i op w fr fs ns = (HRtimeout, ns)\<close>
| \<open>mcthrown (Suc k) i op w fr [] ns = (HRopn i op w fr, ns)\<close>
| \<open>mcthrown (Suc k) i op w fr (CFhandlen l j hv \<phi> # fs) ns =
     (if j = i then
        (case step_prot op \<phi> of
           None \<Rightarrow> (if rx then HRop viol_lbl 0 w [] else HRerr, ns)
         | Some \<phi>' \<Rightarrow>
             thenr
               (mcapply k hv
                  (Vcon (tuple_con 3) [Vlit (LStr op), w, VCont (fr @ [CFhandlen l j hv \<phi>'])]) ns)
               (\<lambda>r ns\<^sub>1. mcresume k r fs ns\<^sub>1))
      else mcthrown k i op w (fr @ [CFhandlen l j hv \<phi>]) fs ns)\<close>
| \<open>mcthrown (Suc k) i op w fr (f # fs) ns = mcthrown k i op w (fr @ [f]) fs ns\<close>
  by pat_completeness auto  (* ~50s *)

text \<open>Every call decrements the fuel:\<close>

termination
  by (relation \<open>measure (\<lambda>x.
        case x of
          Inl (Inl (Inl (k, _))) \<Rightarrow> k
        | Inl (Inl (Inr (k, _))) \<Rightarrow> k
        | Inl (Inr (Inl (k, _))) \<Rightarrow> k
        | Inl (Inr (Inr (k, _))) \<Rightarrow> k
        | Inr (Inl (Inl (k, _))) \<Rightarrow> k
        | Inr (Inl (Inr (k, _))) \<Rightarrow> k
        | Inr (Inr (Inl (k, _))) \<Rightarrow> k
        | Inr (Inr (Inr (Inl (k, _)))) \<Rightarrow> k
        | Inr (Inr (Inr (Inr (k, _)))) \<Rightarrow> k)\<close>)
     auto

text \<open>An operation that escapes a top-level binding is a foreign call if its
  label says so, and stuckness otherwise; an escaped named operation is
  stuckness. \<open>crun\<close> services the foreign calls: it asks the host, records the
  event, and resumes the captured continuation, the whole rest of the binding.
  Its own fuel bounds the number of calls. Every result carries the trace, a
  timeout too: the trace of a diverging program is the limit of those. In the
  relaxed mode a marker reaching the top level, and an escaped named
  operation, end the run with a host event on the marker label.

  A finished run returns the name supply, which the program loop threads from
  one top-level binding to the next, starting at \<open>0\<close>, so no name is minted
  twice.\<close>

fun mcrun ::
  \<open>nat \<Rightarrow> ffi \<Rightarrow> ffi_ev list \<Rightarrow> hres \<times> nat \<Rightarrow> (cval \<times> nat) cres \<times> ffi_ev list\<close>
where
  \<open>mcrun k ffi evs (HRval v, ns) = (Rval (v, ns), evs)\<close>
| \<open>mcrun k ffi evs (HRtimeout, ns) = (Rtimeout, evs)\<close>
| \<open>mcrun k ffi evs (HRerr, ns) = (Rerr, evs)\<close>
| \<open>mcrun k ffi evs (HRopn i op w fr, ns) = (if rx then Rhost (viol_ev w) else Rerr, evs)\<close>
| \<open>mcrun 0 ffi evs (HRop l m w fr, ns) =
     (if rx \<and> l = viol_lbl then Rhost (viol_ev w) else Rtimeout, evs)\<close>
| \<open>mcrun (Suc k) ffi evs (HRop l m w fr, ns) =
     (case ffi_sym l of
        None \<Rightarrow> (if rx \<and> l = viol_lbl then Rhost (viol_ev w) else Rerr, evs)
      | Some sy \<Rightarrow>
          (case ffi sy evs w of
             None \<Rightarrow> (Rerr, evs)
           | Some FErr \<Rightarrow> (Rhost (FFIev sy w FErr), evs)
           | Some (FRet v) \<Rightarrow>
               mcrun k ffi (evs @ [FFIev sy w (FRet v)]) (mcunwind k v fr ns)))\<close>

end

lemmas ceval_induct =
  mceval_mcevcon_mcevalm_mcapply_mcstep_mcunwind_mcresume_mcthrow_mcthrown.induct[where rx=False,
    named_cases ceval cevcon cevalm capply cstep cunwind cresume cthrow cthrown]

lemmas crun_induct = mcrun.induct[where rx=False, named_cases]

abbreviation \<open>ceval \<equiv> mceval False\<close>
abbreviation \<open>cevcon \<equiv> mcevcon False\<close>
abbreviation \<open>cevalm \<equiv> mcevalm False\<close>
abbreviation \<open>capply \<equiv> mcapply False\<close>
abbreviation \<open>cstep \<equiv> mcstep False\<close>
abbreviation \<open>cunwind \<equiv> mcunwind False\<close>
abbreviation \<open>cresume \<equiv> mcresume False\<close>
abbreviation \<open>cthrow \<equiv> mcthrow False\<close>
abbreviation \<open>cthrown \<equiv> mcthrown False\<close>
abbreviation \<open>crun \<equiv> mcrun False\<close>

definition sbind :: \<open>'a cres \<times> 's \<Rightarrow> ('a \<Rightarrow> 's \<Rightarrow> 'b cres \<times> 's) \<Rightarrow> 'b cres \<times> 's\<close> where
  \<open>sbind a f =
     (case a of
        (Rval v, s) \<Rightarrow> f v s
      | (Rtimeout, s) \<Rightarrow> (Rtimeout, s)
      | (Rerr, s) \<Rightarrow> (Rerr, s)
      | (Rhost ev, s) \<Rightarrow> (Rhost ev, s))\<close>

lemma sbind_simps[simp]:
  \<open>sbind (Rval v, s) f = f v s\<close>
  \<open>sbind (Rtimeout, s) f = (Rtimeout, s)\<close>
  \<open>sbind (Rerr, s) f = (Rerr, s)\<close>
  \<open>sbind (Rhost ev, s) f = (Rhost ev, s)\<close>
  by (simp_all add: sbind_def)

lemma sbind_assoc[simp]:
  \<open>sbind (sbind a f) g = sbind a (\<lambda>v s. sbind (f v s) g)\<close>
  by (auto simp: sbind_def split: prod.split cres.split)

text \<open>A core program is a sequence of top-level bindings; its result is the
  value of an entry binding with the trace of foreign calls. A linked program
  takes its entry from a unit; \<open>csem\<close> fixes the whole-program entry
  \<open>main\<close>.\<close>

type_synonym cprog = \<open>(name \<times> cexp) list\<close>

context
  fixes rx :: bool
begin

fun mceval_prog :: \<open>nat \<Rightarrow> ffi \<Rightarrow> (name \<times> cval) list \<Rightarrow> nat \<Rightarrow> ffi_ev list \<Rightarrow> cprog \<Rightarrow>
    ((name \<times> cval) list \<times> nat) cres \<times> ffi_ev list\<close> where
  \<open>mceval_prog k ffi env ns evs [] = (Rval (env, ns), evs)\<close>
| \<open>mceval_prog k ffi env ns evs ((x, e) # ds) =
     sbind (mcrun rx k ffi evs (mceval rx k env e ns))
       (\<lambda>(v, ns') evs'. mceval_prog k ffi ((x, v) # env) ns' evs' ds)\<close>

definition mcentry :: \<open>name \<Rightarrow> ffi \<Rightarrow> cprog \<Rightarrow> nat \<Rightarrow> cval cres \<times> ffi_ev list\<close> where
  \<open>mcentry x ffi p k =
     sbind (mceval_prog k ffi [] 0 [] p) (\<lambda>(env, _) evs.
       (case map_of env x of Some v \<Rightarrow> Rval v | None \<Rightarrow> Rerr, evs))\<close>

end

abbreviation \<open>ceval_prog \<equiv> mceval_prog False\<close>
abbreviation \<open>centry \<equiv> mcentry False\<close>

abbreviation csem :: \<open>ffi \<Rightarrow> cprog \<Rightarrow> nat \<Rightarrow> cval cres \<times> ffi_ev list\<close> where
  \<open>csem \<equiv> centry (str ''main'')\<close>

subsection \<open>Clock monotonicity\<close>

text \<open>More fuel can only turn timeouts into results, never change a result.
  The order is flat, timeout below everything else. With a host in the loop,
  more fuel can also extend the trace: on a result with its trace the order
  is flat on the result and, below a timeout, prefix on the trace.\<close>

lemma Suc_leE:
  assumes \<open>Suc k \<le> k'\<close>
  obtains m where \<open>k' = Suc m\<close> and \<open>k \<le> m\<close>
  using assms by (cases k') auto

definition tres_le :: \<open>'a cres \<times> ffi_ev list \<Rightarrow> 'a cres \<times> ffi_ev list \<Rightarrow> bool\<close>
  (infix \<open>\<sqsubseteq>\<^sub>t\<close> 50) where
  \<open>r \<sqsubseteq>\<^sub>t r' \<longleftrightarrow> (fst r = Rtimeout \<and> (\<exists>es. snd r' = snd r @ es)) \<or> r' = r\<close>

lemma tres_le_refl[simp, intro!]: \<open>r \<sqsubseteq>\<^sub>t r\<close>
  by (simp add: tres_le_def)

lemma tres_le_timeout: \<open>snd r' = evs @ es \<Longrightarrow> (Rtimeout, evs) \<sqsubseteq>\<^sub>t r'\<close>
  by (auto simp: tres_le_def)

lemma tres_le_Rval[simp]: \<open>(Rval v, evs) \<sqsubseteq>\<^sub>t r' \<longleftrightarrow> r' = (Rval v, evs)\<close>
  and tres_le_Rerr[simp]: \<open>(Rerr, evs) \<sqsubseteq>\<^sub>t r' \<longleftrightarrow> r' = (Rerr, evs)\<close>
  and tres_le_Rhost[simp]: \<open>(Rhost ev, evs) \<sqsubseteq>\<^sub>t r' \<longleftrightarrow> r' = (Rhost ev, evs)\<close>
  by (auto simp: tres_le_def)

text \<open>The order on evaluator results with their supply: a timeout is below
  everything, whatever supply it reports.\<close>

definition hres_le :: \<open>hres \<times> nat \<Rightarrow> hres \<times> nat \<Rightarrow> bool\<close>  (infix \<open>\<sqsubseteq>\<^sub>h\<close> 50) where
  \<open>p \<sqsubseteq>\<^sub>h p' \<longleftrightarrow> fst p = HRtimeout \<or> p' = p\<close>

lemma hres_le_refl[simp, intro!]: \<open>p \<sqsubseteq>\<^sub>h p\<close>
  by (simp add: hres_le_def)

lemma HRtimeout_le[simp, intro!]: \<open>(HRtimeout, ns) \<sqsubseteq>\<^sub>h p\<close>
  by (simp add: hres_le_def)

lemma HRval_le[simp]: \<open>(HRval v, ns) \<sqsubseteq>\<^sub>h p \<longleftrightarrow> p = (HRval v, ns)\<close>
  and HRerr_le[simp]: \<open>(HRerr, ns) \<sqsubseteq>\<^sub>h p \<longleftrightarrow> p = (HRerr, ns)\<close>
  and HRop_le[simp]: \<open>(HRop l m v fr, ns) \<sqsubseteq>\<^sub>h p \<longleftrightarrow> p = (HRop l m v fr, ns)\<close>
  and HRopn_le[simp]: \<open>(HRopn i op v fr, ns) \<sqsubseteq>\<^sub>h p \<longleftrightarrow> p = (HRopn i op v fr, ns)\<close>
  by (auto simp: hres_le_def)

lemma bindr_mono:
  assumes \<open>p \<sqsubseteq>\<^sub>h p'\<close>
    and \<open>\<And>v ns. p = (HRval v, ns) \<Longrightarrow> p' = (HRval v, ns) \<Longrightarrow> g v ns \<sqsubseteq>\<^sub>h g' v ns\<close>
  shows \<open>bindr p f g \<sqsubseteq>\<^sub>h bindr p' f g'\<close>
  using assms by (cases p) (auto simp: bindr_def hres_le_def split: hres.split)

lemma thenr_mono:
  assumes \<open>p \<sqsubseteq>\<^sub>h p'\<close>
    and \<open>\<And>r ns. p = (r, ns) \<Longrightarrow> p' = (r, ns) \<Longrightarrow> g r ns \<sqsubseteq>\<^sub>h g' r ns\<close>
    and \<open>\<And>ns. g HRtimeout ns = (HRtimeout, ns)\<close>
  shows \<open>thenr p g \<sqsubseteq>\<^sub>h thenr p' g'\<close>
  using assms by (cases p) (auto simp: thenr_def hres_le_def)

lemma guardr_mono:
  assumes \<open>p \<sqsubseteq>\<^sub>h p'\<close>
    and \<open>\<And>v ns. p = (HRval v, ns) \<Longrightarrow> p' = (HRval v, ns) \<Longrightarrow> g v ns \<sqsubseteq>\<^sub>h g' v ns\<close>
  shows \<open>guardr p g \<sqsubseteq>\<^sub>h guardr p' g'\<close>
  using assms by (cases p) (auto simp: guardr_def hres_le_def split: hres.split)

lemma cresume_timeout[simp]: \<open>cresume k HRtimeout fs ns = (HRtimeout, ns)\<close>
  by (cases k) simp_all

lemma ceval_le: \<open>k \<le> k' \<Longrightarrow> ceval k env e ns \<sqsubseteq>\<^sub>h ceval k' env e ns\<close>
  and cevcon_le: \<open>k \<le> k' \<Longrightarrow> cevcon k env c vs es ns \<sqsubseteq>\<^sub>h cevcon k' env c vs es ns\<close>
  and cevalm_le: \<open>k \<le> k' \<Longrightarrow> cevalm k env u cls ns \<sqsubseteq>\<^sub>h cevalm k' env u cls ns\<close>
  and capply_le: \<open>k \<le> k' \<Longrightarrow> capply k fv av ns \<sqsubseteq>\<^sub>h capply k' fv av ns\<close>
  and cstep_le: \<open>k \<le> k' \<Longrightarrow> cstep k u f ns \<sqsubseteq>\<^sub>h cstep k' u f ns\<close>
  and cunwind_le: \<open>k \<le> k' \<Longrightarrow> cunwind k u fs ns \<sqsubseteq>\<^sub>h cunwind k' u fs ns\<close>
  and cresume_le: \<open>k \<le> k' \<Longrightarrow> cresume k r fs ns \<sqsubseteq>\<^sub>h cresume k' r fs ns\<close>
  and cthrow_le: \<open>k \<le> k' \<Longrightarrow> cthrow k l m w fr fs ns \<sqsubseteq>\<^sub>h cthrow k' l m w fr fs ns\<close>
  and cthrown_le: \<open>k \<le> k' \<Longrightarrow> cthrown k i op w fr fs ns \<sqsubseteq>\<^sub>h cthrown k' i op w fr fs ns\<close>
  by (induction k env e ns and k env c vs es ns and k env u cls ns and k fv av ns
      and k u f ns and k u fs ns and k r fs ns and k l m w fr fs ns and k i op w fr fs ns
      arbitrary: k' and k' and k' and k' and k' and k' and k' and k' and k'
      rule: ceval_induct)
     (auto intro!: bindr_mono thenr_mono guardr_mono elim!: Suc_leE split: option.split)

text \<open>The trace only grows, and \<^const>\<open>crun\<close> is monotone in its fuel and in
  the evaluator's result it services:\<close>

lemma crun_grows: \<open>\<exists>es. snd (crun k ffi evs r) = evs @ es\<close>
  by (induction k ffi evs r rule: crun_induct)
     (fastforce split: option.split ffi_res.split)+

lemma crun_le:
  \<open>k \<le> k' \<Longrightarrow> p \<sqsubseteq>\<^sub>h p' \<Longrightarrow> crun k ffi evs p \<sqsubseteq>\<^sub>t crun k' ffi evs p'\<close>
proof (induction k ffi evs p arbitrary: k' p' rule: crun_induct)
  case (Suc k ffi evs l m w fr ns)
  then obtain k'' where k': \<open>k' = Suc k''\<close> and \<open>k \<le> k''\<close> and p': \<open>p' = (HRop l m w fr, ns)\<close>
    by (auto simp: hres_le_def elim: Suc_leE)
  have IH: \<open>crun k ffi (evs @ [FFIev sy w (FRet v)]) (cunwind k v fr ns) \<sqsubseteq>\<^sub>t
            crun k'' ffi (evs @ [FFIev sy w (FRet v)]) (cunwind k'' v fr ns)\<close>
    if \<open>ffi_sym l = Some sy\<close> \<open>ffi sy evs w = Some (FRet v)\<close> for sy v
    using Suc.IH[OF that refl \<open>k \<le> k''\<close> cunwind_le[OF \<open>k \<le> k''\<close>]] .
  show ?case
    by (auto simp: k' p' split: option.split ffi_res.split intro: IH)
qed (auto simp: hres_le_def intro: tres_le_timeout crun_grows[THEN exE])

lemma sbind_grows:
  assumes a: \<open>\<exists>es. snd a = evs @ es\<close> and f: \<open>\<And>v s. \<exists>es. snd (f v s) = s @ es\<close>
  shows \<open>\<exists>es. snd (sbind a f) = evs @ es\<close>
proof -
  obtain r es where \<open>a = (r, evs @ es)\<close> using a by (cases a) auto
  then show ?thesis using f[of _ \<open>evs @ es\<close>] by (cases r) (auto simp: sbind_def)
qed

lemma sbind_le:
  assumes le: \<open>a \<sqsubseteq>\<^sub>t a'\<close>
    and ff: \<open>\<And>v s. a = (Rval v, s) \<Longrightarrow> a' = (Rval v, s) \<Longrightarrow> f v s \<sqsubseteq>\<^sub>t f' v s\<close>
    and g: \<open>\<And>v s. \<exists>es. snd (f' v s) = s @ es\<close>
  shows \<open>sbind a f \<sqsubseteq>\<^sub>t sbind a' f'\<close>
  using le ff g[of _ \<open>snd a'\<close>]
  by (cases a; cases a') (fastforce simp: sbind_def tres_le_def split: cres.split)

lemma ceval_prog_grows: \<open>\<exists>es. snd (ceval_prog k ffi env ns evs p) = evs @ es\<close>
  by (induction p arbitrary: env ns evs) (auto intro!: sbind_grows crun_grows)

lemma ceval_prog_le:
  \<open>k \<le> k' \<Longrightarrow> ceval_prog k ffi env ns evs p \<sqsubseteq>\<^sub>t ceval_prog k' ffi env ns evs p\<close>
  by (induction p arbitrary: env ns evs)
     (auto intro!: sbind_le ceval_prog_grows crun_le[OF _ ceval_le])

lemma centry_le: \<open>k \<le> k' \<Longrightarrow> centry x ffi p k \<sqsubseteq>\<^sub>t centry x ffi p k'\<close>
  by (auto simp: mcentry_def intro!: sbind_le intro: ceval_prog_le split: prod.split)

end
