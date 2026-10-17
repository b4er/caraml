theory Basis
  imports Types
begin

section \<open>The static basis\<close>

text \<open>The static basis, environment-style after Standard ML's
  \<^cite>\<open>\<open>Sect. 5.1, Fig. 11\<close> in milner1997\<close> with structures \<^emph>\<open>being\<close> environments, and
  constructor by constructor the static twin of the elaborator's
  \<^text>\<open>sentry\<close>. Local pattern binders are \<^text>\<open>TEval\<close> entries consed
  on, as the elaborator does, so shadowing between values and modules is
  by position in one list.

  A type is either a stamped name with its arity (declared or abstract), or a
  transparent type function expanded at use. A semantic signature \<open>(T)E\<close> is
  Standard ML's \<open>\<Sigma>\<close>: an environment with the stamps of its
  abstract types bound. A functor is a closure over its static environment,
  its parameters' resolved signatures, its result signature and its body,
  typed at each application as the elaborator interprets it. Generativity
  comes from fresh stamps per application \<^cite>\<open>\<open>Sect. 5.7\<close> in milner1997\<close>.

  The lemmas are about \<open>bsubstl\<close>, the substitution into a type function's
  body (\<open>bsubstl_closed\<close>, \<open>tsubst_bsubstl_closed\<close>).\<close>

datatype tydef =
    TyAbs tyname nat               \<comment> \<open>stamped name, arity\<close>
  | TyFn \<open>tvar list\<close> kty           \<comment> \<open>transparent: parameters (bound in the body), body\<close>

datatype tentry =
    TEval scheme                        \<comment> \<open>a value\<close>
  | TEcon scheme nat                    \<comment> \<open>constructor: curried scheme, arity\<close>
  | TEtyp tydef                         \<comment> \<open>a type\<close>
  | TEstr \<open>(name \<times> tentry) list\<close>      \<comment> \<open>structure: its static environment\<close>
  | TEfun \<open>(name \<times> nat list \<times> (name \<times> tentry) list) list\<close> \<open>nat list \<times> (name \<times> tentry) list\<close>
      \<comment> \<open>functor signature: parameters \<open>(T)E\<close>, result \<open>(T')E'\<close>\<close>
  | TEsig \<open>nat list \<times> (name \<times> tentry) list\<close>
      \<comment> \<open>signature \<open>(T)E\<close>\<close>
  | TEfix fixity nat                    \<comment> \<open>fixity, under its \<^const>\<open>fix_key\<close>\<close>
  | TEinst \<open>(name \<times> tentry) list\<close>     \<comment> \<open>instance, or implicit parameter: joins resolution\<close>
  | TEop name \<open>tvar list\<close> kty kty
      \<comment> \<open>operation: flat label, the effect's type parameters (bound in the types),
        argument, result\<close>
  | TEffi name scheme                   \<comment> \<open>foreign value: symbol, declared type\<close>
  | TEeff name \<open>name list\<close> nat \<open>name ltlf option\<close>
      \<comment> \<open>effect: its label prefix, the names of its operations, its arity, its protocol
        over the operation names\<close>

type_synonym tenv = \<open>(name \<times> tentry) list\<close>
type_synonym sigsem = \<open>nat list \<times> tenv\<close>

fun tlookup :: \<open>tenv \<Rightarrow> name list \<Rightarrow> tentry option\<close> where
  \<open>tlookup env [] = None\<close>
| \<open>tlookup env [x] = map_of env x\<close>
| \<open>tlookup env (x # xs) =
     (case map_of env x of
        Some (TEstr ex) \<Rightarrow> tlookup ex xs
      | Some (TEinst ex) \<Rightarrow> tlookup ex xs
      | _ \<Rightarrow> None)\<close>

lemmas tlookup_induct = tlookup.induct[named_cases tlookup]

subsubsection \<open>Substitution, free variables, stamps of a basis\<close>

text \<open>Free variables are collected through every entry. Substitution acts on
  the value entries only: every other kind of entry is built by a
  declaration or a signature and mentions no unification variable, so
  leaving it untouched is the identity there, and the elaboration of
  signatures, the resolution of implicits and the lookup of constructors
  are then invariant under substitution outright. A scheme's bound
  variables are of their own sort and are never substituted.\<close>

fun sub_scheme :: \<open>(tvar \<Rightarrow> kty) \<Rightarrow> (rvar \<Rightarrow> krow) \<Rightarrow> scheme \<Rightarrow> scheme\<close> where
  \<open>sub_scheme \<theta> \<rho> (Sch t) = Sch (tsubst \<theta> \<rho> t)\<close>
| \<open>sub_scheme \<theta> \<rho> (Mono t) = Mono (tsubst \<theta> \<rho> t)\<close>

fun sub_ent :: \<open>(tvar \<Rightarrow> kty) \<Rightarrow> (rvar \<Rightarrow> krow) \<Rightarrow> tentry \<Rightarrow> tentry\<close> where
  \<open>sub_ent \<theta> \<rho> (TEval \<sigma>) = TEval (sub_scheme \<theta> \<rho> \<sigma>)\<close>
| \<open>sub_ent \<theta> \<rho> e = e\<close>

definition sub_env :: \<open>(tvar \<Rightarrow> kty) \<Rightarrow> (rvar \<Rightarrow> krow) \<Rightarrow> tenv \<Rightarrow> tenv\<close> where
  \<open>sub_env \<theta> \<rho> = map (apsnd (sub_ent \<theta> \<rho>))\<close>

fun ftv_tydef :: \<open>tydef \<Rightarrow> tvar set\<close> and frv_tydef :: \<open>tydef \<Rightarrow> rvar set\<close> where
  \<open>ftv_tydef (TyAbs c n) = {}\<close>
| \<open>ftv_tydef (TyFn ps t) = ftv t\<close>
| \<open>frv_tydef (TyAbs c n) = {}\<close>
| \<open>frv_tydef (TyFn ps t) = frv t\<close>

fun ftv_ent :: \<open>tentry \<Rightarrow> tvar set\<close> and ftv_env :: \<open>tenv \<Rightarrow> tvar set\<close> where
  \<open>ftv_ent (TEval \<sigma>) = ftv_sch \<sigma>\<close>
| \<open>ftv_ent (TEcon \<sigma> n) = ftv_sch \<sigma>\<close>
| \<open>ftv_ent (TEtyp d) = ftv_tydef d\<close>
| \<open>ftv_ent (TEstr ex) = ftv_env ex\<close>
| \<open>ftv_ent (TEfun ps (T, E)) = \<Union>(set (map (\<lambda>(x, T, E). ftv_env E) ps)) \<union> ftv_env E\<close>
| \<open>ftv_ent (TEsig (T, E)) = ftv_env E\<close>
| \<open>ftv_ent (TEfix f p) = {}\<close>
| \<open>ftv_ent (TEinst ex) = ftv_env ex\<close>
| \<open>ftv_ent (TEop l ps t\<^sub>1 t\<^sub>2) = ftv t\<^sub>1 \<union> ftv t\<^sub>2\<close>
| \<open>ftv_ent (TEffi s \<sigma>) = ftv_sch \<sigma>\<close>
| \<open>ftv_ent (TEeff l ls ar pr) = {}\<close>
| \<open>ftv_env [] = {}\<close>
| \<open>ftv_env ((x, e) # ex) = ftv_ent e \<union> ftv_env ex\<close>

fun frv_ent :: \<open>tentry \<Rightarrow> rvar set\<close> and frv_env :: \<open>tenv \<Rightarrow> rvar set\<close> where
  \<open>frv_ent (TEval \<sigma>) = frv_sch \<sigma>\<close>
| \<open>frv_ent (TEcon \<sigma> n) = frv_sch \<sigma>\<close>
| \<open>frv_ent (TEtyp d) = frv_tydef d\<close>
| \<open>frv_ent (TEstr ex) = frv_env ex\<close>
| \<open>frv_ent (TEfun ps (T, E)) = \<Union>(set (map (\<lambda>(x, T, E). frv_env E) ps)) \<union> frv_env E\<close>
| \<open>frv_ent (TEsig (T, E)) = frv_env E\<close>
| \<open>frv_ent (TEfix f p) = {}\<close>
| \<open>frv_ent (TEinst ex) = frv_env ex\<close>
| \<open>frv_ent (TEop l ps t\<^sub>1 t\<^sub>2) = frv t\<^sub>1 \<union> frv t\<^sub>2\<close>
| \<open>frv_ent (TEffi s \<sigma>) = frv_sch \<sigma>\<close>
| \<open>frv_ent (TEeff l ls ar pr) = {}\<close>
| \<open>frv_env [] = {}\<close>
| \<open>frv_env ((x, e) # ex) = frv_ent e \<union> frv_env ex\<close>

text \<open>The abstract types a basis mentions free, and their substitution at a
  module application; both structural, as substitution is.\<close>

fun ktv_sch :: \<open>scheme \<Rightarrow> tvar set\<close> where
  \<open>ktv_sch (Sch t) = ktv t\<close>
| \<open>ktv_sch (Mono t) = ktv t\<close>

fun ktv_tydef :: \<open>tydef \<Rightarrow> tvar set\<close> where
  \<open>ktv_tydef (TyAbs c n) = {}\<close>
| \<open>ktv_tydef (TyFn ps t) = ktv t\<close>

fun ktv_ent :: \<open>tentry \<Rightarrow> tvar set\<close> and ktv_env :: \<open>tenv \<Rightarrow> tvar set\<close> where
  \<open>ktv_ent (TEval \<sigma>) = ktv_sch \<sigma>\<close>
| \<open>ktv_ent (TEcon \<sigma> n) = ktv_sch \<sigma>\<close>
| \<open>ktv_ent (TEtyp d) = ktv_tydef d\<close>
| \<open>ktv_ent (TEstr ex) = ktv_env ex\<close>
| \<open>ktv_ent (TEfun ps (T, E)) = \<Union>(set (map (\<lambda>(x, T, E). ktv_env E) ps)) \<union> ktv_env E\<close>
| \<open>ktv_ent (TEsig (T, E)) = ktv_env E\<close>
| \<open>ktv_ent (TEfix f p) = {}\<close>
| \<open>ktv_ent (TEinst ex) = ktv_env ex\<close>
| \<open>ktv_ent (TEop l ps t\<^sub>1 t\<^sub>2) = ktv t\<^sub>1 \<union> ktv t\<^sub>2\<close>
| \<open>ktv_ent (TEffi s \<sigma>) = ktv_sch \<sigma>\<close>
| \<open>ktv_ent (TEeff l ls ar pr) = {}\<close>
| \<open>ktv_env [] = {}\<close>
| \<open>ktv_env ((x, e) # ex) = ktv_ent e \<union> ktv_env ex\<close>

fun ksch :: \<open>(tvar \<Rightarrow> kty) \<Rightarrow> scheme \<Rightarrow> scheme\<close> where
  \<open>ksch \<phi> (Sch t) = Sch (ksubst \<phi> t)\<close>
| \<open>ksch \<phi> (Mono t) = Mono (ksubst \<phi> t)\<close>

fun ktydef :: \<open>(tvar \<Rightarrow> kty) \<Rightarrow> tydef \<Rightarrow> tydef\<close> where
  \<open>ktydef \<phi> (TyAbs c n) = TyAbs c n\<close>
| \<open>ktydef \<phi> (TyFn ps t) = TyFn ps (ksubst \<phi> t)\<close>

fun kent :: \<open>(tvar \<Rightarrow> kty) \<Rightarrow> tentry \<Rightarrow> tentry\<close> and kenv :: \<open>(tvar \<Rightarrow> kty) \<Rightarrow> tenv \<Rightarrow> tenv\<close> where
  \<open>kent \<phi> (TEval \<sigma>) = TEval (ksch \<phi> \<sigma>)\<close>
| \<open>kent \<phi> (TEcon \<sigma> n) = TEcon (ksch \<phi> \<sigma>) n\<close>
| \<open>kent \<phi> (TEtyp d) = TEtyp (ktydef \<phi> d)\<close>
| \<open>kent \<phi> (TEstr ex) = TEstr (kenv \<phi> ex)\<close>
| \<open>kent \<phi> (TEfun ps (T, E)) = TEfun (map (\<lambda>(x, T, E). (x, T, kenv \<phi> E)) ps) (T, kenv \<phi> E)\<close>
| \<open>kent \<phi> (TEsig (T, E)) = TEsig (T, kenv \<phi> E)\<close>
| \<open>kent \<phi> (TEfix f p) = TEfix f p\<close>
| \<open>kent \<phi> (TEinst ex) = TEinst (kenv \<phi> ex)\<close>
| \<open>kent \<phi> (TEop l ps t\<^sub>1 t\<^sub>2) = TEop l ps (ksubst \<phi> t\<^sub>1) (ksubst \<phi> t\<^sub>2)\<close>
| \<open>kent \<phi> (TEffi s \<sigma>) = TEffi s (ksch \<phi> \<sigma>)\<close>
| \<open>kent \<phi> (TEeff l ls ar pr) = TEeff l ls ar pr\<close>
| \<open>kenv \<phi> [] = []\<close>
| \<open>kenv \<phi> ((x, e) # ex) = (x, kent \<phi> e) # kenv \<phi> ex\<close>

text \<open>Applying a type function to arguments that may mention a bound
  abstract type. A type of a signature is closed (\<open>kclose\<close>) before it is
  realised, so the argument of a type function may hold a \<open>TA\<close> that a binder
  \<^emph>\<open>around\<close> the application binds. If the function's body has a binder of its
  own above the parameter, the blind \<^const>\<open>bsubst\<close> would let that binder capture
  it: with \<open>type t a = (N : S) \<rightarrow> a\<close>, the type \<open>(M : S) \<rightarrow> M.u t\<close> would become
  \<open>(M : S) \<rightarrow> (N : S) \<rightarrow> N.u\<close>. So the arguments
  are shifted at each binder they pass; on \<^const>\<open>taclosed\<close> arguments this is
  \<^const>\<open>bsubst\<close> (\<open>bsubstl_closed\<close>).\<close>

abbreviation tlift :: \<open>kty \<Rightarrow> kty\<close> where
  \<open>tlift \<equiv> kclose_at 0 []\<close>

fun bsubstl :: \<open>(tvar \<Rightarrow> kty) \<Rightarrow> (rvar \<Rightarrow> krow) \<Rightarrow> kty \<Rightarrow> kty\<close> where
  \<open>bsubstl \<theta> \<rho> (TV a) = TV a\<close>
| \<open>bsubstl \<theta> \<rho> (TB a) = \<theta> a\<close>
| \<open>bsubstl \<theta> \<rho> (TK a) = TK a\<close>
| \<open>bsubstl \<theta> \<rho> (TA k i) = TA k i\<close>
| \<open>bsubstl \<theta> \<rho> (TC c ts) = TC c (map (bsubstl \<theta> \<rho>) ts)\<close>
| \<open>bsubstl \<theta> \<rho> (TApp t\<^sub>1 t\<^sub>2) = TApp (bsubstl \<theta> \<rho> t\<^sub>1) (bsubstl \<theta> \<rho> t\<^sub>2)\<close>
| \<open>bsubstl \<theta> \<rho> (TFn t\<^sub>1 e t\<^sub>2) = TFn (bsubstl \<theta> \<rho> t\<^sub>1) (brsubst \<rho> e) (bsubstl \<theta> \<rho> t\<^sub>2)\<close>
| \<open>bsubstl \<theta> \<rho> (TDep i sg K e t) = TDep i sg K (brsubst \<rho> e) (bsubstl (tlift \<circ> \<theta>) \<rho> t)\<close>
| \<open>bsubstl \<theta> \<rho> (TEv l s t) = TEv (bsubstl \<theta> \<rho> l) (bsubstl \<theta> \<rho> s) (bsubstl \<theta> \<rho> t)\<close>
| \<open>bsubstl \<theta> \<rho> (TAct l K e t) = TAct (bsubstl \<theta> \<rho> l) K (brsubst \<rho> e) (bsubstl \<theta> \<rho> t)\<close>

lemma bsubstl_cong:
  \<open>(\<And>a. a \<in> btv t \<Longrightarrow> \<theta> a = \<theta>' a) \<Longrightarrow> bsubstl \<theta> \<rho> t = bsubstl \<theta>' \<rho> t\<close>
proof (induction t arbitrary: \<theta> \<theta>')
  case (TC c ts)
  have \<open>bsubstl \<theta> \<rho> u = bsubstl \<theta>' \<rho> u\<close> if \<open>u \<in> set ts\<close> for u
    using TC.prems that by (intro TC.IH[OF that]) auto
  then show ?case by simp
next
  case (TDep i sg K e t)
  have \<open>bsubstl (tlift \<circ> \<theta>) \<rho> t = bsubstl (tlift \<circ> \<theta>') \<rho> t\<close>
    using TDep.prems by (intro TDep.IH) simp
  then show ?case by simp
next
  case (TApp t\<^sub>1 t\<^sub>2)
  show ?case using TApp.IH[of \<theta> \<theta>'] TApp.prems by simp
next
  case (TFn t\<^sub>1 e t\<^sub>2)
  show ?case using TFn.IH[of \<theta> \<theta>'] TFn.prems by simp
next
  case (TEv l s t)
  show ?case using TEv.IH[of \<theta> \<theta>'] TEv.prems by simp
next
  case (TAct l K e t)
  show ?case using TAct.IH[of \<theta> \<theta>'] TAct.prems by simp
qed simp_all

lemma bsubstl_closed: \<open>(\<And>a. a \<in> btv t \<Longrightarrow> taclosed (\<theta> a)) \<Longrightarrow> bsubstl \<theta> \<rho> t = bsubst \<theta> \<rho> t\<close>
proof (induction t arbitrary: \<theta>)
  case (TDep i sg K e t)
  have \<open>bsubstl (tlift \<circ> \<theta>) \<rho> t = bsubstl \<theta> \<rho> t\<close>
    using TDep.prems by (intro bsubstl_cong) (simp add: kclose_id)
  then show ?case using TDep by simp
qed (auto intro!: map_cong)

lemma bsubstl_id: \<open>btv t = {} \<Longrightarrow> brv t = {} \<Longrightarrow> bsubstl \<theta> \<rho> t = t\<close>
  by (induction t arbitrary: \<theta>) (auto simp: brsubst_id intro: map_idI)

text \<open>A substitution with \<^const>\<open>taclosed\<close> images goes into the arguments of a lifting
  substitution in a closed body: the shape of an operation's type at an effect's type
  arguments (\<open>op_inst\<close>).\<close>

lemma rsubst_brsubst_RB: \<open>frv_row e = {} \<Longrightarrow> rsubst \<rho> (brsubst RB e) = brsubst RB e\<close>
  by (induction e) auto

lemma tsubst_bsubstl_closed:
  assumes \<open>\<And>a. taclosed (\<theta> a)\<close>
  shows \<open>ftv t = {} \<Longrightarrow> frv t = {} \<Longrightarrow>
         tsubst \<theta> \<rho> (bsubstl \<beta> RB t) = bsubstl (\<lambda>a. tsubst \<theta> \<rho> (\<beta> a)) RB t\<close>
proof (induction t arbitrary: \<beta>)
  case (TC c ts)
  then show ?case by (auto cong: map_cong)
next
  case (TDep i sg K e t)
  have \<open>tsubst \<theta> \<rho> (bsubstl (tlift \<circ> \<beta>) RB t) = bsubstl (\<lambda>a. tsubst \<theta> \<rho> ((tlift \<circ> \<beta>) a)) RB t\<close>
    using TDep by simp
  then show ?case using TDep.prems by (simp add: comp_def tsubst_kclose assms rsubst_brsubst_RB)
qed (auto simp: rsubst_brsubst_RB)

lemma ftv_bsubstl: \<open>ftv (bsubstl \<theta> \<rho> t) = ftv t \<union> (\<Union>a\<in>btv t. ftv (\<theta> a))\<close>
  by (induction t arbitrary: \<theta>) auto

lemma ktv_bsubstl: \<open>ktv (bsubstl \<theta> \<rho> t) \<subseteq> ktv t \<union> (\<Union>a\<in>btv t. ktv (\<theta> a))\<close>
proof -
  have \<open>x \<in> ktv (bsubstl \<theta> \<rho> t) \<Longrightarrow> x \<in> ktv t \<or> (\<exists>a\<in>btv t. x \<in> ktv (\<theta> a))\<close> for x
  proof (induction t arbitrary: \<theta>)
    case (TDep i sg K e t) then show ?case using TDep.IH[of \<open>tlift \<circ> \<theta>\<close>] by (auto simp: comp_def)
  qed fastforce+
  then show ?thesis by blast
qed

lemma btv_bsubstl: \<open>btv (bsubstl \<theta> \<rho> t) = (\<Union>a\<in>btv t. btv (\<theta> a))\<close>
  by (induction t arbitrary: \<theta>) auto

lemma brv_bsubstl: \<open>brv (bsubstl \<theta> \<rho> t) = (\<Union>a\<in>btv t. brv (\<theta> a)) \<union> (\<Union>v\<in>brv t. brv_row (\<rho> v))\<close>
  by (induction t arbitrary: \<theta>) (auto simp: brv_brsubst)

lemma taok_tlift: \<open>taok d t \<Longrightarrow> d' \<le> d \<Longrightarrow> taok (Suc d) (kclose_at d' [] t)\<close>
  by (induction t arbitrary: d d') (auto simp: list_all_iff)

lemma taok_bsubstl: \<open>taok d t \<Longrightarrow> (\<And>a. a \<in> btv t \<Longrightarrow> taok d (\<theta> a)) \<Longrightarrow> taok d (bsubstl \<theta> \<rho> t)\<close>
proof (induction t arbitrary: d \<theta>)
  case (TC c ts)
  have \<open>taok d (bsubstl \<theta> \<rho> u)\<close> if \<open>u \<in> set ts\<close> for u
    using TC.prems that by (intro TC.IH[OF that]) (auto simp: list_all_iff)
  then show ?case by (simp add: list_all_iff)
next
  case (TDep i sg K e t)
  have \<open>taok (Suc d) (bsubstl (tlift \<circ> \<theta>) \<rho> t)\<close>
    using TDep.prems by (intro TDep.IH) (auto intro: taok_tlift)
  then show ?case by simp
qed auto

text \<open>Realisation of stamps \<^cite>\<open>\<open>Sect. 5.2\<close> in milner1997\<close>
  (\<^cite>\<open>\<open>Sect. 5.2\<close> in rossberg2014\<close>, \<open>lookup\<close>): a stamp of an abstract type is replaced by a type,
  in general a type function applied to the arguments at hand. Renaming a
  stamp to a fresh one is the special case \<^const>\<open>TyAbs\<close>.\<close>

type_synonym realisation = \<open>(nat \<times> tydef) list\<close>

fun treal :: \<open>realisation \<Rightarrow> kty \<Rightarrow> kty\<close> where
  \<open>treal \<phi> (TV a) = TV a\<close>
| \<open>treal \<phi> (TB a) = TB a\<close>
| \<open>treal \<phi> (TK a) = TK a\<close>
| \<open>treal \<phi> (TA k i) = TA k i\<close>
| \<open>treal \<phi> (TC c ts) =
     (case map_of \<phi> (stamp c) of
        None \<Rightarrow> TC c (map (treal \<phi>) ts)
      | Some (TyAbs c' n) \<Rightarrow> TC c' (map (treal \<phi>) ts)
      | Some (TyFn ps b) \<Rightarrow>
          bsubstl (\<lambda>a. case map_of (zip ps (map (treal \<phi>) ts)) a of Some t \<Rightarrow> t | None \<Rightarrow> unit_ty)
                 (\<lambda>_. RNil) b)\<close>
| \<open>treal \<phi> (TApp t\<^sub>1 t\<^sub>2) = TApp (treal \<phi> t\<^sub>1) (treal \<phi> t\<^sub>2)\<close>
| \<open>treal \<phi> (TFn t\<^sub>1 e t\<^sub>2) = TFn (treal \<phi> t\<^sub>1) e (treal \<phi> t\<^sub>2)\<close>
| \<open>treal \<phi> (TDep i sg T e t) = TDep i sg T e (treal \<phi> t)\<close>
| \<open>treal \<phi> (TEv l s t) = TEv (treal \<phi> l) (treal \<phi> s) (treal \<phi> t)\<close>
| \<open>treal \<phi> (TAct l K e t) = TAct (treal \<phi> l) K e (treal \<phi> t)\<close>

fun real_scheme :: \<open>realisation \<Rightarrow> scheme \<Rightarrow> scheme\<close> where
  \<open>real_scheme \<phi> (Sch t) = Sch (treal \<phi> t)\<close>
| \<open>real_scheme \<phi> (Mono t) = Mono (treal \<phi> t)\<close>

fun real_tydef :: \<open>realisation \<Rightarrow> tydef \<Rightarrow> tydef\<close> where
  \<open>real_tydef \<phi> (TyAbs c n) =
     (case map_of \<phi> (stamp c) of Some d \<Rightarrow> d | None \<Rightarrow> TyAbs c n)\<close>
| \<open>real_tydef \<phi> (TyFn ps t) = TyFn ps (treal \<phi> t)\<close>

text \<open>The stamp a realisation gives to a stamp: the abstract type it names, or the
  stamp itself. The bound stamps of a functor (its parameters' and its result's) are
  binders that a realisation renames along with the environments they scope over:
  an application's fresh stamps must reach the binder lists of a functor declared
  inside the body, or every application of that functor yields one type.\<close>

definition rstamp :: \<open>realisation \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>rstamp \<phi> k = (case map_of \<phi> k of Some (TyAbs c'' n) \<Rightarrow> stamp c'' | _ \<Rightarrow> k)\<close>

fun real_ent :: \<open>realisation \<Rightarrow> tentry \<Rightarrow> tentry\<close>
and real_env :: \<open>realisation \<Rightarrow> tenv \<Rightarrow> tenv\<close> where
  \<open>real_ent \<phi> (TEval \<sigma>) = TEval (real_scheme \<phi> \<sigma>)\<close>
| \<open>real_ent \<phi> (TEcon \<sigma> n) = TEcon (real_scheme \<phi> \<sigma>) n\<close>
| \<open>real_ent \<phi> (TEtyp d) = TEtyp (real_tydef \<phi> d)\<close>
| \<open>real_ent \<phi> (TEstr ex) = TEstr (real_env \<phi> ex)\<close>
| \<open>real_ent \<phi> (TEfun ps (T, E)) =
     TEfun (map (\<lambda>(x, T, E). (x, map (rstamp \<phi>) T, real_env \<phi> E)) ps)
       (map (rstamp \<phi>) T, real_env \<phi> E)\<close>
| \<open>real_ent \<phi> (TEsig (T, E)) = TEsig (T, real_env \<phi> E)\<close>
| \<open>real_ent \<phi> (TEfix f p) = TEfix f p\<close>
| \<open>real_ent \<phi> (TEinst ex) = TEinst (real_env \<phi> ex)\<close>
| \<open>real_ent \<phi> (TEop l ps t\<^sub>1 t\<^sub>2) = TEop l ps (treal \<phi> t\<^sub>1) (treal \<phi> t\<^sub>2)\<close>
| \<open>real_ent \<phi> (TEffi s \<sigma>) = TEffi s (real_scheme \<phi> \<sigma>)\<close>
| \<open>real_ent \<phi> (TEeff l ls ar pr) = TEeff l ls ar pr\<close>
| \<open>real_env \<phi> [] = []\<close>
| \<open>real_env \<phi> ((x, e) # ex) = (x, real_ent \<phi> e) # real_env \<phi> ex\<close>

lemmas real_ent_induct = real_ent_real_env.induct[named_cases real_ent]

text \<open>Renaming the bound stamps of a signature to fresh ones, positionally:
  the decorrelated copy a binder or a sealing takes \<^cite>\<open>\<open>Sect. 3.4\<close> in vivien2024\<close>
  \<^cite>\<open>\<open>Sect. 5.6\<close> in milner1997\<close>. The spellings, constructor lists and arities of the
  renamed names are kept: a sealed \<open>type t a\<close> stays applicable.\<close>

fun stamp_names :: \<open>tenv \<Rightarrow> (nat \<times> tyname) list\<close>
and stamp_names_ent :: \<open>tentry \<Rightarrow> (nat \<times> tyname) list\<close> where
  \<open>stamp_names [] = []\<close>
| \<open>stamp_names ((x, e) # ex) = stamp_names_ent e @ stamp_names ex\<close>
| \<open>stamp_names_ent (TEtyp (TyAbs c n)) = [(stamp c, c)]\<close>
| \<open>stamp_names_ent (TEstr ex) = stamp_names ex\<close>
| \<open>stamp_names_ent (TEinst ex) = stamp_names ex\<close>
| \<open>stamp_names_ent (TEfun ps (T, E)) = concat (map (\<lambda>(x, T, E). stamp_names E) ps) @ stamp_names E\<close>
| \<open>stamp_names_ent _ = []\<close>

fun stamp_arities :: \<open>tenv \<Rightarrow> (nat \<times> nat) list\<close>
and stamp_arities_ent :: \<open>tentry \<Rightarrow> (nat \<times> nat) list\<close> where
  \<open>stamp_arities [] = []\<close>
| \<open>stamp_arities ((x, e) # ex) = stamp_arities_ent e @ stamp_arities ex\<close>
| \<open>stamp_arities_ent (TEtyp (TyAbs c n)) = [(stamp c, n)]\<close>
| \<open>stamp_arities_ent (TEstr ex) = stamp_arities ex\<close>
| \<open>stamp_arities_ent (TEinst ex) = stamp_arities ex\<close>
| \<open>stamp_arities_ent (TEfun ps (T, E)) =
     concat (map (\<lambda>(x, T, E). stamp_arities E) ps) @ stamp_arities E\<close>
| \<open>stamp_arities_ent _ = []\<close>

definition stamp_arity :: \<open>tenv \<Rightarrow> nat \<Rightarrow> nat\<close> where
  \<open>stamp_arity E s = (case map_of (stamp_arities E) s of Some n \<Rightarrow> n | None \<Rightarrow> 0)\<close>

definition rename_stamps :: \<open>tenv \<Rightarrow> nat list \<Rightarrow> nat list \<Rightarrow> realisation\<close> where
  \<open>rename_stamps E T T' =
     map (\<lambda>(s, s'). (s, case map_of (stamp_names E) s of
                          Some (_, x, cs) \<Rightarrow> TyAbs (s', x, cs) (stamp_arity E s)
                        | None \<Rightarrow> TyAbs (s', [], []) (stamp_arity E s))) (zip T T')\<close>

text \<open>The stamps a basis mentions, for the well-formedness invariant that
  every stamp is below the counter \<^cite>\<open>\<open>Sect. 4.10\<close> in milner1997\<close>.\<close>

fun stamps :: \<open>kty \<Rightarrow> nat set\<close> where
  \<open>stamps (TV a) = {}\<close>
| \<open>stamps (TB a) = {}\<close>
| \<open>stamps (TK a) = {}\<close>
| \<open>stamps (TA k i) = {}\<close>
| \<open>stamps (TC c ts) = {stamp c} \<union> \<Union>(set (map stamps ts))\<close>
| \<open>stamps (TApp t\<^sub>1 t\<^sub>2) = stamps t\<^sub>1 \<union> stamps t\<^sub>2\<close>
| \<open>stamps (TFn t\<^sub>1 e t\<^sub>2) = stamps t\<^sub>1 \<union> stamps t\<^sub>2\<close>
| \<open>stamps (TDep i sg K e t) = stamps t\<close>
| \<open>stamps (TEv l s t) = stamps l \<union> stamps s \<union> stamps t\<close>
| \<open>stamps (TAct l K e t) = stamps l \<union> stamps t\<close>

fun stamps_sch :: \<open>scheme \<Rightarrow> nat set\<close> where
  \<open>stamps_sch (Sch t) = stamps t\<close>
| \<open>stamps_sch (Mono t) = stamps t\<close>

fun stamps_tydef :: \<open>tydef \<Rightarrow> nat set\<close> where
  \<open>stamps_tydef (TyAbs c k) = {stamp c}\<close>
| \<open>stamps_tydef (TyFn ps t) = stamps t\<close>

fun stamps_ent :: \<open>tentry \<Rightarrow> nat set\<close> and stamps_env :: \<open>tenv \<Rightarrow> nat set\<close> where
  \<open>stamps_ent (TEval \<sigma>) = stamps_sch \<sigma>\<close>
| \<open>stamps_ent (TEcon \<sigma> n) = stamps_sch \<sigma>\<close>
| \<open>stamps_ent (TEtyp d) = stamps_tydef d\<close>
| \<open>stamps_ent (TEstr ex) = stamps_env ex\<close>
| \<open>stamps_ent (TEfun ps (T, E)) =
     \<Union>(set (map (\<lambda>(x, T, E). set T \<union> stamps_env E) ps)) \<union> set T \<union> stamps_env E\<close>
| \<open>stamps_ent (TEsig (T, E)) = set T \<union> stamps_env E\<close>
| \<open>stamps_ent (TEfix f p) = {}\<close>
| \<open>stamps_ent (TEinst ex) = stamps_env ex\<close>
| \<open>stamps_ent (TEop l ps t\<^sub>1 t\<^sub>2) = stamps t\<^sub>1 \<union> stamps t\<^sub>2\<close>
| \<open>stamps_ent (TEffi s \<sigma>) = stamps_sch \<sigma>\<close>
| \<open>stamps_ent (TEeff l ls ar pr) = {}\<close>
| \<open>stamps_env [] = {}\<close>
| \<open>stamps_env ((x, e) # ex) = stamps_ent e \<union> stamps_env ex\<close>

text \<open>The type names a type mentions.\<close>

fun tn :: \<open>kty \<Rightarrow> tyname set\<close> where
  \<open>tn (TC c ts) = insert c (\<Union> (set (map tn ts)))\<close>
| \<open>tn (TApp t\<^sub>1 t\<^sub>2) = tn t\<^sub>1 \<union> tn t\<^sub>2\<close>
| \<open>tn (TFn t\<^sub>1 e t\<^sub>2) = tn t\<^sub>1 \<union> tn t\<^sub>2\<close>
| \<open>tn (TDep i sg K e t) = tn t\<close>
| \<open>tn (TEv l s t) = tn l \<union> tn s \<union> tn t\<close>
| \<open>tn (TAct l K e t) = tn l \<union> tn t\<close>
| \<open>tn _ = {}\<close>

fun tn_sch :: \<open>scheme \<Rightarrow> tyname set\<close> where
  \<open>tn_sch (Sch t) = tn t\<close>
| \<open>tn_sch (Mono t) = tn t\<close>

fun tn_tydef :: \<open>tydef \<Rightarrow> tyname set\<close> where
  \<open>tn_tydef (TyAbs c k) = {c}\<close>
| \<open>tn_tydef (TyFn ps t) = tn t\<close>

fun tn_ent :: \<open>tentry \<Rightarrow> tyname set\<close> and tn_env :: \<open>tenv \<Rightarrow> tyname set\<close> where
  \<open>tn_ent (TEval \<sigma>) = tn_sch \<sigma>\<close>
| \<open>tn_ent (TEcon \<sigma> n) = tn_sch \<sigma>\<close>
| \<open>tn_ent (TEtyp d) = tn_tydef d\<close>
| \<open>tn_ent (TEstr ex) = tn_env ex\<close>
| \<open>tn_ent (TEfun ps (T, E)) = \<Union> (set (map (\<lambda>(x, T, E). tn_env E) ps)) \<union> tn_env E\<close>
| \<open>tn_ent (TEsig (T, E)) = tn_env E\<close>
| \<open>tn_ent (TEfix f p) = {}\<close>
| \<open>tn_ent (TEinst ex) = tn_env ex\<close>
| \<open>tn_ent (TEop l ps t\<^sub>1 t\<^sub>2) = tn t\<^sub>1 \<union> tn t\<^sub>2\<close>
| \<open>tn_ent (TEffi s \<sigma>) = tn_sch \<sigma>\<close>
| \<open>tn_ent (TEeff l ls ar pr) = {}\<close>
| \<open>tn_env [] = {}\<close>
| \<open>tn_env ((x, e) # E) = tn_ent e \<union> tn_env E\<close>

end
