theory Typing
  imports Unify Desugar
begin

section \<open>Surface typing\<close>

text \<open>The type system runs on the surface AST, before the module language
  is compiled away: Hindley--Milner with Koka-style effect rows
  \<^cite>\<open>\<open>Sect. 3.1, Fig. 3\<close> in leijen2017\<close> over the term language, the static
  semantics of modules in the environment style of the Standard ML
  \<^cite>\<open>\<open>Sect. 5\<close> in milner1997\<close> over the module language, and type-directed
  resolution of implicit module arguments \<^cite>\<open>\<open>Sect. 2.2--2.3\<close> in white2014\<close>.

  Its output is the surface again, made \<^emph>\<open>explicit\<close>: every implicit
  argument is inserted, every module argument is annotated as \<^const>\<open>AMod\<close> with
  the callee's parameter signature. Function declarations are lowered to their
  recursive value bindings.

  This theory is the declarative side: the judgements are the
  specification against which \<^text>\<open>Infer\<close> is proven sound.\<close>

fun path_nms :: \<open>mpath \<Rightarrow> name list\<close> where
  \<open>path_nms (MkPath xs) = map n_txt xs\<close>

definition mk_nm :: \<open>name \<Rightarrow> nm\<close> where
  \<open>mk_nm x = \<lparr>l_line = 0, l_col = 0, l_off = 0, l_len = 0, n_txt = x\<rparr>\<close>

text \<open>A fixity's precedence keeps its spelling; it reads as a decimal natural.\<close>

definition read_nat :: \<open>name \<Rightarrow> nat option\<close> where
  \<open>read_nat s =
     (if s \<noteq> [] \<and> (\<forall>c \<in> set s. c \<in> set (str ''0123456789''))
      then Some (foldl (\<lambda>n c. 10 * n + (c - 48)) 0 s) else None)\<close>

subsection \<open>Schemes, type functions, enrichment\<close>

text \<open>A scheme is at least as general as another if every instance of the
  latter is an instance of the former \<^cite>\<open>\<open>Sect. 4.5\<close> in milner1997\<close>.\<close>

fun sch_bnd :: \<open>scheme \<Rightarrow> nat\<close> where
  \<open>sch_bnd (Sch t) = kty_bnd t\<close>
| \<open>sch_bnd (Mono t) = kty_bnd t\<close>

text \<open>Skolemising the bound variables of the less general scheme by fresh
  abstract types and closed-row variables, which the matcher holds
  rigid.\<close>

definition skolem :: \<open>nat \<Rightarrow> kty \<Rightarrow> kty\<close> where
  \<open>skolem m t = bsubst (\<lambda>a. TK (m + a)) (\<lambda>v. RV (m + v)) t\<close>

definition sch_ge :: \<open>scheme \<Rightarrow> scheme \<Rightarrow> bool\<close>  (infix \<open>\<sqsupseteq>\<close> 50) where
  \<open>\<sigma>' \<sqsupseteq> \<sigma> = imatch \<sigma>' (skolem (max (sch_bnd \<sigma>') (sch_bnd \<sigma>)) (sch_body \<sigma>))\<close>

fun tydef_arity :: \<open>tydef \<Rightarrow> nat\<close> where
  \<open>tydef_arity (TyAbs c k) = k\<close>
| \<open>tydef_arity (TyFn ps b) = length ps\<close>

text \<open>Applying a type function replaces every bound variable of its body:
  the parameters by the arguments, and any other, which a well-formed body
  has none of, by the unit type.\<close>

fun tydef_app :: \<open>tydef \<Rightarrow> kty list \<Rightarrow> kty\<close> where
  \<open>tydef_app (TyAbs c k) ts = TC c ts\<close>
| \<open>tydef_app (TyFn ps b) ts =
     bsubst (\<lambda>a. case map_of (zip ps ts) a of Some t \<Rightarrow> t | None \<Rightarrow> unit_ty) (\<lambda>_. RNil) b\<close>

fun tydef_bnd :: \<open>tydef \<Rightarrow> nat\<close> where
  \<open>tydef_bnd (TyAbs c k) = 0\<close>
| \<open>tydef_bnd (TyFn ps b) = max (kty_bnd b) (Suc (Max (insert 0 (set ps))))\<close>

text \<open>Two type functions are equal if they agree on fresh rigid
  arguments.\<close>

definition tydef_eq :: \<open>tydef \<Rightarrow> tydef \<Rightarrow> bool\<close> where
  \<open>tydef_eq d d' \<longleftrightarrow>
     tydef_arity d = tydef_arity d' \<and>
     (let m = max (tydef_bnd d) (tydef_bnd d'); args = map TK [m ..< m + tydef_arity d]
      in tydef_app d args \<simeq> tydef_app d' args)\<close>

text \<open>A type substitution given as a list, and the pointwise comparison of
  two such on a set of variables.\<close>

definition tsl :: \<open>(tvar \<times> kty) list \<Rightarrow> tvar \<Rightarrow> kty\<close> where
  \<open>tsl \<phi> a = (case map_of \<phi> a of Some t \<Rightarrow> t | None \<Rightarrow> TK a)\<close>

text \<open>\<^const>\<open>tsl\<close> is the substitution of \<^emph>\<open>free\<close> stamps: a stamp the list
  does not mention stays the free \<open>TK k\<close>. \<open>tsp K \<phi>\<close> is its positional view,
  which opens a binder that closed the stamps \<open>K\<close>: the \<open>i\<close>th abstract type
  of the binder is realised at what \<open>\<phi>\<close> gives its stamp \<open>K ! i\<close>.\<close>

definition tsp :: \<open>tvar list \<Rightarrow> (tvar \<times> kty) list \<Rightarrow> nat \<Rightarrow> kty\<close> where
  \<open>tsp K \<phi> i = (if i < length K then tsl \<phi> (K ! i) else unit_ty)\<close>

text \<open>A realisation read off the type members of a structure is closed
  (\<open>match_dep_closed\<close> for an explicit argument, \<open>tsl_closed_of_fits\<close> for a
  resolved implicit one).\<close>

abbreviation cl_real :: \<open>tvar list \<Rightarrow> (tvar \<times> kty) list \<Rightarrow> bool\<close> where
  \<open>cl_real K \<phi> \<equiv> \<forall>k \<in> set K. ftv (tsl \<phi> k) = {} \<and> frv (tsl \<phi> k) = {}\<close>

definition tsl_eq :: \<open>tvar list \<Rightarrow> (tvar \<times> kty) list \<Rightarrow> (tvar \<times> kty) list \<Rightarrow> bool\<close> where
  \<open>tsl_eq K \<phi> \<phi>' \<longleftrightarrow> list_all (\<lambda>k. tsl \<phi> k \<simeq> tsl \<phi>' k) K\<close>

subsection \<open>Static signatures: matching, enrichment, sealing\<close>

text \<open>Signature matching is Standard ML's \<^cite>\<open>\<open>Sect. 5.6\<close> in milner1997\<close>
  \<^cite>\<open>\<open>Sect. 5.2\<close> in rossberg2014\<close>: first a realisation of the signature's bound
  stamps is read off the structure's type members, then the structure must
  enrich the realised signature, every spec present with a more general
  scheme. Sealing returns the realised signature with fresh stamps for
  its abstract types, taking the structure's operation labels and
  fixities, which the signature does not fix. \<open>match_sig\<close> and \<open>enrich\<close>
  walk the signature's environment as the elaborator's \<open>seal\<close> walks its
  spec list. A datatype spec names its constructors: the structure's type must
  be a datatype with that spelling and constructor list (\<open>cons_match\<close>).\<close>

fun cons_match :: \<open>tyname \<Rightarrow> tydef \<Rightarrow> bool\<close> where
  \<open>cons_match c (TyAbs c' n) = (snd (snd c) = [] \<or> snd c' = snd c)\<close>
| \<open>cons_match c (TyFn ps b) = (snd (snd c) = [])\<close>

fun match_sig :: \<open>tenv \<Rightarrow> nat list \<Rightarrow> tenv \<Rightarrow> realisation option\<close> where
  \<open>match_sig E T [] = Some []\<close>
| \<open>match_sig E T ((t, TEtyp (TyAbs c k)) # r) =
     (if stamp c \<in> set T
      then (case map_of E t of
              Some (TEtyp d) \<Rightarrow>
                (if tydef_arity d = k \<and> cons_match c d
                 then match_sig E T r \<bind> (\<lambda>\<phi>. Some ((stamp c, d) # \<phi>)) else None)
            | _ \<Rightarrow> None)
      else match_sig E T r)\<close>
| \<open>match_sig E T ((x, TEstr E\<^sub>1) # r) =
     (case map_of E x of
        Some (TEstr E\<^sub>2) \<Rightarrow>
          match_sig E\<^sub>2 T E\<^sub>1 \<bind> (\<lambda>\<phi>\<^sub>1. match_sig E T r \<bind> (\<lambda>\<phi>\<^sub>2. Some (\<phi>\<^sub>1 @ \<phi>\<^sub>2)))
      | _ \<Rightarrow> None)\<close>
| \<open>match_sig E T (_ # r) = match_sig E T r\<close>

lemmas match_sig_induct = match_sig.induct[named_cases match_sig]

fun enrich :: \<open>tenv \<Rightarrow> tenv \<Rightarrow> bool\<close> where
  \<open>enrich E [] = True\<close>
| \<open>enrich E ((x, TEval \<sigma>) # r) =
     ((case map_of E x of
         Some (TEval \<sigma>') \<Rightarrow> \<sigma>' \<sqsupseteq> \<sigma>
       | Some (TEcon \<sigma>' n) \<Rightarrow> \<sigma>' \<sqsupseteq> \<sigma>
       | Some (TEffi s \<sigma>') \<Rightarrow> \<sigma>' \<sqsupseteq> \<sigma>
       | _ \<Rightarrow> False) \<and> enrich E r)\<close>
| \<open>enrich E ((x, TEcon \<sigma> n) # r) =
     ((case map_of E x of Some (TEcon \<sigma>' n') \<Rightarrow> n = n' \<and> \<sigma>' \<sqsupseteq> \<sigma> | _ \<Rightarrow> False) \<and> enrich E r)\<close>
| \<open>enrich E ((x, TEtyp d) # r) =
     ((case map_of E x of Some (TEtyp d') \<Rightarrow> tydef_eq d' d | _ \<Rightarrow> False) \<and> enrich E r)\<close>
| \<open>enrich E ((x, TEop l ps t\<^sub>1 t\<^sub>2) # r) =
     ((case map_of E x of
         Some (TEop l' ps' t\<^sub>1' t\<^sub>2') \<Rightarrow> ps' = ps \<and> t\<^sub>1' \<simeq> t\<^sub>1 \<and> t\<^sub>2' \<simeq> t\<^sub>2
       | _ \<Rightarrow> False) \<and>
      enrich E r)\<close>
| \<open>enrich E ((x, TEfix f p) # r) =
     ((case map_of E x of Some (TEfix f' p') \<Rightarrow> f' = f \<and> p' = p | _ \<Rightarrow> False) \<and> enrich E r)\<close>
| \<open>enrich E ((x, TEeff l ls ar) # r) =
     ((case map_of E x of
         Some (TEeff l' ls' ar') \<Rightarrow> ar' = ar
       | _ \<Rightarrow> False) \<and> enrich E r)\<close>
| \<open>enrich E ((x, TEstr E\<^sub>1) # r) =
     ((case map_of E x of Some (TEstr E\<^sub>2) \<Rightarrow> enrich E\<^sub>2 E\<^sub>1 | _ \<Rightarrow> False) \<and> enrich E r)\<close>
| \<open>enrich E (_ # r) = False\<close>

text \<open>The sealed environment: the signature's entries, with the structure's
  labels and fixities.\<close>

fun seal_env :: \<open>tenv \<Rightarrow> tenv \<Rightarrow> tenv\<close> where
  \<open>seal_env E [] = []\<close>
| \<open>seal_env E ((x, TEval \<sigma>) # r) =
     (x, case map_of E x of Some (TEffi s _) \<Rightarrow> TEffi s \<sigma> | _ \<Rightarrow> TEval \<sigma>) # seal_env E r\<close>
| \<open>seal_env E ((x, TEop l ps t\<^sub>1 t\<^sub>2) # r) =
     (x, TEop (case map_of E x of Some (TEop l' _ _ _) \<Rightarrow> l' | _ \<Rightarrow> l) ps t\<^sub>1 t\<^sub>2) # seal_env E r\<close>
| \<open>seal_env E ((x, TEeff l ls ar) # r) =
     (x, case map_of E x of Some (TEeff l' ls' _) \<Rightarrow> TEeff l' ls' ar | _ \<Rightarrow> TEeff l ls ar)
     # seal_env E r\<close>
| \<open>seal_env E ((x, TEfix f p) # r) =
     (x, case map_of E x of Some (TEfix f' p') \<Rightarrow> TEfix f' p' | _ \<Rightarrow> TEfix f p) # seal_env E r\<close>
| \<open>seal_env E ((x, TEstr E\<^sub>1) # r) =
     (x, TEstr (case map_of E x of Some (TEstr E\<^sub>2) \<Rightarrow> seal_env E\<^sub>2 E\<^sub>1 | _ \<Rightarrow> E\<^sub>1)) # seal_env E r\<close>
| \<open>seal_env E (e # r) = e # seal_env E r\<close>

text \<open>A module parameter exports its values and structures to the body,
  constructors demoted to values; neither operations nor fixities travel
  in a dictionary (the elaborator's \<open>param_env\<close>).\<close>

fun param_env :: \<open>tenv \<Rightarrow> tenv\<close> where
  \<open>param_env [] = []\<close>
| \<open>param_env ((x, TEcon \<sigma> n) # r) = (x, TEval \<sigma>) # param_env r\<close>
| \<open>param_env ((x, TEstr E\<^sub>1) # r) = (x, TEstr (param_env E\<^sub>1)) # param_env r\<close>
| \<open>param_env ((x, TEop l ps t\<^sub>1 t\<^sub>2) # r) = param_env r\<close>
| \<open>param_env ((x, TEeff l ls ar) # r) = param_env r\<close>
| \<open>param_env ((x, TEfix f p) # r) = param_env r\<close>
| \<open>param_env (e # r) = e # param_env r\<close>

text \<open>An operation's types are a scheme over the effect's parameters, bound
  as \<^const>\<open>TB\<close> variables \<open>0, \<dots>, n - 1\<close>; a use on a name instantiates them
  with the name's arguments, lifted under the binders of the operation's type
  (\<^const>\<open>bsubstl\<close>, as a realisation applies a type function).\<close>

definition op_inst :: \<open>tvar list \<Rightarrow> kty list \<Rightarrow> kty \<Rightarrow> kty\<close> where
  \<open>op_inst ps args \<tau> = bsubstl (\<lambda>a. case map_of (zip ps args) a of Some t \<Rightarrow> t | None \<Rightarrow> TB a) RB \<tau>\<close>

subsection \<open>Surface types and signatures to the static basis\<close>

text \<open>Elaboration of surface types, with an environment of the type and
  row variables in scope, by spelling. Whether an unknown variable may be
  allocated fresh is a flag: a declaration's annotation introduces its
  variables (explicit type variables, \<^cite>\<open>\<open>Sect. 4.6\<close> in milner1997\<close>), a
  datatype's constructors may only use the declared parameters. An arrow
  written without a row is effect-polymorphic: its row is a fresh
  variable, generalised with the annotation. \<open>TWild\<close> is a fresh variable.

  A signature elaborates to a semantic signature \<open>(T)E\<close>
  \<^cite>\<open>\<open>Sect. 5.1\<close> in milner1997\<close>: a bodyless type spec allocates a bound stamp, a variant
  spec allocates one and binds its constructors, refinements
  \<open>[t = \<tau>]\<close> and \<open>[M = P]\<close> realise bound stamps
  \<^cite>\<open>\<open>Sect. 5.2\<close> in rossberg2014\<close>. A structure spec by a named signature shares that
  signature's bound stamps, so two such specs share their abstract types;
  the bound stamps are listed once. Earlier specs are in scope for later ones. Every
  allocation draws on one counter, shared with the inference algorithm's
  type and row variables.

  A module-dependent arrow in a type, \<open>(S : sg) \<rightarrow> \<tau>\<close>, binds fresh
  stamps for the signature's abstract types and types \<open>\<tau>\<close> with the
  parameter in scope; \<^const>\<open>TDep\<close> records those stamps, so two arrows
  written separately are distinct types \<^cite>\<open>\<open>Sect. 3.2\<close> in vivien2024\<close>.\<close>

text \<open>A term-level module parameter's abstract types are instantiated by
  substitution, so they must be nullary; a functor parameter or a sealing
  keeps stamps of any arity.\<close>

fun abs_ok :: \<open>nat list \<Rightarrow> tenv \<Rightarrow> bool\<close> where
  \<open>abs_ok T [] = True\<close>
| \<open>abs_ok T ((t, TEtyp (TyAbs c k)) # r) = ((stamp c \<in> set T \<longrightarrow> k = 0) \<and> abs_ok T r)\<close>
| \<open>abs_ok T ((x, TEstr E\<^sub>1) # r) = (abs_ok T E\<^sub>1 \<and> abs_ok T r)\<close>
| \<open>abs_ok T (_ # r) = abs_ok T r\<close>

text \<open>An abstract stamp is present in an environment when some type member
  realises it, at any structure nesting \<^cite>\<open>\<open>Sect. 5.6\<close> in milner1997\<close>.\<close>

fun abs_present_ent :: \<open>nat \<Rightarrow> tentry \<Rightarrow> bool\<close> and
  abs_present :: \<open>nat \<Rightarrow> tenv \<Rightarrow> bool\<close>
where
  \<open>abs_present_ent t (TEtyp (TyAbs c k)) = (stamp c = t)\<close>
| \<open>abs_present_ent t (TEstr E) = abs_present t E\<close>
| \<open>abs_present_ent t e = False\<close>
| \<open>abs_present t [] = False\<close>
| \<open>abs_present t ((x, e) # r) = (abs_present_ent t e \<or> abs_present t r)\<close>

definition dep_vars :: \<open>nat list \<Rightarrow> tvar list \<Rightarrow> realisation\<close> where
  \<open>dep_vars T K = map (\<lambda>(t, k). (t, TyFn [] (TK k))) (zip T K)\<close>

type_synonym tvenv = \<open>(name \<times> kty) list \<times> (name \<times> krow) list\<close>

text \<open>A binder is a lexical identifier: it is not empty, and it contains
  neither the path separator \<open>.\<close> (\<^const>\<open>mangle\<close>), nor \<open>%\<close>, with which the
  elaborator's own binders start, nor \<open>(\<close>, with which a tuple's constructor tag
  starts (\<^const>\<open>tuple_con\<close>). The rules that bind a name demand it.\<close>

definition nm_ok :: \<open>name \<Rightarrow> bool\<close> where
  \<open>nm_ok x \<longleftrightarrow> x \<noteq> [] \<and> 0x2E \<notin> set x \<and> 0x25 \<notin> set x \<and> 0x28 \<notin> set x\<close>

text \<open>A row entry names an effect, whose operations it lists, or a name bound by a
  name-dependent arrow, whose operations it lists under the name prefix. While its
  type is elaborated, the bound name lives in the type environment under a reserved
  key, as a fixity does, as the effect of its named operations.\<close>

definition nkey :: \<open>name \<Rightarrow> name\<close> where
  \<open>nkey x = str ''%name.'' @ x\<close>

definition name_at :: \<open>tenv \<Rightarrow> mpath \<Rightarrow> (name \<times> name list) option\<close> where
  \<open>name_at B p =
     (case path_nms p of
        [x] \<Rightarrow> (case map_of B (nkey x) of Some (TEeff l ls ar) \<Rightarrow> Some (l, ls) | _ \<Rightarrow> None)
      | _ \<Rightarrow> None)\<close>

text \<open>The effect a name's type is for, when it is declared; and the entry a binder
  of a name whose effect is declared adds, so that annotations under it may name it.\<close>

definition eff_of_ty :: \<open>tenv \<Rightarrow> kty \<Rightarrow> (name \<times> name list \<times> nat) option\<close> where
  \<open>eff_of_ty B t =
     (case t of
        TC c ts \<Rightarrow> find (\<lambda>(l, ls, ar). eff_ty l ts = t \<and> ar = length ts) (effs B)
      | _ \<Rightarrow> None)\<close>

definition name_env :: \<open>tenv \<Rightarrow> name \<Rightarrow> kty \<Rightarrow> tenv\<close> where
  \<open>name_env B x t =
     (case eff_of_ty B t of Some (l, ls, ar) \<Rightarrow> [(nkey x, TEeff l ls ar)] | None \<Rightarrow> [])\<close>

lemma name_env_cases:
  obtains (none) \<open>name_env B x t = []\<close>
    | (eff) l ls ar where \<open>name_env B x t = [(nkey x, TEeff l ls ar)]\<close>
  by (cases \<open>eff_of_ty B t\<close>) (auto simp: name_env_def)

fun label_stat :: \<open>tenv \<Rightarrow> ty \<Rightarrow> name list option\<close> where
  \<open>label_stat B (TSpine [TPath p]) =
     (case name_at B p of
        Some (l, ls) \<Rightarrow> Some (map (nlbl \<circ> mangle l) ls)
      | None \<Rightarrow>
          (case tlookup B (path_nms p) of
             Some (TEeff l ls ar) \<Rightarrow> Some (map (mangle l) ls)
           | _ \<Rightarrow> None))\<close>
| \<open>label_stat B _ = None\<close>

lemmas label_stat_cases = label_stat.cases[named_cases label_stat]

fun labels_stat :: \<open>tenv \<Rightarrow> ty list \<Rightarrow> name list option\<close> where
  \<open>labels_stat B [] = Some []\<close>
| \<open>labels_stat B (t # ts) =
     label_stat B t \<bind> (\<lambda>ls. labels_stat B ts \<bind> (\<lambda>ls'. Some (ls @ ls')))\<close>

text \<open>The head of a type spine: a type in scope, or a type variable.\<close>

fun head_stat :: \<open>tenv \<Rightarrow> bool \<Rightarrow> tvenv \<Rightarrow> nat \<Rightarrow> mpath \<Rightarrow> kty list
                   \<Rightarrow> (kty \<times> tvenv \<times> nat) option\<close> where
  \<open>head_stat B fr (tvs, rvs) n p args =
     (case tlookup B (path_nms p) of
        Some (TEtyp d) \<Rightarrow>
          (if tydef_arity d = length args then Some (tydef_app d args, (tvs, rvs), n) else None)
      | Some _ \<Rightarrow> None
      | None \<Rightarrow>
          (case path_nms p of
             [a] \<Rightarrow>
               (case map_of tvs a of
                  Some t \<Rightarrow> Some (foldl tapp t args, (tvs, rvs), n)
                | None \<Rightarrow>
                    (if fr then Some (foldl tapp (TV n) args, ((a, TV n) # tvs, rvs), Suc n)
                     else None))
           | _ \<Rightarrow> None))\<close>

text \<open>The effect a path names, at a given arity: its label prefix and its operations.\<close>

definition eff_at :: \<open>tenv \<Rightarrow> mpath \<Rightarrow> nat \<Rightarrow> (name \<times> name list) option\<close> where
  \<open>eff_at B p ar =
     (case tlookup B (path_nms p) of
        Some (TEeff l ls ar') \<Rightarrow> (if ar' = ar then Some (l, ls) else None)
      | _ \<Rightarrow> None)\<close>

text \<open>A row extended by a list of labels.\<close>

definition rext :: \<open>name list \<Rightarrow> krow \<Rightarrow> krow\<close> where
  \<open>rext ls \<epsilon> = foldr RCons ls \<epsilon>\<close>

text \<open>A name type \<open>[E as]\<close> is the type of a handler name for the effect \<open>E\<close> at the
  arguments \<open>as\<close>. Its scope is a fresh variable, which the handler installing the
  name fixes (rule \<open>W_with\<close>); only an open annotation can mint it, so a closed one
  has no name types. A datatype cannot store a name either: a stored name would
  need its scope as a parameter of the datatype, and a name type has no syntax
  for its scope.

  A handler type \<open>handler [E as] a \<rightarrow> [\<rho>] b\<close> is the type rule \<open>W_handlern\<close> gives a
  named handler: a function with latent row \<open>\<rho>\<close> from an action for \<open>E\<close> to \<open>b\<close>, where
  the action returns \<open>a\<close> and performs \<open>E\<close>'s operations on its name on top of \<open>\<rho>\<close>. The
  scope the action binds is fresh.
  A name-dependent arrow \<open>(f : [E as]) \<rightarrow> [\<rho>] \<tau>\<close> is that action type itself: it returns
  \<open>\<tau>\<close> and performs \<open>E\<close>'s operations on \<open>f\<close> on top of \<open>\<rho>\<close>. An absent row is read as for a
  plain arrow. The bound name \<open>f\<close> is in scope in \<open>\<rho>\<close> and \<open>\<tau>\<close> as a row entry
  (\<^const>\<open>name_at\<close>), for the types inside \<open>\<tau>\<close> that perform on \<open>f\<close> (the arrow's own
  row carries \<open>f\<close>'s operations already, so naming \<open>f\<close> there lists them twice). A name
  bound by \<open>with\<close> is in scope in its body the same way when its handler's effect is
  known at the binding (\<^const>\<open>name_env\<close>, rule \<open>W_with\<close>). A handler type binds no
  name.\<close>

function (sequential) ty_stat :: \<open>tenv \<Rightarrow> bool \<Rightarrow> tvenv \<Rightarrow> nat \<Rightarrow> ty \<Rightarrow> (kty \<times> tvenv \<times> nat) option\<close> and
  atoms_stat :: \<open>tenv \<Rightarrow> bool \<Rightarrow> tvenv \<Rightarrow> nat \<Rightarrow> tatom list \<Rightarrow> (kty list \<times> tvenv \<times> nat) option\<close> and
  atom_stat :: \<open>tenv \<Rightarrow> bool \<Rightarrow> tvenv \<Rightarrow> nat \<Rightarrow> tatom \<Rightarrow> (kty \<times> tvenv \<times> nat) option\<close> and
  tys_stat :: \<open>tenv \<Rightarrow> bool \<Rightarrow> tvenv \<Rightarrow> nat \<Rightarrow> ty list \<Rightarrow> (kty list \<times> tvenv \<times> nat) option\<close> and
  spine_stat :: \<open>tenv \<Rightarrow> bool \<Rightarrow> tvenv \<Rightarrow> nat \<Rightarrow> tatom list \<Rightarrow> (kty \<times> tvenv \<times> nat) option\<close> and
  row_stat :: \<open>tenv \<Rightarrow> bool \<Rightarrow> tvenv \<Rightarrow> nat \<Rightarrow> ty option \<Rightarrow> (krow \<times> tvenv \<times> nat) option\<close>
where
  \<open>ty_stat B fr ve n (TSpine as) = spine_stat B fr ve n as\<close>
| \<open>ty_stat B fr ve n (TArrow as ro t) =
     spine_stat B fr ve n as \<bind> (\<lambda>(t\<^sub>1, ve\<^sub>1, n\<^sub>1).
       row_stat B fr ve\<^sub>1 n\<^sub>1 ro \<bind> (\<lambda>(e, ve\<^sub>2, n\<^sub>2).
         ty_stat B fr ve\<^sub>2 n\<^sub>2 t \<bind> (\<lambda>(t\<^sub>2, ve\<^sub>3, n\<^sub>3). Some (TFn t\<^sub>1 e t\<^sub>2, ve\<^sub>3, n\<^sub>3))))\<close>
| \<open>ty_stat B fr ve n (TArrowMod b t) =
     (case mbind_sig b of
        SPath p [] \<Rightarrow>
          (case tlookup B (path_nms p) of
             Some (TEsig (T, E)) \<Rightarrow>
               (let K = [n ..< n + length T]; E\<^sub>K = real_env (dep_vars T K) E
                in (if abs_ok T E
                    then ty_stat ((mbind_nm b, TEstr (param_env E\<^sub>K)) # B) fr ve (n + length T) t \<bind>
                           (\<lambda>(t', ve', n').
                              (if fr
                               then Some (TDep (is_imp b) (mbind_sig b) (length T) (RV n')
                                            (kclose K t'), ve', Suc n')
                               else Some (TDep (is_imp b) (mbind_sig b) (length T) RNil
                                            (kclose K t'), ve', n')))
                    else None))
           | _ \<Rightarrow> None)
      | _ \<Rightarrow> None)\<close>
| \<open>ty_stat B fr ve n (TRow ls ro) = None\<close>
| \<open>ty_stat B fr ve n TErr = None\<close>
| \<open>ty_stat B fr ve n (TArrowName f e ro t) =
     (case e of
        TPath p # as \<Rightarrow>
          (if nm_ok (n_txt f)
           then atoms_stat B fr ve n as \<bind> (\<lambda>(args, ve\<^sub>1, n\<^sub>1).
                  eff_at B p (length args) \<bind> (\<lambda>(l, ls).
                    row_stat ((nkey (n_txt f), TEeff l ls (length args)) # B) fr ve\<^sub>1 n\<^sub>1 ro \<bind>
                      (\<lambda>(\<epsilon>, ve\<^sub>2, n\<^sub>2).
                        ty_stat ((nkey (n_txt f), TEeff l ls (length args)) # B) fr ve\<^sub>2 n\<^sub>2 t \<bind>
                          (\<lambda>(\<tau>, ve\<^sub>3, n\<^sub>3).
                            Some (TAct (eff_ty l args) [n\<^sub>3]
                                    (canon_row (rext (map (nlbl \<circ> mangle l) ls) \<epsilon>)) \<tau>,
                                  ve\<^sub>3, Suc n\<^sub>3)))))
           else None)
      | _ \<Rightarrow> None)\<close>
| \<open>ty_stat B fr ve n (THand e a ro b) =
     (case e of
        TPath p # as \<Rightarrow>
          atoms_stat B fr ve n as \<bind> (\<lambda>(args, ve\<^sub>1, n\<^sub>1).
            spine_stat B fr ve\<^sub>1 n\<^sub>1 a \<bind> (\<lambda>(\<tau>\<^sub>0, ve\<^sub>2, n\<^sub>2).
              row_stat B fr ve\<^sub>2 n\<^sub>2 ro \<bind> (\<lambda>(\<epsilon>, ve\<^sub>3, n\<^sub>3).
                spine_stat B fr ve\<^sub>3 n\<^sub>3 b \<bind> (\<lambda>(\<tau>, ve\<^sub>4, n\<^sub>4).
                  eff_at B p (length args) \<bind> (\<lambda>(l, ls).
                    Some (TFn (TAct (eff_ty l args) [n\<^sub>4]
                                (canon_row (rext (map (nlbl \<circ> mangle l) ls) \<epsilon>)) \<tau>\<^sub>0)
                              \<epsilon> \<tau>,
                          ve\<^sub>4, Suc n\<^sub>4))))))
      | _ \<Rightarrow> None)\<close>
| \<open>ty_stat B fr ve n (TRec _ _) = None\<close>

| \<open>spine_stat B fr ve n [] = None\<close>
| \<open>spine_stat B fr ve n (a # as) =
     (case a of
        TPath p \<Rightarrow> atoms_stat B fr ve n as \<bind> (\<lambda>(ts, ve\<^sub>1, n\<^sub>1). head_stat B fr ve\<^sub>1 n\<^sub>1 p ts)
      | _ \<Rightarrow> (if as = [] then atom_stat B fr ve n a else None))\<close>

| \<open>atom_stat B fr ve n (TPath p) = head_stat B fr ve n p []\<close>
| \<open>atom_stat B fr ve n (TWild _) = (if fr then Some (TV n, ve, Suc n) else None)\<close>
| \<open>atom_stat B fr ve n (TParen ts) =
     (case ts of
        [t] \<Rightarrow> ty_stat B fr ve n t
      | _ \<Rightarrow> tys_stat B fr ve n ts \<bind> (\<lambda>(ts', ve', n'). Some (tuple ts', ve', n')))\<close>
| \<open>atom_stat B fr ve n (TName e) =
     (case e of
        TPath p # as \<Rightarrow>
          (if fr
           then atoms_stat B fr ve n as \<bind> (\<lambda>(args, ve', n').
                  eff_at B p (length args) \<bind> (\<lambda>(l, ls).
                    Some (TEv (eff_ty l args) (TV n') (tuple args), ve', Suc n')))
           else None)
      | _ \<Rightarrow> None)\<close>

| \<open>atoms_stat B fr ve n [] = Some ([], ve, n)\<close>
| \<open>atoms_stat B fr ve n (a # as) =
     atom_stat B fr ve n a \<bind> (\<lambda>(t, ve\<^sub>1, n\<^sub>1).
       atoms_stat B fr ve\<^sub>1 n\<^sub>1 as \<bind> (\<lambda>(ts, ve\<^sub>2, n\<^sub>2). Some (t # ts, ve\<^sub>2, n\<^sub>2)))\<close>

| \<open>tys_stat B fr ve n [] = Some ([], ve, n)\<close>
| \<open>tys_stat B fr ve n (t # ts) =
     ty_stat B fr ve n t \<bind> (\<lambda>(t', ve\<^sub>1, n\<^sub>1).
       tys_stat B fr ve\<^sub>1 n\<^sub>1 ts \<bind> (\<lambda>(ts', ve\<^sub>2, n\<^sub>2). Some (t' # ts', ve\<^sub>2, n\<^sub>2)))\<close>

| \<open>row_stat B fr ve n None = (if fr then Some (RV n, ve, Suc n) else Some (RNil, ve, n))\<close>
| \<open>row_stat B fr ve n (Some r) =
     (case r of
        TRow ls tail \<Rightarrow>
          labels_stat B ls \<bind> (\<lambda>ls'.
            (case tail of
               None \<Rightarrow> Some (canon_row (foldr RCons ls' RNil), ve, n)
             | Some (TSpine [TPath p]) \<Rightarrow>
                 (case path_nms p of
                    [v] \<Rightarrow>
                      (case map_of (snd ve) v of
                         Some r' \<Rightarrow> Some (canon_row (foldr RCons ls' r'), ve, n)
                       | None \<Rightarrow>
                           (if fr
                            then Some (canon_row (foldr RCons ls' (RV n)),
                                       (fst ve, (v, RV n) # snd ve), Suc n)
                            else None))
                  | _ \<Rightarrow> None)
             | _ \<Rightarrow> None))
      | _ \<Rightarrow> None)\<close>
  by pat_completeness auto

termination
  by (relation \<open>measure (\<lambda>x. case x of
        Inl (Inl (B, fr, ve, n, t)) \<Rightarrow> size t
      | Inl (Inr (Inl (B, fr, ve, n, as))) \<Rightarrow> size_list size as
      | Inl (Inr (Inr (B, fr, ve, n, a))) \<Rightarrow> size a
      | Inr (Inl (B, fr, ve, n, ts)) \<Rightarrow> size_list size ts
      | Inr (Inr (Inl (B, fr, ve, n, as))) \<Rightarrow> size_list size as
      | Inr (Inr (Inr (B, fr, ve, n, ro))) \<Rightarrow> size_option size ro)\<close>) auto

lemmas ty_stat_induct =
  ty_stat_atoms_stat_atom_stat_tys_stat_spine_stat_row_stat.induct[named_cases ty_stat]

text \<open>A module-dependent arrow written in a type names a declared signature;
  a literal or refined signature in that position is not supported.

  The flag \<open>fr\<close> says whether the type may mention variables of its own:
  a value's annotation, a value specification and an extern's type are
  closed over whatever they mention, so an unannotated arrow there gets a
  fresh row and a wildcard a fresh type, both generalised; a type
  definition, a constructor argument, an operation's type and a
  refinement are closed already, so an unannotated arrow there is total
  (the meaning of \<open>a \<rightarrow> b\<close> in a type, \<^cite>\<open>\<open>Sect. 2.1\<close> in leijen2017\<close>) and a
  wildcard is an error. Nothing else mints a variable there, so their
  results are closed.\<close>

text \<open>The constructors of a variant, as curried schemes with open rows, and
  the operations of an effect at their flat labels.\<close>

fun cons_stat ::
  \<open>tenv \<Rightarrow> tvenv \<Rightarrow> tvar list \<Rightarrow> tyname \<Rightarrow> nat \<Rightarrow> (nm \<times> tatom list) list \<Rightarrow> (tenv \<times> nat) option\<close>
where
  \<open>cons_stat B ve ps c n [] = Some ([], n)\<close>
| \<open>cons_stat B ve ps c n ((cn, args) # alts) =
     atoms_stat B False ve n args \<bind> (\<lambda>(ts, _, n\<^sub>1).
       (let rows = [n\<^sub>1 ..< n\<^sub>1 + length ts];
            \<tau> = foldr (\<lambda>(t, r) acc. TFn t (RV r) acc) (zip ts rows) (TC c (map TV ps))
        in cons_stat B ve ps c (n\<^sub>1 + length ts) alts \<bind> (\<lambda>(es, n\<^sub>2).
             Some ((n_txt cn,
                    TEcon (close_sch (set ps) (set [n ..< n\<^sub>1 + length ts]) \<tau>) (length ts)) # es,
                   n\<^sub>2))))\<close>

lemmas cons_stat_induct = cons_stat.induct[named_cases cons_stat]

text \<open>An effect's type parameters are elaborated like a data type's: fresh
  variables \<open>eff_ps as n\<close> stand for them while the operation types are
  elaborated, and each entry closes them into bound variables of the
  operation's scheme.\<close>

abbreviation eff_ps :: \<open>nm list \<Rightarrow> nat \<Rightarrow> tvar list\<close> where
  \<open>eff_ps as n \<equiv> [n ..< n + length as]\<close>

abbreviation eff_ve :: \<open>nm list \<Rightarrow> nat \<Rightarrow> tvenv\<close> where
  \<open>eff_ve as n \<equiv> (zip (map n_txt as) (map TV (eff_ps as n)), [])\<close>

fun ops_stat :: \<open>tenv \<Rightarrow> name \<Rightarrow> tvar list \<Rightarrow> tvenv \<Rightarrow> nat \<Rightarrow> (nm \<times> ty) list \<Rightarrow> (tenv \<times> nat) option\<close> where
  \<open>ops_stat B pre ps ve n [] = Some ([], n)\<close>
| \<open>ops_stat B pre ps ve n ((opn, ty) # ops) =
     ty_stat B False ve n ty \<bind> (\<lambda>(\<tau>, _, n\<^sub>1).
       (case \<tau> of
          TFn t\<^sub>1 _ t\<^sub>2 \<Rightarrow>
            ops_stat B pre ps ve n\<^sub>1 ops \<bind> (\<lambda>(es, n\<^sub>2).
              Some ((n_txt opn,
                     TEop (mangle pre (n_txt opn)) ps
                       (close_ty (set ps) {} t\<^sub>1) (close_ty (set ps) {} t\<^sub>2)) # es,
                    n\<^sub>2))
        | _ \<Rightarrow> None))\<close>

lemmas ops_stat_induct = ops_stat.induct[named_cases ops_stat]

text \<open>The result type of a constructor of arity \<open>n\<close>, and whether a scheme is closed.\<close>

fun con_result :: \<open>nat \<Rightarrow> kty \<Rightarrow> kty option\<close> where
  \<open>con_result 0 \<tau> = Some \<tau>\<close>
| \<open>con_result (Suc n) (TFn _ _ \<tau>) = con_result n \<tau>\<close>
| \<open>con_result (Suc n) _ = None\<close>

fun is_sch :: \<open>scheme \<Rightarrow> bool\<close> where
  \<open>is_sch (Sch t) = True\<close>
| \<open>is_sch (Mono t) = False\<close>

text \<open>A refinement \<open>[t = \<tau>]\<close> of a variant spec replicates a datatype: \<open>\<tau>\<close> must be a
  datatype with the spec's constructors (\<open>type t = M.t = A\<close> in OCaml), and not one of the
  signature's own bound stamps \<open>T\<close>.\<close>

definition rep_ok :: \<open>nat list \<Rightarrow> tyname \<Rightarrow> kty \<Rightarrow> bool\<close> where
  \<open>rep_ok T c \<tau> \<longleftrightarrow> snd (snd c) = [] \<or>
     (case \<tau> of TC c' [] \<Rightarrow> snd (snd c') = snd (snd c) \<and> stamp c' \<notin> set T | _ \<Rightarrow> False)\<close>

function (sequential) sig_stat :: \<open>tenv \<Rightarrow> nat \<Rightarrow> msig \<Rightarrow> (sigsem \<times> nat) option\<close> and
  refn_stat :: \<open>tenv \<Rightarrow> nat \<Rightarrow> sigsem \<Rightarrow> mrefn list \<Rightarrow> (sigsem \<times> nat) option\<close> and
  spec_stat :: \<open>tenv \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> tenv \<Rightarrow> mspec list \<Rightarrow> (sigsem \<times> nat) option\<close>
where
  \<open>sig_stat B n (SPath p refs) =
     (case tlookup B (path_nms p) of
        Some (TEsig \<Sigma>) \<Rightarrow> refn_stat B n \<Sigma> refs
      | _ \<Rightarrow> None)\<close>
| \<open>sig_stat B n (SLit specs) = spec_stat B n [] [] specs\<close>
| \<open>sig_stat B n SErr = None\<close>

| \<open>refn_stat B n \<Sigma> [] = Some (\<Sigma>, n)\<close>
| \<open>refn_stat B n (T, E) (RType t ty # refs) =
     (case map_of E (n_txt t) of
        Some (TEtyp (TyAbs c 0)) \<Rightarrow>
          (if stamp c \<in> set T
           then ty_stat B False ([], []) n ty \<bind> (\<lambda>(\<tau>, _, n').
                  if rep_ok T c \<tau>
                  then refn_stat B n' (removeAll (stamp c) T, real_env [(stamp c, TyFn [] \<tau>)] E)
                         refs
                  else None)
           else None)
      | _ \<Rightarrow> None)\<close>
| \<open>refn_stat B n (T, E) (RMod M P # refs) =
     (case (map_of E (n_txt M), tlookup B (path_nms P)) of
        (Some (TEstr E\<^sub>M), Some (TEstr E\<^sub>P)) \<Rightarrow>
          match_sig E\<^sub>P T E\<^sub>M \<bind> (\<lambda>\<phi>.
            refn_stat B n (filter (\<lambda>k. map_of \<phi> k = None) T, real_env \<phi> E) refs)
      | (Some (TEstr E\<^sub>M), Some (TEinst E\<^sub>P)) \<Rightarrow>
          match_sig E\<^sub>P T E\<^sub>M \<bind> (\<lambda>\<phi>.
            refn_stat B n (filter (\<lambda>k. map_of \<phi> k = None) T, real_env \<phi> E) refs)
      | _ \<Rightarrow> None)\<close>

| \<open>spec_stat B n T acc [] =
     (if distinct (map fst acc) then Some ((remdups T, rev acc), n) else None)\<close>
| \<open>spec_stat B n T acc (SpType t as None # ss) =
     spec_stat B (Suc n) (T @ [n]) ((n_txt t, TEtyp (TyAbs (n, n_txt t, []) (length as))) # acc) ss\<close>
| \<open>spec_stat B n T acc (SpType t as (Some ty) # ss) =
     (let ps = [n ..< n + length as]
      in ty_stat (acc @ B) False (zip (map n_txt as) (map TV ps), []) (n + length as) ty \<bind>
           (\<lambda>(\<tau>, _, n').
              spec_stat B n' T ((n_txt t, TEtyp (TyFn ps (close_ty (set ps) {} \<tau>))) # acc) ss))\<close>
| \<open>spec_stat B n T acc (SpData t as alts # ss) =
     (let ps = [Suc n ..< Suc n + length as];
          c = (n, n_txt t, map (\<lambda>(cn, args). (n_txt cn, length args)) alts);
          B' = (n_txt t, TEtyp (TyAbs c (length as))) # acc @ B
      in (if distinct (map (n_txt \<circ> fst) alts) \<and> list_all (\<lambda>(cn, _). nm_ok (n_txt cn)) alts
          then cons_stat B' (zip (map n_txt as) (map TV ps), []) ps c (Suc n + length as) alts \<bind>
                 (\<lambda>(cs, n').
                    spec_stat B n' (T @ [n]) (rev cs @ (n_txt t, TEtyp (TyAbs c (length as))) # acc)
                      ss)
          else None))\<close>
| \<open>spec_stat B n T acc (SpVal x ty # ss) =
     (if nm_ok (n_txt x) then
        ty_stat (acc @ B) True ([], []) n ty \<bind> (\<lambda>(\<tau>, _, n').
          spec_stat B n' T
            ((n_txt x, TEval (close_sch (set [n ..< n']) (set [n ..< n']) \<tau>)) # acc) ss)
      else None)\<close>
| \<open>spec_stat B n T acc (SpEff x as ops # ss) =
     (if distinct (map n_txt as) then
        ops_stat (acc @ B) (mangle (str ''%spec'') (n_txt x)) (eff_ps as n) (eff_ve as n)
          (n + length as) ops \<bind>
          (\<lambda>(es, n').
          spec_stat B n' T
            (rev es @
             (n_txt x,
              TEeff (mangle (str ''%spec'') (n_txt x)) (map fst es) (length as)) #
             acc)
            ss)
      else None)\<close>
| \<open>spec_stat B n T acc (SpFix f p opr # ss) =
     read_nat (n_txt p) \<bind> (\<lambda>prec.
       spec_stat B n T ((fix_key (n_txt opr), TEfix f prec) # acc) ss)\<close>
| \<open>spec_stat B n T acc (SpMod x sg # ss) =
     (if nm_ok (n_txt x) then
        sig_stat (acc @ B) n sg \<bind> (\<lambda>((T', E'), n').
          spec_stat B n' (T @ T') ((n_txt x, TEstr E') # acc) ss)
      else None)\<close>
| \<open>spec_stat B n T acc (SpInc sg # ss) =
     sig_stat (acc @ B) n sg \<bind> (\<lambda>((T', E'), n').
       spec_stat B n' (T @ T') (rev E' @ acc) ss)\<close>
| \<open>spec_stat B n T acc (SpErr # ss) = None\<close>
  by pat_completeness auto

termination
  by (relation \<open>measure (\<lambda>x. case x of
        Inl (B, n, sg) \<Rightarrow> size sg
      | Inr (Inl (B, n, \<Sigma>, refs)) \<Rightarrow> size_list size refs
      | Inr (Inr (B, n, T, acc, ss)) \<Rightarrow> size_list size ss)\<close>) auto

lemmas sig_stat_induct = sig_stat_refn_stat_spec_stat.induct[named_cases sig_stat]

text \<open>Sealing (the static twin of the elaborator's \<open>seal\<close>): match, check
  enrichment, then take the signature with fresh stamps for its abstract
  types \<^cite>\<open>\<open>Sect. 5.6\<close> in milner1997\<close> \<^cite>\<open>\<open>Sect. 4\<close> in rossberg2014\<close>.\<close>

text \<open>An effect is a global label, and sealing must not free it for a second
  declaration. So sealing keeps every effect of the structure the signature omits,
  at any depth, as a \<^emph>\<open>tombstone\<close>: the effect entry under a name no declaration or
  specification can take, a gap for the elaborator, found by \<^const>\<open>eff_lookup\<close> and
  nothing else.\<close>

fun eff_tombs :: \<open>tenv \<Rightarrow> tenv\<close> where
  \<open>eff_tombs [] = []\<close>
| \<open>eff_tombs ((x, TEeff l ls ar) # r) = (0x2E # l, TEeff l ls ar) # eff_tombs r\<close>
| \<open>eff_tombs ((x, TEstr E) # r) = eff_tombs E @ eff_tombs r\<close>
| \<open>eff_tombs ((x, TEinst E) # r) = eff_tombs E @ eff_tombs r\<close>
| \<open>eff_tombs (_ # r) = eff_tombs r\<close>

lemma eff_tombs_shape:
  \<open>(x, e) \<in> set (eff_tombs E) \<Longrightarrow> \<exists>l ls ar. e = TEeff l ls ar \<and> x = 0x2E # l\<close>
  by (induction E rule: eff_tombs.induct) auto

definition hidden_effs :: \<open>tenv \<Rightarrow> tenv \<Rightarrow> tenv\<close> where
  \<open>hidden_effs E E' =
     filter (\<lambda>(x, e). case e of TEeff l _ _ \<Rightarrow> eff_lookup E' l = None | _ \<Rightarrow> True) (eff_tombs E)\<close>

lemma hidden_effs_shape:
  \<open>(x, e) \<in> set (hidden_effs E E') \<Longrightarrow> \<exists>l ls ar. e = TEeff l ls ar \<and> x = 0x2E # l\<close>
  by (auto simp: hidden_effs_def dest: eff_tombs_shape)

text \<open>The shape a signature has for sealing: its values and constructors have closed
  schemes, and a constructor's datatype, when it is one of the bound stamps, is a variant
  spec of the signature (the renaming names the sealed type after it). Sealing and
  \<open>params_stat\<close> check it, with distinct bound stamps and fresh new ones
  (\<open>sig_ok_seal\<close>).\<close>

fun sig_shaped :: \<open>(nat \<times> tyname) list \<Rightarrow> nat list \<Rightarrow> tenv \<Rightarrow> bool\<close> and
  sig_shaped_ent :: \<open>(nat \<times> tyname) list \<Rightarrow> nat list \<Rightarrow> tentry \<Rightarrow> bool\<close>
where
  \<open>sig_shaped N T [] = True\<close>
| \<open>sig_shaped N T ((x, e) # E) = (sig_shaped_ent N T e \<and> sig_shaped N T E)\<close>
| sig_shaped_ent_TEval: \<open>sig_shaped_ent N T (TEval \<sigma>) = is_sch \<sigma>\<close>
| \<open>sig_shaped_ent N T (TEcon \<sigma> n) =
     (is_sch \<sigma> \<and> (\<exists>c\<^sub>0 ps. con_result n (sch_body \<sigma>) = Some (TC c\<^sub>0 ps) \<and>
     (stamp c\<^sub>0 \<in> set T \<longrightarrow> map_of N (stamp c\<^sub>0) = Some c\<^sub>0 \<and> snd (snd c\<^sub>0) \<noteq> [])))\<close>
| sig_shaped_ent_TEstr: \<open>sig_shaped_ent N T (TEstr E) = sig_shaped N T E\<close>
| sig_shaped_ent_other: \<open>sig_shaped_ent N T _ = True\<close>

text \<open>Code equations: the constructor clause in its \<open>case\<close> form, without the
  existential.\<close>

lemma sig_shaped_ent_TEcon_code:
  \<open>sig_shaped_ent N T (TEcon \<sigma> n) = (is_sch \<sigma> \<and>
     (case con_result n (sch_body \<sigma>) of
        Some (TC c\<^sub>0 ps) \<Rightarrow> stamp c\<^sub>0 \<in> set T \<longrightarrow> map_of N (stamp c\<^sub>0) = Some c\<^sub>0 \<and> snd (snd c\<^sub>0) \<noteq> []
      | _ \<Rightarrow> False))\<close>
  by (auto split: option.split kty.split)

lemmas sig_shaped_ent_code[code] =
  sig_shaped_ent_TEval sig_shaped_ent_TEcon_code sig_shaped_ent_TEstr sig_shaped_ent_other

definition sig_ok_seal :: \<open>nat list \<Rightarrow> nat list \<Rightarrow> tenv \<Rightarrow> bool\<close> where
  \<open>sig_ok_seal T K E \<longleftrightarrow> distinct T \<and> sig_shaped (stamp_names E) T E \<and> stamps_env E \<inter> set K = {}\<close>

definition seal_stat :: \<open>tenv \<Rightarrow> nat \<Rightarrow> msig \<Rightarrow> tenv \<Rightarrow> (tenv \<times> nat) option\<close> where
  \<open>seal_stat B n sg E =
     sig_stat B n sg \<bind> (\<lambda>((T, E\<^sub>1), n\<^sub>1).
       match_sig E T E\<^sub>1 \<bind> (\<lambda>\<phi>.
         (let K = [n\<^sub>1 ..< n\<^sub>1 + length T]
          in if enrich E (real_env \<phi> E\<^sub>1) \<and> sig_ok_seal T K E\<^sub>1
             then (let E' = seal_env E (real_env (rename_stamps E\<^sub>1 T K) E\<^sub>1)
                   in Some (E' @ hidden_effs E E', n\<^sub>1 + length T))
             else None)))\<close>

definition sealo_stat :: \<open>tenv \<Rightarrow> nat \<Rightarrow> msig option \<Rightarrow> tenv \<Rightarrow> (tenv \<times> nat) option\<close> where
  \<open>sealo_stat B n so E = (case so of None \<Rightarrow> Some (E, n) | Some sg \<Rightarrow> seal_stat B n sg E)\<close>

text \<open>A functor's result names each of its own stamps by one abstract type it
  declares: an application renames those stamps, one name each, by
  \<^const>\<open>rename_stamps\<close>, which reads the names off the declarations.\<close>

definition res_names :: \<open>tenv \<Rightarrow> nat list \<Rightarrow> bool\<close> where
  \<open>res_names E T \<longleftrightarrow> (\<forall>c \<in> tn_env E. stamp c \<in> set T \<longrightarrow> map_of (stamp_names E) (stamp c) = Some c)\<close>

text \<open>The signature of a module-dependent binder must be a name without
  refinements: \<^const>\<open>TDep\<close> carries the signature's syntax and every
  application re-elaborates it.\<close>

fun named_sig :: \<open>msig \<Rightarrow> bool\<close> where
  \<open>named_sig (SPath p refs) = (refs = [])\<close>
| \<open>named_sig _ = False\<close>

text \<open>The signature of a module binder at a use: the binder's signature
  re-elaborated, its abstract types replaced by the variables the arrow
  binds \<^cite>\<open>\<open>Sect. 3.4\<close> in vivien2024\<close>. Matching a structure against it reads a
  type for each of those variables off the structure's type members.\<close>

definition dep_env :: \<open>tenv \<Rightarrow> nat \<Rightarrow> msig \<Rightarrow> nat \<Rightarrow> (tvar list \<times> tenv \<times> nat) option\<close> where
  \<open>dep_env B n sg m =
     (if named_sig sg then sig_stat B n sg else None) \<bind> (\<lambda>((T, E), n').
       (if length T = m \<and> abs_ok T E \<and> distinct T \<and> (\<forall>t\<in>set T. abs_present t E)
        then Some ([n' ..< n' + m], real_env (dep_vars T [n' ..< n' + m]) E, n' + m)
        else None))\<close>

fun match_dep :: \<open>tenv \<Rightarrow> tvar list \<Rightarrow> tenv \<Rightarrow> (tvar \<times> kty) list option\<close> where
  \<open>match_dep E K [] = Some []\<close>
| \<open>match_dep E K ((t, TEtyp (TyFn [] (TK k))) # r) =
     (if k \<in> set K
      then (case map_of E t of
              Some (TEtyp d) \<Rightarrow>
                (if tydef_arity d = 0
                 then match_dep E K r \<bind> (\<lambda>\<phi>. Some ((k, tydef_app d []) # \<phi>)) else None)
            | _ \<Rightarrow> None)
      else match_dep E K r)\<close>
| \<open>match_dep E K ((x, TEstr E\<^sub>1) # r) =
     (case map_of E x of
        Some (TEstr E\<^sub>2) \<Rightarrow>
          match_dep E\<^sub>2 K E\<^sub>1 \<bind> (\<lambda>\<phi>\<^sub>1. match_dep E K r \<bind> (\<lambda>\<phi>\<^sub>2. Some (\<phi>\<^sub>1 @ \<phi>\<^sub>2)))
      | _ \<Rightarrow> None)\<close>
| \<open>match_dep E K (_ # r) = match_dep E K r\<close>

lemmas match_dep_induct = match_dep.induct[named_cases match_dep]

text \<open>A \<open>TK k\<close> hole reachable inside a signature environment (the shape
  \<open>real_env (dep_vars \<dots>) \<dots>\<close> plants, and \<open>match_dep\<close> reads back): the
  structural companion of \<open>abs_present\<close>.\<close>

fun khole_ent :: \<open>tvar \<Rightarrow> tentry \<Rightarrow> bool\<close> and
  khole :: \<open>tvar \<Rightarrow> tenv \<Rightarrow> bool\<close>
where
  \<open>khole_ent k (TEtyp (TyFn [] (TK k'))) = (k = k')\<close>
| \<open>khole_ent k (TEstr E) = khole k E\<close>
| \<open>khole_ent k e = False\<close>
| \<open>khole k [] = False\<close>
| \<open>khole k ((x, e) # r) = (khole_ent k e \<or> khole k r)\<close>

text \<open>Realising an abstract type to a \<open>TK k\<close> plants a \<open>k\<close>-hole exactly where
  it stood (companion of \<open>abs_present_dep_ktv\<close>).\<close>

lemma khole_dep:
  \<open>abs_present_ent t e \<Longrightarrow> map_of \<phi> t = Some (TyFn [] (TK k)) \<Longrightarrow> khole_ent k (real_ent \<phi> e)\<close>
  \<open>abs_present t E \<Longrightarrow> map_of \<phi> t = Some (TyFn [] (TK k)) \<Longrightarrow> khole k (real_env \<phi> E)\<close>
proof (induction \<phi> e and \<phi> E rule: real_ent_induct)
  case (real_ent_TEtyp \<phi> d)
  then show ?case by (cases d) auto
qed auto

text \<open>\<open>match_dep\<close> covers every \<open>k\<close>-hole it can reach, at any nesting depth
  (the nested companion of \<open>match_dep_dom\<close>).\<close>

lemma match_dep_khole:
  \<open>match_dep E K E' = Some \<phi> \<Longrightarrow> khole k E' \<Longrightarrow> k \<in> set K \<Longrightarrow> k \<in> fst ` set \<phi>\<close>
proof (induction E K E' arbitrary: \<phi> rule: match_dep_induct)
  case (Cons_TEtyp_TyFn_Nil_TK E K t' k' r)
  then show ?case
    using Cons_TEtyp_TyFn_Nil_TK.prems Cons_TEtyp_TyFn_Nil_TK.IH
    by (fastforce simp: bind_eq_Some_conv split: option.split_asm tentry.split_asm if_split_asm)
next
  case (Cons_TEstr E K x E\<^sub>1 r)
  then show ?case
    using Cons_TEstr.prems Cons_TEstr.IH
    by (fastforce simp: bind_eq_Some_conv split: option.split_asm tentry.split_asm)
qed auto

text \<open>Given coverage of \<open>(T, E)\<close>, matching the dependent environment its
  \<open>dep_vars\<close> realisation builds resolves every one of the \<open>K\<close> variables.\<close>

lemma match_dep_covers:
  assumes md: \<open>match_dep E\<^sub>P K (real_env (dep_vars T K) E) = Some \<phi>\<close>
    and cov: \<open>\<forall>t\<in>set T. abs_present t E\<close> and L: \<open>length T = length K\<close> and dT: \<open>distinct T\<close>
  shows \<open>set K \<subseteq> fst ` set \<phi>\<close>
proof (rule subsetI)
  fix k assume kK: \<open>k \<in> set K\<close>
  then obtain j where j: \<open>j < length K\<close> and kj: \<open>K ! j = k\<close> by (auto simp: in_set_conv_nth)
  have dv: \<open>dep_vars T K = zip T (map (\<lambda>k. TyFn [] (TK k)) K)\<close>
    by (simp add: dep_vars_def zip_map2)
  have mo: \<open>map_of (dep_vars T K) (T ! j) = Some (TyFn [] (TK k))\<close>
    unfolding dv using dT L j kj by (simp add: map_of_zip_nth)
  have ap: \<open>abs_present (T ! j) E\<close> using cov j L by simp
  have \<open>khole k (real_env (dep_vars T K) E)\<close> using khole_dep(2)[OF ap mo] .
  then show \<open>k \<in> fst ` set \<phi>\<close> using match_dep_khole[OF md _ kK] by simp
qed

subsection \<open>Implicit resolution\<close>

text \<open>The implicit scope is the instances declared and the implicit
  parameters in scope, unqualified \<^cite>\<open>\<open>Sect. 2.2.2\<close> in white2014\<close>. A candidate
  resolves a request \<open>(K)E\<close> at realisation \<open>\<phi>\<close> if it matches the request
  with that realisation and enriches it; exactly one must (coherence by
  uniqueness, criterion 3 of \<^cite>\<open>\<open>Sect. 2.2.2\<close> in white2014\<close>).\<close>

definition cands :: \<open>tenv \<Rightarrow> (name \<times> tenv) list\<close> where
  \<open>cands B = remdups (List.map_filter
     (\<lambda>(x, e). case e of
                 TEinst E \<Rightarrow> (if map_of B x = Some e then Some (x, E) else None)
               | _ \<Rightarrow> None) B)\<close>

definition fits :: \<open>tvar list \<Rightarrow> tenv \<Rightarrow> (tvar \<times> kty) list \<Rightarrow> tenv \<Rightarrow> bool\<close> where
  \<open>fits K E \<phi> E\<^sub>P \<longleftrightarrow>
     (case match_dep E\<^sub>P K E of
        Some \<phi>' \<Rightarrow> tsl_eq K \<phi>' \<phi> \<and> enrich E\<^sub>P (kenv (tsl \<phi>') E)
      | None \<Rightarrow> False)\<close>

definition imp_res ::
  \<open>(name \<times> tenv) list \<Rightarrow> tvar list \<Rightarrow> tenv \<Rightarrow> (tvar \<times> kty) list \<Rightarrow> name option\<close>
where
  \<open>imp_res cs K E \<phi> = (case filter (\<lambda>(x, E\<^sub>P). fits K E \<phi> E\<^sub>P) cs of [(x, _)] \<Rightarrow> Some x | _ \<Rightarrow> None)\<close>

abbreviation imp_resolve :: \<open>tenv \<Rightarrow> tvar list \<Rightarrow> tenv \<Rightarrow> (tvar \<times> kty) list \<Rightarrow> name option\<close> where
  \<open>imp_resolve B K E \<phi> \<equiv> imp_res (cands B) K E \<phi>\<close>

subsection \<open>Operator chains\<close>

text \<open>An operator chain is resolved by \<^const>\<open>shunt\<close> over its fixities into a
  tree of leaf indices, exactly as the elaborator does over core terms
  (Dijkstra's shunting-yard \<^cite>\<open>dijkstra1961\<close>, with the associativity
  test of \<^cite>\<open>\<open>Sect. 10.6\<close> in marlow2010\<close>); the leaves are typed once, the tree against
  their types. An operator is a value applied to the pair of its operands,
  or a binary constructor.\<close>

datatype optree = Leaf nat | Node obld optree optree

definition op_stat :: \<open>tenv \<Rightarrow> name \<Rightarrow> (obld \<times> fixity \<times> nat) option\<close> where
  \<open>op_stat B opr =
     (let fx = (case map_of B (fix_key opr) of
                  Some (TEfix f p) \<Rightarrow> (f, p) | _ \<Rightarrow> (FixR, 0))
      in (case tlookup B [opr] of
            Some (TEcon \<sigma> n) \<Rightarrow> Some (if n = 2 then OCon opr else OVar opr, fx)
          | Some (TEval \<sigma>) \<Rightarrow> Some (OVar opr, fx)
          | _ \<Rightarrow> None))\<close>

fun ops_of :: \<open>tenv \<Rightarrow> nm list \<Rightarrow> ((obld \<times> fixity \<times> nat) list) option\<close> where
  \<open>ops_of B [] = Some []\<close>
| \<open>ops_of B (opr # oprs) =
     op_stat B (n_txt opr) \<bind> (\<lambda>oe. ops_of B oprs \<bind> (\<lambda>oes. Some (oe # oes)))\<close>

definition chain_tree :: \<open>tenv \<Rightarrow> nm list \<Rightarrow> optree option\<close> where
  \<open>chain_tree B oprs =
     ops_of B oprs \<bind> (\<lambda>oes. shunt Node [] (Leaf 0) (zip oes (map Leaf [1 ..< Suc (length oprs)])))\<close>

fun is_eop :: \<open>expr \<Rightarrow> bool\<close> where
  \<open>is_eop (EOp _ _ _) = True\<close>
| \<open>is_eop _ = False\<close>

inductive wt_tree :: \<open>tenv \<Rightarrow> krow \<Rightarrow> kty list \<Rightarrow> optree \<Rightarrow> kty \<Rightarrow> bool\<close> where
  T_leaf: \<open>i < length \<tau>s \<Longrightarrow> wt_tree B \<epsilon> \<tau>s (Leaf i) (\<tau>s ! i)\<close>
| T_var:  \<open>wt_tree B \<epsilon> \<tau>s l \<tau>\<^sub>l \<Longrightarrow> wt_tree B \<epsilon> \<tau>s r \<tau>\<^sub>r \<Longrightarrow>
           tlookup B [v] = Some (TEval \<sigma>) \<Longrightarrow> \<sigma> \<succeq> \<tau>\<^sub>f \<Longrightarrow>
           \<tau>\<^sub>f \<simeq> TFn (tuple [\<tau>\<^sub>l, \<tau>\<^sub>r]) \<epsilon>\<^sub>l \<tau> \<Longrightarrow> \<epsilon>\<^sub>l \<approx> \<epsilon> \<Longrightarrow>
           wt_tree B \<epsilon> \<tau>s (Node (OVar v) l r) \<tau>\<close>
| T_con:  \<open>wt_tree B \<epsilon> \<tau>s l \<tau>\<^sub>l \<Longrightarrow> wt_tree B \<epsilon> \<tau>s r \<tau>\<^sub>r \<Longrightarrow>
           tlookup B [c] = Some (TEcon \<sigma> 2) \<Longrightarrow> \<sigma> \<succeq> \<tau>\<^sub>c \<Longrightarrow>
           \<tau>\<^sub>c \<simeq> TFn \<tau>\<^sub>l \<epsilon>\<^sub>1 (TFn \<tau>\<^sub>r \<epsilon>\<^sub>2 \<tau>) \<Longrightarrow>
           wt_tree B \<epsilon> \<tau>s (Node (OCon c) l r) \<tau>\<close>

text \<open>An operator pattern \<open>p \<oplus> q\<close> resolves by the same chain: every node must be
  a binary constructor (an operator bound as a value has no meaning in a
  pattern), applied to its operands as parenthesised patterns. The resolution of
  a pattern replaces every chain in it, so the result holds no \<^const>\<open>PatOp\<close>; the
  typing rules and the algorithm type an operator pattern as its resolution, and
  exhaustiveness reads the resolution's constructor head.\<close>

fun tree_pat :: \<open>mpat list \<Rightarrow> optree \<Rightarrow> mpat option\<close> where
  \<open>tree_pat ps (Leaf i) = (if i < length ps then Some (ps ! i) else None)\<close>
| \<open>tree_pat ps (Node (OCon c) l r) =
     tree_pat ps l \<bind> (\<lambda>p. tree_pat ps r \<bind> (\<lambda>q.
       Some (PatApp [PQid (MkPath [mk_nm c]), PParen [p], PParen [q]])))\<close>
| \<open>tree_pat ps (Node (OVar _) _ _) = None\<close>

fun pat_resolve :: \<open>tenv \<Rightarrow> mpat \<Rightarrow> mpat option\<close>
and patom_resolve :: \<open>tenv \<Rightarrow> mpatom \<Rightarrow> mpatom option\<close>
and chain_resolve :: \<open>tenv \<Rightarrow> mpat \<Rightarrow> (mpat list \<times> nm list) option\<close>
and pats_resolve :: \<open>tenv \<Rightarrow> mpat list \<Rightarrow> mpat list option\<close>
and patoms_resolve :: \<open>tenv \<Rightarrow> mpatom list \<Rightarrow> mpatom list option\<close>
and fields_resolve :: \<open>tenv \<Rightarrow> (nm \<times> mpat) list \<Rightarrow> (nm \<times> mpat) list option\<close>
where
  \<open>pat_resolve B (PatApp as) = map_option PatApp (patoms_resolve B as)\<close>
| \<open>pat_resolve B (PatOp as opr p) =
     patoms_resolve B as \<bind> (\<lambda>as'. chain_resolve B p \<bind> (\<lambda>(ps, oprs).
       chain_tree B (opr # oprs) \<bind> tree_pat (PatApp as' # ps)))\<close>
| \<open>pat_resolve B (PatAs p x) = map_option (\<lambda>q. PatAs q x) (pat_resolve B p)\<close>
| \<open>pat_resolve B (PatAnn p ty) = map_option (\<lambda>q. PatAnn q ty) (pat_resolve B p)\<close>
| \<open>patom_resolve B (PParen ps) = map_option PParen (pats_resolve B ps)\<close>
| \<open>patom_resolve B (PList ps) = map_option PList (pats_resolve B ps)\<close>
| \<open>patom_resolve B (PRec fs wild) = map_option (\<lambda>fs'. PRec fs' wild) (fields_resolve B fs)\<close>
| \<open>patom_resolve B a = Some a\<close>
| \<open>chain_resolve B (PatOp as opr p) =
     patoms_resolve B as \<bind> (\<lambda>as'. chain_resolve B p \<bind> (\<lambda>(ps, oprs).
       Some (PatApp as' # ps, opr # oprs)))\<close>
| \<open>chain_resolve B (PatApp as) = map_option (\<lambda>as'. ([PatApp as'], [])) (patoms_resolve B as)\<close>
| \<open>chain_resolve B (PatAs p x) = map_option (\<lambda>q. ([PatAs q x], [])) (pat_resolve B p)\<close>
| \<open>chain_resolve B (PatAnn p ty) = map_option (\<lambda>q. ([PatAnn q ty], [])) (pat_resolve B p)\<close>
| \<open>pats_resolve B [] = Some []\<close>
| \<open>pats_resolve B (p # ps) = pat_resolve B p \<bind> (\<lambda>q. map_option ((#) q) (pats_resolve B ps))\<close>
| \<open>patoms_resolve B [] = Some []\<close>
| \<open>patoms_resolve B (a # as) =
     patom_resolve B a \<bind> (\<lambda>b. map_option ((#) b) (patoms_resolve B as))\<close>
| \<open>fields_resolve B [] = Some []\<close>
| \<open>fields_resolve B ((x, p) # fs) =
     pat_resolve B p \<bind> (\<lambda>q. map_option ((#) (x, q)) (fields_resolve B fs))\<close>

lemmas pat_resolve_induct =
  pat_resolve_patom_resolve_chain_resolve_pats_resolve_patoms_resolve_fields_resolve.induct[
    named_cases pat_resolve]

subsection \<open>Patterns\<close>

text \<open>Pattern typing \<open>wtp B p \<tau> \<Gamma>\<close>: \<open>p\<close> matches scrutinees of type \<open>\<tau>\<close> and
  binds \<open>\<Gamma>\<close>, in the order the elaborator's \<open>elab_pat\<close> produces binders. A
  single-segment name that is not a constructor binds; a constructor
  pattern is saturated; an operator pattern is typed as its resolution. An
  unsuffixed literal is an \<open>int\<close>, a suffixed one has its suffix's type.\<close>

definition is_con :: \<open>tenv \<Rightarrow> name \<Rightarrow> bool\<close> where
  \<open>is_con B x = (case tlookup B [x] of Some (TEcon _ _) \<Rightarrow> True | _ \<Rightarrow> False)\<close>

fun con_ty :: \<open>nat \<Rightarrow> kty \<Rightarrow> (kty list \<times> kty) option\<close> where
  \<open>con_ty 0 \<tau> = Some ([], \<tau>)\<close>
| \<open>con_ty (Suc n) (TFn \<tau>\<^sub>1 _ \<tau>\<^sub>2) = con_ty n \<tau>\<^sub>2 \<bind> (\<lambda>(ts, t). Some (\<tau>\<^sub>1 # ts, t))\<close>
| \<open>con_ty (Suc n) _ = None\<close>

lemmas con_ty_induct = con_ty.induct[named_cases con_ty]

fun fn_pat :: \<open>mpat list \<Rightarrow> mpat\<close> where
  \<open>fn_pat [p] = p\<close>
| \<open>fn_pat ps = PatApp [PParen ps]\<close>

fun fn_ty :: \<open>kty list \<Rightarrow> kty\<close> where
  \<open>fn_ty [\<tau>] = \<tau>\<close>
| \<open>fn_ty \<tau>s = tuple \<tau>s\<close>

inductive wtp :: \<open>tenv \<Rightarrow> mpat \<Rightarrow> kty \<Rightarrow> (name \<times> kty) list \<Rightarrow> bool\<close> and
  wtpa :: \<open>tenv \<Rightarrow> mpatom \<Rightarrow> kty \<Rightarrow> (name \<times> kty) list \<Rightarrow> bool\<close> and
  wtpas :: \<open>tenv \<Rightarrow> mpatom list \<Rightarrow> kty list \<Rightarrow> (name \<times> kty) list \<Rightarrow> bool\<close> and
  wtps :: \<open>tenv \<Rightarrow> mpat list \<Rightarrow> kty list \<Rightarrow> (name \<times> kty) list \<Rightarrow> bool\<close>
where
  P_atom: \<open>wtpa B a \<tau> \<Gamma> \<Longrightarrow> wtp B (PatApp [a]) \<tau> \<Gamma>\<close>
| P_con:  \<open>tlookup B (path_nms p) = Some (TEcon \<sigma> n) \<Longrightarrow> n = length as \<Longrightarrow> as \<noteq> [] \<Longrightarrow>
           \<sigma> \<succeq> \<tau>\<^sub>c \<Longrightarrow> con_ty n \<tau>\<^sub>c = Some (\<tau>s, \<tau>) \<Longrightarrow> wtpas B as \<tau>s' \<Gamma> \<Longrightarrow> \<tau>s' [\<simeq>] \<tau>s \<Longrightarrow>
           wtp B (PatApp (PQid p # as)) \<tau> \<Gamma>\<close>
| P_as:   \<open>wtp B p \<tau> \<Gamma> \<Longrightarrow> nm_ok (n_txt x) \<Longrightarrow> wtp B (PatAs p x) \<tau> ((n_txt x, \<tau>) # \<Gamma>)\<close>
| P_ann:  \<open>wtp B p \<tau> \<Gamma> \<Longrightarrow> ty_stat B True ([], []) n ty = Some (\<tau>\<^sub>a, ve, n') \<Longrightarrow>
           close_sch (set [n ..< n']) (set [n ..< n']) \<tau>\<^sub>a \<succeq> \<tau>' \<Longrightarrow> \<tau>' \<simeq> \<tau> \<Longrightarrow>
           wtp B (PatAnn p ty) \<tau> \<Gamma>\<close>
| P_op:   \<open>pat_resolve B (PatOp as opr p) = Some q \<Longrightarrow> wtp B q \<tau> \<Gamma> \<Longrightarrow>
           wtp B (PatOp as opr p) \<tau> \<Gamma>\<close>
| PA_wild: \<open>wtpa B (PWild x) \<tau> []\<close>
| PA_var: \<open>\<not> is_con B (n_txt x) \<Longrightarrow> nm_ok (n_txt x) \<Longrightarrow>
           wtpa B (PQid (MkPath [x])) \<tau> [(n_txt x, \<tau>)]\<close>
| PA_con: \<open>tlookup B (path_nms p) = Some (TEcon \<sigma> 0) \<Longrightarrow> \<sigma> \<succeq> \<tau>\<^sub>c \<Longrightarrow> \<tau>\<^sub>c \<simeq> \<tau> \<Longrightarrow>
           wtpa B (PQid p) \<tau> []\<close>
| PA_num: \<open>wtpa B (PNum l v None) (TC int_ty []) []\<close>
| PA_numsfx: \<open>sfx_ok k v \<Longrightarrow> wtpa B (PNum l v (Some k)) (TC (sfx_ty k) []) []\<close>
| PA_str: \<open>wtpa B (PStr l cs) (TC string_ty []) []\<close>
| PA_chr: \<open>wtpa B (PChar l c) (TC char_ty []) []\<close>
| PA_par: \<open>wtp B p \<tau> \<Gamma> \<Longrightarrow> wtpa B (PParen [p]) \<tau> \<Gamma>\<close>
| PA_tup: \<open>length ps \<noteq> 1 \<Longrightarrow> wtps B ps \<tau>s \<Gamma> \<Longrightarrow> wtpa B (PParen ps) (tuple \<tau>s) \<Gamma>\<close>
| PA_list: \<open>wtps B ps \<tau>s \<Gamma> \<Longrightarrow> \<forall>\<tau>' \<in> set \<tau>s. \<tau>' \<simeq> \<tau> \<Longrightarrow>
           wtpa B (PList ps) (TC list_ty [\<tau>]) \<Gamma>\<close>
| PAs_nil: \<open>wtpas B [] [] []\<close>
| PAs_cons: \<open>wtpa B a \<tau> \<Gamma>\<^sub>1 \<Longrightarrow> wtpas B as \<tau>s \<Gamma>\<^sub>2 \<Longrightarrow> wtpas B (a # as) (\<tau> # \<tau>s) (\<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2)\<close>
| Ps_nil: \<open>wtps B [] [] []\<close>
| Ps_cons: \<open>wtp B p \<tau> \<Gamma>\<^sub>1 \<Longrightarrow> wtps B ps \<tau>s \<Gamma>\<^sub>2 \<Longrightarrow> wtps B (p # ps) (\<tau> # \<tau>s) (\<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2)\<close>

subsection \<open>Exhaustiveness and syntactic values\<close>

text \<open>Shallow exhaustiveness: an irrefutable clause, or every constructor
  of the scrutinee's stamped type covered by a clause whose sub-patterns
  are irrefutable. The constructors are those the type name lists; a
  clause covers one when its head resolves to a constructor of that stamp
  under the constructor's declared name.\<close>

fun irrefutable :: \<open>tenv \<Rightarrow> mpat \<Rightarrow> bool\<close> and
  irrefutable_atom :: \<open>tenv \<Rightarrow> mpatom \<Rightarrow> bool\<close>
where
  \<open>irrefutable B (PatApp [a]) = irrefutable_atom B a\<close>
| \<open>irrefutable B (PatApp _) = False\<close>
| \<open>irrefutable B (PatAs p x) = irrefutable B p\<close>
| \<open>irrefutable B (PatAnn p _) = irrefutable B p\<close>
| \<open>irrefutable B (PatOp _ _ _) = False\<close>
| \<open>irrefutable_atom B (PWild _) = True\<close>
| \<open>irrefutable_atom B (PQid (MkPath [x])) = (\<not> is_con B (n_txt x))\<close>
| \<open>irrefutable_atom B (PQid _) = False\<close>
| \<open>irrefutable_atom B (PParen ps) = list_all (irrefutable B) ps\<close>
| \<open>irrefutable_atom B _ = False\<close>

definition con_stamp :: \<open>scheme \<Rightarrow> nat \<Rightarrow> nat option\<close> where
  \<open>con_stamp \<sigma> n =
     (case con_result n (sch_body \<sigma>) of Some (TC c _) \<Rightarrow> Some (stamp c) | _ \<Rightarrow> None)\<close>

fun con_head :: \<open>tenv \<Rightarrow> mpat \<Rightarrow> (mpath \<times> mpatom list) option\<close> where
  \<open>con_head B (PatApp (PQid p # as)) = Some (p, as)\<close>
| \<open>con_head B (PatAs p x) = con_head B p\<close>
| \<open>con_head B (PatAnn p _) = con_head B p\<close>
| \<open>con_head B (PatOp as opr p) =
     (case pat_resolve B (PatOp as opr p) of
        Some (PatApp (PQid q # as')) \<Rightarrow> Some (q, as') | _ \<Rightarrow> None)\<close>
| \<open>con_head B _ = None\<close>

definition con_clause :: \<open>tenv \<Rightarrow> nat \<Rightarrow> name \<Rightarrow> nat \<Rightarrow> mpat \<Rightarrow> bool\<close> where
  \<open>con_clause B k C n p \<longleftrightarrow>
     (case con_head B p of
        Some (q, as) \<Rightarrow>
          last (path_nms q) = C \<and> length as = n \<and> list_all (irrefutable_atom B) as \<and>
          (case tlookup B (path_nms q) of
             Some (TEcon \<sigma> n') \<Rightarrow> n' = n \<and> con_stamp \<sigma> n = Some k
           | _ \<Rightarrow> False)
      | None \<Rightarrow> False)\<close>

definition covers :: \<open>tenv \<Rightarrow> kty \<Rightarrow> mpat list \<Rightarrow> bool\<close> where
  \<open>covers B \<tau> ps \<longleftrightarrow>
     list_ex (irrefutable B) ps \<or>
     (case \<tau> of
        TC (k, x, cs) args \<Rightarrow>
          cs \<noteq> [] \<and> list_all (\<lambda>(C, n). list_ex (con_clause B k C n) ps) cs
      | _ \<Rightarrow> False)\<close>

text \<open>The value restriction (non-expansive expressions,
  \<^cite>\<open>\<open>Sect. 4.7--4.8\<close> in milner1997\<close>): a local binding generalises only a
  syntactic value.\<close>

fun val_exp :: \<open>tenv \<Rightarrow> expr \<Rightarrow> bool\<close> and
  val_atom :: \<open>tenv \<Rightarrow> matom \<Rightarrow> bool\<close>
where
  \<open>val_exp B (EFn _ _) = True\<close>
| \<open>val_exp B (EFnMod _ _) = True\<close>
| \<open>val_exp B (EHandlerN _) = True\<close>
| \<open>val_exp B (ESpine [a]) = val_atom B a\<close>
| \<open>val_exp B (ESpine (APath p # as)) =
     ((case tlookup B (path_nms p) of Some (TEcon _ n) \<Rightarrow> n = length as | _ \<Rightarrow> False) \<and>
      list_all (val_atom B) as)\<close>
| \<open>val_exp B (EAnn e _) = val_exp B e\<close>
| \<open>val_exp B _ = False\<close>
| \<open>val_atom B (APath p) =
     (case tlookup B (path_nms p) of
        Some (TEval _) \<Rightarrow> True | Some (TEcon _ _) \<Rightarrow> True | Some (TEffi _ _) \<Rightarrow> True | _ \<Rightarrow> False)\<close>
| \<open>val_atom B (ANum _ _ _) = True\<close>
| \<open>val_atom B (AStr _ _) = True\<close>
| \<open>val_atom B (AChar _ _) = True\<close>
| \<open>val_atom B (AParen es) = list_all (val_exp B) es\<close>
| \<open>val_atom B (AList es) = list_all (val_exp B) es\<close>
| \<open>val_atom B _ = False\<close>

lemmas val_exp_induct = val_exp_val_atom.induct[named_cases val_exp]

subsection \<open>Expressions\<close>

text \<open>The judgement \<open>B,\<epsilon> \<turnstile> e \<leadsto> e' : \<tau>\<close>: under basis \<open>B\<close> and ambient row \<open>\<epsilon>\<close>
  the surface term \<open>e\<close> elaborates to \<open>e'\<close>, which differs from \<open>e\<close> only by
  inserted and annotated module arguments, with type \<open>\<tau>\<close>. The rules follow
  \<^cite>\<open>\<open>Fig. 3\<close> in leijen2017\<close>: the ambient row is shared by the premises of a rule,
  a function captures its body's ambient as its latent row, an application
  requires the latent row to equal the ambient (equality suffices with open
  rows, \<^cite>\<open>\<open>Sect. 3.2\<close> in leijen2017\<close>), an operation demands its label
  in the ambient row, a handler discharges it. Types compare up to \<open>\<simeq>\<close>.

  A spine \<open>f a\<^sub>1 \<dots> a\<^sub>n\<close> is left-nested application of its head. A head
  of module-dependent type takes its module argument first (\<open>AppD\<close> of
  \<^cite>\<open>\<open>Fig. 4\<close> in vivien2024\<close>): an explicit one is the next atom, a path to a structure
  or instance, rewritten to \<^const>\<open>AMod\<close> with the callee's parameter
  signature; an implicit one is resolved from the scope at a realisation
  of the signature's abstract types and inserted
  \<^cite>\<open>\<open>Sect. 2.2--2.3\<close> in white2014\<close>. The realisation is chosen by the derivation;
  the algorithm reads it off unification, after the enclosing binding is inferred
  \<^cite>\<open>\<open>Sect. 5.1\<close> in white2014\<close>.

  A handler \<open>handle e { cls }\<close> is typed clause by clause in the nesting
  the elaborator produces, one handler per clause, the first clause
  innermost: the body runs under the row extended by every handled label,
  a clause's body and its resumption under the row of the clauses outside
  it, whose frames are still installed when the clause runs, a \<open>return\<close>
  clause transforms the result at its position (\<open>handle\<close> of
  \<^cite>\<open>\<open>Fig. 3\<close> in leijen2017\<close> types every clause body and the resumption at the
  row outside the handler; tail-resumptive clauses, \<^cite>\<open>\<open>Sect. 2.6\<close> in xie2021\<close>).
  A named handler (\<open>wt_cls\<close> with the flag set) installs one frame for all
  of its clauses and pops it before a clause body runs, so its clause
  bodies and resumptions live at the ambient row. A \<open>finally\<close> clause runs when
  its handler exits, outside the handled computation: its body is typed at the
  handler's ambient row, for its effect only. \<open>mask\<close> hides the innermost
  handler of its label \<^cite>\<open>\<open>Sect. 5\<close> in xie2020\<close>.

  A local function group \<open>let f bs ps = e | \<dots>\<close> is its lowering
  (\<^const>\<open>dfun_rhs\<close>) bound recursively, its own name monomorphic in its
  right-hand side, and generalised in the body like a \<open>let\<close> of a value; it
  elaborates to the group of one clause without parameters. Guarded
  alternatives have boolean guards and right-hand sides of one type.\<close>

fun hlabels :: \<open>tenv \<Rightarrow> hclause list \<Rightarrow> name list\<close> where
  \<open>hlabels B [] = []\<close>
| \<open>hlabels B (HOp opn _ _ _ # cls) =
     (case tlookup B [n_txt opn] of Some (TEop l _ _ _) \<Rightarrow> l # hlabels B cls | _ \<Rightarrow> hlabels B cls)\<close>
| \<open>hlabels B (_ # cls) = hlabels B cls\<close>

lemmas hlabels_induct = hlabels.induct[named_cases hlabels]

abbreviation binders :: \<open>(name \<times> kty) list \<Rightarrow> tenv\<close> where
  \<open>binders \<Gamma> \<equiv> map (\<lambda>(x, \<tau>). (x, TEval (kmono \<tau>))) \<Gamma>\<close>

fun is_fn :: \<open>expr \<Rightarrow> bool\<close> where
  \<open>is_fn (EFn _ _) = True\<close>
| \<open>is_fn (EFnMod _ _) = True\<close>
| \<open>is_fn _ = False\<close>

inductive
  wt :: \<open>tenv \<Rightarrow> krow \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> kty \<Rightarrow> bool\<close>
    (\<open>_,_ \<turnstile> _ \<leadsto> _ : _\<close> [51, 51, 51, 51, 51] 50) and
  wt_head :: \<open>tenv \<Rightarrow> krow \<Rightarrow> matom \<Rightarrow> matom \<Rightarrow> kty \<Rightarrow> bool\<close> and
  wt_atom :: \<open>tenv \<Rightarrow> krow \<Rightarrow> matom \<Rightarrow> matom \<Rightarrow> kty \<Rightarrow> bool\<close> and
  wt_args :: \<open>tenv \<Rightarrow> krow \<Rightarrow> kty \<Rightarrow> matom list \<Rightarrow> matom list \<Rightarrow> kty \<Rightarrow> bool\<close> and
  wt_exps :: \<open>tenv \<Rightarrow> krow \<Rightarrow> expr list \<Rightarrow> expr list \<Rightarrow> kty list \<Rightarrow> bool\<close> and
  wt_chain :: \<open>tenv \<Rightarrow> krow \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> nm list \<Rightarrow> kty list \<Rightarrow> bool\<close> and
  wt_arms :: \<open>tenv \<Rightarrow> krow \<Rightarrow> kty \<Rightarrow> (mpat \<times> expr) list \<Rightarrow> (mpat \<times> expr) list \<Rightarrow> kty \<Rightarrow> bool\<close> and
  wt_cls :: \<open>tenv \<Rightarrow> krow \<Rightarrow> bool \<Rightarrow> kty \<Rightarrow> kty \<Rightarrow> hclause list \<Rightarrow> hclause list \<Rightarrow> kty \<Rightarrow> bool\<close> and
  wt_alts :: \<open>tenv \<Rightarrow> krow \<Rightarrow> (expr list \<times> expr) list \<Rightarrow> (expr list \<times> expr) list \<Rightarrow> kty \<Rightarrow> bool\<close>
where
  W_spine: \<open>wt_head B \<epsilon> a a' \<tau>\<^sub>0 \<Longrightarrow> wt_args B \<epsilon> \<tau>\<^sub>0 as as' \<tau> \<Longrightarrow>
            B,\<epsilon> \<turnstile> ESpine (a # as) \<leadsto> ESpine (a' # as') : \<tau>\<close>
| W_op:    \<open>wt_chain B \<epsilon> (EOp as opr e) (EOp as' opr e') oprs \<tau>s \<Longrightarrow>
            chain_tree B oprs = Some tree \<Longrightarrow> wt_tree B \<epsilon> \<tau>s tree \<tau> \<Longrightarrow>
            B,\<epsilon> \<turnstile> EOp as opr e \<leadsto> EOp as' opr e' : \<tau>\<close>
| W_ann:   \<open>B,\<epsilon> \<turnstile> e \<leadsto> e' : \<tau> \<Longrightarrow> ty_stat B True ([], []) n ty = Some (\<tau>\<^sub>a, ve, n') \<Longrightarrow>
            close_sch (set [n ..< n']) (set [n ..< n']) \<tau>\<^sub>a \<succeq> \<tau>' \<Longrightarrow> \<tau>' \<simeq> \<tau> \<Longrightarrow>
            B,\<epsilon> \<turnstile> EAnn e ty \<leadsto> EAnn e' ty : \<tau>\<close>
| W_fn:    \<open>wtps B ps \<tau>s \<Gamma> \<Longrightarrow> covers B (fn_ty \<tau>s) [fn_pat ps] \<Longrightarrow>
            (binders \<Gamma> @ B),\<epsilon>' \<turnstile> b \<leadsto> b' : \<tau>\<^sub>b \<Longrightarrow>
            B,\<epsilon> \<turnstile> EFn ps b \<leadsto> EFn ps b' : TFn (fn_ty \<tau>s) \<epsilon>' \<tau>\<^sub>b\<close>
| W_fnmod: \<open>dep_env B n (mbind_sig b) m = Some (K, E, n') \<Longrightarrow>
            set K \<inter> ktv_env B = {} \<Longrightarrow> E\<^sub>K = param_env E \<Longrightarrow>
            ((mbind_nm b, if is_imp b then TEinst E\<^sub>K else TEstr E\<^sub>K) # B),\<epsilon>' \<turnstile> e \<leadsto> e' : \<tau> \<Longrightarrow>
            named_sig (mbind_sig b) \<Longrightarrow> nm_ok (mbind_nm b) \<Longrightarrow>
            B,\<epsilon> \<turnstile> EFnMod b e \<leadsto> EFnMod b e' : TDep (is_imp b) (mbind_sig b) m \<epsilon>' (kclose K \<tau>)\<close>
| W_let:   \<open>B,\<epsilon> \<turnstile> e \<leadsto> e' : \<tau>\<^sub>e \<Longrightarrow> wtp B p \<tau>\<^sub>p \<Gamma> \<Longrightarrow> \<tau>\<^sub>p \<simeq> \<tau>\<^sub>e \<Longrightarrow> covers B \<tau>\<^sub>e [p] \<Longrightarrow>
            as \<inter> ftv_env B = {} \<Longrightarrow> rs \<inter> frv_env B = {} \<Longrightarrow> rs \<inter> frv_row \<epsilon> = {} \<Longrightarrow>
            (as = {} \<and> rs = {}) \<or> val_exp B e' \<Longrightarrow>
            (map (\<lambda>(x, \<tau>). (x, TEval (close_sch as rs \<tau>))) \<Gamma> @ B),\<epsilon> \<turnstile> b \<leadsto> b' : \<tau> \<Longrightarrow>
            btv \<tau>\<^sub>p = {} \<Longrightarrow> brv \<tau>\<^sub>p = {} \<Longrightarrow>
            B,\<epsilon> \<turnstile> ELet p e b \<leadsto> ELet p e' b' : \<tau>\<close>
| W_letfun: \<open>cls \<noteq> [] \<Longrightarrow> r = foldr EFnMod mbs (dfun_rhs cls) \<Longrightarrow> is_fn r \<Longrightarrow>
            ((n_txt f, TEval (kmono \<tau>)) # B),\<epsilon> \<turnstile> r \<leadsto> r' : \<tau>' \<Longrightarrow> \<tau>' \<simeq> \<tau> \<Longrightarrow>
            as \<inter> ftv_env B = {} \<Longrightarrow> rs \<inter> frv_env B = {} \<Longrightarrow> rs \<inter> frv_row \<epsilon> = {} \<Longrightarrow>
            btv \<tau>' = {} \<Longrightarrow> brv \<tau>' = {} \<Longrightarrow> nm_ok (n_txt f) \<Longrightarrow>
            ((n_txt f, TEval (close_sch as rs \<tau>')) # B),\<epsilon> \<turnstile> b \<leadsto> b' : \<tau> \<Longrightarrow>
            B,\<epsilon> \<turnstile> ELetFun f mbs cls b \<leadsto> ELetFun f [] [([], r')] b' : \<tau>\<close>
| W_seq:   \<open>B,\<epsilon> \<turnstile> e\<^sub>1 \<leadsto> e\<^sub>1' : \<tau>\<^sub>1 \<Longrightarrow> B,\<epsilon> \<turnstile> e\<^sub>2 \<leadsto> e\<^sub>2' : \<tau> \<Longrightarrow>
            B,\<epsilon> \<turnstile> ESeq e\<^sub>1 e\<^sub>2 \<leadsto> ESeq e\<^sub>1' e\<^sub>2' : \<tau>\<close>
| W_if:    \<open>B,\<epsilon> \<turnstile> c \<leadsto> c' : \<tau>\<^sub>c \<Longrightarrow> \<tau>\<^sub>c \<simeq> TC bool_ty [] \<Longrightarrow>
            B,\<epsilon> \<turnstile> t \<leadsto> t' : \<tau> \<Longrightarrow> B,\<epsilon> \<turnstile> e \<leadsto> e' : \<tau>' \<Longrightarrow> \<tau>' \<simeq> \<tau> \<Longrightarrow>
            B,\<epsilon> \<turnstile> EIf c t (Some e) \<leadsto> EIf c' t' (Some e') : \<tau>\<close>
| W_if1:   \<open>B,\<epsilon> \<turnstile> c \<leadsto> c' : \<tau>\<^sub>c \<Longrightarrow> \<tau>\<^sub>c \<simeq> TC bool_ty [] \<Longrightarrow>
            B,\<epsilon> \<turnstile> t \<leadsto> t' : \<tau> \<Longrightarrow> \<tau> \<simeq> unit_ty \<Longrightarrow>
            B,\<epsilon> \<turnstile> EIf c t None \<leadsto> EIf c' t' None : unit_ty\<close>
| W_match: \<open>B,\<epsilon> \<turnstile> e \<leadsto> e' : \<tau>\<^sub>0 \<Longrightarrow> wt_arms B \<epsilon> \<tau>\<^sub>0 arms arms' \<tau> \<Longrightarrow>
            covers B \<tau>\<^sub>0 (map fst arms) \<Longrightarrow>
            B,\<epsilon> \<turnstile> EMatch e arms \<leadsto> EMatch e' arms' : \<tau>\<close>
| W_guards: \<open>alts \<noteq> [] \<Longrightarrow> wt_alts B \<epsilon> alts alts' \<tau> \<Longrightarrow>
            B,\<epsilon> \<turnstile> EGuards alts \<leadsto> EGuards alts' : \<tau>\<close>
| W_handle: \<open>\<epsilon>\<^sub>0 \<approx> rext (hlabels B cls) \<epsilon> \<Longrightarrow> \<forall>lbl \<in> set (hlabels B cls). plain_eff B lbl \<Longrightarrow>
            B,\<epsilon>\<^sub>0 \<turnstile> e \<leadsto> e' : \<tau>\<^sub>0 \<Longrightarrow> wt_cls B \<epsilon> False \<tau>\<^sub>0 (tuple []) cls cls' \<tau> \<Longrightarrow>
            B,\<epsilon> \<turnstile> EHandle e cls \<leadsto> EHandle e' cls' : \<tau>\<close>
| W_handler: \<open>wt_cls B \<epsilon>' False \<tau>\<^sub>0 (tuple []) cls cls' \<tau> \<Longrightarrow>
            \<forall>lbl \<in> set (hlabels B cls). plain_eff B lbl \<Longrightarrow>
            \<epsilon>\<^sub>a \<approx> rext (hlabels B cls) \<epsilon>' \<Longrightarrow>
            B,\<epsilon> \<turnstile> EHandler cls \<leadsto> EHandler cls' : TFn (TFn unit_ty \<epsilon>\<^sub>a \<tau>\<^sub>0) \<epsilon>' \<tau>\<close>
| W_mask:  \<open>tlookup B [n_txt l] = Some (TEop lbl ps \<tau>\<^sub>1 \<tau>\<^sub>2) \<Longrightarrow> B,\<epsilon> \<turnstile> e \<leadsto> e' : \<tau> \<Longrightarrow>
            \<epsilon>' \<approx> RCons lbl \<epsilon> \<Longrightarrow>
            B,\<epsilon>' \<turnstile> EMask l e \<leadsto> EMask l e' : \<tau>\<close>
| W_handlern: \<open>hlabels B cls = lbl # rest \<Longrightarrow> eff_of_op B lbl = Some (l, ls, ar) \<Longrightarrow>
            set (hlabels B cls) = set (map (mangle l) ls) \<Longrightarrow>
            wt_cls B \<epsilon>' True \<tau>\<^sub>0 (tuple args) cls cls' \<tau> \<Longrightarrow> length args = ar \<Longrightarrow>
            \<epsilon>\<^sub>0 \<approx> rext (map (nlbl \<circ> mangle l) ls) \<epsilon>' \<Longrightarrow>
            k \<notin> ktv_env B \<Longrightarrow> k \<notin> ktv \<tau>\<^sub>0 \<Longrightarrow> k \<notin> ktv \<tau> \<Longrightarrow> k \<notin> ktv (tuple args) \<Longrightarrow>
            B,\<epsilon> \<turnstile> EHandlerN cls \<leadsto> EHandlerN cls' : TFn (TAct (eff_ty l args) [k] \<epsilon>\<^sub>0 \<tau>\<^sub>0) \<epsilon>' \<tau>\<close>
| W_with:  \<open>B,\<epsilon> \<turnstile> h \<leadsto> h' : \<tau>\<^sub>h \<Longrightarrow> \<tau>\<^sub>h \<simeq> TFn (TAct lt K \<epsilon>\<^sub>0 \<tau>\<^sub>0) \<epsilon>\<^sub>l \<tau> \<Longrightarrow> \<epsilon>\<^sub>l \<approx> \<epsilon> \<Longrightarrow>
            k \<notin> ktv_env B \<Longrightarrow>
            (name_env B (n_txt x) lt' @ (n_txt x, TEval (kmono (TEv lt' (TK k) targs))) # B),\<epsilon>\<^sub>0'
              \<turnstile> e \<leadsto> e' : \<tau>\<^sub>0' \<Longrightarrow>
            k \<notin> ktv \<tau>\<^sub>0' \<Longrightarrow> k \<notin> ktv targs \<Longrightarrow> k \<notin> ktv lt' \<Longrightarrow> nm_ok (n_txt x) \<Longrightarrow>
            length K = 1 \<Longrightarrow> set K \<inter> ktv_env B = {} \<Longrightarrow> set K \<inter> ktv \<tau>\<^sub>0 = {} \<Longrightarrow>
            TAct lt [k] \<epsilon>\<^sub>0 (ksubst (tsl (zip K [TK k])) \<tau>\<^sub>0) \<simeq> TAct lt' [k] \<epsilon>\<^sub>0' \<tau>\<^sub>0' \<Longrightarrow>
            B,\<epsilon> \<turnstile> EWith x h e \<leadsto> EWith x h' e' : \<tau>\<close>

| H_val:   \<open>tlookup B (path_nms p) = Some (TEval \<sigma>) \<Longrightarrow> \<sigma> \<succeq> \<tau> \<Longrightarrow>
            wt_head B \<epsilon> (APath p) (APath p) \<tau>\<close>
| H_con:   \<open>tlookup B (path_nms p) = Some (TEcon \<sigma> n) \<Longrightarrow> \<sigma> \<succeq> \<tau> \<Longrightarrow>
            wt_head B \<epsilon> (APath p) (APath p) \<tau>\<close>
| H_op:    \<open>tlookup B (path_nms p) = Some (TEop l [] \<tau>\<^sub>1 \<tau>\<^sub>2) \<Longrightarrow> l \<in># row_labels \<epsilon>' \<Longrightarrow>
            wt_head B \<epsilon> (APath p) (APath p) (TFn \<tau>\<^sub>1 \<epsilon>' \<tau>\<^sub>2)\<close>
| H_opn:   \<open>path_nms p = [x, op] \<Longrightarrow> tlookup B [x] = Some (TEval \<sigma>) \<Longrightarrow> \<sigma> \<succeq> \<tau>\<^sub>x \<Longrightarrow>
            \<tau>\<^sub>x \<simeq> TEv (eff_ty l args) s (tuple args) \<Longrightarrow>
            tlookup B [op] = Some (TEop lop ps \<tau>\<^sub>1 \<tau>\<^sub>2) \<Longrightarrow> eff_of_op B lop = Some (l, ls, ar) \<Longrightarrow>
            length args = length ps \<Longrightarrow> nlbl lop \<in># row_labels \<epsilon>' \<Longrightarrow>
            wt_head B \<epsilon> (APath p) (APath p) (TFn (op_inst ps args \<tau>\<^sub>1) \<epsilon>' (op_inst ps args \<tau>\<^sub>2))\<close>
| H_ffi:   \<open>tlookup B (path_nms p) = Some (TEffi s \<sigma>) \<Longrightarrow> \<sigma> \<succeq> \<tau> \<Longrightarrow>
            wt_head B \<epsilon> (APath p) (APath p) \<tau>\<close>
| H_atom:  \<open>wt_atom B \<epsilon> a a' \<tau> \<Longrightarrow> (\<forall>p. a \<noteq> APath p) \<Longrightarrow> wt_head B \<epsilon> a a' \<tau>\<close>

| A_path:  \<open>wt_head B \<epsilon> (APath p) (APath p) \<tau> \<Longrightarrow> wt_atom B \<epsilon> (APath p) (APath p) \<tau>\<close>
| A_num:   \<open>wt_atom B \<epsilon> (ANum l v None) (ANum l v None) (TC int_ty [])\<close>
| A_numsfx: \<open>sfx_ok k v \<Longrightarrow>
            wt_atom B \<epsilon> (ANum l v (Some k)) (ANum l v (Some k)) (TC (sfx_ty k) [])\<close>
| A_float: \<open>wt_atom B \<epsilon> (AFloat x) (AFloat x) (TC f64_ty [])\<close>
| A_str:   \<open>wt_atom B \<epsilon> (AStr l cs) (AStr l cs) (TC string_ty [])\<close>
| A_chr:   \<open>wt_atom B \<epsilon> (AChar l c) (AChar l c) (TC char_ty [])\<close>
| A_par:   \<open>B,\<epsilon> \<turnstile> e \<leadsto> e' : \<tau> \<Longrightarrow> wt_atom B \<epsilon> (AParen [e]) (AParen [e']) \<tau>\<close>
| A_tup:   \<open>length es \<noteq> 1 \<Longrightarrow> wt_exps B \<epsilon> es es' \<tau>s \<Longrightarrow>
            wt_atom B \<epsilon> (AParen es) (AParen es') (tuple \<tau>s)\<close>
| A_list:  \<open>wt_exps B \<epsilon> es es' \<tau>s \<Longrightarrow> \<forall>\<tau>' \<in> set \<tau>s. \<tau>' \<simeq> \<tau> \<Longrightarrow>
            wt_atom B \<epsilon> (AList es) (AList es') (TC list_ty [\<tau>])\<close>

| G_nil:   \<open>wt_args B \<epsilon> \<tau> [] [] \<tau>\<close>
| G_app:   \<open>\<tau>\<^sub>0 \<simeq> TFn \<tau>\<^sub>1 \<epsilon>\<^sub>l \<tau>\<^sub>2 \<Longrightarrow> \<epsilon>\<^sub>l \<approx> \<epsilon> \<Longrightarrow> wt_atom B \<epsilon> a a' \<tau>\<^sub>1' \<Longrightarrow> \<tau>\<^sub>1' \<simeq> \<tau>\<^sub>1 \<Longrightarrow>
            wt_args B \<epsilon> \<tau>\<^sub>2 as as' \<tau> \<Longrightarrow>
            wt_args B \<epsilon> \<tau>\<^sub>0 (a # as) (a' # as') \<tau>\<close>
| G_act:   \<open>\<tau>\<^sub>0 \<simeq> TFn (TAct lt K \<epsilon>\<^sub>0 \<tau>\<^sub>0') \<epsilon>\<^sub>l \<tau>\<^sub>2 \<Longrightarrow> \<epsilon>\<^sub>l \<approx> \<epsilon> \<Longrightarrow> wt_atom B \<epsilon> a a' \<tau>\<^sub>1' \<Longrightarrow>
            \<tau>\<^sub>1' \<simeq> TAct lt' K' \<epsilon>\<^sub>0' \<tau>\<^sub>0'' \<Longrightarrow> length K = length K' \<Longrightarrow> set K \<inter> ktv_env B = {} \<Longrightarrow>
            set K \<inter> ktv \<tau>\<^sub>0' = {} \<Longrightarrow>
            TAct lt K' \<epsilon>\<^sub>0 (ksubst (tsl (zip K (map TK K'))) \<tau>\<^sub>0') \<simeq> TAct lt' K' \<epsilon>\<^sub>0' \<tau>\<^sub>0'' \<Longrightarrow>
            wt_args B \<epsilon> \<tau>\<^sub>2 as as' \<tau> \<Longrightarrow>
            wt_args B \<epsilon> \<tau>\<^sub>0 (a # as) (a' # as') \<tau>\<close>
| G_mod:   \<open>\<tau>\<^sub>0 \<simeq> TDep False sg m \<epsilon>\<^sub>l \<tau>\<^sub>2 \<Longrightarrow> \<epsilon>\<^sub>l \<approx> \<epsilon> \<Longrightarrow> tlookup B (path_nms P) = Some ent \<Longrightarrow>
            ent = TEstr E\<^sub>P \<or> ent = TEinst E\<^sub>P \<Longrightarrow>
            dep_env B n sg m = Some (K, E\<^sub>K, n') \<Longrightarrow> match_dep E\<^sub>P K E\<^sub>K = Some \<phi> \<Longrightarrow>
            enrich E\<^sub>P (kenv (tsl \<phi>) E\<^sub>K) \<Longrightarrow>
            wt_args B \<epsilon> (kopen (tsp K \<phi>) \<tau>\<^sub>2) as as' \<tau> \<Longrightarrow> cl_real K \<phi> \<Longrightarrow>
            wt_args B \<epsilon> \<tau>\<^sub>0 (APath P # as) (AMod P sg # as') \<tau>\<close>
| G_imp:   \<open>\<tau>\<^sub>0 \<simeq> TDep True sg m \<epsilon>\<^sub>l \<tau>\<^sub>2 \<Longrightarrow> \<epsilon>\<^sub>l \<approx> \<epsilon> \<Longrightarrow> dep_env B n sg m = Some (K, E\<^sub>K, n') \<Longrightarrow>
            imp_resolve B K E\<^sub>K \<phi> = Some P \<Longrightarrow>
            wt_args B \<epsilon> (kopen (tsp K \<phi>) \<tau>\<^sub>2) as as' \<tau> \<Longrightarrow> fst ` set \<phi> = set K \<Longrightarrow>
            cl_real K \<phi> \<Longrightarrow>
            wt_args B \<epsilon> \<tau>\<^sub>0 as (AMod (MkPath [mk_nm P]) sg # as') \<tau>\<close>

| Es_nil:  \<open>wt_exps B \<epsilon> [] [] []\<close>
| Es_cons: \<open>B,\<epsilon> \<turnstile> e \<leadsto> e' : \<tau> \<Longrightarrow> wt_exps B \<epsilon> es es' \<tau>s \<Longrightarrow>
            wt_exps B \<epsilon> (e # es) (e' # es') (\<tau> # \<tau>s)\<close>

| C_op:    \<open>wt_head B \<epsilon> a a' \<tau>\<^sub>0 \<Longrightarrow> wt_args B \<epsilon> \<tau>\<^sub>0 as as' \<tau> \<Longrightarrow>
            wt_chain B \<epsilon> e e' oprs \<tau>s \<Longrightarrow>
            wt_chain B \<epsilon> (EOp (a # as) opr e) (EOp (a' # as') opr e') (opr # oprs) (\<tau> # \<tau>s)\<close>
| C_last:  \<open>\<not> is_eop e \<Longrightarrow> B,\<epsilon> \<turnstile> e \<leadsto> e' : \<tau> \<Longrightarrow> wt_chain B \<epsilon> e e' [] [\<tau>]\<close>

| M_nil:   \<open>wt_arms B \<epsilon> \<tau>\<^sub>0 [] [] \<tau>\<close>
| M_cons:  \<open>wtp B p \<tau>\<^sub>p \<Gamma> \<Longrightarrow> \<tau>\<^sub>p \<simeq> \<tau>\<^sub>0 \<Longrightarrow> (binders \<Gamma> @ B),\<epsilon> \<turnstile> b \<leadsto> b' : \<tau>' \<Longrightarrow> \<tau>' \<simeq> \<tau> \<Longrightarrow>
            wt_arms B \<epsilon> \<tau>\<^sub>0 arms arms' \<tau> \<Longrightarrow>
            wt_arms B \<epsilon> \<tau>\<^sub>0 ((p, b) # arms) ((p, b') # arms') \<tau>\<close>

| Cl_nil:  \<open>wt_cls B \<epsilon> nm \<tau> targs [] [] \<tau>\<close>
| Cl_op:   \<open>tlookup B [n_txt opn] = Some (TEop l eps \<tau>\<^sub>1 \<tau>\<^sub>2) \<Longrightarrow>
            targs = tuple args \<Longrightarrow> length args = length eps \<Longrightarrow>
            \<tau>\<^sub>1' = op_inst eps args \<tau>\<^sub>1 \<Longrightarrow> \<tau>\<^sub>2' = op_inst eps args \<tau>\<^sub>2 \<Longrightarrow>
            wtps B ps \<tau>s \<Gamma> \<Longrightarrow> fn_ty \<tau>s \<simeq> \<tau>\<^sub>1' \<Longrightarrow> covers B (fn_ty \<tau>s) [fn_pat ps] \<Longrightarrow>
            \<epsilon>' \<approx> (if nm then \<epsilon> else rext (hlabels B cls) \<epsilon>) \<Longrightarrow>
            \<Gamma>' = (case k of None \<Rightarrow> binders \<Gamma>
                   | Some kn \<Rightarrow> (n_txt kn, TEval (kmono (TFn \<tau>\<^sub>2' \<epsilon>' \<tau>\<^sub>0))) # binders \<Gamma>) \<Longrightarrow>
            (\<Gamma>' @ B),\<epsilon>' \<turnstile> b \<leadsto> b' : \<tau>\<^sub>b \<Longrightarrow>
            \<tau>\<^sub>b \<simeq> (case k of None \<Rightarrow> \<tau>\<^sub>2' | Some _ \<Rightarrow> \<tau>\<^sub>0) \<Longrightarrow>
            wt_cls B \<epsilon> nm \<tau>\<^sub>0 targs cls cls' \<tau> \<Longrightarrow>
            (case k of None \<Rightarrow> True | Some kn \<Rightarrow> n_txt kn \<notin> set (map fst \<Gamma>) \<and> nm_ok (n_txt kn)) \<Longrightarrow>
            wt_cls B \<epsilon> nm \<tau>\<^sub>0 targs (HOp opn ps k b # cls) (HOp opn ps k b' # cls') \<tau>\<close>
| Cl_ret:  \<open>wtp B p \<tau>\<^sub>p \<Gamma> \<Longrightarrow> \<tau>\<^sub>p \<simeq> \<tau>\<^sub>0 \<Longrightarrow> covers B \<tau>\<^sub>0 [p] \<Longrightarrow>
            \<epsilon>' \<approx> (if nm then \<epsilon> else rext (hlabels B cls) \<epsilon>) \<Longrightarrow>
            (binders \<Gamma> @ B),\<epsilon>' \<turnstile> b \<leadsto> b' : \<tau>' \<Longrightarrow>
            wt_cls B \<epsilon> nm \<tau>' targs cls cls' \<tau> \<Longrightarrow> nm \<longrightarrow> hlabels B cls = [] \<Longrightarrow>
            wt_cls B \<epsilon> nm \<tau>\<^sub>0 targs (HRet p b # cls) (HRet p b' # cls') \<tau>\<close>
| Cl_fin:  \<open>B,\<epsilon> \<turnstile> b \<leadsto> b' : \<tau>\<^sub>f \<Longrightarrow> \<tau>\<^sub>f \<simeq> unit_ty \<Longrightarrow> wt_cls B \<epsilon> nm \<tau>\<^sub>0 targs cls cls' \<tau> \<Longrightarrow>
            wt_cls B \<epsilon> nm \<tau>\<^sub>0 targs (HFin b # cls) (HFin b' # cls') \<tau>\<close>

| Al_nil:  \<open>wt_alts B \<epsilon> [] [] \<tau>\<close>
| Al_cons: \<open>wt_exps B \<epsilon> gs gs' \<tau>s \<Longrightarrow> \<forall>\<tau>\<^sub>g \<in> set \<tau>s. \<tau>\<^sub>g \<simeq> TC bool_ty [] \<Longrightarrow>
            B,\<epsilon> \<turnstile> e \<leadsto> e' : \<tau>\<^sub>e \<Longrightarrow> \<tau>\<^sub>e \<simeq> \<tau> \<Longrightarrow> wt_alts B \<epsilon> alts alts' \<tau> \<Longrightarrow>
            wt_alts B \<epsilon> ((gs, e) # alts) ((gs', e') # alts') \<tau>\<close>

subsection \<open>Declarations and modules\<close>

text \<open>\<open>B \<turnstile>\<^sub>d ds \<leadsto> ds' : E\<close>: under basis \<open>B\<close> and label prefix \<open>pre\<close>, the
  declarations produce the entries \<open>E\<close>, consed onto \<open>B\<close> for the rest,
  and elaborate to \<open>ds'\<close>. One rule per declaration and module form
  \<^cite>\<open>\<open>Sect. 5.7, App. A\<close> in milner1997\<close>:

    \<^item> a value binding is typed under the closed ambient row, nothing
      captures a top-level frame, and generalised under the value restriction
      \<^cite>\<open>wright1995\<close>: a non-value is bound at its type only, and rejected
      when that type has free variables (as SML does at top level);
      a \<open>fn\<close> right-hand side is recursive, its own name monomorphic in
      scope (\<open>elab_rhs\<close>); an ascription is checked by generality and
      becomes the binding's scheme \<^cite>\<open>\<open>Sect. 4.6\<close> in milner1997\<close>;
    \<^item> a function declaration is its lowering (\<^const>\<open>dsg_decl\<close>);
    \<^item> a datatype allocates a stamp that lists its constructors; an effect
      allocates the flat labels \<open>pre.E.op\<close> the elaborator performs on;
    \<^item> a functor is typed once against its parameter signatures, with
      fresh stamps, into a functor signature (\<open>\<Phi>\<close> of
      \<^cite>\<open>\<open>Sect. 5.7\<close> in milner1997\<close>); application realises the parameters' stamps
      from the argument and renames the result's stamps afresh, which is
      generativity per application. The functor and the argument are
      typed independently in the same basis, and the stamps each adds to
      it are distinct; the argument mentions no stamp the functor binds (its
      parameters' or its result's); the result's fresh stamps avoid the
      argument's, the functor's and the basis's. The elaborator interprets
      the body per application; the typed body is the one it interprets;
    \<^item> effects declared inside a functor body are not supported.\<close>

text \<open>The prefix under which a functor body and the argument of an application
  (\<open>Mo_app\<close>) are typed. No effect (\<open>D_eff\<close>), signature (\<open>D_sig\<close>) or foreign
  declaration (\<open>D_extern\<close>) may be declared under it: a body is interpreted afresh
  at every application, at a prefix of the application's own choosing.\<close>

definition functor_pre :: name where
  \<open>functor_pre = str ''%functor''\<close>

text \<open>Parameters of a functor: each signature elaborated in turn, earlier
  parameters in scope for later ones, bound stamps fresh.\<close>

fun params_stat ::
  \<open>tenv \<Rightarrow> nat \<Rightarrow> (nm \<times> msig) list \<Rightarrow> ((name \<times> sigsem) list \<times> tenv \<times> nat) option\<close>
where
  \<open>params_stat B n [] = Some ([], B, n)\<close>
| \<open>params_stat B n ((x, sg) # ps) =
     sig_stat B n sg \<bind> (\<lambda>((T, E), n\<^sub>1).
       (let K = [n\<^sub>1 ..< n\<^sub>1 + length T]; E\<^sub>K = real_env (rename_stamps E T K) E
        in if sig_ok_seal T K E
           then params_stat ((n_txt x, TEstr E\<^sub>K) # B) (n\<^sub>1 + length T) ps \<bind> (\<lambda>(ps', B', n').
                  Some ((n_txt x, (K, E\<^sub>K)) # ps', B', n'))
           else None))\<close>

text \<open>The binders of the functors of an environment, at any depth: a functor binds its
  parameters' stamps and its result's, and the binders of the functors inside them.\<close>

fun fbnds :: \<open>tenv \<Rightarrow> nat set\<close> and
  fbnds_ent :: \<open>tentry \<Rightarrow> nat set\<close>
where
  \<open>fbnds [] = {}\<close>
| \<open>fbnds ((x, e) # E) = fbnds_ent e \<union> fbnds E\<close>
| \<open>fbnds_ent (TEstr E) = fbnds E\<close>
| \<open>fbnds_ent (TEinst E) = fbnds E\<close>
| \<open>fbnds_ent (TEfun ps (T, E)) = \<Union> (set (map (\<lambda>(x, T, E). set T \<union> fbnds E) ps)) \<union> set T \<union> fbnds E\<close>
| \<open>fbnds_ent (TEsig (T, E)) = fbnds E\<close>
| \<open>fbnds_ent _ = {}\<close>

text \<open>The stamps a functor signature binds: its parameters' and its result's, and
  those of the functors nested in them.\<close>

definition fun_binders :: \<open>(name \<times> sigsem) list \<Rightarrow> sigsem \<Rightarrow> nat set\<close> where
  \<open>fun_binders ps res = fbnds_ent (TEfun ps res)\<close>

text \<open>Functor application: match the argument against the first parameter,
  realise, and either instantiate the result with fresh stamps or keep the
  remaining parameters.\<close>

definition fun_app :: \<open>(name \<times> sigsem) list \<Rightarrow> sigsem \<Rightarrow> tenv \<Rightarrow> nat list \<Rightarrow> tentry option\<close> where
  \<open>fun_app ps res E\<^sub>a K' =
     (case ps of
        [] \<Rightarrow> None
      | (px, (K, E\<^sub>p)) # ps' \<Rightarrow>
          match_sig E\<^sub>a K E\<^sub>p \<bind> (\<lambda>\<phi>.
            (if enrich E\<^sub>a (real_env \<phi> E\<^sub>p)
             then (case ps' of
                     [] \<Rightarrow> (case res of (T', E') \<Rightarrow>
                              (if length K' = length T'
                               then Some (TEstr (real_env (rename_stamps E' T' K') (real_env \<phi> E')))
                               else None))
                   | _ \<Rightarrow> Some (TEfun (map (\<lambda>(x, (T, E)). (x, (T, real_env \<phi> E))) ps')
                                     (case res of (T', E') \<Rightarrow> (T', real_env \<phi> E'))))
             else None)))\<close>

text \<open>A type or an effect entry is invisible to the elaborator: a gap in the
  environment it keeps. A declaration must not hide a constructor or a
  fixity behind a gap.\<close>

fun is_gap :: \<open>tentry \<Rightarrow> bool\<close> where
  \<open>is_gap (TEtyp _) = True\<close>
| \<open>is_gap (TEeff _ _ _) = True\<close>
| \<open>is_gap _ = False\<close>

definition shadow_ok :: \<open>tenv \<Rightarrow> name \<Rightarrow> bool\<close> where
  \<open>shadow_ok B x \<longleftrightarrow>
     (case map_of B x of Some (TEcon _ _) \<Rightarrow> False | Some (TEfix _ _) \<Rightarrow> False | _ \<Rightarrow> True)\<close>

definition gaps_ok :: \<open>tenv \<Rightarrow> tenv \<Rightarrow> bool\<close> where
  \<open>gaps_ok E B \<longleftrightarrow> (\<forall>x e. map_of E x = Some e \<longrightarrow> is_gap e \<longrightarrow> shadow_ok B x)\<close>

lemma gaps_ok_code [code]:
  \<open>gaps_ok E B = list_all (\<lambda>(x, e). is_gap e \<longrightarrow> map_of E x = Some e \<longrightarrow> shadow_ok B x) E\<close>
  unfolding gaps_ok_def list_all_iff by (auto dest: map_of_SomeD)

text \<open>The elaborator identifies a declaration by its flat name, its label
  prefix or its module prefix, and binds those dynamically. The rules forbid
  the rebindings an alias could outlive:

    \<^item> a structure or instance name is never rebound, and never binds the
      name of a functor (\<open>fresh_mod\<close>);
    \<^item> an effect's label prefix is never rebound (\<^const>\<open>eff_lookup\<close>);
    \<^item> a value or constructor name is not rebound once a functor has been
      declared since any of its bindings (\<open>rebind_ok\<close>);
    \<^item> a functor parameter carries no effects (\<open>eff_free\<close>).

  A generative naming of bindings would lift these restrictions.\<close>

fun mod_ent :: \<open>tentry \<Rightarrow> bool\<close> where
  \<open>mod_ent (TEstr _) = True\<close>
| \<open>mod_ent (TEinst _) = True\<close>
| \<open>mod_ent _ = False\<close>

fun fun_ent :: \<open>tentry \<Rightarrow> bool\<close> where
  \<open>fun_ent (TEfun _ _) = True\<close>
| \<open>fun_ent _ = False\<close>

definition fresh_mod :: \<open>tenv \<Rightarrow> name \<Rightarrow> bool\<close> where
  \<open>fresh_mod B x \<longleftrightarrow> (\<forall>e \<in> set B. fst e = x \<longrightarrow> \<not> mod_ent (snd e) \<and> \<not> fun_ent (snd e))\<close>

fun fun_free_ent :: \<open>tentry \<Rightarrow> bool\<close> and
  fun_free :: \<open>tenv \<Rightarrow> bool\<close>
where
  \<open>fun_free_ent (TEfun _ _) = False\<close>
| \<open>fun_free_ent (TEstr E) = fun_free E\<close>
| \<open>fun_free_ent (TEinst E) = fun_free E\<close>
| \<open>fun_free_ent _ = True\<close>
| \<open>fun_free [] = True\<close>
| \<open>fun_free ((x, e) # B) = (fun_free_ent e \<and> fun_free B)\<close>

fun val_con :: \<open>tentry \<Rightarrow> bool\<close> where
  \<open>val_con (TEval _) = True\<close>
| \<open>val_con (TEcon _ _) = True\<close>
| \<open>val_con _ = False\<close>

text \<open>Every earlier value or constructor binding of the name counts, not only the
  most recent entry under it.\<close>

definition rebind_ok :: \<open>tenv \<Rightarrow> name \<Rightarrow> bool\<close> where
  \<open>rebind_ok B x \<longleftrightarrow>
     list_all (\<lambda>i. fst (B ! i) = x \<and> val_con (snd (B ! i)) \<longrightarrow> fun_free (take i B)) [0 ..< length B]\<close>

lemma rebind_ok_split:
  \<open>rebind_ok B x \<longleftrightarrow> (\<forall>B\<^sub>1 e B\<^sub>2. B = B\<^sub>1 @ (x, e) # B\<^sub>2 \<longrightarrow> val_con e \<longrightarrow> fun_free B\<^sub>1)\<close>
proof (intro iffI)
  assume r: \<open>rebind_ok B x\<close>
  show \<open>\<forall>B\<^sub>1 e B\<^sub>2. B = B\<^sub>1 @ (x, e) # B\<^sub>2 \<longrightarrow> val_con e \<longrightarrow> fun_free B\<^sub>1\<close>
  proof (intro allI impI)
    fix B\<^sub>1 e B\<^sub>2 assume b: \<open>B = B\<^sub>1 @ (x, e) # B\<^sub>2\<close> and v: \<open>val_con e\<close>
    have l: \<open>length B\<^sub>1 \<in> set [0 ..< length B]\<close> \<open>B ! length B\<^sub>1 = (x, e)\<close> \<open>take (length B\<^sub>1) B = B\<^sub>1\<close>
      using b by simp_all
    have \<open>fst (B ! length B\<^sub>1) = x \<and> val_con (snd (B ! length B\<^sub>1)) \<longrightarrow> fun_free (take (length B\<^sub>1) B)\<close>
      using r l(1) unfolding rebind_ok_def list_all_iff by blast
    then show \<open>fun_free B\<^sub>1\<close> using l(2,3) v by simp
  qed
next
  assume s: \<open>\<forall>B\<^sub>1 e B\<^sub>2. B = B\<^sub>1 @ (x, e) # B\<^sub>2 \<longrightarrow> val_con e \<longrightarrow> fun_free B\<^sub>1\<close>
  show \<open>rebind_ok B x\<close> unfolding rebind_ok_def list_all_iff
  proof (intro ballI impI)
    fix i assume i: \<open>i \<in> set [0 ..< length B]\<close> and c: \<open>fst (B ! i) = x \<and> val_con (snd (B ! i))\<close>
    have b: \<open>B ! i = (x, snd (B ! i))\<close> using c by (simp add: prod_eq_iff)
    have \<open>B = take i B @ (x, snd (B ! i)) # drop (Suc i) B\<close>
      using i id_take_nth_drop[of i B] b by simp
    then show \<open>fun_free (take i B)\<close> using s c by blast
  qed
qed

text \<open>A module-dependent arrow \<^const>\<open>TDep\<close> names its signature by its
  syntax, and every application re-elaborates that syntax in its own basis
  (\<^const>\<open>dep_env\<close>). So the signature of a binder is a name
  (\<^const>\<open>named_sig\<close>), a signature name is declared once in the whole program
  (\<open>fresh_sig\<close>), and a functor body declares no signature (\<open>sig_free\<close>).\<close>

fun has_sig :: \<open>name \<Rightarrow> tenv \<Rightarrow> bool\<close> and
  has_sig_ent :: \<open>name \<Rightarrow> name \<Rightarrow> tentry \<Rightarrow> bool\<close>
where
  \<open>has_sig x [] = False\<close>
| \<open>has_sig x ((y, e) # B) = (has_sig_ent x y e \<or> has_sig x B)\<close>
| \<open>has_sig_ent x y (TEsig (T, E)) = (x = y \<or> has_sig x E)\<close>
| \<open>has_sig_ent x y (TEstr E) = has_sig x E\<close>
| \<open>has_sig_ent x y (TEinst E) = has_sig x E\<close>
| \<open>has_sig_ent x y _ = False\<close>

definition fresh_sig :: \<open>tenv \<Rightarrow> name \<Rightarrow> bool\<close> where
  \<open>fresh_sig B x \<longleftrightarrow> \<not> has_sig x B\<close>

text \<open>The signature names a type mentions (\<open>tsigs\<close>): those of its module-dependent
  arrows. A let-bound value's type may only mention signatures in scope
  (\<open>sig_scope\<close>: declared in the basis, or already mentioned by one of its types).\<close>

fun sig_key :: \<open>msig \<Rightarrow> name set\<close> where
  \<open>sig_key (SPath p refs) = (if refs = [] then {last (path_nms p)} else {})\<close>
| \<open>sig_key sg = {}\<close>

fun tsigs :: \<open>kty \<Rightarrow> name set\<close> where
  \<open>tsigs (TC c ts) = \<Union>(set (map tsigs ts))\<close>
| \<open>tsigs (TApp t\<^sub>1 t\<^sub>2) = tsigs t\<^sub>1 \<union> tsigs t\<^sub>2\<close>
| \<open>tsigs (TFn t\<^sub>1 e t\<^sub>2) = tsigs t\<^sub>1 \<union> tsigs t\<^sub>2\<close>
| \<open>tsigs (TDep i sg m e t) = sig_key sg \<union> tsigs t\<close>
| \<open>tsigs (TEv l s t) = tsigs l \<union> tsigs s \<union> tsigs t\<close>
| \<open>tsigs (TAct l K e t) = tsigs l \<union> tsigs t\<close>
| \<open>tsigs t = {}\<close>

fun tsigs_sch :: \<open>scheme \<Rightarrow> name set\<close> where
  \<open>tsigs_sch (Sch t) = tsigs t\<close>
| \<open>tsigs_sch (Mono t) = tsigs t\<close>

fun tsigs_tydef :: \<open>tydef \<Rightarrow> name set\<close> where
  \<open>tsigs_tydef (TyAbs c k) = {}\<close>
| \<open>tsigs_tydef (TyFn ps t) = tsigs t\<close>

fun tsigs_ent :: \<open>tentry \<Rightarrow> name set\<close> and
  tsigs_env :: \<open>tenv \<Rightarrow> name set\<close>
where
  \<open>tsigs_ent (TEval \<sigma>) = tsigs_sch \<sigma>\<close>
| \<open>tsigs_ent (TEcon \<sigma> n) = tsigs_sch \<sigma>\<close>
| \<open>tsigs_ent (TEtyp d) = tsigs_tydef d\<close>
| \<open>tsigs_ent (TEstr ex) = tsigs_env ex\<close>
| \<open>tsigs_ent (TEfun ps (T, E)) =
     \<Union>(set (map (\<lambda>(x, T, E). tsigs_env E) ps)) \<union> tsigs_env E\<close>
| \<open>tsigs_ent (TEsig (T, E)) = tsigs_env E\<close>
| \<open>tsigs_ent (TEfix f p) = {}\<close>
| \<open>tsigs_ent (TEinst ex) = tsigs_env ex\<close>
| \<open>tsigs_ent (TEop l ps t\<^sub>1 t\<^sub>2) = tsigs t\<^sub>1 \<union> tsigs t\<^sub>2\<close>
| \<open>tsigs_ent (TEffi s \<sigma>) = tsigs_sch \<sigma>\<close>
| \<open>tsigs_ent (TEeff l ls ar) = {}\<close>
| \<open>tsigs_env [] = {}\<close>
| \<open>tsigs_env ((x, e) # ex) = tsigs_ent e \<union> tsigs_env ex\<close>

lemmas tsigs_ent_induct = tsigs_ent_tsigs_env.induct[named_cases tsigs_ent]

definition sig_scope :: \<open>tenv \<Rightarrow> name set\<close> where
  \<open>sig_scope B = {S. has_sig S B} \<union> tsigs_env B\<close>

fun sig_free_ent :: \<open>tentry \<Rightarrow> bool\<close> and
  sig_free :: \<open>tenv \<Rightarrow> bool\<close>
where
  \<open>sig_free_ent (TEsig _) = False\<close>
| \<open>sig_free_ent (TEstr E) = sig_free E\<close>
| \<open>sig_free_ent (TEinst E) = sig_free E\<close>
| \<open>sig_free_ent _ = True\<close>
| \<open>sig_free [] = True\<close>
| \<open>sig_free ((x, e) # E) = (sig_free_ent e \<and> sig_free E)\<close>

fun eff_free_ent :: \<open>tentry \<Rightarrow> bool\<close> and
  eff_free :: \<open>tenv \<Rightarrow> bool\<close>
where
  \<open>eff_free_ent (TEop _ _ _ _) = False\<close>
| \<open>eff_free_ent (TEeff _ _ _) = False\<close>
| \<open>eff_free_ent (TEstr E) = eff_free E\<close>
| \<open>eff_free_ent (TEinst E) = eff_free E\<close>
| \<open>eff_free_ent _ = True\<close>
| \<open>eff_free [] = True\<close>
| \<open>eff_free ((x, e) # E) = (eff_free_ent e \<and> eff_free E)\<close>

text \<open>Well-formed signature environments: the members a dictionary carries
  are identifiers, and no entry is foreign, an instance, a signature or a
  functor. The declaration of a signature demands it.\<close>

fun sig_wf :: \<open>tenv \<Rightarrow> bool\<close> and
  sig_wf_ent :: \<open>name \<Rightarrow> tentry \<Rightarrow> bool\<close>
where
  \<open>sig_wf [] = True\<close>
| \<open>sig_wf ((x, e) # E) = (sig_wf_ent x e \<and> sig_wf E)\<close>
| \<open>sig_wf_ent x (TEval \<sigma>) = (nm_ok x \<and> is_sch \<sigma>)\<close>
| \<open>sig_wf_ent x (TEcon \<sigma> n) = (nm_ok x \<and> is_sch \<sigma>)\<close>
| \<open>sig_wf_ent x (TEstr E) = (nm_ok x \<and> sig_wf E)\<close>
| \<open>sig_wf_ent x (TEtyp d) = True\<close>
| \<open>sig_wf_ent x (TEop l ps t\<^sub>1 t\<^sub>2) = True\<close>
| \<open>sig_wf_ent x (TEeff l ls ar) = True\<close>
| \<open>sig_wf_ent x (TEfix f p) = True\<close>
| \<open>sig_wf_ent x _ = False\<close>

text \<open>The declaration judgements also give the \<^emph>\<open>foreign declarations\<close> \<open>F\<close> of what
  they type: every \<open>extern\<close>, its symbol with the scheme it was declared at. Unlike
  the environment \<open>E\<close> the list forgets nothing: sealing hides an \<open>extern\<close> from
  the program, not from the host.\<close>

type_synonym fenv = \<open>(name \<times> scheme) list\<close>

text \<open>The judgements also thread a \<^emph>\<open>stamp counter\<close> \<open>j \<dots> j'\<close>, as the checker does:
  every stamp a derivation allocates (a datatype, a signature's or a functor's
  parameters, a sealing, the result names \<open>K'\<close> of an application) is drawn from it,
  above the stamps already allocated. The rules keep their freshness premises; the
  counter only adds the order of allocation, which a hidden datatype does not forget:
  a stamp that sealing removed from the environment still lies below the counter.\<close>

inductive
  wtd :: \<open>tenv \<Rightarrow> name \<Rightarrow> mdecl \<Rightarrow> mdecl \<Rightarrow> tenv \<Rightarrow> fenv \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool\<close> and
  wtds :: \<open>tenv \<Rightarrow> name \<Rightarrow> mdecl list \<Rightarrow> mdecl list \<Rightarrow> tenv \<Rightarrow> fenv \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool\<close> and
  wtm :: \<open>tenv \<Rightarrow> name \<Rightarrow> mexpr \<Rightarrow> mexpr \<Rightarrow> tentry \<Rightarrow> fenv \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool\<close>
where
  D_let:   \<open>\<not> is_fn e \<Longrightarrow> B,RNil \<turnstile> e \<leadsto> e' : \<tau> \<Longrightarrow>
            \<sigma> = gen B RNil \<tau> \<Longrightarrow>
            rebind_ok B (n_txt x) \<Longrightarrow>
            (ftv \<tau> \<subseteq> ftv_env B \<and> frv \<tau> \<subseteq> frv_env B) \<or> val_exp B e' \<Longrightarrow>
            btv \<tau> = {} \<Longrightarrow> brv \<tau> = {} \<Longrightarrow> nm_ok (n_txt x) \<Longrightarrow> ktv \<tau> \<subseteq> ktv_env B \<Longrightarrow>
            tsigs \<tau> \<subseteq> sig_scope B \<Longrightarrow> j \<le> j' \<Longrightarrow>
            wtd B pre (DLet x e) (DLet x e') [(n_txt x, TEval \<sigma>)] [] j j'\<close>
| D_letrec: \<open>is_fn e \<Longrightarrow> ((n_txt x, TEval (kmono \<tau>)) # B),RNil \<turnstile> e \<leadsto> e' : \<tau>' \<Longrightarrow> \<tau>' \<simeq> \<tau> \<Longrightarrow>
            \<sigma> = gen B RNil \<tau>' \<Longrightarrow>
            rebind_ok B (n_txt x) \<Longrightarrow>
            btv \<tau>' = {} \<Longrightarrow> brv \<tau>' = {} \<Longrightarrow> nm_ok (n_txt x) \<Longrightarrow> ktv \<tau>' \<subseteq> ktv_env B \<Longrightarrow>
            tsigs \<tau>' \<subseteq> sig_scope B \<Longrightarrow> j \<le> j' \<Longrightarrow>
            wtd B pre (DLet x e) (DLet x e') [(n_txt x, TEval \<sigma>)] [] j j'\<close>
| D_fun:   \<open>cls \<noteq> [] \<Longrightarrow> wtd B pre (dsg_decl (DFun f mbs cls)) d' E F j j' \<Longrightarrow>
            wtd B pre (DFun f mbs cls) d' E F j j'\<close>
| D_extern: \<open>ty_stat B True ([], []) n ty = Some (\<tau>, ve, n') \<Longrightarrow> (\<exists>t\<^sub>1 e t\<^sub>2. \<tau> = TFn t\<^sub>1 e t\<^sub>2) \<Longrightarrow>
            take (length functor_pre) pre \<noteq> functor_pre \<Longrightarrow> j \<le> j' \<Longrightarrow>
            wtd B pre (DExtern x ty sy) (DExtern x ty sy)
                [(n_txt x, TEffi (n_txt sy) (close_sch (set [n ..< n']) (set [n ..< n']) \<tau>))]
                [(n_txt sy, close_sch (set [n ..< n']) (set [n ..< n']) \<tau>)] j j'\<close>
| D_type:  \<open>distinct ps \<Longrightarrow> length ps = length as \<Longrightarrow>
            ty_stat B False (zip (map n_txt as) (map TV ps), []) n ty = Some (\<tau>, ve, n') \<Longrightarrow> j \<le> j' \<Longrightarrow>
            wtd B pre (DType t as ty) (DType t as ty)
              [(n_txt t, TEtyp (TyFn ps (close_ty (set ps) {} \<tau>)))] [] j j'\<close>
| D_data:  \<open>k \<notin> stamps_env B \<Longrightarrow> distinct (map (n_txt \<circ> fst) alts) \<Longrightarrow>
            c = (k, n_txt t, map (\<lambda>(cn, args). (n_txt cn, length args)) alts) \<Longrightarrow>
            distinct ps \<Longrightarrow> length ps = length as \<Longrightarrow>
            cons_stat ((n_txt t, TEtyp (TyAbs c (length as))) # B)
              (zip (map n_txt as) (map TV ps), []) ps c n alts = Some (cs, n') \<Longrightarrow>
            list_all (\<lambda>(cn, _). rebind_ok B (n_txt cn)) alts \<Longrightarrow>
            list_all (\<lambda>(cn, _). nm_ok (n_txt cn)) alts \<Longrightarrow> j \<le> k \<Longrightarrow> k < j' \<Longrightarrow>
            wtd B pre (DData t as alts) (DData t as alts)
              (cs @ [(n_txt t, TEtyp (TyAbs c (length as)))]) [] j j'\<close>
| D_fix:   \<open>read_nat (n_txt prec) = Some p \<Longrightarrow> j \<le> j' \<Longrightarrow>
            wtd B pre (DFix f prec opr) (DFix f prec opr)
              [(fix_key (n_txt opr), TEfix f p)] [] j j'\<close>
| D_eff:   \<open>distinct (map n_txt as) \<Longrightarrow> take (length functor_pre) pre \<noteq> functor_pre \<Longrightarrow>
            ops_stat B (mangle pre (n_txt x)) (eff_ps as n) (eff_ve as n) (n + length as) ops =
              Some (es, n') \<Longrightarrow>
            eff_lookup B (mangle pre (n_txt x)) = None \<Longrightarrow>
            nm_ok (n_txt x) \<Longrightarrow> list_all (\<lambda>(opn, _). nm_ok (n_txt opn)) ops \<Longrightarrow> j \<le> j' \<Longrightarrow>
            wtd B pre (DEff x as ops) (DEff x as ops)
              (es @ [(n_txt x, TEeff (mangle pre (n_txt x)) (map fst es) (length as))])
              [] j j'\<close>
| D_mod:   \<open>wtm B (mangle pre (n_txt x)) m m' (TEstr E) F j j\<^sub>1 \<Longrightarrow>
            sealo_stat B n so E = Some (E', n') \<Longrightarrow> set [n ..< n'] \<inter> stamps_env B = {} \<Longrightarrow>
            fresh_mod B (n_txt x) \<Longrightarrow> nm_ok (n_txt x) \<Longrightarrow> j\<^sub>1 \<le> n \<Longrightarrow> n' \<le> j' \<Longrightarrow>
            wtd B pre (DMod x [] so m) (DMod x [] so m') [(n_txt x, TEstr E')] F j j'\<close>
| D_modfun: \<open>wtm B (mangle pre (n_txt x)) m m' (TEfun ps res) F j j' \<Longrightarrow> nm_ok (n_txt x) \<Longrightarrow>
            wtd B pre (DMod x [] None m) (DMod x [] None m') [(n_txt x, TEfun ps res)] F j j'\<close>
| D_functor: \<open>params_stat B n (q # qs) = Some (ps, B\<^sub>p, n\<^sub>1) \<Longrightarrow> set [n ..< n\<^sub>1] \<inter> stamps_env B = {} \<Longrightarrow>
            wtm B\<^sub>p functor_pre m m' (TEstr E) F j\<^sub>1 j\<^sub>2 \<Longrightarrow>
            sealo_stat B\<^sub>p n\<^sub>2 so E = Some (E', n') \<Longrightarrow> set [n\<^sub>2 ..< n'] \<inter> stamps_env B\<^sub>p = {} \<Longrightarrow>
            T' = filter (\<lambda>k. k \<notin> stamps_env B\<^sub>p) (sorted_list_of_set (stamps_env E')) \<Longrightarrow>
            list_all (\<lambda>(y, T, E). eff_free E) ps \<Longrightarrow> sig_free E' \<Longrightarrow>
            list_all (\<lambda>(y, _). nm_ok (n_txt y)) (q # qs) \<Longrightarrow> res_names E' T' \<Longrightarrow>
            j \<le> n \<Longrightarrow> n\<^sub>1 \<le> j\<^sub>1 \<Longrightarrow> j\<^sub>2 \<le> n\<^sub>2 \<Longrightarrow> n' \<le> j' \<Longrightarrow>
            wtd B pre (DMod x (q # qs) so m) (DMod x (q # qs) so m')
              [(n_txt x, TEfun ps (T', E'))] F j j'\<close>
| D_impl:  \<open>wtm B (mangle pre (n_txt x)) m m' (TEstr E) F j j\<^sub>1 \<Longrightarrow>
            sealo_stat B n so E = Some (E', n') \<Longrightarrow> set [n ..< n'] \<inter> stamps_env B = {} \<Longrightarrow>
            fresh_mod B (n_txt x) \<Longrightarrow> nm_ok (n_txt x) \<Longrightarrow> j\<^sub>1 \<le> n \<Longrightarrow> n' \<le> j' \<Longrightarrow>
            wtd B pre (DImpl x [] so m) (DImpl x [] so m') [(n_txt x, TEinst E')] F j j'\<close>
| D_implfun: \<open>wtm B (mangle pre (n_txt x)) m m' (TEfun ps res) F j j' \<Longrightarrow> nm_ok (n_txt x) \<Longrightarrow>
            wtd B pre (DImpl x [] None m) (DImpl x [] None m') [(n_txt x, TEfun ps res)] F j j'\<close>
| D_implfunctor: \<open>params_stat B n (q # qs) = Some (ps, B\<^sub>p, n\<^sub>1) \<Longrightarrow>
            set [n ..< n\<^sub>1] \<inter> stamps_env B = {} \<Longrightarrow>
            wtm B\<^sub>p functor_pre m m' (TEstr E) F j\<^sub>1 j\<^sub>2 \<Longrightarrow>
            sealo_stat B\<^sub>p n\<^sub>2 so E = Some (E', n') \<Longrightarrow> set [n\<^sub>2 ..< n'] \<inter> stamps_env B\<^sub>p = {} \<Longrightarrow>
            T' = filter (\<lambda>k. k \<notin> stamps_env B\<^sub>p) (sorted_list_of_set (stamps_env E')) \<Longrightarrow>
            list_all (\<lambda>(y, T, E). eff_free E) ps \<Longrightarrow> sig_free E' \<Longrightarrow>
            list_all (\<lambda>(y, _). nm_ok (n_txt y)) (q # qs) \<Longrightarrow> res_names E' T' \<Longrightarrow>
            j \<le> n \<Longrightarrow> n\<^sub>1 \<le> j\<^sub>1 \<Longrightarrow> j\<^sub>2 \<le> n\<^sub>2 \<Longrightarrow> n' \<le> j' \<Longrightarrow>
            wtd B pre (DImpl x (q # qs) so m) (DImpl x (q # qs) so m')
              [(n_txt x, TEfun ps (T', E'))] F j j'\<close>
| D_sig:   \<open>sig_stat B n sg = Some (\<Sigma>, n') \<Longrightarrow> set [n ..< n'] \<inter> stamps_env B = {} \<Longrightarrow>
            fresh_sig B (n_txt x) \<Longrightarrow> sig_wf (snd \<Sigma>) \<Longrightarrow> take (length functor_pre) pre \<noteq> functor_pre \<Longrightarrow>
            j \<le> n \<Longrightarrow> n' \<le> j' \<Longrightarrow> wtd B pre (DSig x sg) (DSig x sg) [(n_txt x, TEsig \<Sigma>)] [] j j'\<close>
| D_open:  \<open>tlookup B (path_nms p) = Some (TEstr E) \<Longrightarrow> j \<le> j' \<Longrightarrow>
            wtd B pre (DOpen p) (DOpen p) E [] j j'\<close>
| D_inc:   \<open>wtm B pre m m' (TEstr E) F j j' \<Longrightarrow> wtd B pre (DInc m) (DInc m') E F j j'\<close>

| Ds_nil:  \<open>wtds B pre [] [] [] [] j j\<close>
| Ds_cons: \<open>wtd B pre d d' E F j j\<^sub>1 \<Longrightarrow> gaps_ok E B \<Longrightarrow> wtds (E @ B) pre ds ds' E\<^sub>1 F\<^sub>1 j\<^sub>1 j' \<Longrightarrow>
            wtds B pre (d # ds) (d' # ds') (E\<^sub>1 @ E) (F\<^sub>1 @ F) j j'\<close>

| Mo_path: \<open>tlookup B (path_nms p) = Some ent \<Longrightarrow> wtm B pre (MPath p) (MPath p) ent [] j j\<close>
| Mo_struct: \<open>wtds B pre ds ds' E F j j' \<Longrightarrow> wtm B pre (MStruct ds) (MStruct ds') (TEstr E) F j j'\<close>
| Mo_app:  \<open>wtm B pre f f' (TEfun ((px, \<Sigma>\<^sub>p) # ps) res) F\<^sub>f j j\<^sub>1 \<Longrightarrow>
            wtm B (mangle functor_pre px) a a' (TEstr E\<^sub>a) F\<^sub>a j\<^sub>1 j\<^sub>2 \<Longrightarrow>
            fun_app ((px, \<Sigma>\<^sub>p) # ps) res E\<^sub>a K' = Some ent \<Longrightarrow>
            distinct K' \<Longrightarrow>
            set K' \<inter> (stamps_env (E\<^sub>a @ B) \<union> stamps_ent (TEfun ((px, \<Sigma>\<^sub>p) # ps) res)) = {} \<Longrightarrow>
            stamps_ent (TEfun ((px, \<Sigma>\<^sub>p) # ps) res) \<inter> stamps_env E\<^sub>a \<subseteq> stamps_env B \<Longrightarrow>
            fun_binders ((px, \<Sigma>\<^sub>p) # ps) res \<inter> stamps_env E\<^sub>a = {} \<Longrightarrow>
            j\<^sub>2 \<le> j' \<Longrightarrow> set K' \<subseteq> {j\<^sub>2 ..< j'} \<Longrightarrow>
            wtm B pre (MApp f a) (MApp f' a') ent (F\<^sub>a @ F\<^sub>f) j j'\<close>
| Mo_seal: \<open>wtm B pre m m' (TEstr E) F j j\<^sub>1 \<Longrightarrow> seal_stat B n sg E = Some (E', n') \<Longrightarrow>
            set [n ..< n'] \<inter> stamps_env B = {} \<Longrightarrow> j\<^sub>1 \<le> n \<Longrightarrow> n' \<le> j' \<Longrightarrow>
            wtm B pre (MSeal m sg) (MSeal m' sg) (TEstr E') F j j'\<close>

subsection \<open>The initial basis and the top-level judgement\<close>

text \<open>The static twin of the elaborator's \<open>prelude\<close>: the booleans, the list
  constructors, and the built-in types by name.\<close>

definition tbase :: tenv where
  \<open>tbase = [
    (str ''True'', TEcon (kmono (TC bool_ty [])) 0),
    (str ''False'', TEcon (kmono (TC bool_ty [])) 0),
    (str ''Nil'', TEcon (Sch (TC list_ty [TB 0])) 0),
    (str ''Cons'',
     TEcon (Sch (TFn (TB 0) (RB 1) (TFn (TC list_ty [TB 0]) (RB 2) (TC list_ty [TB 0])))) 2),
    (str ''bool'', TEtyp (TyAbs bool_ty 0)),
    (str ''list'', TEtyp (TyAbs list_ty 1)),
    (str ''int'', TEtyp (TyAbs int_ty 0)),
    (str ''f64'', TEtyp (TyAbs f64_ty 0)),
    (str ''string'', TEtyp (TyAbs string_ty 0)),
    (str ''char'', TEtyp (TyAbs char_ty 0))
  ] @ map (\<lambda>k. (fst (snd (sfx_ty k)), TEtyp (TyAbs (sfx_ty k) 0)))
        [I8, I16, I32, I64, U8, U16, U32, U64]\<close>

text \<open>A program is a whole unit: it must bind \<open>main\<close> at the top level; the
  output is the explicit program. This is the \<^text>\<open>has_type\<close> of the \<^text>\<open>type_system\<close>
  locale.\<close>

definition has_main :: \<open>mdecl list \<Rightarrow> bool\<close> where
  \<open>has_main ds \<longleftrightarrow> list_ex (\<lambda>d. case d of DLet x _ \<Rightarrow> n_txt x = str ''main'' | _ \<Rightarrow> False) ds\<close>

definition has_type :: \<open>tenv \<Rightarrow> mdecl list \<Rightarrow> mdecl list \<Rightarrow> tenv \<Rightarrow> fenv \<Rightarrow> bool\<close> where
  \<open>has_type B ds ds' B' F \<longleftrightarrow>
     (\<exists>E j j'. stamps_env B \<subseteq> {..<j} \<and> wtds B [] ds ds' E F j j' \<and> B' = E @ B \<and> has_main ds')\<close>

subsection \<open>The variables of a realised environment\<close>

text \<open>Realising an environment adds at most the variables of the realisation;
  the parameter environment of a binder and the realisation \<open>dep_vars\<close> plants
  add none but the binder's stamps.\<close>

lemma frv_brsubst: \<open>frv_row (brsubst \<rho> r) = frv_row r \<union> (\<Union>v\<in>brv_row r. frv_row (\<rho> v))\<close>
  by (induction r) auto

lemma ftv_bsubst: \<open>ftv (bsubst \<theta> \<rho> t) = ftv t \<union> (\<Union>a\<in>btv t. ftv (\<theta> a))\<close>
  by (induction t) auto

lemma frv_bsubst:
  \<open>frv (bsubst \<theta> \<rho> t) = frv t \<union> (\<Union>a\<in>btv t. frv (\<theta> a)) \<union> (\<Union>v\<in>brv t. frv_row (\<rho> v))\<close>
  by (induction t) (auto simp: frv_brsubst)

lemma ktv_bsubst: \<open>ktv (bsubst \<theta> \<rho> t) \<subseteq> ktv t \<union> (\<Union>a\<in>btv t. ktv (\<theta> a))\<close>
proof (induction t)
  case (TC c ts) then show ?case by fastforce
qed auto

lemma frv_bsubstl:
  \<open>frv (bsubstl \<theta> \<rho> t) = frv t \<union> (\<Union>a\<in>btv t. frv (\<theta> a)) \<union> (\<Union>v\<in>brv t. frv_row (\<rho> v))\<close>
  by (induction t arbitrary: \<theta>) (auto simp: frv_brsubst)

definition real_ktv :: \<open>realisation \<Rightarrow> tvar set\<close> where
  \<open>real_ktv \<phi> = (\<Union>(k, d) \<in> set \<phi>. ktv_tydef d)\<close>

definition real_ftv :: \<open>realisation \<Rightarrow> tvar set\<close> where
  \<open>real_ftv \<phi> = (\<Union>(k, d) \<in> set \<phi>. ftv_tydef d)\<close>

definition real_frv :: \<open>realisation \<Rightarrow> rvar set\<close> where
  \<open>real_frv \<phi> = (\<Union>(k, d) \<in> set \<phi>. frv_tydef d)\<close>

lemma map_of_real:
  assumes \<open>map_of \<phi> k = Some d\<close>
  shows \<open>ktv_tydef d \<subseteq> real_ktv \<phi> \<and> ftv_tydef d \<subseteq> real_ftv \<phi> \<and> frv_tydef d \<subseteq> real_frv \<phi>\<close>
  using assms by (auto simp: real_ktv_def real_ftv_def real_frv_def dest: map_of_SomeD)

lemma treal_vars:
  \<open>ftv (treal \<phi> t) \<subseteq> ftv t \<union> real_ftv \<phi>\<close> \<open>frv (treal \<phi> t) \<subseteq> frv t \<union> real_frv \<phi>\<close>
  \<open>ktv (treal \<phi> t) \<subseteq> ktv t \<union> real_ktv \<phi>\<close>
proof (induction t)
  case (TC c ts)
  have e: \<open>x \<in> ftv (treal \<phi> t) \<Longrightarrow> t \<in> set ts \<Longrightarrow> x \<in> \<Union>(ftv ` set ts) \<union> real_ftv \<phi>\<close>
    \<open>x \<in> frv (treal \<phi> t) \<Longrightarrow> t \<in> set ts \<Longrightarrow> x \<in> \<Union>(frv ` set ts) \<union> real_frv \<phi>\<close>
    \<open>x \<in> ktv (treal \<phi> t) \<Longrightarrow> t \<in> set ts \<Longrightarrow> x \<in> \<Union>(ktv ` set ts) \<union> real_ktv \<phi>\<close> for x t
    using TC.IH[of t] by blast+
  have ts: \<open>\<Union>(ftv ` set (map (treal \<phi>) ts)) \<subseteq> \<Union>(ftv ` set ts) \<union> real_ftv \<phi>\<close>
    \<open>\<Union>(frv ` set (map (treal \<phi>) ts)) \<subseteq> \<Union>(frv ` set ts) \<union> real_frv \<phi>\<close>
    \<open>\<Union>(ktv ` set (map (treal \<phi>) ts)) \<subseteq> \<Union>(ktv ` set ts) \<union> real_ktv \<phi>\<close>
    by (auto dest!: e)
  {
    fix ps b assume \<open>map_of \<phi> (stamp c) = Some (TyFn ps b)\<close>
    from map_of_real[OF this] have b: \<open>ktv b \<subseteq> real_ktv \<phi>\<close> \<open>ftv b \<subseteq> real_ftv \<phi>\<close>
      \<open>frv b \<subseteq> real_frv \<phi>\<close> by simp_all
    let ?\<theta> = \<open>\<lambda>a. case map_of (zip ps (map (treal \<phi>) ts)) a of Some t \<Rightarrow> t | None \<Rightarrow> unit_ty\<close>
    have \<theta>: \<open>ftv (?\<theta> a) \<subseteq> \<Union>(ftv ` set ts) \<union> real_ftv \<phi>\<close> \<open>frv (?\<theta> a) \<subseteq> \<Union>(frv ` set ts) \<union> real_frv \<phi>\<close>
      \<open>ktv (?\<theta> a) \<subseteq> \<Union>(ktv ` set ts) \<union> real_ktv \<phi>\<close> for a
      by (auto split: option.split dest!: map_of_SomeD set_zip_rightD e)
    have \<open>ftv (bsubstl ?\<theta> (\<lambda>_. RNil) b) \<subseteq> \<Union>(ftv ` set ts) \<union> real_ftv \<phi>\<close>
      unfolding ftv_bsubstl by (intro Un_least UN_least) (use b \<theta> in auto)
    moreover have \<open>frv (bsubstl ?\<theta> (\<lambda>_. RNil) b) \<subseteq> \<Union>(frv ` set ts) \<union> real_frv \<phi>\<close>
      unfolding frv_bsubstl by (intro Un_least UN_least) (use b \<theta> in auto)
    moreover have \<open>ktv (bsubstl ?\<theta> (\<lambda>_. RNil) b) \<subseteq> \<Union>(ktv ` set ts) \<union> real_ktv \<phi>\<close>
      by (rule subset_trans[OF ktv_bsubstl]) (intro Un_least UN_least, use b \<theta> in auto)
    ultimately have \<open>ftv (bsubstl ?\<theta> (\<lambda>_. RNil) b) \<subseteq> \<Union>(ftv ` set ts) \<union> real_ftv \<phi>\<close>
      \<open>frv (bsubstl ?\<theta> (\<lambda>_. RNil) b) \<subseteq> \<Union>(frv ` set ts) \<union> real_frv \<phi>\<close>
      \<open>ktv (bsubstl ?\<theta> (\<lambda>_. RNil) b) \<subseteq> \<Union>(ktv ` set ts) \<union> real_ktv \<phi>\<close> by simp_all
  }
  note fn = this
  show \<open>ftv (treal \<phi> (TC c ts)) \<subseteq> ftv (TC c ts) \<union> real_ftv \<phi>\<close>
    using ts fn by (auto split: option.split tydef.split)
  show \<open>frv (treal \<phi> (TC c ts)) \<subseteq> frv (TC c ts) \<union> real_frv \<phi>\<close>
    using ts fn by (auto split: option.split tydef.split)
  show \<open>ktv (treal \<phi> (TC c ts)) \<subseteq> ktv (TC c ts) \<union> real_ktv \<phi>\<close>
    using ts fn by (auto split: option.split tydef.split)
next
  case (TDep i sg K e t)
  then show \<open>ktv (treal \<phi> (TDep i sg K e t)) \<subseteq> ktv (TDep i sg K e t) \<union> real_ktv \<phi>\<close> by auto
qed auto

lemma real_scheme_vars:
  \<open>ftv_sch (real_scheme \<phi> \<sigma>) \<subseteq> ftv_sch \<sigma> \<union> real_ftv \<phi>\<close>
  \<open>frv_sch (real_scheme \<phi> \<sigma>) \<subseteq> frv_sch \<sigma> \<union> real_frv \<phi>\<close>
  \<open>ktv_sch (real_scheme \<phi> \<sigma>) \<subseteq> ktv_sch \<sigma> \<union> real_ktv \<phi>\<close>
  by (cases \<sigma>; simp add: treal_vars)+

lemma real_tydef_vars:
  \<open>ftv_tydef (real_tydef \<phi> d) \<subseteq> ftv_tydef d \<union> real_ftv \<phi>\<close>
  \<open>frv_tydef (real_tydef \<phi> d) \<subseteq> frv_tydef d \<union> real_frv \<phi>\<close>
  \<open>ktv_tydef (real_tydef \<phi> d) \<subseteq> ktv_tydef d \<union> real_ktv \<phi>\<close>
  by (cases d; auto simp: treal_vars split: option.split dest!: map_of_real)+

lemma Un_sub_Un: \<open>A \<subseteq> C \<union> R \<Longrightarrow> B \<subseteq> D \<union> R \<Longrightarrow> A \<union> B \<subseteq> (C \<union> D) \<union> R\<close>
  by auto

lemma UN_map_subset:
  \<open>(\<And>x. x \<in> set xs \<Longrightarrow> f x \<subseteq> g x \<union> S) \<Longrightarrow> \<Union>(set (map f xs)) \<subseteq> \<Union>(set (map g xs)) \<union> S\<close>
  by auto

lemma real_env_vars:
  \<open>ftv_ent (real_ent \<phi> e) \<subseteq> ftv_ent e \<union> real_ftv \<phi> \<and>
   frv_ent (real_ent \<phi> e) \<subseteq> frv_ent e \<union> real_frv \<phi> \<and>
   ktv_ent (real_ent \<phi> e) \<subseteq> ktv_ent e \<union> real_ktv \<phi>\<close>
  \<open>ftv_env (real_env \<phi> E) \<subseteq> ftv_env E \<union> real_ftv \<phi> \<and>
   frv_env (real_env \<phi> E) \<subseteq> frv_env E \<union> real_frv \<phi> \<and>
   ktv_env (real_env \<phi> E) \<subseteq> ktv_env E \<union> real_ktv \<phi>\<close>
proof (induction \<phi> e and \<phi> E rule: real_ent_induct)
  case (real_ent_TEfun \<phi> ps T E)
  have ih: \<open>(x, T', E') \<in> set ps \<Longrightarrow>
      ftv_env (real_env \<phi> E') \<subseteq> ftv_env E' \<union> real_ftv \<phi> \<and>
      frv_env (real_env \<phi> E') \<subseteq> frv_env E' \<union> real_frv \<phi> \<and>
      ktv_env (real_env \<phi> E') \<subseteq> ktv_env E' \<union> real_ktv \<phi>\<close> for x T' E'
    using real_ent_TEfun.IH by blast
  have fv: \<open>\<Union>(set (map (\<lambda>(x, T, E). ftv_env (real_env \<phi> E)) ps)) \<subseteq>
      \<Union>(set (map (\<lambda>(x, T, E). ftv_env E) ps)) \<union> real_ftv \<phi>\<close>
    by (rule UN_map_subset) (auto split: prod.splits dest!: ih)
  have rv: \<open>\<Union>(set (map (\<lambda>(x, T, E). frv_env (real_env \<phi> E)) ps)) \<subseteq>
      \<Union>(set (map (\<lambda>(x, T, E). frv_env E) ps)) \<union> real_frv \<phi>\<close>
    by (rule UN_map_subset) (auto split: prod.splits dest!: ih)
  have kv: \<open>\<Union>(set (map (\<lambda>(x, T, E). ktv_env (real_env \<phi> E)) ps)) \<subseteq>
      \<Union>(set (map (\<lambda>(x, T, E). ktv_env E) ps)) \<union> real_ktv \<phi>\<close>
    by (rule UN_map_subset) (auto split: prod.splits dest!: ih)
  show ?case
    using fv rv kv real_ent_TEfun.IH
    unfolding real_ent.simps ftv_ent.simps frv_ent.simps ktv_ent.simps
    by (intro conjI Un_sub_Un) (simp_all add: split_def o_def)
next
  case (real_ent_TEop \<phi> l ps t\<^sub>1 t\<^sub>2)
  show ?case
    using treal_vars[of \<phi> t\<^sub>1] treal_vars[of \<phi> t\<^sub>2]
    unfolding real_ent.simps ftv_ent.simps frv_ent.simps ktv_ent.simps
    by (intro conjI Un_sub_Un)
next
  case (real_env_Cons \<phi> x e ex)
  then show ?case
    unfolding real_env.simps ftv_env.simps frv_env.simps ktv_env.simps
    by (intro conjI Un_sub_Un) auto
qed (simp_all add: treal_vars real_scheme_vars real_tydef_vars)

lemmas real_env_ftv = real_env_vars(2)[THEN conjunct1]
  and real_env_frv = real_env_vars(2)[THEN conjunct2, THEN conjunct1]
  and real_env_ktv = real_env_vars(2)[THEN conjunct2, THEN conjunct2]

lemma
  shows param_env_ftv: \<open>ftv_env (param_env E) \<subseteq> ftv_env E\<close>
    and param_env_frv: \<open>frv_env (param_env E) \<subseteq> frv_env E\<close>
    and param_env_ktv: \<open>ktv_env (param_env E) \<subseteq> ktv_env E\<close>
  by (induction E rule: param_env.induct) auto

lemma
  shows dep_vars_ftv: \<open>real_ftv (dep_vars T K) = {}\<close>
    and dep_vars_frv: \<open>real_frv (dep_vars T K) = {}\<close>
    and dep_vars_ktv: \<open>real_ktv (dep_vars T K) \<subseteq> set K\<close>
  by (auto simp: dep_vars_def real_ftv_def real_frv_def real_ktv_def dest: set_zip_rightD)

end
