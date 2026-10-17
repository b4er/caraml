theory Expressions
  imports Loc Names Protocol
begin

section \<open>The surface AST\<close>

text \<open>A name (\<^typ>\<open>nm\<close>) keeps its position for error reports, positions live at the
  leaves only. The \<^text>\<open>Err\<close> constructors let error recovery yield a node. Spellings
  are not interpreted: an operator bound as a value, \<open>(+)\<close>, is an ordinary \<^typ>\<open>nm\<close>.\<close>

datatype mpath = MkPath \<open>nm list\<close>  \<comment> \<open>qualified name \<open>A.B.x\<close>\<close>

subsection \<open>Types, effect rows, and signatures\<close>

text \<open>Signatures live in one block with the types: a module binder, explicit
  \<open>(M : SIG)\<close> \<^cite>\<open>vivien2024\<close> or implicit \<open>{M : SIG}\<close> \<^cite>\<open>white2014\<close>, is the
  domain of a module-dependent arrow, and a signature refines by types.\<close>

datatype ty =
    TSpine \<open>tatom list\<close>                \<comment> \<open>application spine \<open>t \<tau>\<^sub>1 \<dots> \<tau>\<^sub>n\<close>\<close>
  | TArrow \<open>tatom list\<close> \<open>ty option\<close> ty \<comment> \<open>\<open>app \<rightarrow> \<tau>\<close> or \<open>app \<rightarrow> [row] \<tau>\<close> (empty row is total)\<close>
  | TArrowMod mbind ty                 \<comment> \<open>\<open>(M : SIG) \<rightarrow> \<tau>\<close>, \<open>{M : SIG} \<rightarrow> \<tau>\<close>: module-dependent arrow\<close>
  | TRow \<open>ty list\<close> \<open>ty option\<close>         \<comment> \<open>effect row \<open>[\<tau>\<^sub>1, \<dots>]\<close>, open \<open>[\<tau>\<^sub>1, \<dots> | \<rho>]\<close>\<close>
  | TErr                               \<comment> \<open>error-recovery node\<close>
and tatom =
    TPath mpath                        \<comment> \<open>constructor or variable; scope decides\<close>
  | TWild nm                           \<comment> \<open>\<open>_\<close>: a type to infer\<close>
  | TParen \<open>ty list\<close>                   \<comment> \<open>\<open>(\<tau>)\<close> group, \<open>()\<close> unit, \<open>(\<tau>\<^sub>1, \<dots>, \<tau>\<^sub>n)\<close> tuple\<close>
and mbind =
    BMod nm msig                       \<comment> \<open>\<open>(M : SIG)\<close>: module parameter, passed at the call\<close>
  | BImp nm msig                       \<comment> \<open>\<open>{M : SIG}\<close>: implicit module parameter,
                                          resolved at the call\<close>
and mrefn =
    RType nm ty                        \<comment> \<open>\<open>[t = \<tau>]\<close>: fix a type member\<close>
  | RMod nm mpath                      \<comment> \<open>\<open>[M = P]\<close>: fix a module member (structure sharing)\<close>
and msig =
    SPath mpath \<open>mrefn list\<close>           \<comment> \<open>signature by name, refined: \<open>SIG[t = \<tau>, M = P]\<close>\<close>
  | SLit \<open>mspec list\<close>                  \<comment> \<open>literal signature: a block of specs\<close>
  | SErr                               \<comment> \<open>error-recovery node\<close>
and mspec =
    SpType nm \<open>nm list\<close> \<open>ty option\<close>    \<comment> \<open>\<open>type t a\<^sub>1 \<dots> a\<^sub>n\<close> (abstract when no body)\<close>
  | SpData nm \<open>nm list\<close> \<open>(nm \<times> tatom list) list\<close>
                                       \<comment> \<open>\<open>type t as = C\<^sub>1 \<tau>s | \<dots>\<close>: the constructors stay matchable\<close>
  | SpVal nm ty                        \<comment> \<open>value spec \<open>x : \<tau>\<close>\<close>
  | SpEff nm \<open>nm list\<close> \<open>(nm \<times> ty) list\<close> \<open>nm ltlf option\<close>
                                       \<comment> \<open>\<open>effect E[as] { op : \<tau>; \<dots>; protocol \<phi> }\<close>: operations
                                          exported, protocol over them (atoms are operation names)\<close>
  | SpFix fixity nm nm                 \<comment> \<open>\<open>infix{l,r} p \<oplus>\<close> (fixity survives sealing)\<close>
  | SpMod nm msig                      \<comment> \<open>\<open>module M : SIG\<close>\<close>
  | SpInc msig                         \<comment> \<open>\<open>include SIG\<close>: splice the specs\<close>
  | SpErr                              \<comment> \<open>error-recovery node\<close>

subsection \<open>Patterns\<close>

datatype mpat =
    PatApp \<open>mpatom list\<close>    \<comment> \<open>application spine \<open>C p\<^sub>1 \<dots> p\<^sub>n\<close>\<close>
  | PatAs \<open>mpatom list\<close> nm  \<comment> \<open>\<open>C p\<^sub>1 \<dots> p\<^sub>n as x\<close>\<close>
  | PatAnn mpat ty          \<comment> \<open>annotated pattern \<open>p : \<tau>\<close>\<close>
and mpatom =
    PWild nm                \<comment> \<open>wildcard \<open>\_\<close>\<close>
  | PQid mpath              \<comment> \<open>constructor if one is in scope, else a binder\<close>
  | PNum nm                 \<comment> \<open>numeric literal\<close>
  | PStr nm                 \<comment> \<open>string literal\<close>
  | PChar nm                \<comment> \<open>character literal\<close>
  | PParen \<open>mpat list\<close>      \<comment> \<open>\<open>(p)\<close> group, \<open>()\<close> unit, \<open>(p\<^sub>1, \<dots>, p\<^sub>n)\<close> tuple\<close>
  | PList \<open>mpat list\<close>       \<comment> \<open>\<open>[p\<^sub>1, \<dots>, p\<^sub>n]\<close>: list literal, sugar for the list constructors\<close>

subsection \<open>Expressions\<close>

text \<open>Applications are spines of atoms. \<^text>\<open>AParen\<close> records where the parentheses
  were (so a printed AST can reparse to itself).

  Operator chains are left unresolved until elaboration \<^cite>\<open>\<open>Sect. 10.6\<close> in marlow2010\<close>.
  A prefix operator (such as \<open>-x\<close>) is the chain with an empty left spine.

  A module argument is a bare path (an \<^text>\<open>APath\<close>), or not written at all when
  implicit. The type system rewrites both to \<^text>\<open>AMod P SIG\<close>
  \<^cite>\<open>\<open>Sect. 2.3\<close> in white2014\<close> \<^cite>\<open>vivien2024\<close>, with \<open>SIG\<close> the callee's
  parameter signature; \<^text>\<open>AMod\<close> is the one constructor that only the type system
  produces.

  The unnamed \<^text>\<open>handle e { cls }\<close> finds its handler by label and nesting
  \<^cite>\<open>leijen2017\<close>. A named handler \<^cite>\<open>\<open>Sect. 2.3\<close> in xie2021names\<close> is a
  first-class value applied to a name-taking action \<^text>\<open>fn[x] e\<close>: running it binds a
  fresh handler name to \<open>x\<close>, and \<^text>\<open>x.op a\<close> is caught by that activation alone.
  \<open>x\<close> is bound by the action's rank-2 binder, so a name cannot escape its handler
  \<^cite>\<open>\<open>Sect. 2.5\<close> in xie2021names\<close>.\<close>

datatype expr =
    ESpine \<open>matom list\<close>                \<comment> \<open>application spine \<open>f a\<^sub>1 \<dots> a\<^sub>n\<close>\<close>
  | EOp \<open>matom list\<close> nm expr           \<comment> \<open>operator chain \<open>app \<oplus> e\<close>\<close>
  | EAnn expr ty                       \<comment> \<open>ascription \<open>e : \<tau>\<close>\<close>
  | EFn \<open>mpat list\<close> expr               \<comment> \<open>\<open>fn(p\<^sub>1, \<dots>, p\<^sub>n) e\<close>: anonymous function\<close>
  | EFnMod mbind expr                  \<comment> \<open>\<open>fn(M : SIG) e\<close>, \<open>fn{M : SIG} e\<close>: anonymous functor\<close>
  | ELet mpat expr expr                \<comment> \<open>\<open>let p = e\<close> then body\<close>
  | EBind mpat expr expr               \<comment> \<open>\<open>let p <- e\<close> then body: effectful bind\<close>
  | ESeq expr expr                     \<comment> \<open>\<open>e\<^sub>1; e\<^sub>2\<close>: own node, not \<open>let _ =\<close>, for print fidelity\<close>
  | EIf expr expr \<open>expr option\<close>        \<comment> \<open>\<open>if c { t } else { e }\<close>;
                                          no \<open>else\<close> is unit\<close>
  | EMatch expr \<open>(mpat \<times> expr) list\<close>   \<comment> \<open>\<open>match e { p \<rightarrow> e; \<dots> }\<close>\<close>
  | EHandle expr \<open>hclause list\<close>        \<comment> \<open>\<open>handle e { cls }\<close>: run \<open>e\<close> under the clauses\<close>
  | EHandler \<open>hclause list\<close>            \<comment> \<open>\<open>handler { cls }\<close>: first-class handler\<close>
  | EMask nm expr                      \<comment> \<open>\<open>mask[l] e\<close>: skip the innermost \<open>l\<close>-handler\<close>
  | EFnName nm expr                    \<comment> \<open>\<open>fn[x] e\<close>: name-taking action (\<open>x\<close> the handler name)\<close>
  | EHandlerN \<open>hclause list\<close>           \<comment> \<open>\<open>handler { cls }\<close>: first-class named handler\<close>
  | EHandleN nm \<open>hclause list\<close> expr    \<comment> \<open>\<open>handle x { cls } e\<close>: sugar for
                                          \<open>handler { cls } (fn[x] e)\<close>\<close>
  | EErr                               \<comment> \<open>error-recovery node\<close>
and matom =
    APath mpath                        \<comment> \<open>variable, constructor, module, or qualified name\<close>
  | ANum nm                            \<comment> \<open>numeric literal\<close>
  | AStr nm                            \<comment> \<open>string literal\<close>
  | AChar nm                           \<comment> \<open>character literal: a Unicode scalar value\<close>
  | AParen \<open>expr list\<close>                 \<comment> \<open>\<open>(e)\<close> group, \<open>()\<close> unit, \<open>(e\<^sub>1, \<dots>, e\<^sub>n)\<close> tuple\<close>
  | AList \<open>expr list\<close>                  \<comment> \<open>\<open>[e\<^sub>1, \<dots>, e\<^sub>n]\<close>: list literal, sugar for the
                                          list constructors\<close>
  | AMod mpath msig                    \<comment> \<open>\<open>(P : SIG)\<close>: explicit module argument, \<open>P\<close> at the
                                          callee's parameter signature\<close>
and hclause =
    HOp nm \<open>mpat list\<close> \<open>nm option\<close> expr
                                       \<comment> \<open>\<open>op(p\<^sub>1, \<dots>) as k \<rightarrow> e\<close>; tail-resumptive without \<open>as k\<close>\<close>
  | HRet mpat expr                     \<comment> \<open>\<open>return(p) e\<close>: transform the normal result\<close>
  | HFin expr                          \<comment> \<open>\<open>finally e\<close>: run on any exit\<close>
  | HErr                               \<comment> \<open>error-recovery node\<close>

subsection \<open>Reading literals\<close>

text \<open>A literal keeps its surface spelling. The readers accept decimal naturals;
  strings and characters lose their quotes and admit no escape sequences.\<close>

definition read_nat :: \<open>name \<Rightarrow> nat option\<close> where
  \<open>read_nat s =
     (if s \<noteq> [] \<and> (\<forall>c \<in> set s. c \<in> set (str ''0123456789''))
      then Some (foldl (\<lambda>n c. 10 * n + (c - 48)) 0 s) else None)\<close>

definition read_string :: \<open>name \<Rightarrow> name option\<close> where
  \<open>read_string s =
     (case s of
        [] \<Rightarrow> None
      | q # cs \<Rightarrow>
          (if q = 0x22 \<and> cs \<noteq> [] \<and> last cs = 0x22 \<and>
              (\<forall>c \<in> set (butlast cs). c \<noteq> 0x22 \<and> c \<noteq> 0x5C)
           then Some (butlast cs) else None))\<close>

definition read_char :: \<open>name \<Rightarrow> nat option\<close> where
  \<open>read_char s =
     (case s of
        [q\<^sub>1, c, q\<^sub>2] \<Rightarrow>
          (if q\<^sub>1 = 0x27 \<and> q\<^sub>2 = 0x27 \<and> c \<noteq> 0x5C
           then Some c else None)
      | _ \<Rightarrow> None)\<close>

subsection \<open>Linear resumptions\<close>

text \<open>A resumption \<open>k\<close> is \<^emph>\<open>linear\<close> in a clause body when it is resumed at most once.
  Branches count by their maximum; an occurrence under a binder that may run more than
  once (a function, a module abstraction, a name-taking action, a handler clause, a
  first-class handler) counts twice. Named handlers of an effect with a protocol demand
  linear clauses, so that a resumption never forks the trace of an instance (the
  one-shot discipline of \<^cite>\<open>\<open>Sect. 6\<close> in phippscostin2023\<close>).

  The count over-approximates; a shadowing binder is not tracked.\<close>

fun kuses :: \<open>name \<Rightarrow> expr \<Rightarrow> nat\<close>
and kuses_atom :: \<open>name \<Rightarrow> matom \<Rightarrow> nat\<close>
and kuses_cls :: \<open>name \<Rightarrow> hclause \<Rightarrow> nat\<close> where
  \<open>kuses k (ESpine as) = sum_list (map (kuses_atom k) as)\<close>
| \<open>kuses k (EOp as opr e) =
     sum_list (map (kuses_atom k) as) + (if n_txt opr = k then 1 else 0) + kuses k e\<close>
| \<open>kuses k (EAnn e _) = kuses k e\<close>
| \<open>kuses k (EFn _ b) = 2 * kuses k b\<close>
| \<open>kuses k (EFnMod _ b) = 2 * kuses k b\<close>
| \<open>kuses k (ELet _ e b) = kuses k e + kuses k b\<close>
| \<open>kuses k (EBind _ e b) = kuses k e + kuses k b\<close>
| \<open>kuses k (ESeq e\<^sub>1 e\<^sub>2) = kuses k e\<^sub>1 + kuses k e\<^sub>2\<close>
| \<open>kuses k (EIf c t None) = kuses k c + kuses k t\<close>
| \<open>kuses k (EIf c t (Some e)) = kuses k c + max (kuses k t) (kuses k e)\<close>
| \<open>kuses k (EMatch e arms) = kuses k e + fold max (map (\<lambda>(_, b). kuses k b) arms) 0\<close>
| \<open>kuses k (EHandle e cls) = kuses k e + fold max (map (kuses_cls k) cls) 0\<close>
| \<open>kuses k (EHandler cls) = 2 * fold max (map (kuses_cls k) cls) 0\<close>
| \<open>kuses k (EMask _ e) = kuses k e\<close>
| \<open>kuses k (EFnName _ b) = 2 * kuses k b\<close>
| \<open>kuses k (EHandlerN cls) = 2 * fold max (map (kuses_cls k) cls) 0\<close>
| \<open>kuses k (EHandleN _ cls e) = kuses k e + fold max (map (kuses_cls k) cls) 0\<close>
| \<open>kuses k EErr = 0\<close>
| \<open>kuses_atom k (APath (MkPath xs)) =
     (case xs of x # _ \<Rightarrow> (if n_txt x = k then 1 else 0) | [] \<Rightarrow> 0)\<close>
| \<open>kuses_atom k (AParen es) = sum_list (map (kuses k) es)\<close>
| \<open>kuses_atom k (AList es) = sum_list (map (kuses k) es)\<close>
| \<open>kuses_atom k _ = 0\<close>
| \<open>kuses_cls k (HOp _ _ _ b) = 2 * kuses k b\<close>
| \<open>kuses_cls k (HRet _ b) = kuses k b\<close>
| \<open>kuses_cls k (HFin e) = kuses k e\<close>
| \<open>kuses_cls k HErr = 0\<close>

definition linear_k :: \<open>name \<Rightarrow> expr \<Rightarrow> bool\<close> where
  \<open>linear_k k b \<longleftrightarrow> kuses k b \<le> 1\<close>

end
