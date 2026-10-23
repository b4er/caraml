theory Expressions
  imports Loc Names
begin

section \<open>The surface AST\<close>

text \<open>A name (\<^typ>\<open>nm\<close>) keeps its position for error reports, positions live at the
  leaves only. The \<^text>\<open>Err\<close> constructors let error recovery yield a node. Spellings
  are not interpreted: an operator bound as a value, \<open>(+)\<close>, is an ordinary \<^typ>\<open>nm\<close>.
  Literals are decoded by the lexer: an integer carries its value and suffix, a string
  or character its codepoints, a float its text.\<close>

datatype mpath = MkPath \<open>nm list\<close>  \<comment> \<open>qualified name \<open>A.B.x\<close>\<close>

subsection \<open>Types, effect rows, and signatures\<close>

text \<open>Signatures live in one block with the types: a module binder, explicit
  \<open>(M : SIG)\<close> \<^cite>\<open>vivien2024\<close> or implicit \<open>{M : SIG}\<close> \<^cite>\<open>white2014\<close>, is the
  domain of a module-dependent arrow, and a signature refines by types.

  A name type \<open>[E as]\<close> is the type of a handler name \<^cite>\<open>xie2021names\<close>: a domain
  \<open>[E] -> \<tau>\<close> binds an anonymous name, \<open>(f : [E]) -> \<tau>\<close> one that the rest of the
  type refers to. A row entry naming a bound name is a \<^text>\<open>TPath\<close>, resolved by
  scope.\<close>

datatype ty =
    TSpine \<open>tatom list\<close>                \<comment> \<open>application spine \<open>t \<tau>\<^sub>1 \<dots> \<tau>\<^sub>n\<close>\<close>
  | TArrow \<open>tatom list\<close> \<open>ty option\<close> ty \<comment> \<open>\<open>app \<rightarrow> \<tau>\<close> or \<open>app \<rightarrow> [row] \<tau>\<close> (empty row is total)\<close>
  | TArrowMod mbind ty                 \<comment> \<open>\<open>(M : SIG) \<rightarrow> \<tau>\<close>, \<open>{M : SIG} \<rightarrow> \<tau>\<close>: module-dependent arrow\<close>
  | TArrowName nm \<open>tatom list\<close> ty     \<comment> \<open>\<open>(f : [E as]) \<rightarrow> \<tau>\<close>: name-dependent arrow\<close>
  | THand \<open>tatom list\<close> \<open>tatom list\<close> \<open>ty option\<close> \<open>tatom list\<close>
                                       \<comment> \<open>\<open>handler [E as] a \<rightarrow> [row] b\<close>: effect, action type,
                                          row, result\<close>
  | TRow \<open>ty list\<close> \<open>ty option\<close>         \<comment> \<open>effect row \<open>[\<tau>\<^sub>1, \<dots>]\<close>, open \<open>[\<tau>\<^sub>1, \<dots> | \<rho>]\<close>\<close>
  | TRec \<open>(nm \<times> ty) list\<close> \<open>ty option\<close>  \<comment> \<open>record type \<open>(x : \<tau>, \<dots>)\<close>, open \<open>(x : \<tau> | \<rho>)\<close>\<close>
  | TErr                               \<comment> \<open>error-recovery node\<close>
and tatom =
    TPath mpath                        \<comment> \<open>constructor or variable; scope decides\<close>
  | TWild nm                           \<comment> \<open>\<open>_\<close>: a type to infer\<close>
  | TParen \<open>ty list\<close>                   \<comment> \<open>\<open>(\<tau>)\<close> group, \<open>()\<close> unit, \<open>(\<tau>\<^sub>1, \<dots>, \<tau>\<^sub>n)\<close> tuple\<close>
  | TName \<open>tatom list\<close>                 \<comment> \<open>\<open>[E as]\<close>: name type of effect \<open>E\<close> at \<open>as\<close>\<close>
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
  | SpEff nm \<open>nm list\<close> \<open>(nm \<times> ty) list\<close>
                                       \<comment> \<open>\<open>effect E as ops\<close>: operations exported\<close>
  | SpFix fixity nm nm                 \<comment> \<open>\<open>infix{l,r} p \<oplus>\<close> (fixity survives sealing)\<close>
  | SpMod nm msig                      \<comment> \<open>\<open>module M : SIG\<close>\<close>
  | SpInc msig                         \<comment> \<open>\<open>include SIG\<close>: splice the specs\<close>
  | SpErr                              \<comment> \<open>error-recovery node\<close>

subsection \<open>Patterns\<close>

datatype mpat =
    PatApp \<open>mpatom list\<close>      \<comment> \<open>application spine \<open>C p\<^sub>1 \<dots> p\<^sub>n\<close>\<close>
  | PatOp \<open>mpatom list\<close> nm mpat
                              \<comment> \<open>operator chain \<open>app \<oplus> p\<close>, resolved by fixity\<close>
  | PatAs mpat nm             \<comment> \<open>\<open>p as x\<close>\<close>
  | PatAnn mpat ty            \<comment> \<open>annotated pattern \<open>p : \<tau>\<close>\<close>
and mpatom =
    PWild nm                  \<comment> \<open>wildcard \<open>\_\<close>\<close>
  | PQid mpath                \<comment> \<open>constructor if one is in scope, else a binder\<close>
  | PNum loc int \<open>suffix option\<close>
                              \<comment> \<open>integer literal\<close>
  | PStr loc \<open>nat list\<close>       \<comment> \<open>string literal\<close>
  | PChar loc nat             \<comment> \<open>character literal\<close>
  | PParen \<open>mpat list\<close>        \<comment> \<open>\<open>(p)\<close> group, \<open>()\<close> unit, \<open>(p\<^sub>1, \<dots>, p\<^sub>n)\<close> tuple\<close>
  | PList \<open>mpat list\<close>         \<comment> \<open>\<open>[p\<^sub>1, \<dots>, p\<^sub>n]\<close>: list literal, sugar for the list constructors\<close>
  | PRec \<open>(nm \<times> mpat) list\<close> bool
                              \<comment> \<open>record \<open>(x = p, \<dots>)\<close>, open \<open>(x = p | _)\<close> when the flag is set\<close>

subsection \<open>Expressions\<close>

text \<open>Applications are spines of atoms. \<^text>\<open>AParen\<close> records where the parentheses
  were (so a printed AST can reparse to itself).

  Operator chains are left unresolved until elaboration \<^cite>\<open>\<open>Sect. 10.6\<close> in marlow2010\<close>.

  A module argument is a bare path (an \<^text>\<open>APath\<close>), or not written at all when
  implicit. The type system rewrites both to \<^text>\<open>AMod P SIG\<close>
  \<^cite>\<open>\<open>Sect. 2.3\<close> in white2014\<close> \<^cite>\<open>vivien2024\<close>, with \<open>SIG\<close> the callee's
  parameter signature. On a left-hand side, \<^text>\<open>AMod\<close> and \<^text>\<open>ABind\<close> are the
  module binders of a clause; elsewhere the checker rejects them.

  The unnamed \<^text>\<open>EHandle e cls\<close> finds its handler by label and nesting
  \<^cite>\<open>leijen2017\<close>. A named handler \<^cite>\<open>\<open>Sect. 2.3\<close> in xie2021names\<close> is a
  first-class value installed by \<^text>\<open>EWith x h e\<close>: running it binds a fresh
  handler name to \<open>x\<close> in \<open>e\<close>, and \<^text>\<open>x.op a\<close> is caught by that activation alone.

  A right-hand side with guards is an \<^text>\<open>EGuards\<close>: the alternatives in order,
  the otherwise alternative with no guards; when none holds, the next arm or clause is
  tried.\<close>

datatype expr =
    ESpine \<open>matom list\<close>                \<comment> \<open>application spine \<open>f a\<^sub>1 \<dots> a\<^sub>n\<close>\<close>
  | EOp \<open>matom list\<close> nm expr           \<comment> \<open>operator chain \<open>app \<oplus> e\<close>\<close>
  | EAnn expr ty                       \<comment> \<open>ascription \<open>e : \<tau>\<close>\<close>
  | EFn \<open>mpat list\<close> expr               \<comment> \<open>\<open>\<lambda>p\<^sub>1 \<dots> p\<^sub>n -> e\<close>: anonymous function\<close>
  | EFnMod mbind expr                  \<comment> \<open>anonymous functor\<close>
  | ELet mpat expr expr                \<comment> \<open>\<open>let p = e\<close> then body\<close>
  | ELetFun nm \<open>mbind list\<close> \<open>(mpat list \<times> expr) list\<close> expr
                                       \<comment> \<open>\<open>let f bs ps = e | \<dots>\<close> then body: a local clause group\<close>
  | ESeq expr expr                     \<comment> \<open>\<open>e\<^sub>1; e\<^sub>2\<close>: own node, not \<open>let _ =\<close>, for print fidelity\<close>
  | EIf expr expr \<open>expr option\<close>        \<comment> \<open>\<open>if c then t else e\<close>\<close>
  | EMatch expr \<open>(mpat \<times> expr) list\<close>   \<comment> \<open>\<open>match e with p -> e \<dots>\<close>\<close>
  | EGuards \<open>(expr list \<times> expr) list\<close>  \<comment> \<open>\<open>| g, \<dots> = e | \<dots>\<close>: guarded alternatives\<close>
  | EHandle expr \<open>hclause list\<close>        \<comment> \<open>run \<open>e\<close> under the clauses\<close>
  | EHandler \<open>hclause list\<close>            \<comment> \<open>first-class handler\<close>
  | EHandlerN \<open>hclause list\<close>           \<comment> \<open>\<open>handler cls\<close>: first-class named handler\<close>
  | EWith nm expr expr                 \<comment> \<open>\<open>with x = h\<close> then body: install a named handler\<close>
  | EMask nm expr                      \<comment> \<open>\<open>mask l e\<close>: skip the innermost \<open>l\<close>-handler\<close>
  | EErr                               \<comment> \<open>error-recovery node\<close>
and matom =
    APath mpath                        \<comment> \<open>variable, constructor, module, or qualified name\<close>
  | ANum loc int \<open>suffix option\<close>      \<comment> \<open>integer literal\<close>
  | AFloat nm                          \<comment> \<open>float literal, by its text\<close>
  | AStr loc \<open>nat list\<close>                \<comment> \<open>string literal\<close>
  | AChar loc nat                      \<comment> \<open>character literal: a Unicode scalar value\<close>
  | AParen \<open>expr list\<close>                 \<comment> \<open>\<open>(e)\<close> group, \<open>()\<close> unit, \<open>(e\<^sub>1, \<dots>, e\<^sub>n)\<close> tuple\<close>
  | AList \<open>expr list\<close>                  \<comment> \<open>\<open>[e\<^sub>1, \<dots>, e\<^sub>n]\<close>: list literal, sugar for the
                                          list constructors\<close>
  | ARec \<open>(nm \<times> expr) list\<close>           \<comment> \<open>record \<open>(x = e, \<dots>)\<close>\<close>
  | ADot matom nm                      \<comment> \<open>\<open>a.x\<close>, \<open>a.1\<close>: selection by a label or a position\<close>
  | AMod mpath msig                    \<comment> \<open>\<open>(P : SIG)\<close>: explicit module argument, \<open>P\<close> at the
                                          callee's parameter signature\<close>
  | ABind nm msig                      \<comment> \<open>\<open>{M : SIG}\<close>: an implicit binder on a left-hand side\<close>
and hclause =
    HOp nm \<open>mpat list\<close> \<open>nm option\<close> expr
                                       \<comment> \<open>\<open>op p as k -> e\<close>; tail-resumptive without \<open>as k\<close>\<close>
  | HRet mpat expr                     \<comment> \<open>\<open>return p -> e\<close>: transform the normal result\<close>
  | HFin expr                          \<comment> \<open>\<open>finally -> e\<close>: run on any exit\<close>
  | HErr                               \<comment> \<open>error-recovery node\<close>

end
