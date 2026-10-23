theory Module_Expressions
  imports Expressions
begin

section \<open>Modules and declarations\<close>

text \<open>Signatures are in \<^theory>\<open>CaraML_Syntax.Expressions\<close>, with the types.\<close>

datatype mexpr =
    MPath mpath                        \<comment> \<open>module or functor by name\<close>
  | MStruct \<open>mdecl list\<close>               \<comment> \<open>literal structure \<open>{ ds }\<close> or a layout block\<close>
  | MApp mexpr mexpr                   \<comment> \<open>functor application \<open>F (M)\<close>, curried\<close>
  | MSeal mexpr msig                   \<comment> \<open>sealing \<open>M : SIG\<close> in expression position\<close>
  | MErr                               \<comment> \<open>error-recovery node\<close>
and mdecl =
    DLet nm expr                       \<comment> \<open>value binding, produced by lowering only\<close>
  | DFun nm \<open>mbind list\<close> \<open>(mpat list \<times> expr) list\<close>
                                       \<comment> \<open>clauses \<open>f {M : SIG} p\<^sub>1 \<dots> = e | \<dots>\<close>: module binders
                                          first, then per-clause patterns; sugar for a
                                          recursive \<open>DLet\<close>\<close>
  | DExtern nm ty nm                   \<comment> \<open>\<open>extern x : \<tau> = "sym"\<close>: foreign value by symbol
                                          (the symbol's text decoded)\<close>
  | DType nm \<open>nm list\<close> ty              \<comment> \<open>\<open>type t a\<^sub>1 \<dots> a\<^sub>n = \<tau>\<close>\<close>
  | DData nm \<open>nm list\<close> \<open>(nm \<times> tatom list) list\<close>
                                       \<comment> \<open>variant \<open>type t as = C\<^sub>1 \<tau>s | \<dots>\<close>\<close>
  | DFix fixity nm nm                  \<comment> \<open>\<open>infix{l,r} p \<oplus>\<close>: associativity, precedence, operator\<close>
  | DEff nm \<open>nm list\<close> \<open>(nm \<times> ty) list\<close>
                                       \<comment> \<open>\<open>effect E as ops\<close>: type parameters, operations\<close>
  | DMod nm \<open>(nm \<times> msig) list\<close> \<open>msig option\<close> mexpr
                                       \<comment> \<open>all module forms; no parameters is a plain module\<close>
  | DSig nm msig                       \<comment> \<open>\<open>signature S = SIG\<close>\<close>
  | DImpl nm \<open>(nm \<times> msig) list\<close> \<open>msig option\<close> mexpr
                                       \<comment> \<open>as \<open>DMod\<close>, but the name joins implicit resolution\<close>
  | DOpen mpath                        \<comment> \<open>\<open>open P\<close>: splice \<open>P\<close>'s names in as aliases\<close>
  | DInc mexpr                         \<comment> \<open>\<open>include M\<close>: splice, evaluating \<open>M\<close> first\<close>
  | DErr                               \<comment> \<open>error-recovery node\<close>

end
