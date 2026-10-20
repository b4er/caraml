theory Tok
  imports Main
begin

section \<open>The tokens of the surface syntax\<close>

text \<open>The terminals of \<open>parser/grammar.md\<close>: the keywords, the dedicated symbols
  and delimiters, the two identifier classes, operators, selectors and
  literals. A token carries no payload; the parser's decoders compute a
  literal's value and a selector's name from the span text with the readers of
  the lexer, which are proved defined on every lexed token.

  A selector is \<^emph>\<open>tight\<close> (\<open>TSel\<close>, no trivia before its dot) or \<^emph>\<open>loose\<close>
  (\<open>LSel\<close>) and carries a lower-case name (\<open>L\<close>), an upper-case name (\<open>U\<close>) or a
  digit run (\<open>N\<close>), so the grammar can tell \<open>M.x\<close> from \<open>p.1\<close>. A backticked
  name is an \<open>Op\<close>; \<open>\<lambda>\<close> and \<open>\\<close> are \<open>KLambda\<close>, \<open>->\<close> and \<open>\<rightarrow>\<close>
  are \<open>Arrow\<close>.\<close>

datatype tok
  = KLet | KWith | KIf | KThen | KElse | KMatch | KHandler | KMask | KReturn | KFinally
  | KAs | KType | KExtern | KInfixl | KInfixr | KInfix | KEffect | KModule | KSignature
  | KInstance | KOpen | KInclude
  | Assign | Colon | Arrow | Bar | Comma | Semi | LP | RP | LB | RB | LC | RC | KWild | KLambda
  | LId | UId | Op
  | TSelL | TSelU | TSelN | LSelL | LSelU | LSelN
  | IntL | FloatL | StrL | StrI | CharL

end
