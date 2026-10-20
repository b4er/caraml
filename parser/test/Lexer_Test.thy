theory Lexer_Test
  imports CaraML_Parser.Lexer_Correct
begin

section \<open>The lexer on the examples of \<open>grammar.md\<close> \<section>1\<close>

text \<open>One check per rule of the lexical structure, with every example the
  grammar gives, errors included. \<^text>\<open>toks s\<close> is the token classes of
  \<^text>\<open>s\<close>, \<^text>\<open>lexs s\<close> its lexemes, and \<^text>\<open>err s\<close> says that
  \<^text>\<open>s\<close> has a lexical error.\<close>

abbreviation \<open>toks s \<equiv> map tok (snd (the (caraml_lex s)))\<close>
abbreviation \<open>lexs s \<equiv> map (s_txt \<circ> span) (snd (the (caraml_lex s)))\<close>
abbreviation \<open>err s \<equiv> caraml_lex s = None\<close>
abbreviation \<open>lrm \<equiv> 0x202E :: codepoint\<close>  \<comment> \<open>a bidirectional control\<close>

subsection \<open>Keywords, symbols and delimiters\<close>

lemma \<open>toks (cp ''let with if then else match handler mask return finally as type'')
       = [KLet, KWith, KIf, KThen, KElse, KMatch, KHandler, KMask, KReturn, KFinally, KAs, KType]\<close>
  by eval

lemma \<open>toks (cp ''extern infixl infixr infix effect module signature instance open include'')
       = [KExtern, KInfixl, KInfixr, KInfix, KEffect, KModule, KSignature, KInstance, KOpen,
          KInclude]\<close>
  by eval

\<comment> \<open>no longer keywords\<close>
lemma \<open>toks (cp ''in fn handle where literal'') = [LId, LId, LId, LId, LId]\<close>
  by eval

\<comment> \<open>a keyword extended by identifier characters is an identifier\<close>
lemma \<open>toks (cp ''lets if' then_'') = [LId, LId, LId]\<close>
  by eval

lemma \<open>toks (cp ''= : -> | '' @ [bslash, sp, 0x2192, sp, 0x3BB])
       = [Assign, Colon, Arrow, Bar, KLambda, Arrow, KLambda]\<close>
  by eval

\<comment> \<open>a symbol run that is not a reserved symbol is an operator, \<open>\\<close> included\<close>
lemma \<open>toks ([bslash, bslash, sp, bslash] @ cp ''-> <- --> == :: |> ->>'')
       = [Op, Op, Op, Op, Op, Op, Op, Op]\<close>
  by eval

lemma \<open>toks (cp ''( ) [ ] { } , ;'') = [LP, RP, LB, RB, LC, RC, Comma, Semi]\<close>
  by eval

\<comment> \<open>\<open>\<lambda>\<close> is a delimiter, not a letter\<close>
lemma \<open>toks ([0x3BB] @ cp ''x'') = [KLambda, LId]\<close>
  by eval

subsection \<open>Identifiers, the wildcard and backticked names\<close>

lemma \<open>toks (cp ''x x' x_1 M M' M_1 _'') = [LId, LId, LId, UId, UId, UId, KWild]\<close>
  by eval

\<comment> \<open>the prime continues an identifier: \<open>f'a' x\<close>\<close>
lemma \<open>lexs (cp ''f'' @ [cq] @ cp ''a'' @ [cq] @ cp '' x'')
       = [cp ''f'' @ [cq] @ cp ''a'' @ [cq], cp ''x'']\<close>
  by eval

lemma \<open>err (cp ''_1'')\<close> and \<open>err (cp ''_x'')\<close> and \<open>toks (cp ''_ 1'') = [KWild, IntL]\<close>
  by eval+

lemma \<open>toks (cp ''x `f` y'') = [LId, Op, LId]\<close>
  and \<open>op_name (cp ''`f`'') = cp ''f''\<close>
  and \<open>op_name (cp ''<>'') = cp ''<>''\<close>
  by eval+

lemma \<open>err (cp ''`let`'')\<close> and \<open>err (cp ''`F`'')\<close> and \<open>err (cp ''`f'')\<close> and \<open>err (cp ''``'')\<close>
  by eval+

subsection \<open>Selectors\<close>

lemma \<open>toks (cp ''p.1.2'') = [LId, TSelN, TSelN]\<close>
  and \<open>lexs (cp ''p.1.2'') = [cp ''p'', cp ''.1'', cp ''.2'']\<close>
  by eval+

lemma \<open>toks (cp ''1.2.3'') = [FloatL, TSelN]\<close>
  and \<open>lexs (cp ''1.2.3'') = [cp ''1.2'', cp ''.3'']\<close>
  by eval+

lemma \<open>toks (cp ''.5'') = [LSelN]\<close> and \<open>toks (cp ''x .5'') = [LId, LSelN]\<close>
  by eval+

lemma \<open>toks (cp ''M.x M.N.y p.q x .y M .N'')
       = [UId, TSelL, UId, TSelU, TSelL, LId, TSelL, LId, LSelL, UId, LSelU]\<close>
  by eval

\<comment> \<open>a selector after a comment or a newline is loose; after \<open>)\<close> it is tight\<close>
lemma \<open>toks (cp ''x{- -}.y x'' @ [nl] @ cp ''.y (x).y'')
       = [LId, LSelL, LId, LSelL, LP, LId, RP, TSelL]\<close>
  by eval

lemma \<open>sel_name (cp ''.x'') = cp ''x''\<close> and \<open>sel_name (cp ''.12'') = cp ''12''\<close>
  by eval+

\<comment> \<open>any other dot is an error\<close>
lemma \<open>err (cp ''x.'')\<close> and \<open>err (cp ''x . y'')\<close> and \<open>err (cp ''x.(y)'')\<close> and \<open>err (cp ''.1x'')\<close>
  and \<open>err (cp ''x.let'' @ [sp, dot])\<close>
  by eval+

\<comment> \<open>a keyword after a dot is a name\<close>
lemma \<open>toks (cp ''x.let'') = [LId, TSelL]\<close>
  by eval

subsection \<open>Numerals\<close>

lemma \<open>toks (cp ''0 42 1_000 0xFF 0xf_f 0b1010 0b1_0'')
       = [IntL, IntL, IntL, IntL, IntL, IntL, IntL]\<close>
  by eval

lemma \<open>int_of_lexeme (cp ''1_000'') = (1000, None)\<close>
  and \<open>int_of_lexeme (cp ''0xFF'') = (255, None)\<close>
  and \<open>int_of_lexeme (cp ''0b1010'') = (10, None)\<close>
  and \<open>int_of_lexeme (cp ''255u8'') = (255, Some U8)\<close>
  and \<open>int_of_lexeme (cp ''-0x80i8'') = (- 128, Some I8)\<close>
  by eval+

\<comment> \<open>underscores only between digits\<close>
lemma \<open>err (cp ''1_'')\<close> and \<open>err (cp ''1__0'')\<close> and \<open>err (cp ''0x_F'')\<close> and \<open>err (cp ''0x'')\<close>
  by eval+

lemma \<open>toks (cp ''1i8 1i16 1i32 1i64 1u8 1u16 1u32 1u64'')
       = [IntL, IntL, IntL, IntL, IntL, IntL, IntL, IntL]\<close>
  by eval

\<comment> \<open>ranges\<close>
lemma \<open>err (cp ''256u8'')\<close> and \<open>err (cp ''-1u8'')\<close> and \<open>err (cp ''128i8'')\<close>
  and \<open>err (cp ''0xFFi8'')\<close>
  by eval+

lemma \<open>toks (cp ''-0x80i8 -128i8 127i8 255u8 0xFFu8 18446744073709551615u64'')
       = [IntL, IntL, IntL, IntL, IntL, IntL]\<close>
  and \<open>err (cp ''18446744073709551616u64'')\<close>
  by eval+

\<comment> \<open>floats: digits on both sides of the dot, an optional exponent, no suffix\<close>
lemma \<open>toks (cp ''1.0 1.5e3 1.5E-3 1e3 1e-3 1_0.0_1e1_0'')
       = [FloatL, FloatL, FloatL, FloatL, FloatL, FloatL]\<close>
  by eval

lemma \<open>err (cp ''1.'')\<close> and \<open>err (cp ''1.5e'')\<close> and \<open>err (cp ''1.5u8'')\<close>
  and \<open>err (cp ''1e'')\<close> and \<open>err (cp ''1e+3'')\<close>
  by eval+

\<comment> \<open>a dot with no digit after it starts a selector, as in \<open>1.2.3\<close>\<close>
lemma \<open>toks (cp ''1.e3'') = [IntL, TSelL]\<close> and \<open>toks (cp ''0x1.5'') = [IntL, TSelN]\<close>
  by eval+

\<comment> \<open>a letter directly after a numeral is an error\<close>
lemma \<open>err (cp ''1x'')\<close> and \<open>err (cp ''1i9'')\<close> and \<open>err (cp ''0xFFg'')\<close> and \<open>err (cp ''1.5f'')\<close>
  by eval+

subsection \<open>Negative literals\<close>

lemma \<open>toks (cp ''x-1'') = [LId, Op, IntL]\<close>
  and \<open>toks (cp ''x - 1'') = [LId, Op, IntL]\<close>
  and \<open>toks (cp ''f -1'') = [LId, IntL]\<close>
  and \<open>toks (cp ''(-1)'') = [LP, IntL, RP]\<close>
  and \<open>toks (cp ''(- 1)'') = [LP, Op, IntL, RP]\<close>
  and \<open>toks (cp ''-1'') = [IntL]\<close>
  and \<open>toks (cp ''-1.5'') = [FloatL]\<close>
  and \<open>toks (cp ''x = -1'') = [LId, Assign, IntL]\<close>
  by eval+

lemma \<open>lexs (cp ''f -1'') = [cp ''f'', cp ''-1'']\<close>
  and \<open>lexs (cp ''x-1'') = [cp ''x'', cp ''-'', cp ''1'']\<close>
  and \<open>int_of_lexeme (cp ''-1'') = (- 1, None)\<close>
  by eval+

\<comment> \<open>after a literal, a selector, \<open>)\<close>, \<open>]\<close>, \<open>}\<close> or \<open>_\<close> the dash is an operator\<close>
lemma \<open>toks (cp ''1-1 x.y-1 (x)-1 [x]-1 {x}-1 _-1'')
       = [IntL, Op, IntL, LId, TSelL, Op, IntL, LP, LId, RP, Op, IntL, LB, LId, RB, Op, IntL,
          LC, LId, RC, Op, IntL, KWild, Op, IntL]\<close>
  by eval

\<comment> \<open>\<open>-\<close> is not an operator where a negative literal may start\<close>
lemma \<open>err (cp ''- 1u8'' @ [sp] @ cp ''-1u8'')\<close> and \<open>toks (cp ''- 1u8'') = [Op, IntL]\<close>
  by eval+

subsection \<open>Comments\<close>

lemma \<open>toks (cp ''x --> y'') = [LId, Op, LId]\<close>
  and \<open>toks (cp ''x -- y'') = [LId]\<close>
  and \<open>toks (cp ''x --- y'' @ [nl] @ cp ''z'') = [LId, LId]\<close>
  and \<open>toks (cp ''x --| y'') = [LId, Op, LId]\<close>
  by eval+

lemma \<open>toks (cp ''x {- {- -} -} y'') = [LId, LId]\<close>
  and \<open>err (cp ''x {- {- -} y'')\<close>
  and \<open>toks (cp ''x {--} y'') = [LId, LId]\<close>
  by eval+

lemma \<open>map (s_txt \<circ> snd) (the (comments_of (cp ''x {- {- -} -} y -- z'')))
       = [cp ''{- {- -} -}'', cp ''-- z'']\<close>
  by eval

subsection \<open>Bidirectional controls\<close>

lemma \<open>err (cp ''x -- '' @ [lrm])\<close>
  and \<open>err (cp ''x {- '' @ [lrm] @ cp '' -} y'')\<close>
  and \<open>err ([qt] @ cp ''a'' @ [lrm] @ cp ''b'' @ [qt])\<close>
  and \<open>err ([cq, lrm, cq])\<close>
  and \<open>err (cp ''x '' @ [0x2066] @ cp '' y'')\<close>
  by eval+

\<comment> \<open>escaped, a control is a character like any other\<close>
lemma \<open>toks ([qt, bslash] @ cp ''u{202E}'' @ [qt]) = [StrL]\<close>
  and \<open>str_pieces ([qt, bslash] @ cp ''u{202E}'' @ [qt]) = [Txt [lrm]]\<close>
  by eval+

subsection \<open>Strings and characters\<close>

lemma \<open>toks ([qt] @ cp ''a${M.x}b'' @ [qt]) = [StrI]\<close>
  and \<open>str_pieces ([qt] @ cp ''a${M.x}b'' @ [qt])
       = [Txt (cp ''a''), Hole [cp ''M'', cp ''x''], Txt (cp ''b'')]\<close>
  and \<open>str_pieces ([qt] @ cp ''${x}'' @ [qt]) = [Hole [cp ''x'']]\<close>
  and \<open>str_pieces ([qt] @ cp ''${A.B.c}${d}'' @ [qt])
       = [Hole [cp ''A'', cp ''B'', cp ''c''], Hole [cp ''d'']]\<close>
  by eval+

lemma \<open>toks ([qt, bslash] @ cp ''$'' @ [qt]) = [StrL]\<close>
  and \<open>str_pieces ([qt, bslash] @ cp ''$'' @ [qt]) = [Txt (cp ''$'')]\<close>
  and \<open>str_pieces ([qt] @ cp ''$x $'' @ [qt]) = [Txt (cp ''$x $'')]\<close>  \<comment> \<open>no brace: text\<close>
  by eval+

\<comment> \<open>the escapes: \<open>"a\tb\nc\rd\0\"\'\\"\<close>\<close>
lemma \<open>str_pieces ([qt] @ cp ''a'' @ [bslash] @ cp ''tb'' @ [bslash] @ cp ''nc'' @ [bslash]
                   @ cp ''rd'' @ [bslash] @ cp ''0'' @ [bslash, qt, bslash, cq, bslash, bslash, qt])
       = [Txt (cp ''a'' @ [0x09] @ cp ''b'' @ [nl] @ cp ''c'' @ [0x0D] @ cp ''d''
               @ [0, qt, cq, bslash])]\<close>
  and \<open>str_pieces ([qt, bslash] @ cp ''u{41}'' @ [bslash] @ cp ''u{1F642}'' @ [qt])
       = [Txt [0x41, 0x1F642]]\<close>
  and \<open>str_pieces [qt, qt] = []\<close>
  by eval+

lemma \<open>err ([qt, bslash] @ cp ''q'' @ [qt])\<close>
  and \<open>err ([qt, bslash] @ cp ''u{110000}'' @ [qt])\<close>
  and \<open>err ([qt, bslash] @ cp ''u{}'' @ [qt])\<close>
  and \<open>err ([qt, bslash] @ cp ''u{1234567}'' @ [qt])\<close>
  and \<open>err ([qt, bslash] @ cp ''u{D800}'' @ [qt])\<close>
  and \<open>err ([qt] @ cp ''a'')\<close>
  and \<open>err ([qt] @ cp ''a'' @ [nl] @ cp ''b'' @ [qt])\<close>
  and \<open>err ([qt] @ cp ''${}'' @ [qt])\<close>
  and \<open>err ([qt] @ cp ''${x.y}'' @ [qt])\<close>
  and \<open>err ([qt] @ cp ''${M}'' @ [qt])\<close>
  and \<open>err ([qt] @ cp ''${f x}'' @ [qt])\<close>
  and \<open>err ([qt] @ cp ''${x'' @ [qt])\<close>
  by eval+

lemma \<open>toks (cp ''x '' @ [qt] @ cp ''ab'' @ [qt] @ cp ''y'') = [LId, StrL, LId]\<close>
  by eval

\<comment> \<open>\<open>'a' '\n' '\u{1F642}' '\''\<close>\<close>
lemma \<open>toks ([cq, 0x61, cq, sp, cq, bslash] @ cp ''n'' @ [cq, sp, cq, bslash] @ cp ''u{1F642}''
             @ [cq, sp, cq, bslash, cq, cq]) = [CharL, CharL, CharL, CharL]\<close>
  and \<open>char_value [cq, 0x61, cq] = 0x61\<close>
  and \<open>char_value ([cq, bslash] @ cp ''n'' @ [cq]) = nl\<close>
  and \<open>char_value ([cq, bslash] @ cp ''u{1F642}'' @ [cq]) = 0x1F642\<close>
  and \<open>char_value [cq, bslash, cq, cq] = cq\<close>
  by eval+

lemma \<open>err ([cq, bslash] @ cp ''u{110000}'' @ [cq])\<close> and \<open>err [cq, cq]\<close>
  and \<open>err ([cq] @ cp ''ab'' @ [cq])\<close> and \<open>err [cq, 0x61]\<close> and \<open>err [cq, nl, cq]\<close>
  by eval+

subsection \<open>A small program\<close>

lemma \<open>toks (cp ''module M = {'' @ [nl] @ cp ''  let f = '' @ [bslash] @ cp ''x -> x.1 + -1'' @ [nl]
             @ cp ''}'')
       = [KModule, UId, Assign, LC, KLet, LId, Assign, KLambda, LId, Arrow, LId, TSelN, Op, IntL,
          RC]\<close>
  by eval

\<comment> \<open>spans: line, column and offset of each token\<close>
lemma \<open>map (\<lambda>t. (s_line (span t), s_col (span t), s_off (span t)))
         (snd (the (caraml_lex (cp ''ab'' @ [nl] @ cp '' c''))))
       = [(0, 0, 0), (1, 1, 4)]\<close>
  by eval

end
