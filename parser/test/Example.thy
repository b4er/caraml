theory Example
  imports LR_Parser.LR_Parser CaraML_Parser.Lexer_Correct
begin

subsection \<open>Examples\<close>

subsubsection \<open>Unicode\<close>

lemma \<open>utf8_decode ''abc'' = Inr [0x61, 0x62, 0x63]\<close>
  by eval

lemma
  \<open>utf8_decode (''x '' @ [CHR 0xE2, CHR 0x86, CHR 0x92] @ '' y'') =
   Inr [0x78, 0x20, 0x2192, 0x20, 0x79]\<close>  \<comment> \<open>the string @{text \<open>x \<rightarrow> y\<close>}\<close>
  by eval

lemma \<open>utf8_decode [CHR 0xCD, CHR 0xB0] = Inr [0x370]\<close>
  by eval  \<comment> \<open>unicode turnstile \<turnstile>\<close>

lemma
  \<open>utf8_decode [CHR 0xF0, CHR 0x9F, CHR 0x99, CHR 0x82] =
   Inr [0x1F642]\<close>  \<comment> \<open>four byte emoji (Slightly Smiling Face)\<close>
  by eval

lemma \<open>utf8_encode [0x2192] = [CHR 0xE2, CHR 0x86, CHR 0x92]\<close>
  by eval

text \<open>Failure cases, each with its diagnostic:\<close>

lemma \<open>utf8_decode [CHR ''a'', CHR 0x80] = Inl (StrayCont 1 (CHR 0x80))\<close>
  by eval

lemma \<open>utf8_decode [CHR 0xC0, CHR 0x80] = Inl (Overlong 0 2 0)\<close>  \<comment> \<open>overlong NUL\<close>
  by eval

lemma \<open>utf8_decode [CHR 0xED, CHR 0xA0, CHR 0x80] = Inl (Surrogate 0 0xD800)\<close>
  by eval

lemma \<open>utf8_decode [CHR 0xF4, CHR 0x90, CHR 0x80, CHR 0x80] = Inl (OutOfRange 0 0x110000)\<close>
  by eval

lemma \<open>utf8_decode [CHR 0xE2, CHR 0x86] = Inl (Truncated 0 3 2)\<close>
  by eval

lemma \<open>utf8_decode [CHR 0xE2, CHR 0x41, CHR 0x86] = Inl (BadCont 0 1 (CHR 0x41))\<close>
  by eval

lemma \<open>utf8_decode [CHR 0xFF] = Inl (InvalidByte 0 (CHR 0xFF))\<close>
  by eval

subsubsection \<open>Lexer\<close>

\<comment> \<open>a line comment is kept with its raw lexeme\<close>
lemma \<open>map (s_txt \<circ> snd) (the (comments_of (cp ''x -- hi'' @ [nl] @ cp ''y''))) = [cp ''-- hi'']\<close>
  by eval

\<comment> \<open>block comments nest: the inner \<open>-}\<close> does not close the outer one\<close>
lemma \<open>map (s_txt \<circ> snd) (the (comments_of (cp ''a {- b {- c -} d -} e'')))
       = [cp ''{- b {- c -} d -}'']\<close>
  by eval

\<comment> \<open>\<open>->\<close> and \<open>-->\<close> are operators, not comments; comment markers inside a string are literal\<close>
lemma \<open>comments_of (cp ''a --> b'') = Some []\<close>
  by eval

lemma \<open>comments_of (cp ''x '' @ [qt] @ cp ''-- {- y'' @ [qt] @ cp '' z'') = Some []\<close>
  by eval

\<comment> \<open>comments move no token: the columns the parser reads are those of the source\<close>
lemma \<open>map_option (map (s_col \<circ> span) \<circ> snd)
         (caraml_lex (cp ''x {- c -} y'' @ [nl] @ cp ''  -- d'' @ [nl] @ cp ''  z''))
     = Some [0, 10, 2]\<close>
  by eval

text \<open>@{text \<open>f \<rightarrow> \<alpha>\<close>} at the codepoint level and from the raw UTF-8 bytes
  (@{text \<open>\<rightarrow>\<close>} is @{text \<open>E2 86 92\<close>}, @{text \<open>\<alpha>\<close>} is @{text \<open>CE B1\<close>}).\<close>

lemma \<open>map tok (snd (the (caraml_lex [0x66, 0x20, 0x2192, 0x20, 0x3B1]))) = [LId, Arrow, LId]\<close>
  by eval

lemma \<open>map_sum id caraml_lex
         (utf8_decode (map char_of ([0x66, 0x20, 0xE2, 0x86, 0x92, 0x20, 0xCE, 0xB1] :: nat list)))
       = Inr (caraml_lex [0x66, 0x20, 0x2192, 0x20, 0x3B1])\<close>
  by eval

text \<open>A string literal keeps its raw lexeme: \<open>"a\"b"\<close> is one \<^const>\<open>StrL\<close>
  token whose span text still holds the escape; \<^const>\<open>str_pieces\<close> decodes
  it. A string with a hole is a \<^const>\<open>StrI\<close>.\<close>

lemma \<open>map tok (snd (the (caraml_lex [0x22, 0x61, 0x5C, 0x22, 0x62, 0x22]))) = [StrL]\<close>
  and \<open>s_txt (span (hd (snd (the (caraml_lex [0x22, 0x61, 0x5C, 0x22, 0x62, 0x22])))))
       = [0x22, 0x61, 0x5C, 0x22, 0x62, 0x22]\<close>
  and \<open>str_pieces [0x22, 0x61, 0x5C, 0x22, 0x62, 0x22] = [Txt [0x61, 0x22, 0x62]]\<close>
  by eval+

lemma \<open>caraml_lex [0x22, 0x61, 0x5C, 0x22] = None\<close>  \<comment> \<open>\<open>"a\": unterminated\<close>\<close>
  by eval

abbreviation \<open>toks s \<equiv> map tok (snd (the (caraml_lex s)))\<close>

lemma \<open>toks ([qt] @ cp ''a'' @ [dollar, curlyo] @ cp ''b'' @ [curlyc] @ cp ''c'' @ [qt]) = [StrI]\<close>
  \<comment> \<open>\<open>"a${b}c"\<close>\<close>
  by eval

lemma \<open>toks ([qt] @ cp ''a'' @ [bslash, dollar, curlyo] @ cp ''b'' @ [curlyc, qt]) = [StrL]\<close>
  \<comment> \<open>\<open>"a\${b}"\<close>: an escaped dollar opens no hole\<close>
  by eval

lemma \<open>toks [cq, qt, cq] = [CharL]\<close>  \<comment> \<open>\<open>'"'\<close>\<close>
  by eval

lemma \<open>caraml_lex ([qt] @ cp ''a'' @ [dollar, curlyo] @ cp ''b'') = None\<close>  \<comment> \<open>unclosed hole\<close>
  by eval

grammar (relation) grammar_test =
  tokens \<open>(trivia, tok, nat) token\<close>
  terminals "module" = KModule
  productions
    X = "module" LId \<Rightarrow> \<open>\<lambda>m. (span m, trailing m)\<close>

parser parse_test for grammar_test

thm parse_test.sound parse_test.complete

datatype 'a result = Ok 'a
  | Utf8Error utf8_error
  | LexError
  | ParseError

definition read_src where
  \<open>read_src src \<equiv> case utf8_decode src of
    Inl err \<Rightarrow> Utf8Error err
  | Inr src' \<Rightarrow> (case caraml_lex src' of
      None \<Rightarrow> LexError
    | Some (h, ts) \<Rightarrow>
        (case parse_test ts of
          None \<Rightarrow> ParseError
        | Some ast \<Rightarrow> Ok ast)
    )
  \<close>

value \<open>read_src ''module{-lost-}foobar --ba''\<close>

end
