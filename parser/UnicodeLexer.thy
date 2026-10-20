theory UnicodeLexer
  imports Grammar_Command.Token Tok Unicode
begin

section \<open>The Unicode alphabet of the lexer\<close>

text \<open>Character classes over \<^typ>\<open>codepoint\<close>, as finite unions of codepoint
  intervals; extending the alphabet is a local change to these definitions and
  their disjointness lemmas (linear arithmetic). The lexer proper lives in
  \<^text>\<open>Lexer\<close>.

  The identifier classes take the UAX 31 approach of case-classified letter
  ranges without embedding the character database: ASCII letters plus, as a
  representative non-ASCII block, Greek. \<^text>\<open>\<alpha>\<close> (\<^text>\<open>U+03B1\<close>) is a
  lower-case identifier start, \<^text>\<open>\<Lambda>\<close> (\<^text>\<open>U+039B\<close>) an upper-case one;
  case separates value identifiers from constructor, type and module
  identifiers exactly as in ASCII. Keywords are ASCII, so no extended letter
  spells a keyword. Symbol characters add the Arrows and Mathematical
  Operators blocks (\<^text>\<open>U+2190..U+22FF\<close>), so \<^text>\<open>\<rightarrow>\<close>, \<^text>\<open>\<circ>\<close>,
  \<^text>\<open>\<oplus>\<close> are available as operators.

  \<^term>\<open>cp\<close> embeds ASCII string literals into codepoint sequences.\<close>

abbreviation cp :: \<open>string \<Rightarrow> ustring\<close> where
  \<open>cp \<equiv> map of_char\<close>

text \<open>\<^const>\<open>of_char\<close> on the ASCII characters, evaluated once: every proof that
  compares literal lexemes otherwise re-evaluates \<^const>\<open>of_char\<close> through
  \<^const>\<open>horner_sum\<close> for each character.\<close>

lemma of_char_literals[simp]:
  \<open>of_char (CHR 0x09) = (0x09 :: nat)\<close>
  \<open>of_char (CHR 0x0A) = (0x0A :: nat)\<close>
  \<open>of_char (CHR 0x0D) = (0x0D :: nat)\<close>
  \<open>of_char (CHR '' '') = (0x20 :: nat)\<close>
  \<open>of_char (CHR ''!'') = (0x21 :: nat)\<close>
  \<open>of_char (CHR 0x22) = (0x22 :: nat)\<close>
  \<open>of_char (CHR ''#'') = (0x23 :: nat)\<close>
  \<open>of_char (CHR ''$'') = (0x24 :: nat)\<close>
  \<open>of_char (CHR ''%'') = (0x25 :: nat)\<close>
  \<open>of_char (CHR ''&'') = (0x26 :: nat)\<close>
  \<open>of_char (CHR 0x27) = (0x27 :: nat)\<close>
  \<open>of_char (CHR ''('') = (0x28 :: nat)\<close>
  \<open>of_char (CHR '')'') = (0x29 :: nat)\<close>
  \<open>of_char (CHR ''*'') = (0x2A :: nat)\<close>
  \<open>of_char (CHR ''+'') = (0x2B :: nat)\<close>
  \<open>of_char (CHR '','') = (0x2C :: nat)\<close>
  \<open>of_char (CHR ''-'') = (0x2D :: nat)\<close>
  \<open>of_char (CHR ''.'') = (0x2E :: nat)\<close>
  \<open>of_char (CHR ''/'') = (0x2F :: nat)\<close>
  \<open>of_char (CHR ''0'') = (0x30 :: nat)\<close>
  \<open>of_char (CHR ''1'') = (0x31 :: nat)\<close>
  \<open>of_char (CHR ''2'') = (0x32 :: nat)\<close>
  \<open>of_char (CHR ''3'') = (0x33 :: nat)\<close>
  \<open>of_char (CHR ''4'') = (0x34 :: nat)\<close>
  \<open>of_char (CHR ''5'') = (0x35 :: nat)\<close>
  \<open>of_char (CHR ''6'') = (0x36 :: nat)\<close>
  \<open>of_char (CHR ''7'') = (0x37 :: nat)\<close>
  \<open>of_char (CHR ''8'') = (0x38 :: nat)\<close>
  \<open>of_char (CHR ''9'') = (0x39 :: nat)\<close>
  \<open>of_char (CHR '':'') = (0x3A :: nat)\<close>
  \<open>of_char (CHR '';'') = (0x3B :: nat)\<close>
  \<open>of_char (CHR ''<'') = (0x3C :: nat)\<close>
  \<open>of_char (CHR ''='') = (0x3D :: nat)\<close>
  \<open>of_char (CHR ''>'') = (0x3E :: nat)\<close>
  \<open>of_char (CHR ''?'') = (0x3F :: nat)\<close>
  \<open>of_char (CHR ''@'') = (0x40 :: nat)\<close>
  \<open>of_char (CHR ''A'') = (0x41 :: nat)\<close>
  \<open>of_char (CHR ''B'') = (0x42 :: nat)\<close>
  \<open>of_char (CHR ''C'') = (0x43 :: nat)\<close>
  \<open>of_char (CHR ''D'') = (0x44 :: nat)\<close>
  \<open>of_char (CHR ''E'') = (0x45 :: nat)\<close>
  \<open>of_char (CHR ''F'') = (0x46 :: nat)\<close>
  \<open>of_char (CHR ''G'') = (0x47 :: nat)\<close>
  \<open>of_char (CHR ''H'') = (0x48 :: nat)\<close>
  \<open>of_char (CHR ''I'') = (0x49 :: nat)\<close>
  \<open>of_char (CHR ''J'') = (0x4A :: nat)\<close>
  \<open>of_char (CHR ''K'') = (0x4B :: nat)\<close>
  \<open>of_char (CHR ''L'') = (0x4C :: nat)\<close>
  \<open>of_char (CHR ''M'') = (0x4D :: nat)\<close>
  \<open>of_char (CHR ''N'') = (0x4E :: nat)\<close>
  \<open>of_char (CHR ''O'') = (0x4F :: nat)\<close>
  \<open>of_char (CHR ''P'') = (0x50 :: nat)\<close>
  \<open>of_char (CHR ''Q'') = (0x51 :: nat)\<close>
  \<open>of_char (CHR ''R'') = (0x52 :: nat)\<close>
  \<open>of_char (CHR ''S'') = (0x53 :: nat)\<close>
  \<open>of_char (CHR ''T'') = (0x54 :: nat)\<close>
  \<open>of_char (CHR ''U'') = (0x55 :: nat)\<close>
  \<open>of_char (CHR ''V'') = (0x56 :: nat)\<close>
  \<open>of_char (CHR ''W'') = (0x57 :: nat)\<close>
  \<open>of_char (CHR ''X'') = (0x58 :: nat)\<close>
  \<open>of_char (CHR ''Y'') = (0x59 :: nat)\<close>
  \<open>of_char (CHR ''Z'') = (0x5A :: nat)\<close>
  \<open>of_char (CHR ''['') = (0x5B :: nat)\<close>
  \<open>of_char (CHR 0x5C) = (0x5C :: nat)\<close>
  \<open>of_char (CHR '']'') = (0x5D :: nat)\<close>
  \<open>of_char (CHR ''^'') = (0x5E :: nat)\<close>
  \<open>of_char (CHR ''_'') = (0x5F :: nat)\<close>
  \<open>of_char (CHR ''`'') = (0x60 :: nat)\<close>
  \<open>of_char (CHR ''a'') = (0x61 :: nat)\<close>
  \<open>of_char (CHR ''b'') = (0x62 :: nat)\<close>
  \<open>of_char (CHR ''c'') = (0x63 :: nat)\<close>
  \<open>of_char (CHR ''d'') = (0x64 :: nat)\<close>
  \<open>of_char (CHR ''e'') = (0x65 :: nat)\<close>
  \<open>of_char (CHR ''f'') = (0x66 :: nat)\<close>
  \<open>of_char (CHR ''g'') = (0x67 :: nat)\<close>
  \<open>of_char (CHR ''h'') = (0x68 :: nat)\<close>
  \<open>of_char (CHR ''i'') = (0x69 :: nat)\<close>
  \<open>of_char (CHR ''j'') = (0x6A :: nat)\<close>
  \<open>of_char (CHR ''k'') = (0x6B :: nat)\<close>
  \<open>of_char (CHR ''l'') = (0x6C :: nat)\<close>
  \<open>of_char (CHR ''m'') = (0x6D :: nat)\<close>
  \<open>of_char (CHR ''n'') = (0x6E :: nat)\<close>
  \<open>of_char (CHR ''o'') = (0x6F :: nat)\<close>
  \<open>of_char (CHR ''p'') = (0x70 :: nat)\<close>
  \<open>of_char (CHR ''q'') = (0x71 :: nat)\<close>
  \<open>of_char (CHR ''r'') = (0x72 :: nat)\<close>
  \<open>of_char (CHR ''s'') = (0x73 :: nat)\<close>
  \<open>of_char (CHR ''t'') = (0x74 :: nat)\<close>
  \<open>of_char (CHR ''u'') = (0x75 :: nat)\<close>
  \<open>of_char (CHR ''v'') = (0x76 :: nat)\<close>
  \<open>of_char (CHR ''w'') = (0x77 :: nat)\<close>
  \<open>of_char (CHR ''x'') = (0x78 :: nat)\<close>
  \<open>of_char (CHR ''y'') = (0x79 :: nat)\<close>
  \<open>of_char (CHR ''z'') = (0x7A :: nat)\<close>
  \<open>of_char (CHR ''{'') = (0x7B :: nat)\<close>
  \<open>of_char (CHR ''|'') = (0x7C :: nat)\<close>
  \<open>of_char (CHR ''}'') = (0x7D :: nat)\<close>
  \<open>of_char (CHR ''~'') = (0x7E :: nat)\<close>
  by simp_all

declare of_char_Char[simp del]

definition is_lower :: \<open>codepoint \<Rightarrow> bool\<close> where
  \<open>is_lower c \<longleftrightarrow> (0x61 \<le> c \<and> c \<le> 0x7A) \<or> (0x3B1 \<le> c \<and> c \<le> 0x3C9 \<and> c \<noteq> 0x3BB)\<close>

definition is_upper :: \<open>codepoint \<Rightarrow> bool\<close> where
  \<open>is_upper c \<longleftrightarrow> (0x41 \<le> c \<and> c \<le> 0x5A) \<or> (0x391 \<le> c \<and> c \<le> 0x3A9 \<and> c \<noteq> 0x3A2)\<close>

definition is_alpha :: \<open>codepoint \<Rightarrow> bool\<close> where
  \<open>is_alpha c \<longleftrightarrow> is_lower c \<or> is_upper c\<close>

definition is_digit :: \<open>codepoint \<Rightarrow> bool\<close> where
  \<open>is_digit c \<longleftrightarrow> 0x30 \<le> c \<and> c \<le> 0x39\<close>

definition is_hexdigit :: \<open>codepoint \<Rightarrow> bool\<close> where
  \<open>is_hexdigit c \<longleftrightarrow> is_digit c \<or> (0x61 \<le> c \<and> c \<le> 0x66) \<or> (0x41 \<le> c \<and> c \<le> 0x46)\<close>

definition is_bindigit :: \<open>codepoint \<Rightarrow> bool\<close> where
  \<open>is_bindigit c \<longleftrightarrow> c = 0x30 \<or> c = 0x31\<close>

text \<open>An identifier starts with a letter and continues with letters, digits,
  underscore and prime. The underscore alone is the wildcard token; it is not
  an identifier start, so \<open>_1\<close> and \<open>_x\<close> are no identifiers.\<close>

definition is_idstart :: \<open>codepoint \<Rightarrow> bool\<close> where
  \<open>is_idstart c \<longleftrightarrow> is_lower c \<or> is_upper c\<close>

definition is_idchar :: \<open>codepoint \<Rightarrow> bool\<close> where
  \<open>is_idchar c \<longleftrightarrow> is_alpha c \<or> is_digit c \<or> c = 0x5F \<or> c = 0x27\<close>

text \<open>Symbol characters form operators and the reserved symbols. The backslash
  is one of them, so that \<open>\\<close> spells \<open>\<lambda>\<close> the way \<open>|\<close> spells the bar: alone it
  is the reserved symbol, in a longer run it is part of an operator. The dot
  is not a symbol character (it occurs only in selectors and numerals).\<close>

definition is_symchar :: \<open>codepoint \<Rightarrow> bool\<close> where
  \<open>is_symchar c \<longleftrightarrow>
     c \<in> {0x21, 0x23, 0x24, 0x25, 0x26, 0x2A, 0x2B, 0x2D, 0x2F, 0x3A,
          0x3C, 0x3D, 0x3E, 0x3F, 0x40, 0x5C, 0x5E, 0x7C, 0x7E} \<or>
     (0x2190 \<le> c \<and> c \<le> 0x22FF)\<close>

text \<open>Delimiters are single-character tokens. \<open>\<lambda>\<close> (U+03BB) is one, not a
  letter, so that \<open>\<lambda>x\<close> reads as \<open>\<lambda>\<close> followed by \<open>x\<close>.\<close>

definition is_delim :: \<open>codepoint \<Rightarrow> bool\<close> where
  \<open>is_delim c \<longleftrightarrow> c \<in> {0x28, 0x29, 0x2C, 0x3B, 0x5B, 0x5D, 0x7B, 0x7D, 0x3BB}\<close>

text \<open>UAX #31 \<open>Pattern_White_Space\<close>, and the newlines among them.\<close>

definition is_whitespace :: \<open>codepoint \<Rightarrow> bool\<close> where
  \<open>is_whitespace c \<longleftrightarrow>
      0x09 \<le> c \<and> c \<le> 0x0D             \<comment>\<open>TAB, LF, VT, FF, CR\<close>
    \<or> c = 0x20                         \<comment>\<open>SPACE\<close>
    \<or> c = 0x85                         \<comment>\<open>NEL\<close>
    \<or> c = 0x200E \<or> c = 0x200F          \<comment>\<open>LRM, RLM\<close>
    \<or> c = 0x2028 \<or> c = 0x2029\<close>         \<comment>\<open>LS, PS\<close>

definition is_newline :: \<open>nat \<Rightarrow> bool\<close> where
  \<open>is_newline c \<longleftrightarrow>
      0x0A \<le> c \<and> c \<le> 0x0D             \<comment>\<open>LF, VT, FF, CR\<close>
    \<or> c = 0x85                         \<comment>\<open>NEL\<close>
    \<or> c = 0x2028 \<or> c = 0x2029\<close>         \<comment>\<open>LS, PS\<close>

text \<open>The bidirectional controls (the embeddings, overrides and isolates) are
  rejected wherever they appear unescaped, comments and strings included,
  because of the Trojan Source attack (Boucher and Anderson 2021).\<close>

definition is_bidi :: \<open>codepoint \<Rightarrow> bool\<close> where
  \<open>is_bidi c \<longleftrightarrow> (0x202A \<le> c \<and> c \<le> 0x202E) \<or> (0x2066 \<le> c \<and> c \<le> 0x2069)\<close>

abbreviation nl :: codepoint where \<open>nl \<equiv> 0x0A\<close>
abbreviation sp :: codepoint where \<open>sp \<equiv> 0x20\<close>
abbreviation qt :: codepoint where \<open>qt \<equiv> 0x22\<close>
abbreviation cq :: codepoint where \<open>cq \<equiv> 0x27\<close>
abbreviation bslash :: codepoint where \<open>bslash \<equiv> 0x5C\<close>
abbreviation curlyo :: codepoint where \<open>curlyo \<equiv> 0x7B\<close>
abbreviation curlyc :: codepoint where \<open>curlyc \<equiv> 0x7D\<close>
abbreviation dash :: codepoint where \<open>dash \<equiv> 0x2D\<close>
abbreviation dollar :: codepoint where \<open>dollar \<equiv> 0x24\<close>
abbreviation dot :: codepoint where \<open>dot \<equiv> 0x2E\<close>
abbreviation uscore :: codepoint where \<open>uscore \<equiv> 0x5F\<close>
abbreviation tick :: codepoint where \<open>tick \<equiv> 0x60\<close>

text \<open>The char quote \<open>'\<close> (U+0027) doubles as the identifier prime: it is an
  identifier continuation but not a start, so \<open>'a'\<close> is a char literal while
  \<open>f'a'\<close> is one identifier.\<close>

lemmas class_defs = is_idstart_def is_idchar_def is_alpha_def is_lower_def is_upper_def
  is_digit_def is_hexdigit_def is_bindigit_def is_symchar_def is_delim_def is_bidi_def

end
