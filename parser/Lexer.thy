theory Lexer
  imports Trivia Literals
begin

section \<open>The CaraML tokens\<close>

text \<open>The tokens are those of \<open>grammar.md\<close> §1: keywords, reserved symbols,
  delimiters, identifiers, operators, selectors and literals. Keywords, symbols
  and delimiters are given by one table each; the token relation and the
  classifiers of the executable lexer both read them. A reserved symbol may
  have several spellings (\<open>->\<close> and \<open>\<rightarrow>\<close>, \<open>\\<close> and \<open>\<lambda>\<close>). A run of symbol
  characters that is not a reserved symbol is an operator, so \<open>\\<close> inside a
  longer run (\<open>\\\<close>, \<open>\->\<close>) is part of an operator, as \<open>|\<close> is in \<open>||\<close>. A
  backticked lower-case name is an operator too.

  \<^bold>\<open>Payloads.\<close> A token carries no decoded value: its record is the plain
  \<^type>\<open>token\<close> of the parser, whose span text \<^const>\<open>s_txt\<close> is the
  lexeme. The decoders of the parser compute the values from the lexeme with
  the readers of \<^theory>\<open>CaraML_Parser.Literals\<close>: \<^text>\<open>int_of_lexeme\<close>
  gives an integer literal's value and suffix, \<^text>\<open>str_pieces\<close> a string's
  text pieces and paths, \<^text>\<open>char_value\<close> a character's codepoint,
  \<^text>\<open>sel_name\<close> a selector's name and \<^text>\<open>op_name\<close> an operator's
  name, without backticks. The lexer's correctness covers them: the lexeme of
  a literal token is exactly what its reader consumes, so the decoders are
  defined on every token the lexer produces (\<^text>\<open>decoders_defined\<close> in
  \<open>Lexer_Correct\<close>). A float keeps its text.\<close>

definition keyword_table :: \<open>(ustring \<times> tok) list\<close> where
  \<open>keyword_table =
     [(cp ''let'', KLet), (cp ''with'', KWith), (cp ''if'', KIf), (cp ''then'', KThen),
      (cp ''else'', KElse), (cp ''match'', KMatch), (cp ''handler'', KHandler),
      (cp ''mask'', KMask), (cp ''return'', KReturn), (cp ''finally'', KFinally),
      (cp ''as'', KAs), (cp ''type'', KType), (cp ''extern'', KExtern),
      (cp ''infixl'', KInfixl), (cp ''infixr'', KInfixr), (cp ''infix'', KInfix),
      (cp ''effect'', KEffect), (cp ''module'', KModule), (cp ''signature'', KSignature),
      (cp ''instance'', KInstance), (cp ''open'', KOpen), (cp ''include'', KInclude)]\<close>

definition symbol_table :: \<open>(ustring \<times> tok) list\<close> where
  \<open>symbol_table =
     [(cp ''='', Assign), (cp '':'', Colon), (cp ''->'', Arrow), ([0x2192], Arrow),
      (cp ''|'', Bar), ([bslash], KLambda)]\<close>

definition delim_table :: \<open>(codepoint \<times> tok) list\<close> where
  \<open>delim_table =
     [(0x28, LP), (0x29, RP), (0x5B, LB), (0x5D, RB), (0x7B, LC), (0x7D, RC),
      (0x2C, Comma), (0x3B, Semi), (0x3BB, KLambda)]\<close>

abbreviation \<open>is_keyword u \<equiv> u \<in> fst ` set keyword_table\<close>
abbreviation \<open>is_symbol u \<equiv> u \<in> fst ` set symbol_table\<close>

text \<open>\<^text>\<open>starts P s\<close>: the input \<^text>\<open>s\<close> begins with a character
  satisfying \<^text>\<open>P\<close>. The token rules use it on the input after a lexeme
  to say that no character could extend the lexeme.\<close>

definition starts :: \<open>(codepoint \<Rightarrow> bool) \<Rightarrow> ustring \<Rightarrow> bool\<close> where
  \<open>starts P s \<longleftrightarrow> (case s of [] \<Rightarrow> False | c # _ \<Rightarrow> P c)\<close>

subsection \<open>The lexer state\<close>

text \<open>Two rules of §1 look at the previous token. A \<open>-\<close> directly before a
  digit starts a negative literal unless it directly follows an operand; a
  selector is tight when nothing separates its dot from the previous token.
  The state records whether the previous token ends an operand and whether it
  was followed by trivia. The grammar names the operand-ending tokens as an
  identifier, a literal, \<open>)\<close>, \<open>]\<close> or \<open>}\<close>; the selectors and the
  wildcard end an operand too, as they stand where identifiers stand.\<close>

record lstate =
  operand :: bool
  adjacent :: bool

definition operand_end :: \<open>tok \<Rightarrow> bool\<close> where
  \<open>operand_end t \<longleftrightarrow>
     t \<in> {LId, UId, KWild, IntL, FloatL, StrL, StrI, CharL, RP, RB, RC,
           TSelL, TSelU, TSelN, LSelL, LSelU, LSelN}\<close>

definition lex_step :: \<open>lstate \<Rightarrow> tok \<Rightarrow> bool \<Rightarrow> lstate\<close> where
  \<open>lex_step st t adj = \<lparr>operand = operand_end t, adjacent = adj\<rparr>\<close>

definition lex_init :: lstate where
  \<open>lex_init = \<lparr>operand = False, adjacent = False\<rparr>\<close>

abbreviation \<open>after_operand st \<equiv> operand st \<and> adjacent st\<close>

text \<open>\<^text>\<open>neg_ok st u\<close>: a lexeme starting with a dash is allowed in state
  \<^text>\<open>st\<close>. \<^text>\<open>sel_tok st c\<close> names the selector token by the state and
  the first character after the dot.\<close>

definition neg_ok :: \<open>lstate \<Rightarrow> ustring \<Rightarrow> bool\<close> where
  \<open>neg_ok st u \<longleftrightarrow> (starts (\<lambda>c. c = dash) u \<longrightarrow> \<not> after_operand st)\<close>

definition sel_tok :: \<open>lstate \<Rightarrow> codepoint \<Rightarrow> tok\<close> where
  \<open>sel_tok st c =
     (if is_digit c then (if adjacent st then TSelN else LSelN)
      else if is_upper c then (if adjacent st then TSelU else LSelU)
      else (if adjacent st then TSelL else LSelL))\<close>

subsection \<open>The token relation\<close>

text \<open>\<^text>\<open>TOKEN(st, u, tail) \<leadsto> t\<close>: in state \<^text>\<open>st\<close>, the lexeme
  \<^text>\<open>u\<close> followed by the input \<^text>\<open>tail\<close> is the token \<^text>\<open>t\<close>.
  Each rule describes a maximal lexeme: a run that the next character does
  not extend, or a literal that its reader consumes exactly. So at most one
  lexeme matches at any input, and the longest match is that one. The
  conditions on \<^text>\<open>tail\<close> make the errors of §1 lexical: \<open>_1\<close>, \<open>1_\<close>,
  \<open>1x\<close> and \<open>0x_F\<close> match no token at all. A lone dash before a digit, where
  a negative literal may start, is not an operator, so \<open>-1u8\<close> is an error
  and not \<open>- 1u8\<close>. A \<open>{\<close> directly before a dash opens a block comment and is
  no delimiter, so an unterminated block comment is an error too.\<close>

inductive match_token :: \<open>lstate \<Rightarrow> ustring \<Rightarrow> ustring \<Rightarrow> tok \<Rightarrow> bool\<close>
  (\<open>(6TOKEN'(_,/ _,/ _')/ \<leadsto>/ _)\<close> [0, 0, 0, 51] 50) where
  Key: \<open>\<lbrakk> (u, t) \<in> set keyword_table; \<not> starts is_idchar tail \<rbrakk> \<Longrightarrow>
    TOKEN(st, u, tail) \<leadsto> t\<close>
| LId: \<open>\<lbrakk> is_lower c; list_all is_idchar cs; \<not> is_keyword (c # cs); \<not> starts is_idchar tail \<rbrakk>
    \<Longrightarrow> TOKEN(st, c # cs, tail) \<leadsto> LId\<close>
| UId: \<open>\<lbrakk> is_upper c; list_all is_idchar cs; \<not> starts is_idchar tail \<rbrakk> \<Longrightarrow>
    TOKEN(st, c # cs, tail) \<leadsto> UId\<close>
| Sym: \<open>\<lbrakk> (u, t) \<in> set symbol_table; \<not> starts is_symchar tail \<rbrakk> \<Longrightarrow>
    TOKEN(st, u, tail) \<leadsto> t\<close>
| Op: \<open>\<lbrakk> u \<noteq> []; list_all is_symchar u; \<not> is_symbol u; \<not> starts is_symchar tail;
          \<not> (u = [dash] \<and> starts is_digit tail \<and> \<not> after_operand st) \<rbrakk> \<Longrightarrow>
    TOKEN(st, u, tail) \<leadsto> Op\<close>
| Delim: \<open>\<lbrakk> (c, t) \<in> set delim_table; \<not> (c = curlyo \<and> starts (\<lambda>d. d = dash) tail) \<rbrakk>
            \<Longrightarrow> TOKEN(st, [c], tail) \<leadsto> t\<close>
| Wild: \<open>\<not> starts is_idchar tail \<Longrightarrow> TOKEN(st, [uscore], tail) \<leadsto> KWild\<close>
| Tick: \<open>\<lbrakk> is_lower c; list_all is_idchar cs; \<not> is_keyword (c # cs) \<rbrakk> \<Longrightarrow>
    TOKEN(st, tick # c # cs @ [tick], tail) \<leadsto> Op\<close>
| Int: \<open>\<lbrakk> read_num (u @ tail) = Some (NInt v sfx, tail); in_range sfx v;
          \<not> starts is_idchar tail; neg_ok st u \<rbrakk> \<Longrightarrow>
    TOKEN(st, u, tail) \<leadsto> IntL\<close>
| Float: \<open>\<lbrakk> read_num (u @ tail) = Some (NFloat, tail); \<not> starts is_idchar tail; neg_ok st u \<rbrakk>
    \<Longrightarrow> TOKEN(st, u, tail) \<leadsto> FloatL\<close>
| Sel: \<open>\<lbrakk> is_idstart c; list_all is_idchar cs; \<not> starts is_idchar tail \<rbrakk> \<Longrightarrow>
    TOKEN(st, dot # c # cs, tail) \<leadsto> sel_tok st c\<close>
| SelN: \<open>\<lbrakk> is_digit c; list_all is_digit cs; \<not> starts is_idchar tail \<rbrakk> \<Longrightarrow>
    TOKEN(st, dot # c # cs, tail) \<leadsto> sel_tok st c\<close>
| Str: \<open>read_str (cs @ tail) = Some (ps, tail) \<Longrightarrow>
    TOKEN(st, qt # cs, tail) \<leadsto> (if has_hole ps then StrI else StrL)\<close>
| Char: \<open>read_char (cs @ tail) = Some (c, tail) \<Longrightarrow> TOKEN(st, cq # cs, tail) \<leadsto> CharL\<close>

text \<open>The bidirectional controls are rejected on the whole source: a control
  is an error wherever it stands, and no escape produces a raw control
  character, so this is the same as rejecting it in every token and every
  comment.\<close>

definition no_bidi :: \<open>ustring \<Rightarrow> bool\<close> where
  \<open>no_bidi s \<longleftrightarrow> list_all (Not \<circ> is_bidi) s\<close>

subsection \<open>Decoders\<close>

text \<open>The decoders read a literal's value from its lexeme; see the payload
  note above. On a lexeme that is not of the token's form they return a
  default, which the correctness theorem rules out.\<close>

definition int_of_lexeme :: \<open>ustring \<Rightarrow> int \<times> suffix option\<close> where
  \<open>int_of_lexeme u = (case read_num u of Some (NInt v sfx, _) \<Rightarrow> (v, sfx) | _ \<Rightarrow> (0, None))\<close>

definition str_pieces :: \<open>ustring \<Rightarrow> piece list\<close> where
  \<open>str_pieces u = (case read_str (tl u) of Some (ps, _) \<Rightarrow> ps | None \<Rightarrow> [])\<close>

definition char_value :: \<open>ustring \<Rightarrow> codepoint\<close> where
  \<open>char_value u = (case read_char (tl u) of Some (c, _) \<Rightarrow> c | None \<Rightarrow> 0)\<close>

definition sel_name :: \<open>ustring \<Rightarrow> ustring\<close> where
  \<open>sel_name u = tl u\<close>

definition op_name :: \<open>ustring \<Rightarrow> ustring\<close> where
  \<open>op_name u = (if starts (\<lambda>c. c = tick) u then butlast (tl u) else u)\<close>

section \<open>The executable lexer\<close>

text \<open>The token scanner reads one token by the class of the first character
  and the state. Identifier and symbol runs are classified by the tables;
  numerals, strings and characters are cut where their reader stops.
  \<^text>\<open>cut s r\<close> is the part of \<^text>\<open>s\<close> before its suffix \<^text>\<open>r\<close>.\<close>

definition cut :: \<open>ustring \<Rightarrow> ustring \<Rightarrow> ustring\<close> where
  \<open>cut s r = take (length s - length r) s\<close>

definition classify_id :: \<open>ustring \<Rightarrow> tok\<close> where
  \<open>classify_id u =
     (case map_of keyword_table u of
        Some t \<Rightarrow> t
      | None \<Rightarrow> if is_upper (hd u) then UId else LId)\<close>

definition classify_sym :: \<open>ustring \<Rightarrow> tok\<close> where
  \<open>classify_sym u = (case map_of symbol_table u of Some t \<Rightarrow> t | None \<Rightarrow> Op)\<close>

definition classify_delim :: \<open>codepoint \<Rightarrow> tok\<close> where
  \<open>classify_delim c = the (map_of delim_table c)\<close>

type_synonym scan = \<open>(tok \<times> ustring \<times> ustring) option\<close>

definition scan_num :: \<open>ustring \<Rightarrow> scan\<close> where
  \<open>scan_num s =
     (case read_num s of
        None \<Rightarrow> None
      | Some (n, r) \<Rightarrow>
          if starts is_idchar r then None
          else (case n of
                  NFloat \<Rightarrow> Some (FloatL, cut s r, r)
                | NInt v sfx \<Rightarrow> if in_range sfx v then Some (IntL, cut s r, r) else None))\<close>

definition scan_sel :: \<open>lstate \<Rightarrow> ustring \<Rightarrow> scan\<close> where
  \<open>scan_sel st s =
     (case s of
        [] \<Rightarrow> None
      | c # cs \<Rightarrow>
          if is_digit c then
            (let r = dropWhile is_digit cs
             in if starts is_idchar r then None
                else Some (sel_tok st c, dot # c # takeWhile is_digit cs, r))
          else if is_idstart c then
            Some (sel_tok st c, dot # c # takeWhile is_idchar cs, dropWhile is_idchar cs)
          else None)\<close>

definition scan_str :: \<open>ustring \<Rightarrow> scan\<close> where
  \<open>scan_str s =
     (case read_str s of
        None \<Rightarrow> None
      | Some (ps, r) \<Rightarrow> Some (if has_hole ps then StrI else StrL, qt # cut s r, r))\<close>

definition scan_char :: \<open>ustring \<Rightarrow> scan\<close> where
  \<open>scan_char s =
     (case read_char s of None \<Rightarrow> None | Some (c, r) \<Rightarrow> Some (CharL, cq # cut s r, r))\<close>

definition scan_tick :: \<open>ustring \<Rightarrow> scan\<close> where
  \<open>scan_tick s =
     (case s of
        [] \<Rightarrow> None
      | c # cs \<Rightarrow>
          if is_lower c then
            (let u = c # takeWhile is_idchar cs
             in case dropWhile is_idchar cs of
                  k # r \<Rightarrow> if k = tick \<and> \<not> is_keyword u then Some (Op, tick # u @ [tick], r)
                           else None
                | [] \<Rightarrow> None)
          else None)\<close>

fun lex_token :: \<open>lstate \<Rightarrow> ustring \<Rightarrow> scan\<close> where
  \<open>lex_token st [] = None\<close>
| \<open>lex_token st (c # cs) =
    (if is_idstart c then
       (let u = c # takeWhile is_idchar cs in Some (classify_id u, u, dropWhile is_idchar cs))
     else if c = dash \<and> starts is_digit cs \<and> \<not> after_operand st then scan_num (c # cs)
     else if is_symchar c then
       (let u = c # takeWhile is_symchar cs in Some (classify_sym u, u, dropWhile is_symchar cs))
     else if is_digit c then scan_num (c # cs)
     else if is_delim c then
       (if c = curlyo \<and> starts (\<lambda>d. d = dash) cs then None else Some (classify_delim c, [c], cs))
     else if c = uscore then (if starts is_idchar cs then None else Some (KWild, [c], cs))
     else if c = dot then scan_sel st cs
     else if c = qt then scan_str cs
     else if c = cq then scan_char cs
     else if c = tick then scan_tick cs
     else None)\<close>

text \<open>\<^text>\<open>lex_body\<close> alternates \<^const>\<open>lex_token\<close> and \<^const>\<open>lex_trivia\<close>,
  passing the cursor and the state along, and stops at the first input that
  is not a token. \<^text>\<open>caraml_lex\<close> rejects a source with a bidirectional
  control, reads the header, then the body from the initial state, and
  succeeds only if nothing remains.\<close>

(*<*)
lemma cut_split: \<open>suffix r s \<Longrightarrow> cut s r @ r = s\<close>
  by (auto simp: cut_def suffix_def)

lemma cut_length: \<open>suffix r s \<Longrightarrow> length (cut s r) = length s - length r\<close>
  by (auto simp: cut_def suffix_def)

lemma dropWhile_Cons_length: \<open>dropWhile P xs = y # ys \<Longrightarrow> length ys < length xs\<close>
  using length_dropWhile_le[of P xs] by simp

lemma lex_token_size: \<open>lex_token st s = Some (t, u, r) \<Longrightarrow> length r < length s\<close>
  by (cases s)
     (auto simp: Let_def scan_num_def scan_sel_def scan_str_def scan_char_def scan_tick_def
           split: if_splits option.splits prod.splits numeral.splits list.splits
           dest!: read_num_suffix read_str_suffix read_char_suffix dropWhile_Cons_length
           intro: le_less_trans[OF length_dropWhile_le] le_imp_less_Suc[OF length_dropWhile_le])
(*>*)

function (sequential) lex_body where
  \<open>lex_body st line col off acc [] = Some (rev acc, [])\<close>
| \<open>lex_body st line col off acc cs = (
     case lex_token st cs of
       None \<Rightarrow> Some (rev acc, cs)
     | Some (t, u, cs\<^sub>1) \<Rightarrow>
         (case lex_trivia (advance_line line u) (advance_col col u) (off + length u) cs\<^sub>1 of
            None \<Rightarrow> None
          | Some (trs, line\<^sub>2, col\<^sub>2, off\<^sub>2, cs\<^sub>2) \<Rightarrow>
              lex_body (lex_step st t (trs = [])) line\<^sub>2 col\<^sub>2 off\<^sub>2
                (\<lparr>tok = t, span = span_of line col off u, trailing = trs\<rparr> # acc) cs\<^sub>2))\<close>
  by pat_completeness auto

termination
  by (relation \<open>measure (\<lambda>(_,_,_,_,_,cs). length cs)\<close>)
     (auto simp del: lex_token.simps dest!: lex_token_size lex_trivia_size)

definition caraml_lex ::
  \<open>ustring \<Rightarrow> ((trivia, codepoint) header \<times> (trivia, tok, codepoint) token list) option\<close>
where
  \<open>caraml_lex cs =
     (if no_bidi cs then do {
        (header, line, col, off, cs') \<leftarrow> lex_trivia 0 0 0 cs;
        (body, tail) \<leftarrow> lex_body lex_init line col off [] cs';
        if tail = [] then Some (header, body) else None
      } else None)\<close>

text \<open>Comments are not lost: they sit, with their spans, in the header and in
  each token's \<^const>\<open>trailing\<close> trivia. \<^text>\<open>comments_of\<close> collects
  them in source order; it is the comment channel for tooling.\<close>

definition comments_of :: \<open>ustring \<Rightarrow> (trivia \<times> codepoint span) list option\<close> where
  \<open>comments_of cs = map_option
     (\<lambda>(header, body). filter (\<lambda>(t, _). t \<noteq> Space) (header @ concat (map trailing body)))
     (caraml_lex cs)\<close>

end
