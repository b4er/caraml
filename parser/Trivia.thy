theory Trivia
  imports Lexing UnicodeLexer
begin

section \<open>Trivia: whitespace and comments\<close>

text \<open>The trivia of CaraML source are whitespace, line comments and block
  comments, instantiating the trivia part of \<^theory>\<open>CaraML_Parser.Lexing\<close>:
  the relation, then the executable scanner. A block comment body is balanced:
  it contains no unmatched \<^verbatim>\<open>{-\<close> or \<^verbatim>\<open>-}\<close>, nested comments are
  again balanced, and it does not end in \<^verbatim>\<open>{\<close>, which would fuse with
  the closing \<^verbatim>\<open>-}\<close>. Bidirectional controls are excluded from the
  whole source by the lexer, so no trivium needs to mention them.\<close>

datatype trivia = Space | LineComment | BlockComment

abbreviation \<open>comment_delim cs \<equiv> prefix (cp ''{-'') cs \<or> prefix (cp ''-}'') cs\<close>

inductive comment_body where
  Nil:  \<open>comment_body []\<close>
| Chr:  \<open>\<lbrakk> \<not> comment_delim (c # cs); \<not> (c = curlyo \<and> cs = []); comment_body cs \<rbrakk>
          \<Longrightarrow> comment_body (c # cs)\<close>
| Nest: \<open>\<lbrakk> comment_body b; comment_body cs \<rbrakk> \<Longrightarrow> comment_body (cp ''{-'' @ b @ cp ''-}'' @ cs)\<close>

text \<open>Whitespace is a nonempty run of whitespace characters. A line comment is
  a run of at least two dashes that no symbol character extends, followed by
  the rest of the line. A block comment is a balanced body between
  \<^verbatim>\<open>{-\<close> and \<^verbatim>\<open>-}\<close>.\<close>

inductive match_trivia where
  Space:  \<open>\<lbrakk> cs \<noteq> []; list_all is_whitespace cs \<rbrakk> \<Longrightarrow> match_trivia cs tail Space\<close>
| Line:   \<open>\<lbrakk> n = length (takeWhile (\<lambda>c. c = dash) cs);  2 \<le> n;
               drop n cs = [] \<or> \<not> is_symchar (hd (drop n cs));
               list_all (Not \<circ> is_newline) cs;
               tail = [] \<or> \<not> is_symchar (hd tail) \<rbrakk>
            \<Longrightarrow> match_trivia cs tail LineComment\<close>
| Block:  \<open>comment_body cs \<Longrightarrow> match_trivia (cp ''{-'' @ cs @ cp ''-}'') tail BlockComment\<close>

lemma tr_deterministic:
  assumes \<open>match_trivia ts tail t\<close> and \<open>match_trivia ts tail t'\<close>
  shows \<open>t = t'\<close>
  using assms
proof (induction arbitrary: t' rule: match_trivia.induct)
  case (Space cs)
  from Space.prems show ?case
  proof (cases rule: match_trivia.cases)
    case Line
    with Space.hyps have False
      by (cases cs) (auto simp: is_whitespace_def)
    then show ?thesis ..
  qed (use Space.hyps in \<open>auto simp: is_whitespace_def\<close>)
next
  case (Line n cs)
  from Line.prems show ?case
  proof (cases rule: match_trivia.cases)
    case Space
    with Nil Line.hyps have \<open>cs \<noteq> [] \<and> \<not> is_whitespace (hd cs)\<close>
      by (cases cs; cases \<open>hd cs = dash\<close>; simp add: is_whitespace_def)
    with Space show ?thesis
      by (cases cs) auto
  qed (use Line.hyps in auto)
qed (auto elim: match_trivia.cases simp: is_whitespace_def)

lemma match_trivia_nonempty: \<open>match_trivia u tail r \<Longrightarrow> u \<noteq> []\<close>
  by (auto elim: match_trivia.cases)

text \<open>The trivia predicate is deterministic and rejects the empty string.\<close>

global_interpretation trivia_lang match_trivia is_newline
  by unfold_locales (auto dest: tr_deterministic match_trivia_nonempty)

section \<open>The trivia scanner\<close>

text \<open>\<^text>\<open>lex_block_cmt k acc cs\<close> scans the body of a block comment at
  nesting depth \<^text>\<open>k\<close>, accumulating the characters read in reverse.
  \<^text>\<open>lex_trivia'\<close> reads whitespace runs, line comments and block
  comments until neither applies; \<^text>\<open>lex_trivia\<close> starts it with an
  empty accumulator. Each takes the cursor \<^text>\<open>(line, col, off)\<close> and
  returns the lexemes it read, the cursor after them, and the remaining
  input.\<close>

fun lex_block_cmt where
  \<open>lex_block_cmt (k :: nat) acc (c\<^sub>1 # c\<^sub>2 # cs) = (
    if [c\<^sub>1,c\<^sub>2] = cp ''{-'' then
      lex_block_cmt (k+1) (c\<^sub>2 # c\<^sub>1 # acc) cs
    else if [c\<^sub>1,c\<^sub>2] = cp ''-}'' then
      (if k = 1 then Some (rev acc @ [c\<^sub>1,c\<^sub>2], cs) else
        lex_block_cmt (k-1) (c\<^sub>2 # c\<^sub>1 # acc) cs)
    else lex_block_cmt k (c\<^sub>1 # acc) (c\<^sub>2 # cs)
  )\<close>
| \<open>lex_block_cmt _ _ _ = None\<close>

(*<*)
lemma lex_block_cmt_size: \<open>lex_block_cmt k acc cs = Some (x, cs') \<Longrightarrow> length cs' \<le> length cs\<close>
  by (induction k acc cs arbitrary: x cs' rule: lex_block_cmt.induct)
     (auto split: if_splits)
(*>*)

function (sequential) lex_trivia' where
  \<open>lex_trivia' line col off acc (c\<^sub>1 # c\<^sub>2 # cs) =
     (if is_whitespace c\<^sub>1 then (
       let
         consume = c\<^sub>1 # takeWhile is_whitespace (c\<^sub>2 # cs);
         rest = drop (length consume) (c\<^sub>1 # c\<^sub>2 # cs);

         line' = advance_line line consume;
         col' = advance_col col consume;
         off' = off + length consume
        in
          lex_trivia' line' col' off'
            ((Space, span_of line col off consume) # acc) rest
     ) else if [c\<^sub>1, c\<^sub>2] = cp ''--'' then (
       let
         u = takeWhile ((=) dash) cs;
         after = drop (length u) cs
        in
          if after = [] \<or> \<not> is_symchar (hd after) then (
            let
              body = takeWhile (\<lambda>c. \<not> is_newline c) after;
              consume = c\<^sub>1 # c\<^sub>2 # (u @ body);
              rest = drop (length body) after;

              line' = advance_line line consume;
              col' = advance_col col consume;
              off' = off + length consume
             in
               lex_trivia' line' col' off'
                 ((LineComment, span_of line col off consume) # acc) rest
          ) else
            Some (acc, line, col, off, c\<^sub>1 # c\<^sub>2 # cs)
     ) else if [c\<^sub>1, c\<^sub>2] = cp ''{-'' then (
        case lex_block_cmt 1 [] cs of
          Some (tail, rest) \<Rightarrow> (
            let
              consume = cp ''{-'' @ tail;

              line' = advance_line line consume;
              col' = advance_col col consume;
              off' = off + length consume
             in
               lex_trivia' line' col' off'
                 ((BlockComment, span_of line col off consume) # acc) rest)
        | _ \<Rightarrow> Some (acc, line, col, off, c\<^sub>1 # c\<^sub>2 # cs)
     ) else Some (acc, line, col, off, c\<^sub>1 # c\<^sub>2 # cs))\<close>
| \<open>lex_trivia' line col off acc cs =
    (if cs \<noteq> '''' \<and> list_all is_whitespace cs then
      Some ((Space, span_of line col off cs) # acc,
            advance_line line cs, advance_col col cs, off + length cs, [])
     else Some (acc, line, col, off, cs))\<close>
  by auto pat_completeness

termination
  by (relation \<open>measure (\<lambda>(line,col,off,acc,cs). length cs)\<close>)
    (auto dest: lex_block_cmt_size)

definition \<open>lex_trivia line col off cs =
  map_option (\<lambda>(acc, line, col, off, rest). (rev acc, line, col, off, rest))
    (lex_trivia' line col off [] cs)\<close>

(*<*)
lemma lex_trivia'_size:
  \<open>lex_trivia' line col off acc cs = Some (a, line', col', off', cs') \<Longrightarrow> length cs' \<le> length cs\<close>
  by (induction line col off acc cs arbitrary: a line' col' off' cs' rule: lex_trivia'.induct;
      fastforce split: if_splits option.splits dest: lex_block_cmt_size
                simp: Let_def)

lemma lex_trivia_size:
  \<open>lex_trivia line col off cs = Some (x, l', c', o', cs') \<Longrightarrow> length cs' \<le> length cs\<close>
  by (auto simp add: lex_trivia_def dest: lex_trivia'_size)

lemma advance_line_append[simp]:
  \<open>advance_line line (u @ v) = advance_line (advance_line line u) v\<close>
  by (simp add: advance_line_def)

lemma advance_col_append[simp]:
  \<open>advance_col col (u @ v) = advance_col (advance_col col u) v\<close>
  by (auto simp add: advance_col_def takeWhile_append)

lemmas advance_append = advance_line_append advance_col_append

lemma consumed_rev_Cons:
  \<open>consumed (rev ((t, sp') # xs)) = consumed (rev xs) @ s_txt sp'\<close>
  by (simp add: consumed_def List.bind_def)

lemma lex_trivia'_defined: \<open>lex_trivia' line col off acc cs \<noteq> None\<close>
  by (induction line col off acc cs rule: lex_trivia'.induct)
     (auto simp: Let_def split: option.splits)

lemma lex_trivia_ex_Some:
  \<open>\<exists>r line' col' off' rest. lex_trivia line col off cs = Some (r, line', col', off', rest)\<close>
  using lex_trivia'_defined[of line col off \<open>[]\<close> cs]
  by (cases \<open>lex_trivia' line col off [] cs\<close>) (auto simp: lex_trivia_def)
(*>*)

end
