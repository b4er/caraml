theory Lexing
  imports
    Grammar_Command.Token
    "HOL-Library.Monad_Syntax"
    "HOL-Library.Sublist"
begin

section \<open>Longest-match lexing with trivia\<close>

text \<open>A lexer turns a character sequence into a token sequence. The lexer
  specified here records more than the tokens: every token carries its source
  span (line, column, offset, length and text) and the \<^emph>\<open>trivia\<close> that
  follow it, that is the whitespace and comments the grammar ignores but
  diagnostics and a source-preserving unparser need. The trivia before the
  first token form the \<^emph>\<open>header\<close>.

  The specification is stated for an arbitrary character type \<^typ>\<open>'ch\<close>,
  token type \<^typ>\<open>'tok\<close> and trivia type \<^typ>\<open>'trivia\<close>. Two predicates say
  which strings are trivia and which are tokens; the longest-match rule then
  determines the lexer. Both predicates see the input after the candidate
  lexeme, so a rule can forbid what follows (a line comment that a longer
  operator extends, a numeral directly followed by a letter). The token
  predicate also depends on a \<^emph>\<open>state\<close> of type \<^typ>\<open>'st\<close> that every token
  advances together with the fact whether trivia separate it from the next
  lexeme: CaraML needs it for negative literals and tight selectors. A
  predicate on the whole input says which sources are readable at all. The
  theory \<open>Lexer\<close> instantiates the parameters for CaraML and gives an
  executable lexer that is sound and complete for that instance.\<close>

type_synonym ('trivia, 'ch) header = \<open>('trivia \<times> 'ch span) list\<close>

definition strip :: \<open>('tok, 'ch) token list \<Rightarrow> 'tok list\<close> where
  \<open>strip = map tok\<close>

text \<open>A lexed token is a token with its span, extended by the trivia that
  follow it. A header is the list of trivia before the first token, each with
  its span; \<^const>\<open>strip\<close> forgets spans and trivia.\<close>

record ('trivia, 'tok, 'ch) token = \<open>('tok, 'ch) Token.token\<close> +
  trailing :: \<open>('trivia \<times> 'ch span) list\<close>

subsection \<open>Longest matches\<close>

text \<open>\<^text>\<open>match p s\<close> collects the prefixes of \<^text>\<open>s\<close> that \<^text>\<open>p\<close>
  accepts, each paired with its reading. \<^text>\<open>match_ctx\<close> does the same for
  a predicate that also inspects the input after the prefix.\<close>

definition match :: \<open>('ch list \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'ch list \<Rightarrow> ('a \<times> 'ch list) set\<close> where
  \<open>match p s = {(t, u) | t u. prefix u s \<and> p u t}\<close>

definition match_ctx ::
  \<open>('ch list \<Rightarrow> 'ch list \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'ch list \<Rightarrow> ('a \<times> 'ch list) set\<close> where
  \<open>match_ctx p s = match (\<lambda>u t. p u (drop (length u) s) t) s\<close>

(*<*)
lemma match_ctxE:
  assumes \<open>(t, u) \<in> match_ctx p s\<close>
  obtains tail where \<open>s = u @ tail\<close> \<open>p u tail t\<close>
  using assms by (auto simp: match_ctx_def match_def prefix_def)

lemma match_ctxI:
  assumes \<open>s = u @ tail\<close> \<open>p u tail t\<close>
  shows \<open>(t, u) \<in> match_ctx p s\<close>
  using assms by (auto simp: match_ctx_def match_def prefix_def)

lemma finite_match:
  fixes p :: \<open>'ch list \<Rightarrow> 'a \<Rightarrow> bool\<close>
  assumes det: \<open>\<And>u t t'. p u t \<Longrightarrow> p u t' \<Longrightarrow> t = t'\<close>
  shows \<open>finite (match p s)\<close>
proof -
  let ?f = \<open>\<lambda>i. ((THE t. p (take i s) t), take i s)\<close>
  have \<open>match p s \<subseteq> ?f ` {..length s}\<close>
  proof
    fix x assume \<open>x \<in> match p s\<close>
    then obtain t u where
      x: \<open>x = (t, u)\<close> and pfx: \<open>prefix u s\<close> and p: \<open>p u t\<close>
      by (auto simp: match_def)
    from pfx obtain v where s: \<open>s = u @ v\<close> and
       len: \<open>length u \<le> length s\<close> and
       u: \<open>take (length u) s = u\<close>
      by (auto simp: prefix_def)
    from p have \<open>(THE t'. p u t') = t\<close> by (auto intro: det)
    with p x u have \<open>x = ?f (length u)\<close> by simp
    with len show \<open>x \<in> ?f ` {..length s}\<close> by (auto simp: image_iff)
  qed
  then show ?thesis by (rule finite_subset) simp
qed
(*>*)

text \<open>For a deterministic predicate the set of matches is finite, so a nonempty
  set of matches has a unique longest element, and \<^text>\<open>longest\<close> picks
  it; \<^text>\<open>longest_ctx\<close> does the same for a context-aware predicate.\<close>

lemma longest_unique:
  fixes p :: \<open>'ch list \<Rightarrow> 'a \<Rightarrow> bool\<close>
  assumes det: \<open>\<And>u t t'. p u t \<Longrightarrow> p u t' \<Longrightarrow> t = t'\<close>
  assumes ne: \<open>match p s \<noteq> {}\<close>
  shows \<open>\<exists>!x. x \<in> match p s \<and> (\<forall>y \<in> match p s. length (snd y) \<le> length (snd x))\<close>
proof -
  from finite_match[of p s] det have fin: \<open>finite ((length \<circ> snd) ` match p s)\<close> by auto
  from ne have im_ne: \<open>(length \<circ> snd) ` match p s \<noteq> {}\<close> by simp
  from Max_in[OF fin im_ne] obtain x
    where xin: \<open>x \<in> match p s\<close>
      and len: \<open>length (snd x) = Max ((length \<circ> snd) ` match p s)\<close>
    by auto
  have xmax: \<open>\<And>y. y \<in> match p s \<Longrightarrow> length (snd y) \<le> length (snd x)\<close>
    using fin len by (auto intro: Max_ge)
  show ?thesis
  proof (rule ex1I[of _ x])
    show \<open>x \<in> match p s \<and> (\<forall>y \<in> match p s. length (snd y) \<le> length (snd x))\<close>
      using xin xmax by blast
  next
    fix x' assume \<open>x' \<in> match p s \<and> (\<forall>y \<in> match p s. length (snd y) \<le> length (snd x'))\<close>
    then have xin': \<open>x' \<in> match p s\<close>
      and xmax': \<open>\<And>y. y \<in> match p s \<Longrightarrow> length (snd y) \<le> length (snd x')\<close>
      by auto
    obtain t u where xeq: \<open>x = (t, u)\<close> by (cases x)
    obtain t' u' where x'eq: \<open>x' = (t', u')\<close> by (cases x')
    from xmax[OF xin'] xmax'[OF xin] have \<open>length (snd x') = length (snd x)\<close>
      by (rule antisym)
    with xin xeq xin' x'eq det have \<open>u = u'\<close> \<open>t = t'\<close>
      by (auto simp: match_def prefix_def)
    with xeq x'eq show \<open>x' = x\<close> by auto
  qed
qed

abbreviation \<open>is_longest p s x \<equiv> \<forall>y \<in> match p s. length (snd y) \<le> length (snd x)\<close>

definition longest :: \<open>('ch list \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'ch list \<Rightarrow> ('a \<times> 'ch list) option\<close> where
  \<open>longest p s =
     (if match p s = {} then None else Some (THE x. x \<in> match p s \<and> is_longest p s x))\<close>

definition longest_ctx ::
  \<open>('ch list \<Rightarrow> 'ch list \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'ch list \<Rightarrow> ('a \<times> 'ch list) option\<close> where
  \<open>longest_ctx p s = longest (\<lambda>u t. p u (drop (length u) s) t) s\<close>

(*<*)
lemma longest_None_iff: \<open>longest p s = None \<longleftrightarrow> match p s = {}\<close>
  by (auto simp: longest_def)

lemma longest_Some_iff:
  fixes p :: \<open>'ch list \<Rightarrow> 'a \<Rightarrow> bool\<close>
  assumes det: \<open>\<And>u t t'. p u t \<Longrightarrow> p u t' \<Longrightarrow> t = t'\<close>
  shows \<open>longest p s = Some x \<longleftrightarrow>
     x \<in> match p s \<and> (\<forall>y \<in> match p s. length (snd y) \<le> length (snd x))\<close>
  (is \<open>_ \<longleftrightarrow> ?P x\<close>)
proof (cases \<open>match p s = {}\<close>)
  case False
  from longest_unique[OF det False] have ex1: \<open>\<exists>!x. ?P x\<close> .
  show ?thesis
  proof
    assume \<open>longest p s = Some x\<close>
    with False have \<open>x = (THE y. ?P y)\<close> by (simp add: longest_def)
    with theI'[OF ex1] show \<open>?P x\<close> by simp
  next
    assume \<open>?P x\<close>
    from the1_equality[OF ex1 this]
      have \<open>(THE y. ?P y) = x\<close> .
    with False show \<open>longest p s = Some x\<close> by (simp add: longest_def)
  qed
qed (auto simp: longest_def)

lemma longest_Some_prefix:
  fixes p :: \<open>'ch list \<Rightarrow> 'a \<Rightarrow> bool\<close>
  assumes det: \<open>\<And>u t t'. p u t \<Longrightarrow> p u t' \<Longrightarrow> t = t'\<close>
  shows \<open>longest p s = Some (a, u) \<Longrightarrow> prefix u s\<close>
  by (auto simp: longest_Some_iff[OF det] match_def)

lemma longest_ctx_None_iff: \<open>longest_ctx p s = None \<longleftrightarrow> match_ctx p s = {}\<close>
  by (auto simp: longest_ctx_def match_ctx_def longest_None_iff)

lemma longest_ctx_Some_iff:
  fixes p :: \<open>'ch list \<Rightarrow> 'ch list \<Rightarrow> 'a \<Rightarrow> bool\<close>
  assumes det: \<open>\<And>u tail t t'. p u tail t \<Longrightarrow> p u tail t' \<Longrightarrow> t = t'\<close>
  shows \<open>longest_ctx p s = Some x \<longleftrightarrow>
     x \<in> match_ctx p s \<and> (\<forall>y \<in> match_ctx p s. length (snd y) \<le> length (snd x))\<close>
  unfolding longest_ctx_def match_ctx_def by (rule longest_Some_iff) (rule det)

lemma longest_ctx_Some_prefix:
  fixes p :: \<open>'ch list \<Rightarrow> 'ch list \<Rightarrow> 'a \<Rightarrow> bool\<close>
  assumes det: \<open>\<And>u tail t t'. p u tail t \<Longrightarrow> p u tail t' \<Longrightarrow> t = t'\<close>
  shows \<open>longest_ctx p s = Some (a, u) \<Longrightarrow> prefix u s\<close>
  by (auto simp: longest_ctx_Some_iff[OF det] match_ctx_def match_def)
(*>*)

subsection \<open>Trivia\<close>

text \<open>The predicate \<^text>\<open>match_trivia u tail r\<close> reads the string \<^text>\<open>u\<close>
  as the trivium \<^text>\<open>r\<close> and also sees the input \<^text>\<open>tail\<close> that follows
  \<^text>\<open>u\<close>. \<^text>\<open>is_newline\<close> drives the line and column bookkeeping.\<close>

locale trivia_syntax =
  fixes match_trivia :: \<open>'ch list \<Rightarrow> 'ch list \<Rightarrow> 'trivia \<Rightarrow> bool\<close>
    (\<open>(7TRIVIA'(_')/ \<leadsto>/ _)\<close> [1000, 51] 50)
    and is_newline :: \<open>'ch \<Rightarrow> bool\<close>
begin

text \<open>Advancing a cursor over a lexeme: the line grows by the number of
  newlines in the lexeme; the column restarts after the last newline, or
  grows by the length of the lexeme if it contains none.\<close>

definition advance_line :: \<open>nat \<Rightarrow> 'ch list \<Rightarrow> nat\<close> where
  \<open>advance_line line u = line + length (filter is_newline u)\<close>

definition advance_col :: \<open>nat \<Rightarrow> 'ch list \<Rightarrow> nat\<close> where
  \<open>advance_col col u =
     (if \<exists>c \<in> set u. is_newline c
      then length (takeWhile (\<lambda>c. \<not> is_newline c) (rev u))
      else col + length u)\<close>

definition trivia :: \<open>'ch list \<Rightarrow> ('trivia \<times> 'ch list) set\<close> where
  \<open>trivia = match_ctx match_trivia\<close>

text \<open>The reference reading of trivia is a relation. \<^text>\<open>STRIP(line, col,
  off, s) \<leadsto> (tsp, r)\<close> consumes trivia at the front of \<^text>\<open>s\<close>, one longest
  match at a time, records each with its span, and stops with the remaining
  input \<^text>\<open>r\<close> when no trivium matches.\<close>

abbreviation
  \<open>span_of line col off s \<equiv> \<lparr>s_line = line, s_col = col, s_off = off, s_len = length s, s_txt = s\<rparr>\<close>

inductive strip_trivia (\<open>(6STRIP'(_, _, _, _')/ \<leadsto>/ '(_, _'))\<close>) where
  strip_Stop:
    \<open>longest_ctx match_trivia r = None \<Longrightarrow> STRIP(line,col,off, r) \<leadsto> ([], r)\<close>
| strip_Step:
    \<open>\<lbrakk> longest_ctx match_trivia s = Some (t, u);
       STRIP(advance_line line u, advance_col col u, off + length u, drop (length u) s) \<leadsto> (tsp, r)
     \<rbrakk> \<Longrightarrow>
     STRIP(line,col,off, s) \<leadsto> ((t, span_of line col off u) # tsp, r)\<close>

text \<open>\<^text>\<open>consumed\<close> concatenates the texts of a list of spans.\<close>

definition consumed :: \<open>('a \<times> 'ch span) list \<Rightarrow> 'ch list\<close> where
  \<open>consumed asp = map snd asp \<bind> s_txt\<close>

(*<*)
lemma consumed_Nil [simp]: \<open>consumed [] = []\<close>
  and consumed_Cons [simp]: \<open>consumed ((a, sp') # asp) = s_txt sp' @ consumed asp\<close>
  by (simp_all add: consumed_def)
(*>*)

end

(*<*)
declare
  trivia_syntax.advance_line_def[code]
  trivia_syntax.advance_col_def[code]
(*>*)

text \<open>The trivia predicate must be deterministic, so that a string reads as at
  most one trivium, and must reject the empty string, so that the lexer always
  makes progress.\<close>

locale trivia_lang = trivia_syntax match_trivia is_newline
  for match_trivia :: \<open>'ch list \<Rightarrow> 'ch list \<Rightarrow> 'trivia \<Rightarrow> bool\<close>
    (\<open>(7TRIVIA'(_')/ \<leadsto>/ _)\<close> [1000, 51] 50)
    and is_newline +
  assumes
    trivia_det [dest]: \<open>match_trivia u tail r \<Longrightarrow> match_trivia u tail r' \<Longrightarrow> r = r'\<close>
    and trivia_empty [simp]: \<open>\<not> match_trivia [] tail r\<close>
begin

(*<*)
lemma trivia_snd_nonempty: \<open>(t, u) \<in> trivia s \<Longrightarrow> u \<noteq> []\<close>
  by (auto simp: trivia_def match_ctx_def match_def)

lemma trivia_det_ctx:
  \<open>(\<lambda>u t. match_trivia u (drop (length u) s) t) u t \<Longrightarrow>
   (\<lambda>u t. match_trivia u (drop (length u) s) t) u t' \<Longrightarrow> t = t'\<close>
  by auto

lemmas trivia_finite = finite_match[OF trivia_det_ctx, folded match_ctx_def trivia_def]
lemmas trivia_longest_unique = longest_unique[OF trivia_det_ctx, folded match_ctx_def trivia_def]
lemmas trivia_longest_Some_iff =
  longest_Some_iff[OF trivia_det_ctx, folded match_ctx_def trivia_def]

lemma longest_ctx_trivia_None_iff: \<open>longest_ctx match_trivia s = None \<longleftrightarrow> trivia s = {}\<close>
  by (simp add: longest_ctx_None_iff trivia_def)

lemma longest_ctx_trivia_Some_prefix:
  assumes \<open>longest_ctx match_trivia s = Some (a, u)\<close>
  shows \<open>prefix u s\<close>
  using assms by (auto simp: longest_ctx_def intro: longest_Some_prefix[OF trivia_det_ctx])

lemma longest_ctx_trivia_Some_iff:
  \<open>longest_ctx match_trivia s = Some x \<longleftrightarrow>
     x \<in> trivia s \<and> (\<forall>y \<in> trivia s. length (snd y) \<le> length (snd x))\<close>
  by (simp add: longest_ctx_def trivia_def match_ctx_def longest_Some_iff[OF trivia_det_ctx])
(*>*)

lemma longests_deterministic:
  assumes \<open>STRIP(line,col,off, s) \<leadsto> (tsp\<^sub>1, r\<^sub>1)\<close>
      and \<open>STRIP(line,col,off, s) \<leadsto> (tsp\<^sub>2, r\<^sub>2)\<close>
  shows \<open>tsp\<^sub>1 = tsp\<^sub>2 \<and> r\<^sub>1 = r\<^sub>2\<close>
  using assms
proof (induction arbitrary: tsp\<^sub>2 r\<^sub>2 rule: strip_trivia.induct)
  case (strip_Step s t u line col off tsp r)
  from \<open>STRIP(line,col,off, s) \<leadsto> (tsp\<^sub>2, r\<^sub>2)\<close> show ?case
  proof (cases rule: strip_trivia.cases)
    case (strip_Step t' u' tsp')
    with strip_Step.hyps(1) have \<open>t' = t\<close> \<open>u' = u\<close> by simp_all
    with strip_Step strip_Step.IH show ?thesis by auto
  qed (use strip_Step.hyps(1) in simp)
qed (auto elim: strip_trivia.cases)

text \<open>A \<^text>\<open>STRIP\<close> derivation splits its input into the consumed trivia
  and the rest.\<close>

lemma longests_input_eq:
  \<open>STRIP(line,col,off, s) \<leadsto> (tsp, r) \<Longrightarrow> s = consumed tsp @ r\<close>
  by (induction rule: strip_trivia.induct)
     (fastforce simp: prefix_def dest!: longest_ctx_trivia_Some_prefix)+

end

subsection \<open>Tokens\<close>

text \<open>\<^text>\<open>match_token st u tail t\<close> reads \<^text>\<open>u\<close> as the token \<^text>\<open>t\<close> in
  the state \<^text>\<open>st\<close> before the input \<^text>\<open>tail\<close>; \<^text>\<open>step st t adj\<close> is
  the state after the token, \<^text>\<open>adj\<close> saying whether the next lexeme
  directly follows it; \<^text>\<open>init\<close> is the state at the start of the input and
  \<^text>\<open>final\<close> says which states may end it. \<^text>\<open>source_ok\<close> is the
  condition on the whole input.\<close>

locale token_syntax = trivia_syntax match_trivia is_newline
  for match_trivia :: \<open>'ch list \<Rightarrow> 'ch list \<Rightarrow> 'trivia \<Rightarrow> bool\<close>
    (\<open>(7TRIVIA'(_')/ \<leadsto>/ _)\<close> [1000, 51] 50)
    and is_newline +
  fixes match_token :: \<open>'st \<Rightarrow> 'ch list \<Rightarrow> 'ch list \<Rightarrow> 'tok \<Rightarrow> bool\<close>
    (\<open>(6TOKEN'(_,/ _,/ _')/ \<leadsto>/ _)\<close> [1000, 1000, 1000, 51] 50)
    and step :: \<open>'st \<Rightarrow> 'tok \<Rightarrow> bool \<Rightarrow> 'st\<close>
    and init :: \<open>'st\<close>
    and final :: \<open>'st \<Rightarrow> bool\<close>
    and source_ok :: \<open>'ch list \<Rightarrow> bool\<close>
begin

definition lexemes :: \<open>'st \<Rightarrow> 'ch list \<Rightarrow> ('tok \<times> 'ch list) set\<close> where
  \<open>lexemes st = match_ctx (match_token st)\<close>

text \<open>The body of the input follows the header. \<^text>\<open>LEX\<^sub>B\<^sub>o\<^sub>d\<^sub>y\<close> reads it
  token by token: the longest token match in the current state, then the
  trivia after it, then the rest in the state the token leads to; the input
  may end only in a final state. A token's span covers the lexeme only; the
  trivia keep their own spans in \<^const>\<open>trailing\<close>.\<close>

abbreviation mk_lexed_token ::
  \<open>nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'tok \<Rightarrow> 'ch list \<Rightarrow> ('trivia \<times> 'ch span) list \<Rightarrow> ('trivia, 'tok, 'ch) token\<close>
where
  \<open>mk_lexed_token line col off t u tsp \<equiv> \<lparr>tok = t, span = span_of line col off u, trailing = tsp\<rparr>\<close>

inductive lexed_body ::
  \<open>'st \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'ch list \<Rightarrow> ('trivia, 'tok, 'ch) token list \<Rightarrow> bool\<close>
  (\<open>(8LEX\<^sub>B\<^sub>o\<^sub>d\<^sub>y'(_,/ _,/ _,/ _,/ _')/ \<leadsto>/ _)\<close> [0, 0, 0, 0, 0, 51] 50)
where
  lexed_body_Nil:
    \<open>final st \<Longrightarrow> LEX\<^sub>B\<^sub>o\<^sub>d\<^sub>y(st, line,col,off, []) \<leadsto> []\<close>
| lexed_body_Step:
    \<open>\<lbrakk> longest_ctx (match_token st) (c # cs) = Some (t, u);
       STRIP(advance_line line u, advance_col col u, off + length u,
             drop (length u) (c # cs)) \<leadsto> (tsp, rem);
       LEX\<^sub>B\<^sub>o\<^sub>d\<^sub>y(step st t (tsp = []),
              advance_line line (u @ consumed tsp),
              advance_col col (u @ consumed tsp),
              off + length u + length (consumed tsp),
              rem) \<leadsto> r
     \<rbrakk> \<Longrightarrow>
     LEX\<^sub>B\<^sub>o\<^sub>d\<^sub>y(st, line,col,off, c # cs) \<leadsto> mk_lexed_token line col off t u tsp # r\<close>

text \<open>A readable input reads as its header followed by its body, read from
  the initial state.\<close>

inductive lexed ::
  \<open>nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'ch list \<Rightarrow>
   (('trivia, 'ch) header \<times> ('trivia, 'tok, 'ch) token list) \<Rightarrow> bool\<close>
  (\<open>(4LEX'(_,/ _,/ _,/ _')/ \<leadsto>/ _)\<close> [0, 0, 0, 0, 51] 50)
where
  \<open>\<lbrakk> source_ok s;
     STRIP(line, col, off, s) \<leadsto> (header, tail);
     LEX\<^sub>B\<^sub>o\<^sub>d\<^sub>y(init, advance_line line (consumed header),
            advance_col  col (consumed header),
            off + length (consumed header),
            tail) \<leadsto> r
   \<rbrakk> \<Longrightarrow>
   LEX(line,col,off, s) \<leadsto> (header, r)\<close>

definition spans_of :: \<open>('trivia, 'tok, 'ch) token \<Rightarrow> 'ch span list\<close> where
  \<open>spans_of t = span t # map snd (trailing t)\<close>

end

text \<open>Both predicates must be deterministic and reject the empty string, so
  that every step of a reading is a longest match of a deterministic
  predicate; then an input has at most one reading.\<close>

locale token_lang =
  token_syntax match_trivia is_newline match_token step init final source_ok +
  trivia_lang match_trivia is_newline
  for match_trivia :: \<open>'ch list \<Rightarrow> 'ch list \<Rightarrow> 'trivia \<Rightarrow> bool\<close>
    (\<open>(7TRIVIA'(_')/ \<leadsto>/ _)\<close> [1000, 51] 50)
    and is_newline
    and match_token :: \<open>'st \<Rightarrow> 'ch list \<Rightarrow> 'ch list \<Rightarrow> 'tok \<Rightarrow> bool\<close>
    (\<open>(6TOKEN'(_,/ _,/ _')/ \<leadsto>/ _)\<close> [1000, 1000, 1000, 51] 50)
    and step init final source_ok +
  assumes
    token_det [dest]: \<open>match_token st u tail t \<Longrightarrow> match_token st u tail t' \<Longrightarrow> t = t'\<close>
    and token_empty [simp]: \<open>\<not> match_token st [] tail t\<close>
begin

(*<*)
lemma lexemes_snd_nonempty: \<open>(t, u) \<in> lexemes st s \<Longrightarrow> u \<noteq> []\<close>
  by (auto simp: lexemes_def match_ctx_def match_def)

lemma token_det_ctx:
  \<open>(\<lambda>u t. match_token st u (drop (length u) s) t) u t \<Longrightarrow>
   (\<lambda>u t. match_token st u (drop (length u) s) t) u t' \<Longrightarrow> t = t'\<close>
  by auto

lemmas lexemes_finite = finite_match[OF token_det_ctx, folded match_ctx_def lexemes_def]
lemmas lexemes_longest_unique = longest_unique[OF token_det_ctx, folded match_ctx_def lexemes_def]

lemma lexemes_longest_Some_iff:
  \<open>longest_ctx (match_token st) s = Some x \<longleftrightarrow>
     x \<in> lexemes st s \<and> (\<forall>y \<in> lexemes st s. length (snd y) \<le> length (snd x))\<close>
  by (simp add: longest_ctx_def lexemes_def match_ctx_def longest_Some_iff[OF token_det_ctx])

lemma lexemes_longest_None_iff: \<open>longest_ctx (match_token st) s = None \<longleftrightarrow> lexemes st s = {}\<close>
  by (simp add: longest_ctx_None_iff lexemes_def)

lemma lexemes_longest_Some_prefix:
  \<open>longest_ctx (match_token st) s = Some (t, u) \<Longrightarrow> prefix u s\<close>
  by (auto simp: lexemes_longest_Some_iff lexemes_def match_ctx_def match_def)

lemma lexemes_longest_SomeD:
  \<open>longest_ctx (match_token st) s = Some (t, u) \<Longrightarrow> match_token st u (drop (length u) s) t\<close>
  by (auto simp: lexemes_longest_Some_iff lexemes_def match_ctx_def match_def)
(*>*)

lemma lexed_body_deterministic:
  assumes \<open>LEX\<^sub>B\<^sub>o\<^sub>d\<^sub>y(st, line,col,off, s) \<leadsto> r\<^sub>1\<close> \<open>LEX\<^sub>B\<^sub>o\<^sub>d\<^sub>y(st, line,col,off, s) \<leadsto> r\<^sub>2\<close>
  shows \<open>r\<^sub>1 = r\<^sub>2\<close>
  using assms
proof (induction arbitrary: r\<^sub>2 rule: lexed_body.induct)
  case (lexed_body_Nil st line col off)
  from \<open>LEX\<^sub>B\<^sub>o\<^sub>d\<^sub>y(st, line,col,off, []) \<leadsto> r\<^sub>2\<close> show ?case
    by (cases rule: lexed_body.cases) auto
next
  case (lexed_body_Step st c cs t u line col off tsp rem r)
  from \<open>lexed_body st line col off (c # cs) r\<^sub>2\<close> show ?case
  proof (cases rule: lexed_body.cases)
    case (lexed_body_Step t' u' tsp' rem' r')
    with lexed_body_Step.hyps(1) have tu: \<open>t' = t\<close> \<open>u' = u\<close> by simp_all
    with lexed_body_Step.hyps(2)
         \<open>STRIP(advance_line line u', advance_col col u', off + length u',
                drop (length u') (c # cs)) \<leadsto> (tsp', rem')\<close>
      have tr: \<open>tsp' = tsp\<close> \<open>rem' = rem\<close>
      by (auto dest: longests_deterministic)
    from tu tr \<open>LEX\<^sub>B\<^sub>o\<^sub>d\<^sub>y(_,_,_,_, rem') \<leadsto> r'\<close> lexed_body_Step.IH
      have \<open>r' = r\<close> by blast
    with tu tr \<open>r\<^sub>2 = _\<close> show ?thesis by simp
  qed
qed

lemma lexed_deterministic:
  assumes \<open>LEX(line,col,off, s) \<leadsto> r\<^sub>1\<close> \<open>LEX(line,col,off, s) \<leadsto> r\<^sub>2\<close>
  shows \<open>r\<^sub>1 = r\<^sub>2\<close>
proof -
  from \<open>LEX(line,col,off, s) \<leadsto> r\<^sub>1\<close> obtain header\<^sub>1 tail\<^sub>1 r\<^sub>1' where 1:
    \<open>r\<^sub>1 = (header\<^sub>1, r\<^sub>1')\<close>
    \<open>STRIP(line, col, off, s) \<leadsto> (header\<^sub>1, tail\<^sub>1)\<close>
    \<open>LEX\<^sub>B\<^sub>o\<^sub>d\<^sub>y(init, advance_line line (consumed header\<^sub>1),
            advance_col col (consumed header\<^sub>1),
            off + length (consumed header\<^sub>1),
            tail\<^sub>1) \<leadsto> r\<^sub>1'\<close>
    by (auto elim: lexed.cases)
  from \<open>lexed line col off s r\<^sub>2\<close> obtain header\<^sub>2 tail\<^sub>2 r\<^sub>2' where 2:
    \<open>r\<^sub>2 = (header\<^sub>2, r\<^sub>2')\<close>
    \<open>STRIP(line, col, off, s) \<leadsto> (header\<^sub>2, tail\<^sub>2)\<close>
    \<open>LEX\<^sub>B\<^sub>o\<^sub>d\<^sub>y(init, advance_line line (consumed header\<^sub>2),
            advance_col col (consumed header\<^sub>2),
            off + length (consumed header\<^sub>2),
            tail\<^sub>2) \<leadsto> r\<^sub>2'\<close>
    by (auto elim: lexed.cases)
  from 1(2) 2(2) have header: \<open>header\<^sub>1 = header\<^sub>2\<close> and tail: \<open>tail\<^sub>1 = tail\<^sub>2\<close>
    by (auto dest: longests_deterministic)
  with 1(3) 2(3) have \<open>r\<^sub>1' = r\<^sub>2'\<close>
    by (auto dest: lexed_body_deterministic)
  with 1(1) 2(1) header show ?thesis by simp
qed

text \<open>No character is lost: concatenating the texts of all spans, the header
  first and then each token with its trailing trivia, gives the input back.\<close>

(*<*)
lemma lex_body_invert:
  \<open>LEX\<^sub>B\<^sub>o\<^sub>d\<^sub>y(st, line,col,off, s) \<leadsto> body \<Longrightarrow> concat (map spans_of body) \<bind> s_txt = s\<close>
proof (induction rule: lexed_body.induct)
  case (lexed_body_Step st c cs t u line col off tsp rem r)
  from lexed_body_Step have \<open>c # cs = u @ consumed tsp @ rem\<close>
    using lexemes_longest_Some_prefix[unfolded prefix_def] longests_input_eq
    by fastforce
  with lexed_body_Step.IH show ?case
    by (simp add: List.bind_def spans_of_def consumed_def)
qed simp
(*>*)

lemma lex_invert:
  assumes \<open>LEX(line,col,off, s) \<leadsto> (header, body)\<close>
  shows \<open>(map snd header @ concat (map spans_of body)) \<bind> s_txt = s\<close>
  using assms
proof (cases rule: lexed.cases)
  case (1 tail)
  then have \<open>s = consumed header @ tail\<close>
    using longests_input_eq by blast
  with lex_body_invert[OF 1(3)] show ?thesis
    by (auto simp: List.bind_def consumed_def)
qed

end

text \<open>A lexer is a function that agrees with the relation from the initial
  cursor: every result is a reading, and every reading is returned.\<close>

locale lexer =
  token_lang match_trivia is_newline match_token step init final source_ok
  for match_trivia :: \<open>'ch list \<Rightarrow> 'ch list \<Rightarrow> 'trivia \<Rightarrow> bool\<close>
    and is_newline :: \<open>'ch \<Rightarrow> bool\<close>
    and match_token :: \<open>'st \<Rightarrow> 'ch list \<Rightarrow> 'ch list \<Rightarrow> 'tok \<Rightarrow> bool\<close>
    and step :: \<open>'st \<Rightarrow> 'tok \<Rightarrow> bool \<Rightarrow> 'st\<close>
    and init :: \<open>'st\<close>
    and final :: \<open>'st \<Rightarrow> bool\<close>
    and source_ok :: \<open>'ch list \<Rightarrow> bool\<close> +
  fixes lex :: \<open>'ch list \<Rightarrow>
                 (('trivia, 'ch) header \<times>
                  ('trivia, 'tok, 'ch) token list) option\<close>
  assumes lex_sound: \<open>lex s = Some (header, body) \<Longrightarrow> LEX(0,0,0, s) \<leadsto> (header, body)\<close>
      and lex_complete: \<open>LEX(0,0,0, s) \<leadsto> (header, body) \<Longrightarrow> lex s = Some (header, body)\<close>

end
