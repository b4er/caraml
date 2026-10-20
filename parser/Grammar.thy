theory Grammar
  imports LR_Parser.LR_Parser Lexer_Correct CaraML_Syntax.Module_Expressions CaraML_Spec.Pipeline
begin

definition loc_of_span :: \<open>nat span \<Rightarrow> loc\<close> where
  \<open>loc_of_span s = \<lparr> l_line = s_line s, l_col = s_col s,
                      l_off = s_off s, l_len = s_len s \<rparr>\<close>

definition nm_of_span :: \<open>nat span \<Rightarrow> nm\<close> where
  \<open>nm_of_span s = \<lparr> l_line = s_line s, l_col = s_col s,
                     l_off = s_off s, l_len = s_len s, n_txt = s_txt s \<rparr>\<close>

lemma truncate_nm_of_span[simp]: \<open>loc.truncate (nm_of_span s) = loc_of_span s\<close>
  by (simp add: nm_of_span_def loc_of_span_def loc.defs)

section \<open>Grammar\<close>

text \<open>A layout-sensitive stub of the module language: a file is a block of
  declarations, and a declaration is \<open>module M\<close> or \<open>module M = \<lblot>block\<rblot>\<close>.

  The annotations follow adams2013: the indentation of a nonterminal is the
  column of its first token (\<open>\<^sup>=\<close>), the rest of a declaration sits to the
  right of its \<open>module\<close> (\<open>\<^sup>>\<close>), and a nested block is indented past the
  \<open>module\<close> that opens it (\<open>Decls\<^sup>>\<close>) with its declarations aligned
  (\<open>Decl\<^sup>=\<close>). The start indentation is \<open>0\<close>, so top-level declarations
  start at column \<open>0\<close>; a block ends at the first token left of its column.\<close>

grammar (relation) caraml =
  tokens \<open>(trivia, tok, nat) token\<close>
  terminals "module" = KModule and "=" = Assign
  productions
      File :: \<open>mdecl list\<close>
        = Decls\<^sup>=  \<Rightarrow> \<open>\<lambda>ds. ds\<close>
        |         \<Rightarrow> \<open>[]\<close>
    and
      Decls :: \<open>mdecl list\<close>
        = Decl\<^sup>=         \<Rightarrow> \<open>\<lambda>d. [d]\<close>
        | Decls\<^sup>= Decl\<^sup>=  \<Rightarrow> \<open>\<lambda>ds d. ds @ [d]\<close>
    and
      Decl :: \<open>mdecl\<close>
        = "module"\<^sup>= UId\<^sup>>             \<Rightarrow> \<open>\<lambda>x. DMod (nm_of_span (Token.span x)) [] None (MStruct [])\<close>
        | "module"\<^sup>= UId\<^sup>> "="\<^sup>> Decls\<^sup>>
            \<Rightarrow> \<open>\<lambda>x ds. DMod (nm_of_span (Token.span x)) [] None (MStruct ds)\<close>

parser caraml_parse for caraml

subsection \<open>Layouts\<close>

text \<open>Tokens on one line, positioned by column only.\<close>

definition tk :: \<open>nat \<Rightarrow> tok \<Rightarrow> string \<Rightarrow> (trivia, tok, nat) token\<close> where
  \<open>tk c x s = \<lparr>tok = x,
              span = \<lparr>s_line = 0, s_col = c, s_off = 0, s_len = length s, s_txt = map of_char s\<rparr>,
              trailing = []\<rparr>\<close>

definition md :: \<open>nat \<Rightarrow> string \<Rightarrow> mdecl list \<Rightarrow> mdecl\<close> where
  \<open>md c s ds = DMod (nm_of_span (Token.span (tk c UId s))) [] None (MStruct ds)\<close>

lemma \<open>caraml_parse [] = Some []\<close>
  by eval

lemma \<open>caraml_parse [tk 0 KModule ''module'', tk 7 UId ''A'',
                     tk 0 KModule ''module'', tk 7 UId ''B'']
       = Some [md 7 ''A'' [], md 7 ''B'' []]\<close>
  by eval

lemma \<open>caraml_parse [tk 0 KModule ''module'', tk 7 UId ''A'', tk 9 Assign ''='',
                     tk 2 KModule ''module'', tk 9 UId ''B'',
                     tk 2 KModule ''module'', tk 9 UId ''C'',
                     tk 0 KModule ''module'', tk 7 UId ''D'']
       = Some [md 7 ''A'' [md 9 ''B'' [], md 9 ''C'' []], md 7 ''D'' []]\<close>
  by eval

text \<open>Rejected: a block at the column of its header, a misaligned block, a
  top-level declaration off column \<open>0\<close>.\<close>

lemma \<open>caraml_parse [tk 0 KModule ''module'', tk 7 UId ''A'', tk 9 Assign ''='',
                     tk 0 KModule ''module'', tk 7 UId ''B'']
       = None\<close>
  by eval

lemma \<open>caraml_parse [tk 0 KModule ''module'', tk 7 UId ''A'', tk 9 Assign ''='',
                     tk 2 KModule ''module'', tk 9 UId ''B'',
                     tk 3 KModule ''module'', tk 10 UId ''C'']
       = None\<close>
  by eval

lemma \<open>caraml_parse [tk 1 KModule ''module'', tk 8 UId ''A''] = None\<close>
  by eval

section \<open>Source to surface AST\<close>

text \<open>The executable front end: UTF-8 decoding, the lexer, the generated
  parser. A file is a declaration list.\<close>

definition read_src :: \<open>string \<Rightarrow> mdecl list option\<close> where
  \<open>read_src src = utf8_decode' src \<bind> caraml_lex \<bind> caraml_parse \<circ> snd\<close>

text \<open>The relational specification it is measured against, composed from the
  three stages' own specifications; the parse relation is taken at the start
  indentation \<open>0\<close>.\<close>

definition reads :: \<open>string \<Rightarrow> mdecl list \<Rightarrow> bool\<close> where
  \<open>reads src ast \<longleftrightarrow>
     (\<exists>cps h ts. utf8 src cps \<and> lexed 0 0 0 cps (h, ts) \<and> caraml_File 0 ts ast)\<close>

text \<open>The executable front end reads exactly what the specification says:
  soundness and completeness of the three stages compose into the
  interpretation of \<^locale>\<open>frontend\<close>.\<close>

interpretation caraml_frontend: frontend read_src reads
proof
  fix f a
  show \<open>read_src f = Some a \<Longrightarrow> reads f a\<close>
    by (fastforce simp: read_src_def reads_def bind_eq_Some_conv utf8_decode'_Some_iff
        dest: caraml_lex_sound caraml_parse.sound)
  show \<open>reads f a \<Longrightarrow> read_src f = Some a\<close>
    by (fastforce simp: read_src_def reads_def bind_eq_Some_conv utf8_decode'_Some_iff
        intro: caraml_lex_complete caraml_parse.complete)
qed

end
