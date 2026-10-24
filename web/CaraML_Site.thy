theory CaraML_Site
  imports
    CaraML_Parser.Lexer
    Site.Site
  keywords
    "why" "ml" "hs" "both" "expert" "abi" "caraml" :: document_body
begin

text \<open>Configuration of the CaraML website:\<close>

setup \<open>
  Site.title "CaraML" #>
  Site.logo "assets/caraml-icon.svg" #>
  Site.icon "assets/caraml-icon.svg" #>
  Site.parts
   [("start", "Get started"),
    ("docs", "Documentation"),
    ("report", "Language report"),
    ("compiler", "Compiler")] #>
  Site.repository "https://github.com/b4er/caraml" #>
  Site.sources
   ["CaraML_Prelude",
    "CaraML_Spec",
    "CaraML_Syntax",
    "CaraML_Core",
    "CaraML_Typing",
    "CaraML_Parser",
    "CaraML_Export"] #>
  Site.bib "../root.bib" #>
  Site.axes
   [("ml", "OCaml or SML", ["no", "yes"]),
    ("haskell", "Haskell", ["no", "yes"]),
    ("proof", "Proofs", ["result", "expert"]),
    ("systems", "C or Rust", ["no", "yes"])] #>
  Site.profiles
   [("newcomer", ["no", "no", "result", "no"]),
    ("ml", ["yes", "no", "result", "no"]),
    ("haskell", ["no", "yes", "result", "no"]),
    ("expert", ["yes", "yes", "expert", "yes"])] #>
  Site.axis_tags
   [("ml", [("", ""), ("OCaml", "Differences between CaraML and OCaml.")]),
    ("haskell", [("", ""), ("Haskell", "Differences between CaraML and Haskell.")]),
    ("proof", [("", "The theorem after the prose."),
               ("proofs", "The proof, the sources and the open obligations.")]),
    ("systems", [("", ""), ("ABI", "Asides on representation, marshalling and the ABI.")])] #>
  Site.control_label "Asides"
\<close>

ML \<open>
  Site.block_command \<^command_keyword>\<open>why\<close> "ml=no haskell=no";
  Site.block_command \<^command_keyword>\<open>ml\<close> "ml=yes haskell=no";
  Site.block_command \<^command_keyword>\<open>hs\<close> "ml=no haskell=yes";
  Site.block_command \<^command_keyword>\<open>both\<close> "ml=yes haskell=yes";
  Site.block_command \<^command_keyword>\<open>expert\<close> "proof=expert";
  Site.block_command \<^command_keyword>\<open>abi\<close> "systems=yes";
\<close>

section \<open>CaraML blocks\<close>

text \<open>
  A \<open>caraml\<close> block is a program: its text is lexed with \<^const>\<open>caraml_lex\<close>,
  and the command reports a mark on every token and comment; the generator
  renders the marks. A block that does not lex is an error.
\<close>

datatype mark = Keyword | Reserved | Delim | Ident | Number | Text | Operator | Comment

text \<open>The mark of a token class. Selectors count as identifiers, \<open>\<lambda>\<close> and the
  arrow as reserved symbols, interpolated strings and characters as text.\<close>

definition mark_of_tok :: \<open>tok \<Rightarrow> mark\<close> where
  \<open>mark_of_tok t =
     (if t \<in> {Assign, Colon, Arrow, Bar, KLambda} then Reserved
      else if t \<in> {Comma, Semi, LP, RP, LB, RB, LC, RC} then Delim
      else if t \<in> {LId, UId, TSelL, TSelU, TSelN, LSelL, LSelU, LSelN} then Ident
      else if t \<in> {IntL, FloatL} then Number
      else if t \<in> {StrL, StrI, CharL} then Text
      else if t = Op then Operator
      else Keyword)\<close>

text \<open>A mark is an offset, a length and a class; comments are marked, whitespace is not:\<close>

definition comment_marks :: \<open>(trivia \<times> codepoint span) list \<Rightarrow> (nat \<times> nat \<times> mark) list\<close> where
  \<open>comment_marks ts = [(s_off s, s_len s, Comment). (t, s) \<leftarrow> ts, t \<noteq> Space]\<close>

definition site_lex :: \<open>ustring \<Rightarrow> (nat \<times> nat \<times> mark) list option\<close> where
  \<open>site_lex cs =
     map_option (\<lambda>(h, ts). comment_marks h @
         concat (map (\<lambda>t. (s_off (span t), s_len (span t), mark_of_tok (tok t))
                            # comment_marks (trailing t)) ts))
       (caraml_lex cs)\<close>

code_reflect CaraML_Lex
  datatypes mark = Keyword | Reserved | Delim | Ident | Number | Text | Operator | Comment
  functions site_lex nat_of_integer integer_of_nat

ML \<open>
local
  val symbol_codes =
    Lazy.lazy (fn () =>
      let
        fun code ("code:" :: hex :: _) =
              Option.map #1 (Int.scan StringCvt.HEX Substring.getc (Substring.full hex))
          | code (_ :: rest) = code rest
          | code [] = NONE;
        fun entry line =
          (case String.tokens (fn c => c = #" " orelse c = #"\t") line of
            sym :: rest => (case code rest of SOME c => Symtab.update (sym, c) | NONE => I)
          | [] => I);
      in fold entry (split_lines (File.read (Path.explode "~~/etc/symbols"))) Symtab.empty end);

  fun codepoint sym =
    (case Symbol.decode sym of
      Symbol.Char s => Char.ord (String.sub (s, 0))
    | Symbol.UTF8 s => (case UTF8.decode_permissive s of [c] => c | _ => 0xFFFD)
    | Symbol.Sym _ => the_default 0xFFFD (Symtab.lookup (Lazy.force symbol_codes) sym)
    | _ => 0xFFFD);

  fun markup_of CaraML_Lex.Keyword = SOME Markup.keyword1
    | markup_of CaraML_Lex.Reserved = SOME Markup.keyword2
    | markup_of CaraML_Lex.Delim = SOME Markup.delimiter
    | markup_of CaraML_Lex.Ident = NONE
    | markup_of CaraML_Lex.Number = SOME Markup.numeral
    | markup_of CaraML_Lex.Text = SOME Markup.string
    | markup_of CaraML_Lex.Operator = SOME Markup.operator
    | markup_of CaraML_Lex.Comment = SOME Markup.comment1;

  val to_int = CaraML_Lex.integer_of_nat;
  val of_int = CaraML_Lex.nat_of_integer;
in

fun check_caraml _ src =
  let
    val syms = Input.source_explode src;
    val input = map (of_int o codepoint o Symbol_Pos.symbol) syms;
    fun report (off, (len, m)) =
      (case markup_of m of
        NONE => ()
      | SOME markup =>
          Position.report
            (Position.range_position
              (Symbol_Pos.range (take (to_int len) (drop (to_int off) syms))))
            markup);
  in
    (case CaraML_Lex.site_lex input of
      NONE => error ("CaraML block does not lex" ^ Position.here (Input.pos_of src))
    | SOME marks => List.app report marks)
  end;

end;

Site.checked_command \<^command_keyword>\<open>caraml\<close> "a CaraML program, lexed and marked up"
  check_caraml;
\<close>

end
