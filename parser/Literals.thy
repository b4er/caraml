theory Literals
  imports UnicodeLexer CaraML_Syntax.Names "HOL-Library.Sublist"
begin

section \<open>Literals: numerals, strings and characters\<close>

text \<open>The literal forms of \<open>grammar.md\<close> \<section>1 are given as \<^emph>\<open>readers\<close>: a reader
  consumes a prefix of its input and returns what it read with the rest of the
  input. The readers decide both the lexer's specification (a literal token is
  exactly the prefix its reader consumes) and the parser's decoders (the value
  of a literal is what its reader returns on the span text), so the lexer's
  correctness covers the values the parser sees. The readers are greedy with
  one character of lookahead, as the forms of \<section>1 allow.

  A numeral is \<open>"-"? (Dec | "0x" Hex | "0b" Bin) Suffix?\<close> or a float \<open>"-"? Dec ("."
  Dec)? (("e" | "E") "-"? Dec)?\<close> with a fraction or an exponent; digit runs
  take single underscores between digits. Only the integer value matters
  (floats keep their text); a suffixed integer must lie in its type's range.
  Strings and characters are decoded to codepoints through the escapes \<open>\0 \t
  \n \r \" \' \\ \$ \u{h\<dots>}\<close>, and \<open>${path}\<close> in a string is a hole holding a
  value path, so a string is a list of pieces.\<close>

subsection \<open>Digit runs\<close>

text \<open>\<^text>\<open>scan_digits D s\<close> reads the longest prefix of \<^text>\<open>s\<close> of the form
  \<open>D ("_"? D)*\<close>, and nothing if \<^text>\<open>s\<close> does not start with a digit;
  \<^text>\<open>scan_more\<close> continues a run after a digit. \<^text>\<open>digits_value\<close> is
  the value of a run, underscores skipped.\<close>

fun scan_more :: \<open>(codepoint \<Rightarrow> bool) \<Rightarrow> ustring \<Rightarrow> ustring \<times> ustring\<close> where
  \<open>scan_more D [] = ([], [])\<close>
| \<open>scan_more D (c # cs) =
     (if D c then apfst ((#) c) (scan_more D cs)
      else case cs of
        d # cs' \<Rightarrow> if c = uscore \<and> D d then apfst (\<lambda>ds. c # d # ds) (scan_more D cs')
                   else ([], c # cs)
      | [] \<Rightarrow> ([], [c]))\<close>

definition scan_digits :: \<open>(codepoint \<Rightarrow> bool) \<Rightarrow> ustring \<Rightarrow> (ustring \<times> ustring) option\<close> where
  \<open>scan_digits D s =
     (case s of c # cs \<Rightarrow> if D c then Some (apfst ((#) c) (scan_more D cs)) else None
      | [] \<Rightarrow> None)\<close>

definition digit_val :: \<open>codepoint \<Rightarrow> nat\<close> where
  \<open>digit_val c =
     (if 0x61 \<le> c \<and> c \<le> 0x66 then c - 0x61 + 10
      else if 0x41 \<le> c \<and> c \<le> 0x46 then c - 0x41 + 10
      else c - 0x30)\<close>

definition digits_value :: \<open>nat \<Rightarrow> ustring \<Rightarrow> int\<close> where
  \<open>digits_value base ds =
     foldl (\<lambda>v c. if c = uscore then v else v * int base + int (digit_val c)) 0 ds\<close>

(*<*)
lemma scan_more_split: \<open>scan_more D s = (ds, r) \<Longrightarrow> s = ds @ r\<close>
  by (induction D s arbitrary: ds r rule: scan_more.induct)
     (auto simp: apfst_def map_prod_def split: if_splits list.splits prod.splits)

lemma scan_digits_split: \<open>scan_digits D s = Some (ds, r) \<Longrightarrow> s = ds @ r \<and> ds \<noteq> []\<close>
  by (auto simp: scan_digits_def apfst_def map_prod_def split: list.splits if_splits prod.splits
      dest: scan_more_split)
(*>*)

subsection \<open>Numerals\<close>

definition suffix_table :: \<open>(ustring \<times> suffix) list\<close> where
  \<open>suffix_table =
     [(cp ''i8'', I8), (cp ''i16'', I16), (cp ''i32'', I32), (cp ''i64'', I64),
      (cp ''u8'', U8), (cp ''u16'', U16), (cp ''u32'', U32), (cp ''u64'', U64)]\<close>

fun suffix_bounds :: \<open>suffix \<Rightarrow> int \<times> int\<close> where
  \<open>suffix_bounds I8 = (- 128, 127)\<close>
| \<open>suffix_bounds I16 = (- 32768, 32767)\<close>
| \<open>suffix_bounds I32 = (- 2147483648, 2147483647)\<close>
| \<open>suffix_bounds I64 = (- 9223372036854775808, 9223372036854775807)\<close>
| \<open>suffix_bounds U8 = (0, 255)\<close>
| \<open>suffix_bounds U16 = (0, 65535)\<close>
| \<open>suffix_bounds U32 = (0, 4294967295)\<close>
| \<open>suffix_bounds U64 = (0, 18446744073709551615)\<close>

text \<open>An unsuffixed integer literal has the unbounded type \<open>int\<close>, so only a
  suffix bounds the value:\<close>

definition in_range :: \<open>suffix option \<Rightarrow> int \<Rightarrow> bool\<close> where
  \<open>in_range sfx v \<longleftrightarrow>
     (case sfx of None \<Rightarrow> True
      | Some s \<Rightarrow> fst (suffix_bounds s) \<le> v \<and> v \<le> snd (suffix_bounds s))\<close>

definition read_suffix :: \<open>ustring \<Rightarrow> suffix option \<times> ustring\<close> where
  \<open>read_suffix s =
     (case find (\<lambda>(u, _). prefix u s) suffix_table of
        None \<Rightarrow> (None, s)
      | Some (u, x) \<Rightarrow> (Some x, drop (length u) s))\<close>

datatype numeral = NInt int \<open>suffix option\<close> | NFloat

text \<open>\<^text>\<open>read_radix\<close> reads a hexadecimal or binary integer after its
  prefix, \<^text>\<open>read_frac\<close> a fraction (a dot with digits on both sides) and
  \<^text>\<open>read_exp\<close> an exponent, each returning the rest of the input.
  \<^text>\<open>read_unsigned\<close> combines them into a numeral without sign, and
  \<^text>\<open>read_num\<close> adds the leading dash. Whether a dash may start a numeral
  is the lexer's decision, made from its state.\<close>

definition read_radix :: \<open>ustring \<Rightarrow> (int \<times> ustring) option\<close> where
  \<open>read_radix s =
     (case s of
        z # x # r \<Rightarrow>
          if z = 0x30 \<and> x = 0x78
          then map_option (apfst (digits_value 16)) (scan_digits is_hexdigit r)
          else if z = 0x30 \<and> x = 0x62
          then map_option (apfst (digits_value 2)) (scan_digits is_bindigit r)
          else None
      | _ \<Rightarrow> None)\<close>

definition read_frac :: \<open>ustring \<Rightarrow> ustring option\<close> where
  \<open>read_frac s =
     (case s of d # r \<Rightarrow> if d = dot then map_option snd (scan_digits is_digit r) else None
      | [] \<Rightarrow> None)\<close>

definition drop_dash :: \<open>ustring \<Rightarrow> ustring\<close> where
  \<open>drop_dash s = (case s of m # r \<Rightarrow> if m = dash then r else s | [] \<Rightarrow> s)\<close>

definition read_exp :: \<open>ustring \<Rightarrow> ustring option\<close> where
  \<open>read_exp s =
     (case s of
        e # r \<Rightarrow> if e = 0x65 \<or> e = 0x45 then map_option snd (scan_digits is_digit (drop_dash r))
                 else None
      | [] \<Rightarrow> None)\<close>

definition read_unsigned :: \<open>ustring \<Rightarrow> (numeral \<times> ustring) option\<close> where
  \<open>read_unsigned s =
     (case read_radix s of
        Some (v, r) \<Rightarrow> (case read_suffix r of (sfx, r') \<Rightarrow> Some (NInt v sfx, r'))
      | None \<Rightarrow>
        (case scan_digits is_digit s of
           None \<Rightarrow> None
         | Some (ds, r) \<Rightarrow>
             (let (frac, r\<^sub>1) = (case read_frac r of Some r\<^sub>1 \<Rightarrow> (True, r\<^sub>1) | None \<Rightarrow> (False, r));
                  (ex, r\<^sub>2) = (case read_exp r\<^sub>1 of Some r\<^sub>2 \<Rightarrow> (True, r\<^sub>2) | None \<Rightarrow> (False, r\<^sub>1))
              in if frac \<or> ex then Some (NFloat, r\<^sub>2)
                 else (case read_suffix r of
                         (sfx, r') \<Rightarrow> Some (NInt (digits_value 10 ds) sfx, r')))))\<close>

fun negate :: \<open>numeral \<Rightarrow> numeral\<close> where
  \<open>negate (NInt v sfx) = NInt (- v) sfx\<close>
| \<open>negate NFloat = NFloat\<close>

definition read_num :: \<open>ustring \<Rightarrow> (numeral \<times> ustring) option\<close> where
  \<open>read_num s =
     (case s of
        c # r \<Rightarrow> if c = dash then map_option (apfst negate) (read_unsigned r) else read_unsigned s
      | [] \<Rightarrow> None)\<close>

text \<open>A reader consumes a suffix of its input: the rest is a suffix of the
  input, and a numeral is at least one character long.\<close>

(*<*)
lemma suffix_refl [simp]: \<open>suffix r r\<close>
  by (simp add: suffix_def)

lemma suffix_append_right [simp]: \<open>suffix r (u @ r)\<close>
  by (rule suffixI) (rule refl)

lemma suffix_Cons_append [simp]: \<open>suffix r (c # u @ r)\<close>
  by (rule suffix_ConsI) simp

lemma read_suffix_suffix: \<open>read_suffix s = (sfx, r) \<Longrightarrow> suffix r s\<close>
  by (auto simp: read_suffix_def suffix_drop split: option.splits prod.splits)

lemma read_radix_suffix: \<open>read_radix s = Some (v, r) \<Longrightarrow> suffix r s \<and> length r < length s\<close>
  by (auto simp: read_radix_def apfst_def map_prod_def split: list.splits if_splits prod.splits
      dest!: scan_digits_split intro!: suffix_ConsI)

lemma read_frac_suffix: \<open>read_frac s = Some r \<Longrightarrow> suffix r s \<and> length r < length s\<close>
  by (auto simp: read_frac_def split: list.splits if_splits prod.splits
      dest!: scan_digits_split)

lemma suffix_trans [trans]: \<open>suffix r u \<Longrightarrow> suffix u s \<Longrightarrow> suffix r s\<close>
  by (rule suffix_order.trans)

lemma suffix_length_trans: \<open>suffix r u \<Longrightarrow> suffix u s \<Longrightarrow> length u < length s \<Longrightarrow> length r < length s\<close>
  using suffix_length_le by fastforce

lemma suffix_append_length: \<open>suffix r u \<Longrightarrow> x \<noteq> [] \<Longrightarrow> length r < length x + length u\<close>
  using suffix_length_le[of r u] by (cases x) auto

lemma drop_dash_suffix: \<open>suffix (drop_dash s) s \<and> length (drop_dash s) \<le> length s\<close>
  by (auto simp: drop_dash_def split: list.splits intro: suffix_ConsI)

lemma read_exp_suffix: \<open>read_exp s = Some r \<Longrightarrow> suffix r s \<and> length r < length s\<close>
proof -
  assume \<open>read_exp s = Some r\<close>
  then obtain e t ds where s: \<open>s = e # t\<close>
    and sd: \<open>scan_digits is_digit (drop_dash t) = Some (ds, r)\<close>
    by (auto simp: read_exp_def split: list.splits if_splits)
  from scan_digits_split[OF sd] obtain d ds' where \<open>drop_dash t = d # ds' @ r\<close>
    by (cases ds) auto
  then have \<open>suffix r (drop_dash t)\<close> \<open>length r < length (drop_dash t)\<close> by auto
  with drop_dash_suffix[of t] show ?thesis
    by (auto simp: s intro: suffix_ConsI suffix_trans)
qed

lemma read_unsigned_suffix:
  \<open>read_unsigned s = Some (n, r) \<Longrightarrow> suffix r s \<and> length r < length s\<close>
proof (cases \<open>read_radix s\<close>)
  case (Some p)
  obtain v t where p: \<open>p = (v, t)\<close> by (cases p)
  assume h: \<open>read_unsigned s = Some (n, r)\<close>
  from Some p have rt: \<open>suffix t s\<close> \<open>length t < length s\<close> using read_radix_suffix by auto
  obtain sfx r' where rs: \<open>read_suffix t = (sfx, r')\<close> by (cases \<open>read_suffix t\<close>)
  from h Some p rs have r: \<open>r = r'\<close> by (simp add: read_unsigned_def)
  from read_suffix_suffix[OF rs] have \<open>suffix r t\<close> by (simp add: r)
  with rt show ?thesis
    by (auto intro: suffix_trans suffix_length_trans)
next
  case None
  assume h: \<open>read_unsigned s = Some (n, r)\<close>
  then obtain ds t where sd: \<open>scan_digits is_digit s = Some (ds, t)\<close>
    by (auto simp: read_unsigned_def None split: option.splits)
  from scan_digits_split[OF sd] have st: \<open>s = ds @ t\<close> and dne: \<open>ds \<noteq> []\<close> by auto
  have fr: \<open>\<And>x. read_frac t = Some x \<Longrightarrow> suffix x t\<close> using read_frac_suffix by blast
  have ex: \<open>\<And>u x. read_exp u = Some x \<Longrightarrow> suffix x u\<close> using read_exp_suffix by blast
  have \<open>suffix r t\<close>
    using h sd fr ex read_suffix_suffix
    by (cases \<open>read_frac t\<close>; cases \<open>read_exp t\<close>)
       (auto simp: read_unsigned_def None Let_def split: option.splits prod.splits if_splits
        intro: suffix_trans)
  with dne st show ?thesis
    by (auto intro: suffix_append_length suffix_appendI)
qed

lemma read_num_suffix: \<open>read_num s = Some (n, r) \<Longrightarrow> suffix r s \<and> length r < length s\<close>
  by (auto simp: read_num_def split: list.splits if_splits
      dest!: read_unsigned_suffix intro: suffix_ConsI)
(*>*)

subsection \<open>Escapes, strings and characters\<close>

text \<open>\<^text>\<open>read_escape\<close> reads the escape after a backslash: a letter, a
  punctuation character, or \<open>u{h\<dots>}\<close> with one to six hexadecimal digits that
  form a Unicode scalar value.\<close>

definition read_escape :: \<open>ustring \<Rightarrow> (codepoint \<times> ustring) option\<close> where
  \<open>read_escape s =
     (case s of
        [] \<Rightarrow> None
      | c # r \<Rightarrow>
          if c = 0x30 then Some (0, r)
          else if c = 0x74 then Some (0x09, r)
          else if c = 0x6E then Some (0x0A, r)
          else if c = 0x72 then Some (0x0D, r)
          else if c = qt \<or> c = cq \<or> c = bslash \<or> c = dollar then Some (c, r)
          else if c = 0x75 then
            (case r of
               b # r' \<Rightarrow>
                 if b = curlyo then
                   (let hs = takeWhile is_hexdigit r'
                    in case drop (length hs) r' of
                         k # r'' \<Rightarrow>
                           if k = curlyc \<and> hs \<noteq> [] \<and> length hs \<le> 6
                              \<and> is_valid_cp (nat (digits_value 16 hs))
                           then Some (nat (digits_value 16 hs), r'') else None
                       | [] \<Rightarrow> None)
                 else None
             | [] \<Rightarrow> None)
          else None)\<close>

text \<open>A string is a list of pieces: text, decoded, and holes, each holding a
  value path \<open>M.N.x\<close> as its names. \<^text>\<open>scan_path\<close> reads the path of a hole
  up to its closing brace.\<close>

datatype piece = Txt ustring | Hole \<open>ustring list\<close>

fun is_hole :: \<open>piece \<Rightarrow> bool\<close> where
  \<open>is_hole (Hole _) = True\<close>
| \<open>is_hole (Txt _) = False\<close>

fun scan_path :: \<open>ustring list \<Rightarrow> ustring \<Rightarrow> ustring \<Rightarrow> (ustring list \<times> ustring) option\<close> where
  \<open>scan_path acc nm [] = None\<close>
| \<open>scan_path acc nm (c # cs) =
     (if is_idchar c then scan_path acc (nm @ [c]) cs
      else if c = dot then
        (if nm \<noteq> [] \<and> is_upper (hd nm) then scan_path (acc @ [nm]) [] cs else None)
      else if c = curlyc then
        (if nm \<noteq> [] \<and> is_lower (hd nm) then Some (acc @ [nm], cs) else None)
      else None)\<close>

fun add_char :: \<open>codepoint \<Rightarrow> piece list \<Rightarrow> piece list\<close> where
  \<open>add_char c (Txt t # ps) = Txt (c # t) # ps\<close>
| \<open>add_char c ps = Txt [c] # ps\<close>

(*<*)
lemma drop_eq_Cons_suffix: \<open>drop k s = c # r \<Longrightarrow> suffix r s \<and> length r < length s\<close>
  by (metis suffix_drop suffix_ConsD length_Cons Suc_le_lessD length_drop diff_le_self)

lemma read_escape_suffix: \<open>read_escape s = Some (c, r) \<Longrightarrow> suffix r s \<and> length r < length s\<close>
  by (auto simp: read_escape_def Let_def split: list.splits if_splits
      dest!: drop_eq_Cons_suffix intro: suffix_trans suffix_length_trans suffix_ConsI)
(*>*)

text \<open>\<^text>\<open>read_str\<close> reads a string body after the opening quote up to and
  including the closing quote; a newline or the end of the input before it,
  a bad escape and a bad hole fail. A dollar not followed by a brace is text.\<close>

function (sequential) read_str :: \<open>ustring \<Rightarrow> (piece list \<times> ustring) option\<close> where
  \<open>read_str [] = None\<close>
| \<open>read_str (c # cs) =
     (if c = qt then Some ([], cs)
      else if is_newline c then None
      else if c = bslash then
        (case read_escape cs of
           None \<Rightarrow> None
         | Some (d, r) \<Rightarrow> map_option (apfst (add_char d)) (read_str r))
      else if c = dollar \<and> (case cs of b # _ \<Rightarrow> b = curlyo | [] \<Rightarrow> False) then
        (case scan_path [] [] (tl cs) of
           None \<Rightarrow> None
         | Some (p, r) \<Rightarrow> map_option (apfst ((#) (Hole p))) (read_str r))
      else map_option (apfst (add_char c)) (read_str cs))\<close>
  by pat_completeness auto

(*<*)
lemma scan_path_suffix:
  \<open>scan_path acc nm s = Some (p, r) \<Longrightarrow> suffix r s \<and> length r < length s\<close>
  by (induction acc nm s arbitrary: p r rule: scan_path.induct)
     (auto split: if_splits intro: suffix_ConsI)
(*>*)

termination
  by (relation \<open>measure length\<close>)
     (auto dest!: read_escape_suffix scan_path_suffix)

definition has_hole :: \<open>piece list \<Rightarrow> bool\<close> where
  \<open>has_hole ps \<longleftrightarrow> (\<exists>p \<in> set ps. is_hole p)\<close>

text \<open>\<^text>\<open>read_char\<close> reads a character body after the opening quote: one
  character, plain or escaped, then the closing quote.\<close>

definition read_char :: \<open>ustring \<Rightarrow> (codepoint \<times> ustring) option\<close> where
  \<open>read_char s =
     (let close = (\<lambda>d r. case r of q # r' \<Rightarrow> if q = cq then Some (d, r') else None | [] \<Rightarrow> None)
      in case s of
           [] \<Rightarrow> None
         | c # r \<Rightarrow>
             if c = cq \<or> is_newline c then None
             else if c = bslash then
               (case read_escape r of Some (d, r') \<Rightarrow> close d r' | None \<Rightarrow> None)
             else close c r)\<close>

(*<*)
lemma read_str_suffix: \<open>read_str s = Some (ps, r) \<Longrightarrow> suffix r s \<and> length r < length s\<close>
proof (induction s arbitrary: ps r rule: read_str.induct)
  case 1
  then show ?case by simp
next
  case (2 c cs)
  note ih = "2.IH"
  from "2.prems" show ?case
  proof (cases \<open>c = qt\<close>)
    case True
    with "2.prems" show ?thesis by (auto intro: suffix_ConsI)
  next
    case qt: False
    show ?thesis
    proof (cases \<open>is_newline c\<close>)
      case True
      with "2.prems" qt show ?thesis by simp
    next
      case nl: False
      show ?thesis
      proof (cases \<open>c = bslash\<close>)
        case True
        with "2.prems" qt nl obtain d r' qs where e: \<open>read_escape cs = Some (d, r')\<close>
          and rr: \<open>read_str r' = Some (qs, r)\<close>
          by (auto split: option.splits)
        from read_escape_suffix[OF e] ih(1)[OF qt nl True e refl rr]
        show ?thesis by (auto intro: suffix_ConsI suffix_trans suffix_length_trans)
      next
        case nb: False
        show ?thesis
        proof (cases \<open>c = dollar \<and> (case cs of b # _ \<Rightarrow> b = curlyo | [] \<Rightarrow> False)\<close>)
          case True
          then obtain cs' where cs: \<open>cs = curlyo # cs'\<close> by (cases cs) auto
          with "2.prems" qt nl nb True obtain p r' qs where e: \<open>scan_path [] [] cs' = Some (p, r')\<close>
            and rr: \<open>read_str r' = Some (qs, r)\<close>
            by (auto split: option.splits)
          from e have e': \<open>scan_path [] [] (tl cs) = Some (p, r')\<close> by (simp add: cs)
          from scan_path_suffix[OF e] ih(2)[OF qt nl nb True e' refl rr] cs
          show ?thesis by (auto intro: suffix_ConsI suffix_trans suffix_length_trans)
        next
          case False
          with "2.prems" qt nl nb obtain qs where rr: \<open>read_str cs = Some (qs, r)\<close> by auto
          from ih(3)[OF qt nl nb False rr]
          show ?thesis by (auto intro: suffix_ConsI suffix_trans suffix_length_trans)
        qed
      qed
    qed
  qed
qed

lemma read_char_suffix: \<open>read_char s = Some (c, r) \<Longrightarrow> suffix r s \<and> length r < length s\<close>
  by (auto simp: read_char_def Let_def is_newline_def
      split: list.splits if_splits option.splits prod.splits
      dest!: read_escape_suffix intro: suffix_trans suffix_length_trans suffix_ConsI)
(*>*)

end
