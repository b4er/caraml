theory Unicode
  imports Main
begin

section \<open>UTF-8\<close>

text \<open>
  Isabelle's \<^typ>\<open>char\<close> is a byte, so non-ASCII source text arrives as
  multi-byte sequences and the codepoints a lexer works on have to be recovered
  from them. Three layers: an inductive specification \<^text>\<open>utf8\<close>
  transcribing the encoding table of RFC 3629 rule by rule, a decoder
  \<^text>\<open>utf8_decode\<close> returning either the codepoints or a diagnostic
  located at a byte offset, and the equivalence \<^text>\<open>utf8_decode_Inr_iff\<close>
  of the two, which pins the decoder down completely: it succeeds exactly on
  well-formed input and then returns exactly the specified codepoints.
\<close>

subsection \<open>Codepoints\<close>

text \<open>
  A codepoint is a number up to \<^text>\<open>U+10FFFF\<close>. The surrogate block
  \<^text>\<open>U+D800..U+DFFF\<close> is reserved for UTF-16 and has no UTF-8 encoding
  (RFC 3629, Sect. 3).
\<close>

type_synonym codepoint = nat

type_synonym ustring = \<open>codepoint list\<close>

definition is_surrogate :: \<open>codepoint \<Rightarrow> bool\<close> where
  \<open>is_surrogate c \<longleftrightarrow> 0xD800 \<le> c \<and> c \<le> 0xDFFF\<close>

definition is_valid_cp :: \<open>codepoint \<Rightarrow> bool\<close> where
  \<open>is_valid_cp c \<longleftrightarrow> c \<le> 0x10FFFF \<and> \<not> is_surrogate c\<close>

subsection \<open>Byte classes\<close>

text \<open>
  The high bits of a byte decide its class: ASCII \<^text>\<open>0xxxxxxx\<close>,
  continuation \<^text>\<open>10xxxxxx\<close>, and the leaders \<^text>\<open>110xxxxx\<close>,
  \<^text>\<open>1110xxxx\<close> and \<^text>\<open>11110xxx\<close>, announcing sequences of length
  2, 3 and 4. Bytes \<^text>\<open>0xF8..0xFF\<close> start no sequence at all.
\<close>

definition is_ascii :: \<open>char \<Rightarrow> bool\<close> where
  \<open>is_ascii b \<longleftrightarrow> of_char b \<le> (0x7F :: nat)\<close>

definition is_cont :: \<open>char \<Rightarrow> bool\<close> where
  \<open>is_cont b \<longleftrightarrow> 0x80 \<le> (of_char b :: nat) \<and> of_char b \<le> (0xBF :: nat)\<close>

definition is_lead2 :: \<open>char \<Rightarrow> bool\<close> where
  \<open>is_lead2 b \<longleftrightarrow> 0xC0 \<le> (of_char b :: nat) \<and> of_char b \<le> (0xDF :: nat)\<close>

definition is_lead3 :: \<open>char \<Rightarrow> bool\<close> where
  \<open>is_lead3 b \<longleftrightarrow> 0xE0 \<le> (of_char b :: nat) \<and> of_char b \<le> (0xEF :: nat)\<close>

definition is_lead4 :: \<open>char \<Rightarrow> bool\<close> where
  \<open>is_lead4 b \<longleftrightarrow> 0xF0 \<le> (of_char b :: nat) \<and> of_char b \<le> (0xF7 :: nat)\<close>

text \<open>A continuation byte carries six bits of the codepoint.\<close>

definition cont_val :: \<open>char \<Rightarrow> nat\<close> where
  \<open>cont_val b = of_char b mod 0x40\<close>

definition cont_byte :: \<open>nat \<Rightarrow> char\<close> where
  \<open>cont_byte x = char_of (0x80 + x mod 0x40)\<close>

subsection \<open>Specification\<close>

text \<open>
  \<^text>\<open>utf8_cp c bs\<close> holds when \<^text>\<open>bs\<close> is the encoding of the single
  codepoint \<^text>\<open>c\<close>. The four rules transcribe the table of RFC 3629,
  Sect. 3, the divisions splitting \<^text>\<open>c\<close> into the six-bit groups above
  bits 6, 12 and 18:

  \<^verbatim>\<open>
  0x0000..0x007F     0xxxxxxx
  0x0080..0x07FF     110xxxxx 10xxxxxx
  0x0800..0xFFFF     1110xxxx 10xxxxxx 10xxxxxx   (surrogates excluded)
  0x10000..0x10FFFF  11110xxx 10xxxxxx 10xxxxxx 10xxxxxx\<close>

  The lower bound of each rule rejects overlong forms, leaving every codepoint
  exactly one encoding, the shortest.
\<close>

inductive utf8_cp :: \<open>codepoint \<Rightarrow> string \<Rightarrow> bool\<close> where
  utf8_cp1: \<open>c \<le> 0x7F \<Longrightarrow>
    utf8_cp c [char_of c]\<close>
| utf8_cp2: \<open>0x80 \<le> c \<Longrightarrow> c \<le> 0x7FF \<Longrightarrow>
    utf8_cp c [char_of (0xC0 + c div 0x40), cont_byte c]\<close>
| utf8_cp3: \<open>0x800 \<le> c \<Longrightarrow> c \<le> 0xFFFF \<Longrightarrow> \<not> is_surrogate c \<Longrightarrow>
    utf8_cp c [char_of (0xE0 + c div 0x1000), cont_byte (c div 0x40), cont_byte c]\<close>
| utf8_cp4: \<open>0x10000 \<le> c \<Longrightarrow> c \<le> 0x10FFFF \<Longrightarrow>
    utf8_cp c [char_of (0xF0 + c div 0x40000), cont_byte (c div 0x1000),
               cont_byte (c div 0x40), cont_byte c]\<close>

inductive utf8 :: \<open>string \<Rightarrow> ustring \<Rightarrow> bool\<close> where
  utf8_Nil: \<open>utf8 [] []\<close>
| utf8_Cons: \<open>utf8_cp c bs \<Longrightarrow> utf8 s cs \<Longrightarrow> utf8 (bs @ s) (c # cs)\<close>

subsection \<open>Encoder\<close>

text \<open>
  The encoder mirrors the four rules. It is total, but only its restriction to
  \<^const>\<open>is_valid_cp\<close> inputs is meaningful.
\<close>

definition utf8_encode_cp :: \<open>codepoint \<Rightarrow> string\<close> where
  \<open>utf8_encode_cp c =
    (if c \<le> 0x7F then [char_of c]
     else if c \<le> 0x7FF then [char_of (0xC0 + c div 0x40), cont_byte c]
     else if c \<le> 0xFFFF then
       [char_of (0xE0 + c div 0x1000), cont_byte (c div 0x40), cont_byte c]
     else
       [char_of (0xF0 + c div 0x40000), cont_byte (c div 0x1000),
        cont_byte (c div 0x40), cont_byte c])\<close>

definition utf8_encode :: \<open>ustring \<Rightarrow> string\<close> where
  \<open>utf8_encode cs = concat (map utf8_encode_cp cs)\<close>

text \<open>The specification is deterministic and total on valid codepoints, with
  \<^const>\<open>utf8_encode_cp\<close> computing its unique witness.\<close>

lemma utf8_cp_valid: \<open>utf8_cp c bs \<Longrightarrow> is_valid_cp c\<close>
  by (cases rule: utf8_cp.cases)
     (auto simp: is_valid_cp_def is_surrogate_def)

lemma utf8_cp_encode_eq: \<open>utf8_cp c bs \<Longrightarrow> bs = utf8_encode_cp c\<close>
  by (cases rule: utf8_cp.cases) (auto simp: utf8_encode_cp_def)

lemma utf8_cp_encode: \<open>is_valid_cp c \<Longrightarrow> utf8_cp c (utf8_encode_cp c)\<close>
  by (auto simp: utf8_encode_cp_def is_valid_cp_def not_le
      intro: utf8_cp.intros)

lemma utf8_cp_iff: \<open>utf8_cp c bs \<longleftrightarrow> is_valid_cp c \<and> bs = utf8_encode_cp c\<close>
  by (auto intro: utf8_cp_encode dest: utf8_cp_valid utf8_cp_encode_eq)

subsection \<open>Decoder\<close>

text \<open>
  Errors are structured and carry byte offsets into the input, counted from
  \<^text>\<open>0\<close>, so that a caller can point at the offending byte.
\<close>

datatype utf8_error =
    InvalidByte nat char        \<comment> \<open>offset; byte \<^text>\<open>0xF8..0xFF\<close>, starts no sequence\<close>
  | StrayCont nat char          \<comment> \<open>offset; continuation byte outside a sequence\<close>
  | BadCont nat nat char        \<comment> \<open>sequence start; offset and value of non-continuation byte\<close>
  | Truncated nat nat nat       \<comment> \<open>sequence start; bytes needed; bytes available\<close>
  | Overlong nat nat codepoint  \<comment> \<open>sequence start; length; codepoint with shorter encoding\<close>
  | Surrogate nat codepoint     \<comment> \<open>sequence start; codepoint in \<^text>\<open>U+D800..U+DFFF\<close>\<close>
  | OutOfRange nat codepoint    \<comment> \<open>sequence start; codepoint beyond \<^text>\<open>U+10FFFF\<close>\<close>

text \<open>Decoding one sequence of length 2, 3 or 4 from its already separated
  bytes, \<^text>\<open>i\<close> being the offset of the leader.\<close>

definition decode2 :: \<open>nat \<Rightarrow> char \<Rightarrow> char \<Rightarrow> utf8_error + codepoint\<close> where
  \<open>decode2 i b\<^sub>0 b\<^sub>1 =
    (if \<not> is_cont b\<^sub>1 then Inl (BadCont i (i + 1) b\<^sub>1)
     else let c = (of_char b\<^sub>0 mod 0x20) * 0x40 + cont_val b\<^sub>1 in
       if c < 0x80 then Inl (Overlong i 2 c) else Inr c)\<close>

definition decode3 :: \<open>nat \<Rightarrow> char \<Rightarrow> char \<Rightarrow> char \<Rightarrow> utf8_error + codepoint\<close> where
  \<open>decode3 i b\<^sub>0 b\<^sub>1 b\<^sub>2 =
    (if \<not> is_cont b\<^sub>1 then Inl (BadCont i (i + 1) b\<^sub>1)
     else if \<not> is_cont b\<^sub>2 then Inl (BadCont i (i + 2) b\<^sub>2)
     else let c = (of_char b\<^sub>0 mod 0x10) * 0x1000 + cont_val b\<^sub>1 * 0x40 + cont_val b\<^sub>2 in
       if c < 0x800 then Inl (Overlong i 3 c)
       else if is_surrogate c then Inl (Surrogate i c)
       else Inr c)\<close>

definition decode4 :: \<open>nat \<Rightarrow> char \<Rightarrow> char \<Rightarrow> char \<Rightarrow> char \<Rightarrow> utf8_error + codepoint\<close> where
  \<open>decode4 i b\<^sub>0 b\<^sub>1 b\<^sub>2 b\<^sub>3 =
    (if \<not> is_cont b\<^sub>1 then Inl (BadCont i (i + 1) b\<^sub>1)
     else if \<not> is_cont b\<^sub>2 then Inl (BadCont i (i + 2) b\<^sub>2)
     else if \<not> is_cont b\<^sub>3 then Inl (BadCont i (i + 3) b\<^sub>3)
     else let c = (of_char b\<^sub>0 mod 0x8) * 0x40000 + cont_val b\<^sub>1 * 0x1000 +
                  cont_val b\<^sub>2 * 0x40 + cont_val b\<^sub>3 in
       if c < 0x10000 then Inl (Overlong i 4 c)
       else if 0x10FFFF < c then Inl (OutOfRange i c)
       else Inr c)\<close>

text \<open>The main loop dispatches on the class of the leading byte and threads
  \<^text>\<open>i\<close>, the offset of that byte in the whole input.\<close>

fun utf8_decode_at :: \<open>nat \<Rightarrow> string \<Rightarrow> utf8_error + ustring\<close> where
  \<open>utf8_decode_at i [] = Inr []\<close>
| \<open>utf8_decode_at i (b # bs) =
    (if is_ascii b then
       map_sum id ((#) (of_char b)) (utf8_decode_at (i + 1) bs)
     else if is_cont b then Inl (StrayCont i b)
     else if is_lead2 b then
       (case bs of
          b\<^sub>1 # bs' \<Rightarrow>
            (case decode2 i b b\<^sub>1 of
               Inl e \<Rightarrow> Inl e
             | Inr c \<Rightarrow> map_sum id ((#) c) (utf8_decode_at (i + 2) bs'))
        | _ \<Rightarrow> Inl (Truncated i 2 (1 + length bs)))
     else if is_lead3 b then
       (case bs of
          b\<^sub>1 # b\<^sub>2 # bs' \<Rightarrow>
            (case decode3 i b b\<^sub>1 b\<^sub>2 of
               Inl e \<Rightarrow> Inl e
             | Inr c \<Rightarrow> map_sum id ((#) c) (utf8_decode_at (i + 3) bs'))
        | _ \<Rightarrow> Inl (Truncated i 3 (1 + length bs)))
     else if is_lead4 b then
       (case bs of
          b\<^sub>1 # b\<^sub>2 # b\<^sub>3 # bs' \<Rightarrow>
            (case decode4 i b b\<^sub>1 b\<^sub>2 b\<^sub>3 of
               Inl e \<Rightarrow> Inl e
             | Inr c \<Rightarrow> map_sum id ((#) c) (utf8_decode_at (i + 4) bs'))
        | _ \<Rightarrow> Inl (Truncated i 4 (1 + length bs)))
     else Inl (InvalidByte i b))\<close>

definition utf8_decode :: \<open>string \<Rightarrow> utf8_error + ustring\<close> where
  \<open>utf8_decode = utf8_decode_at 0\<close>

text \<open>Where diagnostics are not wanted, decoding is an \<^typ>\<open>'a option\<close>.\<close>

definition utf8_decode' :: \<open>string \<Rightarrow> ustring option\<close> where
  \<open>utf8_decode' = case_sum (\<lambda>_. None) Some \<circ> utf8_decode\<close>

subsection \<open>Completeness\<close>

lemma of_char_cont_byte[simp]: \<open>of_char (cont_byte x) = (0x80 + x mod 0x40 :: nat)\<close>
  by (simp add: cont_byte_def)

lemma is_cont_cont_byte[simp]: \<open>is_cont (cont_byte x)\<close>
  by (simp add: is_cont_def)

lemma digit_div: \<open>r < n \<Longrightarrow> (q * n + r) div n = (q :: nat)\<close>
  by simp

lemma digit_mod: \<open>r < n \<Longrightarrow> (q * n + r) mod n = (r :: nat)\<close>
  by simp

lemma cont_val_cont_byte[simp]: \<open>cont_val (cont_byte x) = x mod 0x40\<close>
  using mod_mult_self3[of 2 \<open>0x40\<close> \<open>x mod 0x40\<close>] by (simp add: cont_val_def)

text \<open>Recomposing a codepoint from the six-bit groups an encoding splits it
  into.\<close>

lemma nat_digits3:
  fixes c :: nat
  shows \<open>c div 0x1000 * 0x1000 + c div 0x40 mod 0x40 * 0x40 + c mod 0x40 = c\<close>
  using mod_mult2_eq[of c \<open>0x40\<close> \<open>0x40\<close>, simplified]
    div_mult_mod_eq[of c \<open>0x1000\<close>] div_mult_mod_eq[of c \<open>0x40\<close>]
  by linarith

lemma nat_digits4:
  fixes c :: nat
  shows \<open>c div 0x40000 * 0x40000 + c div 0x1000 mod 0x40 * 0x1000 +
         c div 0x40 mod 0x40 * 0x40 + c mod 0x40 = c\<close>
  using mod_mult2_eq[of c \<open>0x1000\<close> \<open>0x40\<close>, simplified]
    div_mult_mod_eq[of c \<open>0x40000\<close>] div_mult_mod_eq[of c \<open>0x1000\<close>] nat_digits3[of c]
  by linarith

text \<open>The step the induction turns on: a specified sequence at the front of
  the input decodes and consumes exactly itself.\<close>

lemma utf8_decode_at_cp:
  assumes \<open>utf8_cp c bs\<close>
  shows \<open>utf8_decode_at i (bs @ s) = map_sum id ((#) c) (utf8_decode_at (i + length bs) s)\<close>
  using assms
proof (cases rule: utf8_cp.cases)
  case utf8_cp2
  have d: \<open>c div 0x40 < 0x20\<close>
    using \<open>c \<le> 0x7FF\<close> by (simp add: div_less_iff_less_mult)
  have dec: \<open>decode2 i (char_of (0xC0 + c div 0x40)) (cont_byte c) = Inr c\<close>
    using \<open>0x80 \<le> c\<close> d mod_mult_self3[of 6 \<open>0x20\<close> \<open>c div 0x40\<close>]
    by (simp add: decode2_def Let_def div_mult_mod_eq)
  with utf8_cp2 d show ?thesis
    by (simp add: is_ascii_def is_cont_def is_lead2_def)
next
  case utf8_cp3
  have d: \<open>c div 0x1000 < 0x10\<close> and i3: \<open>i + 3 = Suc (Suc (Suc i))\<close>
    using \<open>c \<le> 0xFFFF\<close> by (simp_all add: div_less_iff_less_mult)
  have dec: \<open>decode3 i (char_of (0xE0 + c div 0x1000)) (cont_byte (c div 0x40)) (cont_byte c)
               = Inr c\<close>
    using \<open>0x800 \<le> c\<close> \<open>\<not> is_surrogate c\<close> d
      mod_mult_self3[of 14 \<open>0x10\<close> \<open>c div 0x1000\<close>]
    by (simp add: decode3_def Let_def nat_digits3)
  with utf8_cp3 d show ?thesis
    by (simp add: i3 is_ascii_def is_cont_def is_lead2_def is_lead3_def)
next
  case utf8_cp4
  have d: \<open>c div 0x40000 < 0x8\<close> and i4: \<open>i + 4 = Suc (Suc (Suc (Suc i)))\<close>
    using \<open>c \<le> 0x10FFFF\<close> by (simp_all add: div_less_iff_less_mult)
  have dec: \<open>decode4 i (char_of (0xF0 + c div 0x40000)) (cont_byte (c div 0x1000))
               (cont_byte (c div 0x40)) (cont_byte c) = Inr c\<close>
    using \<open>0x10000 \<le> c\<close> \<open>c \<le> 0x10FFFF\<close> d
      mod_mult_self3[of 30 \<open>0x8\<close> \<open>c div 0x40000\<close>]
    by (simp add: decode4_def Let_def nat_digits4)
  with utf8_cp4 d show ?thesis
    by (simp add: i4 is_ascii_def is_cont_def is_lead2_def is_lead3_def is_lead4_def)
qed (simp add: is_ascii_def)

lemma utf8_decode_at_complete:
  assumes \<open>utf8 s cs\<close>
  shows \<open>utf8_decode_at i s = Inr cs\<close>
  using assms by (induction arbitrary: i rule: utf8.induct) (simp_all add: utf8_decode_at_cp)

subsection \<open>Soundness\<close>

text \<open>The decomposition lemmas rebuild a byte from its class test and its
  payload. With them, each successful branch of the decoder yields exactly one
  rule of the specification.\<close>

lemma cont_byte_eqI:
  assumes \<open>is_cont b\<close> and \<open>c mod 0x40 = cont_val b\<close>
  shows \<open>cont_byte c = b\<close>
proof -
  have \<open>of_char b - 0x80 < (0x40 :: nat)\<close>
    using assms by (auto simp: is_cont_def)
  with assms show ?thesis
    using mod_mult_self3[of 2 \<open>0x40\<close> \<open>of_char b - 0x80 :: nat\<close>]
    by (simp add: is_cont_def cont_byte_def cont_val_def)
qed

lemma lead2_decomp:
  assumes \<open>is_lead2 b\<close>
  shows \<open>char_of (0xC0 + of_char b mod 0x20 :: nat) = b\<close>
proof -
  have \<open>of_char b - 0xC0 < (0x20 :: nat)\<close>
    using assms by (auto simp: is_lead2_def)
  with assms show ?thesis
    using mod_mult_self3[of 6 \<open>0x20\<close> \<open>of_char b - 0xC0 :: nat\<close>] by (simp add: is_lead2_def)
qed

lemma lead3_decomp:
  assumes \<open>is_lead3 b\<close>
  shows \<open>char_of (0xE0 + of_char b mod 0x10 :: nat) = b\<close>
proof -
  have \<open>of_char b - 0xE0 < (0x10 :: nat)\<close>
    using assms by (auto simp: is_lead3_def)
  with assms show ?thesis
    using mod_mult_self3[of 14 \<open>0x10\<close> \<open>of_char b - 0xE0 :: nat\<close>] by (simp add: is_lead3_def)
qed

lemma lead4_decomp:
  assumes \<open>is_lead4 b\<close>
  shows \<open>char_of (0xF0 + of_char b mod 0x8 :: nat) = b\<close>
proof -
  have \<open>of_char b - 0xF0 < (0x8 :: nat)\<close>
    using assms by (auto simp: is_lead4_def)
  with assms show ?thesis
    using mod_mult_self3[of 30 \<open>0x8\<close> \<open>of_char b - 0xF0 :: nat\<close>] by (simp add: is_lead4_def)
qed

lemma utf8_cp_asciiI:
  assumes \<open>is_ascii b\<close>
  shows \<open>utf8_cp (of_char b) [b]\<close>
  using assms utf8_cp1[of \<open>of_char b\<close>] by (simp add: is_ascii_def)

lemma utf8_cp_lead2I:
  assumes l: \<open>is_lead2 b\<^sub>0\<close> and cb: \<open>is_cont b\<^sub>1\<close>
    and c: \<open>c = of_char b\<^sub>0 mod 0x20 * 0x40 + cont_val b\<^sub>1\<close>
    and lo: \<open>0x80 \<le> c\<close>
  shows \<open>utf8_cp c [b\<^sub>0, b\<^sub>1]\<close>
proof -
  have cv: \<open>cont_val b\<^sub>1 < 0x40\<close> and x: \<open>of_char b\<^sub>0 mod 0x20 < (0x20 :: nat)\<close>
    by (simp_all add: cont_val_def)
  then have hi: \<open>c \<le> 0x7FF\<close> using c by linarith
  have dv: \<open>c div 0x40 = of_char b\<^sub>0 mod 0x20\<close> and md: \<open>c mod 0x40 = cont_val b\<^sub>1\<close>
    by (simp_all only: c digit_div[OF cv] digit_mod[OF cv])
  show ?thesis
    using utf8_cp2[OF lo hi] by (simp add: dv lead2_decomp[OF l] cont_byte_eqI[OF cb md])
qed

lemma utf8_cp_lead3I:
  assumes l: \<open>is_lead3 b\<^sub>0\<close> and cb\<^sub>1: \<open>is_cont b\<^sub>1\<close> and cb\<^sub>2: \<open>is_cont b\<^sub>2\<close>
    and c: \<open>c = of_char b\<^sub>0 mod 0x10 * 0x1000 + cont_val b\<^sub>1 * 0x40 + cont_val b\<^sub>2\<close>
    and lo: \<open>0x800 \<le> c\<close> and sur: \<open>\<not> is_surrogate c\<close>
  shows \<open>utf8_cp c [b\<^sub>0, b\<^sub>1, b\<^sub>2]\<close>
proof -
  have cv\<^sub>1: \<open>cont_val b\<^sub>1 < 0x40\<close> and cv\<^sub>2: \<open>cont_val b\<^sub>2 < 0x40\<close>
    and x: \<open>of_char b\<^sub>0 mod 0x10 < (0x10 :: nat)\<close>
    by (simp_all add: cont_val_def)
  then have hi: \<open>c \<le> 0xFFFF\<close> using c by linarith
  have e: \<open>c = (of_char b\<^sub>0 mod 0x10 * 0x40 + cont_val b\<^sub>1) * 0x40 + cont_val b\<^sub>2\<close>
    by (simp add: c algebra_simps)
  have dv\<^sub>1: \<open>c div 0x40 = of_char b\<^sub>0 mod 0x10 * 0x40 + cont_val b\<^sub>1\<close>
    and md\<^sub>1: \<open>c mod 0x40 = cont_val b\<^sub>2\<close>
    by (simp_all only: e digit_div[OF cv\<^sub>2] digit_mod[OF cv\<^sub>2])
  have dv\<^sub>2: \<open>c div 0x1000 = of_char b\<^sub>0 mod 0x10\<close>
    and md\<^sub>2: \<open>c div 0x40 mod 0x40 = cont_val b\<^sub>1\<close>
    by (simp_all only: div_mult2_eq[of c \<open>0x40\<close> \<open>0x40\<close>, simplified] dv\<^sub>1
        digit_div[OF cv\<^sub>1] digit_mod[OF cv\<^sub>1])
  show ?thesis
    using utf8_cp3[OF lo hi sur]
    by (simp add: dv\<^sub>2 lead3_decomp[OF l]
        cont_byte_eqI[OF cb\<^sub>1 md\<^sub>2] cont_byte_eqI[OF cb\<^sub>2 md\<^sub>1])
qed

lemma utf8_cp_lead4I:
  assumes l: \<open>is_lead4 b\<^sub>0\<close>
    and cb\<^sub>1: \<open>is_cont b\<^sub>1\<close> and cb\<^sub>2: \<open>is_cont b\<^sub>2\<close> and cb\<^sub>3: \<open>is_cont b\<^sub>3\<close>
    and c: \<open>c = of_char b\<^sub>0 mod 0x8 * 0x40000 + cont_val b\<^sub>1 * 0x1000 +
                cont_val b\<^sub>2 * 0x40 + cont_val b\<^sub>3\<close>
    and lo: \<open>0x10000 \<le> c\<close> and hi: \<open>c \<le> 0x10FFFF\<close>
  shows \<open>utf8_cp c [b\<^sub>0, b\<^sub>1, b\<^sub>2, b\<^sub>3]\<close>
proof -
  have cv\<^sub>1: \<open>cont_val b\<^sub>1 < 0x40\<close> and cv\<^sub>2: \<open>cont_val b\<^sub>2 < 0x40\<close>
    and cv\<^sub>3: \<open>cont_val b\<^sub>3 < 0x40\<close>
    by (simp_all add: cont_val_def)
  have e: \<open>c = ((of_char b\<^sub>0 mod 0x8 * 0x40 + cont_val b\<^sub>1) * 0x40 + cont_val b\<^sub>2) * 0x40 +
               cont_val b\<^sub>3\<close>
    by (simp add: c algebra_simps)
  have dv\<^sub>1: \<open>c div 0x40 = (of_char b\<^sub>0 mod 0x8 * 0x40 + cont_val b\<^sub>1) * 0x40 + cont_val b\<^sub>2\<close>
    and md\<^sub>1: \<open>c mod 0x40 = cont_val b\<^sub>3\<close>
    by (simp_all only: e digit_div[OF cv\<^sub>3] digit_mod[OF cv\<^sub>3])
  have dv\<^sub>2: \<open>c div 0x1000 = of_char b\<^sub>0 mod 0x8 * 0x40 + cont_val b\<^sub>1\<close>
    and md\<^sub>2: \<open>c div 0x40 mod 0x40 = cont_val b\<^sub>2\<close>
    by (simp_all only: div_mult2_eq[of c \<open>0x40\<close> \<open>0x40\<close>, simplified] dv\<^sub>1
        digit_div[OF cv\<^sub>2] digit_mod[OF cv\<^sub>2])
  have dv\<^sub>3: \<open>c div 0x40000 = of_char b\<^sub>0 mod 0x8\<close>
    and md\<^sub>3: \<open>c div 0x1000 mod 0x40 = cont_val b\<^sub>1\<close>
    by (simp_all only: div_mult2_eq[of c \<open>0x1000\<close> \<open>0x40\<close>, simplified] dv\<^sub>2
        digit_div[OF cv\<^sub>1] digit_mod[OF cv\<^sub>1])
  show ?thesis
    using utf8_cp4[OF lo hi]
    by (simp add: dv\<^sub>3 lead4_decomp[OF l] cont_byte_eqI[OF cb\<^sub>1 md\<^sub>3]
        cont_byte_eqI[OF cb\<^sub>2 md\<^sub>2] cont_byte_eqI[OF cb\<^sub>3 md\<^sub>1])
qed

text \<open>Inverting a successful run of the decoder.\<close>

lemma decode2_InrD:
  assumes \<open>decode2 i b\<^sub>0 b\<^sub>1 = Inr c\<close>
  shows \<open>is_cont b\<^sub>1\<close>
    and \<open>c = of_char b\<^sub>0 mod 0x20 * 0x40 + cont_val b\<^sub>1\<close>
    and \<open>0x80 \<le> c\<close>
  using assms by (auto simp: decode2_def Let_def not_less split: if_splits)

lemma decode3_InrD:
  assumes \<open>decode3 i b\<^sub>0 b\<^sub>1 b\<^sub>2 = Inr c\<close>
  shows \<open>is_cont b\<^sub>1\<close> and \<open>is_cont b\<^sub>2\<close>
    and \<open>c = of_char b\<^sub>0 mod 0x10 * 0x1000 + cont_val b\<^sub>1 * 0x40 + cont_val b\<^sub>2\<close>
    and \<open>0x800 \<le> c\<close> and \<open>\<not> is_surrogate c\<close>
  using assms by (auto simp: decode3_def Let_def not_less split: if_splits)

lemma decode4_InrD:
  assumes \<open>decode4 i b\<^sub>0 b\<^sub>1 b\<^sub>2 b\<^sub>3 = Inr c\<close>
  shows \<open>is_cont b\<^sub>1\<close> and \<open>is_cont b\<^sub>2\<close> and \<open>is_cont b\<^sub>3\<close>
    and \<open>c = of_char b\<^sub>0 mod 0x8 * 0x40000 + cont_val b\<^sub>1 * 0x1000 +
             cont_val b\<^sub>2 * 0x40 + cont_val b\<^sub>3\<close>
    and \<open>0x10000 \<le> c\<close> and \<open>c \<le> 0x10FFFF\<close>
  using assms by (auto simp: decode4_def Let_def not_less split: if_splits)

lemma map_sum_Inr_iff: \<open>map_sum f g x = Inr z \<longleftrightarrow> (\<exists>y. x = Inr y \<and> z = g y)\<close>
  by (cases x) auto

lemma utf8_decode_at_ConsE:
  assumes dec: \<open>utf8_decode_at i (b # bs) = Inr cs\<close>
  obtains
    (ascii) cs' where \<open>is_ascii b\<close> \<open>cs = of_char b # cs'\<close>
      \<open>utf8_decode_at (i + 1) bs = Inr cs'\<close>
  | (lead2) b\<^sub>1 bs' c cs' where \<open>is_lead2 b\<close> \<open>bs = b\<^sub>1 # bs'\<close>
      \<open>decode2 i b b\<^sub>1 = Inr c\<close> \<open>cs = c # cs'\<close>
      \<open>utf8_decode_at (i + 2) bs' = Inr cs'\<close>
  | (lead3) b\<^sub>1 b\<^sub>2 bs' c cs' where \<open>is_lead3 b\<close> \<open>bs = b\<^sub>1 # b\<^sub>2 # bs'\<close>
      \<open>decode3 i b b\<^sub>1 b\<^sub>2 = Inr c\<close> \<open>cs = c # cs'\<close>
      \<open>utf8_decode_at (i + 3) bs' = Inr cs'\<close>
  | (lead4) b\<^sub>1 b\<^sub>2 b\<^sub>3 bs' c cs' where \<open>is_lead4 b\<close> \<open>bs = b\<^sub>1 # b\<^sub>2 # b\<^sub>3 # bs'\<close>
      \<open>decode4 i b b\<^sub>1 b\<^sub>2 b\<^sub>3 = Inr c\<close> \<open>cs = c # cs'\<close>
      \<open>utf8_decode_at (i + 4) bs' = Inr cs'\<close>
proof -
  from dec consider
      \<open>is_ascii b\<close>
    | \<open>\<not> is_ascii b\<close> \<open>\<not> is_cont b\<close> \<open>is_lead2 b\<close>
    | \<open>\<not> is_ascii b\<close> \<open>\<not> is_cont b\<close> \<open>\<not> is_lead2 b\<close> \<open>is_lead3 b\<close>
    | \<open>\<not> is_ascii b\<close> \<open>\<not> is_cont b\<close> \<open>\<not> is_lead2 b\<close> \<open>\<not> is_lead3 b\<close> \<open>is_lead4 b\<close>
    by (auto split: if_splits)

  thus thesis
    apply (cases)
       apply (use dec in \<open>auto intro: ascii simp: map_sum_Inr_iff\<close>)[]
      apply (use dec in \<open>auto intro: lead2 simp: map_sum_Inr_iff split: list.splits sum.splits\<close>)[]
     apply (use dec in \<open>auto intro: lead3 simp: map_sum_Inr_iff split: list.splits sum.splits\<close>)[]
    apply (use dec in \<open>auto intro: lead4 simp: map_sum_Inr_iff split: list.splits sum.splits\<close>)[]
    done
qed

lemma utf8_decode_at_sound:
  \<open>utf8_decode_at i s = Inr cs \<Longrightarrow> utf8 s cs\<close>
proof (induction s arbitrary: i cs rule: length_induct)
  case (1 s)
  show ?case
  proof (cases s)
    case (Cons b bs)
    from "1.prems"[unfolded Cons] show ?thesis
    proof (cases rule: utf8_decode_at_ConsE)
      case (ascii cs')
      have cp: \<open>utf8_cp (of_char b) [b]\<close>
        by (rule utf8_cp_asciiI[OF ascii(1)])
      have \<open>utf8 bs cs'\<close>
        using "1.IH"[rule_format, of bs \<open>i + 1\<close> cs'] Cons ascii(3) by simp
      with Cons ascii(2) show ?thesis using utf8_Cons[OF cp] by simp
    next
      case (lead2 b\<^sub>1 bs' c cs')
      have cp: \<open>utf8_cp c [b, b\<^sub>1]\<close>
        by (rule utf8_cp_lead2I[OF lead2(1) decode2_InrD[OF lead2(3)]])
      have \<open>utf8 bs' cs'\<close>
        using "1.IH"[rule_format, of bs' \<open>i + 2\<close> cs'] Cons lead2(2,5) by simp
      with Cons lead2(2,4) show ?thesis using utf8_Cons[OF cp] by simp
    next
      case (lead3 b\<^sub>1 b\<^sub>2 bs' c cs')
      have cp: \<open>utf8_cp c [b, b\<^sub>1, b\<^sub>2]\<close>
        by (rule utf8_cp_lead3I[OF lead3(1) decode3_InrD[OF lead3(3)]])
      have \<open>utf8 bs' cs'\<close>
        using "1.IH"[rule_format, of bs' \<open>i + 3\<close> cs'] Cons lead3(2,5) by simp
      with Cons lead3(2,4) show ?thesis using utf8_Cons[OF cp] by simp
    next
      case (lead4 b\<^sub>1 b\<^sub>2 b\<^sub>3 bs' c cs')
      have cp: \<open>utf8_cp c [b, b\<^sub>1, b\<^sub>2, b\<^sub>3]\<close>
        by (rule utf8_cp_lead4I[OF lead4(1) decode4_InrD[OF lead4(3)]])
      have \<open>utf8 bs' cs'\<close>
        using "1.IH"[rule_format, of bs' \<open>i + 4\<close> cs'] Cons lead4(2,5) by simp
      with Cons lead4(2,4) show ?thesis using utf8_Cons[OF cp] by simp
    qed
  qed (use "1.prems" in \<open>auto intro: utf8.intros\<close>)
qed

subsection \<open>Correctness\<close>

theorem utf8_decode_Inr_iff: \<open>utf8_decode s = Inr cs \<longleftrightarrow> utf8 s cs\<close>
  by (auto simp: utf8_decode_def intro: utf8_decode_at_complete dest: utf8_decode_at_sound)

corollary utf8_decode_Inl_iff: \<open>(\<exists>e. utf8_decode s = Inl e) \<longleftrightarrow> (\<nexists>cs. utf8 s cs)\<close>
  using utf8_decode_Inr_iff[of s] by (cases \<open>utf8_decode s\<close>) auto

corollary utf8_unique: \<open>utf8 s cs \<Longrightarrow> utf8 s cs' \<Longrightarrow> cs = cs'\<close>
  using utf8_decode_Inr_iff[of s cs] utf8_decode_Inr_iff[of s cs'] by auto

lemma utf8_valid: \<open>utf8 s cs \<Longrightarrow> \<forall>c \<in> set cs. is_valid_cp c\<close>
  by (induction rule: utf8.induct) (auto dest: utf8_cp_valid)

corollary utf8_decode_valid: \<open>utf8_decode s = Inr cs \<Longrightarrow> \<forall>c \<in> set cs. is_valid_cp c\<close>
  by (simp add: utf8_decode_Inr_iff utf8_valid)

lemma utf8_encode_utf8: \<open>\<forall>c \<in> set cs. is_valid_cp c \<Longrightarrow> utf8 (utf8_encode cs) cs\<close>
  by (induction cs) (auto simp: utf8_encode_def intro: utf8.intros utf8_cp_encode)

theorem utf8_decode_encode:
  \<open>\<forall>c \<in> set cs. is_valid_cp c \<Longrightarrow> utf8_decode (utf8_encode cs) = Inr cs\<close>
  by (simp add: utf8_decode_Inr_iff utf8_encode_utf8)

lemma utf8_decode'_Some_iff: \<open>utf8_decode' s = Some cs \<longleftrightarrow> utf8 s cs\<close>
  using utf8_decode_Inr_iff[of s] by (cases \<open>utf8_decode s\<close>) (auto simp: utf8_decode'_def)

end
