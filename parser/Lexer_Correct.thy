theory Lexer_Correct
  imports Lexer Trivia_Correct Literals_Correct
begin

section \<open>Correctness of the lexer\<close>

text \<open>The token relation and the token scanner agree: a scan result is a token
  of the relation on the split it reports, and every token of the relation is
  what the scanner returns on its lexeme followed by its tail. So the relation
  is deterministic, the longest match at any input is the scan result, and the
  body scanner follows a reading step by step. The decoders are then defined
  on every token the lexer produces.\<close>

subsection \<open>Character classes and tables\<close>

(*<*)
lemma class_disjoint:
  \<open>is_idstart c \<Longrightarrow> \<not> is_symchar c\<close> \<open>is_idstart c \<Longrightarrow> \<not> is_digit c\<close>
  \<open>is_idstart c \<Longrightarrow> \<not> is_delim c\<close> \<open>is_symchar c \<Longrightarrow> \<not> is_digit c\<close>
  \<open>is_symchar c \<Longrightarrow> \<not> is_delim c\<close> \<open>is_digit c \<Longrightarrow> \<not> is_delim c\<close>
  \<open>is_lower c \<Longrightarrow> \<not> is_upper c\<close>
  by (auto simp: class_defs)

lemma class_idchar:
  \<open>is_idchar c \<longleftrightarrow> is_idstart c \<or> is_digit c \<or> c = uscore \<or> c = cq\<close>
  by (auto simp: class_defs)

lemma class_dash:
  \<open>\<not> is_idstart dash\<close> \<open>\<not> is_idchar dash\<close> \<open>is_symchar dash\<close> \<open>\<not> is_digit dash\<close> \<open>\<not> is_delim dash\<close>
  by (simp_all add: class_defs)

lemma class_uscore:
  \<open>\<not> is_idstart uscore\<close> \<open>is_idchar uscore\<close> \<open>\<not> is_symchar uscore\<close> \<open>\<not> is_digit uscore\<close>
  \<open>\<not> is_delim uscore\<close>
  by (simp_all add: class_defs)

lemma class_dot:
  \<open>\<not> is_idstart dot\<close> \<open>\<not> is_idchar dot\<close> \<open>\<not> is_symchar dot\<close> \<open>\<not> is_digit dot\<close> \<open>\<not> is_delim dot\<close>
  by (simp_all add: class_defs)

lemma class_qt:
  \<open>\<not> is_idstart qt\<close> \<open>\<not> is_idchar qt\<close> \<open>\<not> is_symchar qt\<close> \<open>\<not> is_digit qt\<close> \<open>\<not> is_delim qt\<close>
  by (simp_all add: class_defs)

lemma class_cq:
  \<open>\<not> is_idstart cq\<close> \<open>is_idchar cq\<close> \<open>\<not> is_symchar cq\<close> \<open>\<not> is_digit cq\<close> \<open>\<not> is_delim cq\<close>
  by (simp_all add: class_defs)

lemma class_tick:
  \<open>\<not> is_idstart tick\<close> \<open>\<not> is_idchar tick\<close> \<open>\<not> is_symchar tick\<close> \<open>\<not> is_digit tick\<close>
  \<open>\<not> is_delim tick\<close>
  by (simp_all add: class_defs)

lemmas class_specials = class_dash class_uscore class_dot class_qt class_cq class_tick

lemma keyword_table_form:
  \<open>(u, t) \<in> set keyword_table \<Longrightarrow> \<exists>c cs. u = c # cs \<and> is_lower c \<and> list_all is_idchar cs\<close>
  by (auto simp: keyword_table_def class_defs)

lemma keyword_table_distinct: \<open>distinct (map fst keyword_table)\<close>
  by (simp add: keyword_table_def)

lemma symbol_table_form:
  \<open>(u, t) \<in> set symbol_table \<Longrightarrow>
   \<exists>c cs. u = c # cs \<and> is_symchar c \<and> list_all is_symchar cs \<and> (c = dash \<longrightarrow> cs \<noteq> [])\<close>
  by (auto simp: symbol_table_def class_defs)

lemma symbol_table_distinct: \<open>distinct (map fst symbol_table)\<close>
  by (simp add: symbol_table_def)

lemma delim_table_distinct: \<open>distinct (map fst delim_table)\<close>
  by (simp add: delim_table_def)

lemma is_delim_table: \<open>is_delim c \<longleftrightarrow> c \<in> fst ` set delim_table\<close>
  by (auto simp: is_delim_def delim_table_def)

lemma delim_table_class:
  \<open>(c, t) \<in> set delim_table \<Longrightarrow> \<not> is_idstart c \<and> c \<noteq> dash \<and> \<not> is_symchar c \<and> \<not> is_digit c\<close>
  by (auto simp: delim_table_def class_defs)

lemma keyword_lower: \<open>is_keyword u \<Longrightarrow> is_lower (hd u)\<close>
  by (auto dest!: keyword_table_form)

lemma starts_append: \<open>starts P (xs @ ys) \<longleftrightarrow> (if xs = [] then starts P ys else P (hd xs))\<close>
  by (cases xs) (auto simp: starts_def)

lemma starts_Cons [simp]: \<open>starts P (c # cs) \<longleftrightarrow> P c\<close>
  and starts_Nil [simp]: \<open>\<not> starts P []\<close>
  by (simp_all add: starts_def)

lemma starts_dropWhile: \<open>\<not> starts P (dropWhile P xs)\<close>
  by (induction xs) auto

lemma takeWhile_run: \<open>list_all P xs \<Longrightarrow> \<not> starts P ys \<Longrightarrow> takeWhile P (xs @ ys) = xs\<close>
  and dropWhile_run: \<open>list_all P xs \<Longrightarrow> \<not> starts P ys \<Longrightarrow> dropWhile P (xs @ ys) = ys\<close>
  by (induction xs) (auto simp: starts_def split: list.splits)

lemma cut_append [simp]: \<open>cut (u @ r) r = u\<close>
  by (simp add: cut_def)
(*>*)

subsection \<open>The token scanner against the token relation\<close>

text \<open>A scan splits its input into a token of the relation and the rest; the
  rules reject the empty lexeme.\<close>

lemma match_token_nonempty: \<open>TOKEN(st, u, tail) \<leadsto> t \<Longrightarrow> u \<noteq> []\<close>
  by (cases rule: match_token.cases)
     (auto dest!: read_num_suffix keyword_table_form symbol_table_form)

(*<*)
lemma cut_ne: \<open>suffix r s \<Longrightarrow> length r < length s \<Longrightarrow> cut s r \<noteq> []\<close>
  by (auto simp: cut_def suffix_def)

lemma scan_num_sound:
  assumes \<open>scan_num s = Some (t, u, r)\<close>
  shows \<open>s = u @ r \<and> u \<noteq> [] \<and> \<not> starts is_idchar r \<and>
    ((t = FloatL \<and> read_num s = Some (NFloat, r)) \<or>
     (t = IntL \<and> (\<exists>v sfx. read_num s = Some (NInt v sfx, r) \<and> in_range sfx v)))\<close>
  using assms
  by (auto simp: scan_num_def split: option.splits prod.splits numeral.splits if_splits
      dest!: read_num_suffix simp: cut_split cut_ne)

lemma num_tok:
  assumes \<open>scan_num s = Some (t, u, r)\<close> \<open>s = c # cs\<close> \<open>c = dash \<longrightarrow> \<not> after_operand st\<close>
  shows \<open>s = u @ r \<and> TOKEN(st, u, r) \<leadsto> t\<close>
proof -
  from scan_num_sound[OF assms(1)] have
    sr: \<open>s = u @ r\<close> and ne: \<open>u \<noteq> []\<close> and nr: \<open>\<not> starts is_idchar r\<close>
    and k: \<open>(t = FloatL \<and> read_num s = Some (NFloat, r)) \<or>
      (t = IntL \<and> (\<exists>v sfx. read_num s = Some (NInt v sfx, r) \<and> in_range sfx v))\<close> by blast+
  from ne sr assms(2) obtain u' where ue: \<open>u = c # u'\<close> by (cases u) auto
  have no: \<open>neg_ok st u\<close> using ue assms(3) by (simp add: neg_ok_def)
  from k sr nr no show ?thesis
    by (auto intro: match_token.Int match_token.Float)
qed

lemma list_all_takeWhile: \<open>list_all P (takeWhile P xs)\<close>
  by (induction xs) auto

lemma scan_sel_sound:
  assumes \<open>scan_sel st cs = Some (t, u, r)\<close>
  shows \<open>dot # cs = u @ r \<and> TOKEN(st, u, r) \<leadsto> t\<close>
proof (cases cs)
  case Nil with assms show ?thesis by (simp add: scan_sel_def)
next
  case (Cons c cs')
  show ?thesis
  proof (cases \<open>is_digit c\<close>)
    case True
    with assms Cons have e: \<open>t = sel_tok st c\<close> \<open>u = dot # c # takeWhile is_digit cs'\<close>
      \<open>r = dropWhile is_digit cs'\<close> \<open>\<not> starts is_idchar r\<close>
      by (auto simp: scan_sel_def Let_def split: if_splits)
    have \<open>cs' = takeWhile is_digit cs' @ r\<close> by (simp add: e(3))
    then show ?thesis
      using True e Cons by (auto intro!: match_token.SelN simp: list_all_takeWhile)
  next
    case False
    with assms Cons have i: \<open>is_idstart c\<close>
      by (auto simp: scan_sel_def split: if_splits)
    with False assms Cons have e: \<open>t = sel_tok st c\<close> \<open>u = dot # c # takeWhile is_idchar cs'\<close>
      \<open>r = dropWhile is_idchar cs'\<close>
      by (auto simp: scan_sel_def)
    have \<open>cs' = takeWhile is_idchar cs' @ r\<close> by (simp add: e(3))
    then show ?thesis
      using i e Cons by (auto intro!: match_token.Sel simp: list_all_takeWhile starts_dropWhile)
  qed
qed

lemma scan_str_sound:
  assumes \<open>scan_str cs = Some (t, u, r)\<close>
  shows \<open>qt # cs = u @ r \<and> TOKEN(st, u, r) \<leadsto> t\<close>
proof -
  from assms obtain ps where rs: \<open>read_str cs = Some (ps, r)\<close>
    and e: \<open>t = (if has_hole ps then StrI else StrL)\<close> \<open>u = qt # cut cs r\<close>
    by (auto simp: scan_str_def split: option.splits prod.splits)
  from read_str_suffix[OF rs] have \<open>cut cs r @ r = cs\<close> by (blast intro: cut_split)
  then have \<open>TOKEN(st, qt # cut cs r, r) \<leadsto> (if has_hole ps then StrI else StrL)\<close>
    by (intro match_token.Str) (simp add: rs)
  with e \<open>cut cs r @ r = cs\<close> show ?thesis by simp
qed

lemma scan_char_sound:
  assumes \<open>scan_char cs = Some (t, u, r)\<close>
  shows \<open>cq # cs = u @ r \<and> TOKEN(st, u, r) \<leadsto> t\<close>
proof -
  from assms obtain c where rs: \<open>read_char cs = Some (c, r)\<close>
    and e: \<open>t = CharL\<close> \<open>u = cq # cut cs r\<close>
    by (auto simp: scan_char_def split: option.splits prod.splits)
  from read_char_suffix[OF rs] have \<open>cut cs r @ r = cs\<close> by (blast intro: cut_split)
  with rs e show ?thesis by (auto intro: match_token.Char)
qed

lemma scan_tick_sound:
  assumes \<open>scan_tick cs = Some (t, u, r)\<close>
  shows \<open>tick # cs = u @ r \<and> TOKEN(st, u, r) \<leadsto> t\<close>
proof (cases cs)
  case Nil with assms show ?thesis by (simp add: scan_tick_def)
next
  case (Cons c cs')
  from assms Cons obtain k where lw: \<open>is_lower c\<close>
    and dw: \<open>dropWhile is_idchar cs' = k # r\<close> and kt: \<open>k = tick\<close>
    and nk: \<open>\<not> is_keyword (c # takeWhile is_idchar cs')\<close>
    and e: \<open>t = Op\<close> \<open>u = tick # (c # takeWhile is_idchar cs') @ [tick]\<close>
    by (auto simp: scan_tick_def Let_def split: if_splits list.splits)
  have \<open>cs' = takeWhile is_idchar cs' @ tick # r\<close>
    using takeWhile_dropWhile_id[of is_idchar cs'] dw kt by simp
  then show ?thesis
    using lw nk e Cons by (auto intro!: match_token.Tick simp: list_all_takeWhile)
qed
(*>*)

lemma lex_token_sound:
  \<open>lex_token st s = Some (t, u, r) \<Longrightarrow> s = u @ r \<and> TOKEN(st, u, r) \<leadsto> t\<close>
proof (cases s)
  case Nil then show \<open>lex_token st s = Some (t, u, r) \<Longrightarrow> ?thesis\<close> by simp
next
  case (Cons c cs)
  assume h0: \<open>lex_token st s = Some (t, u, r)\<close>
  note h = h0[unfolded Cons lex_token.simps]
  show ?thesis
  proof (cases \<open>is_idstart c\<close>)
    case True
    let ?u = \<open>c # takeWhile is_idchar cs\<close> and ?r = \<open>dropWhile is_idchar cs\<close>
    from h[unfolded if_P[OF True]] have e: \<open>t = classify_id ?u\<close> \<open>u = ?u\<close> \<open>r = ?r\<close>
      by (auto simp: Let_def)
    have nr: \<open>\<not> starts is_idchar ?r\<close> by (rule starts_dropWhile)
    have sr: \<open>s = ?u @ ?r\<close> by (simp add: Cons)
    show ?thesis
    proof (cases \<open>map_of keyword_table ?u\<close>)
      case (Some t')
      then have \<open>(?u, t') \<in> set keyword_table\<close> by (rule map_of_SomeD)
      with Some e nr sr show ?thesis by (auto simp: classify_id_def intro: match_token.Key)
    next
      case None
      then have nk: \<open>\<not> is_keyword ?u\<close> by (auto simp: map_of_eq_None_iff)
      show ?thesis
      proof (cases \<open>is_upper c\<close>)
        case True
        with None e nr sr show ?thesis
          by (auto simp: classify_id_def list_all_takeWhile intro: match_token.UId)
      next
        case False
        with \<open>is_idstart c\<close> have \<open>is_lower c\<close> by (simp add: class_defs) presburger
        with None False e nr sr nk show ?thesis
          by (auto simp: classify_id_def list_all_takeWhile intro: match_token.LId)
      qed
    qed
  next
    case nid: False
    note h1 = h[unfolded if_not_P[OF nid]]
    show ?thesis
    proof (cases \<open>c = dash \<and> starts is_digit cs \<and> \<not> after_operand st\<close>)
      case True
      from h1[unfolded if_P[OF True]] have \<open>scan_num s = Some (t, u, r)\<close> by (simp add: Cons)
      moreover have \<open>c = dash \<longrightarrow> \<not> after_operand st\<close> using True by simp
      ultimately show ?thesis by (rule num_tok[OF _ Cons])
    next
      case nd: False
      note h2 = h1[unfolded if_not_P[OF nd]]
      show ?thesis
      proof (cases \<open>is_symchar c\<close>)
        case True
        let ?u = \<open>c # takeWhile is_symchar cs\<close> and ?r = \<open>dropWhile is_symchar cs\<close>
        from h2[unfolded if_P[OF True]] have e: \<open>t = classify_sym ?u\<close> \<open>u = ?u\<close> \<open>r = ?r\<close>
          by (auto simp: Let_def)
        have nr: \<open>\<not> starts is_symchar ?r\<close> by (rule starts_dropWhile)
        have sr: \<open>s = ?u @ ?r\<close> by (simp add: Cons)
        have ls: \<open>list_all is_symchar ?u\<close> using True by (simp add: list_all_takeWhile)
        show ?thesis
        proof (cases \<open>map_of symbol_table ?u\<close>)
          case (Some t')
          then have \<open>(?u, t') \<in> set symbol_table\<close> by (rule map_of_SomeD)
          with Some e nr sr show ?thesis by (auto simp: classify_sym_def intro: match_token.Sym)
        next
          case None
          then have ns: \<open>\<not> is_symbol ?u\<close> by (auto simp: map_of_eq_None_iff)
          have nn: \<open>\<not> (?u = [dash] \<and> starts is_digit ?r \<and> \<not> after_operand st)\<close>
          proof
            assume a: \<open>?u = [dash] \<and> starts is_digit ?r \<and> \<not> after_operand st\<close>
            then have \<open>c = dash\<close> \<open>takeWhile is_symchar cs = []\<close> by simp_all
            then have \<open>?r = cs\<close> by (cases cs) auto
            with a nd \<open>c = dash\<close> show False by simp
          qed
          from None e nr sr ls ns nn show ?thesis
            by (auto simp: classify_sym_def intro: match_token.Op)
        qed
      next
        case nsy: False
        note h3 = h2[unfolded if_not_P[OF nsy]]
        show ?thesis
        proof (cases \<open>is_digit c\<close>)
          case True
          from h3[unfolded if_P[OF True]] have \<open>scan_num s = Some (t, u, r)\<close> by (simp add: Cons)
          moreover have \<open>c = dash \<longrightarrow> \<not> after_operand st\<close> using True class_dash by blast
          ultimately show ?thesis by (rule num_tok[OF _ Cons])
        next
          case ndg: False
          note h4 = h3[unfolded if_not_P[OF ndg]]
          show ?thesis
          proof (cases \<open>is_delim c\<close>)
            case True
            from h4[unfolded if_P[OF True]] have e: \<open>t = classify_delim c\<close> \<open>u = [c]\<close> \<open>r = cs\<close>
              and nc: \<open>\<not> (c = curlyo \<and> starts (\<lambda>d. d = dash) cs)\<close>
              by (simp_all split: if_splits)
            from True obtain t' where \<open>(c, t') \<in> set delim_table\<close>
              by (auto simp: is_delim_table)
            then have \<open>map_of delim_table c = Some t'\<close>
              by (intro map_of_is_SomeI[OF delim_table_distinct])
            with e nc \<open>(c, t') \<in> set delim_table\<close> show ?thesis
              by (auto simp: classify_delim_def Cons intro: match_token.Delim)
          next
            case ndl: False
            note h5 = h4[unfolded if_not_P[OF ndl]]
            show ?thesis
            proof (cases \<open>c = uscore\<close>)
              case True
              from h5[unfolded if_P[OF True]]
              have \<open>\<not> starts is_idchar cs\<close> \<open>t = KWild\<close> \<open>u = [c]\<close> \<open>r = cs\<close>
                by (auto split: if_splits)
              with True show ?thesis by (auto simp: Cons intro: match_token.Wild)
            next
              case nus: False
              note h6 = h5[unfolded if_not_P[OF nus]]
              show ?thesis
              proof (cases \<open>c = dot\<close>)
                case True
                from scan_sel_sound[OF h6[unfolded if_P[OF True]]] True
                show ?thesis by (simp add: Cons)
              next
                case ndt: False
                note h7 = h6[unfolded if_not_P[OF ndt]]
                show ?thesis
                proof (cases \<open>c = qt\<close>)
                  case True
                  from scan_str_sound[OF h7[unfolded if_P[OF True]]] True
                  show ?thesis by (simp add: Cons)
                next
                  case nqt: False
                  note h8 = h7[unfolded if_not_P[OF nqt]]
                  show ?thesis
                  proof (cases \<open>c = cq\<close>)
                    case True
                    from scan_char_sound[OF h8[unfolded if_P[OF True]]] True
                    show ?thesis by (simp add: Cons)
                  next
                    case ncq: False
                    note h9 = h8[unfolded if_not_P[OF ncq]]
                    show ?thesis
                    proof (cases \<open>c = tick\<close>)
                      case True
                      from scan_tick_sound[OF h9[unfolded if_P[OF True]]] True
                      show ?thesis by (simp add: Cons)
                    next
                      case nt: False
                      from h9[unfolded if_not_P[OF nt]] show ?thesis by simp
                    qed
                  qed
                qed
              qed
            qed
          qed
        qed
      qed
    qed
  qed
qed

text \<open>Conversely the scanner finds every token of the relation, with its
  lexeme: the rules describe maximal lexemes, so there is nothing longer to
  find.\<close>

(*<*)
lemma scan_digits_starts: \<open>scan_digits D s = Some p \<Longrightarrow> starts D s\<close>
  by (auto simp: scan_digits_def starts_def split: list.splits if_splits)

lemma read_unsigned_starts: \<open>read_unsigned s = Some x \<Longrightarrow> starts is_digit s\<close>
  by (auto simp: read_unsigned_def read_radix_def starts_def class_defs
      dest: scan_digits_starts[unfolded starts_def]
      split: option.splits list.splits if_splits prod.splits)

lemma cls_sym:
  \<open>is_symchar c \<Longrightarrow> \<not> is_idstart c \<and> \<not> is_digit c \<and> \<not> is_delim c \<and> c \<noteq> uscore \<and> c \<noteq> dot
     \<and> c \<noteq> qt \<and> c \<noteq> cq \<and> c \<noteq> tick\<close>
  by (auto simp: class_defs)

lemma cls_digit:
  \<open>is_digit c \<Longrightarrow> \<not> is_idstart c \<and> \<not> is_symchar c \<and> \<not> is_delim c \<and> c \<noteq> dash\<close>
  by (auto simp: class_defs)

lemma cls_lower: \<open>is_lower c \<Longrightarrow> is_idstart c\<close> and cls_upper: \<open>is_upper c \<Longrightarrow> is_idstart c\<close>
  by (auto simp: class_defs)

lemma cls_digit_idchar: \<open>is_digit c \<Longrightarrow> is_idchar c\<close>
  by (simp add: class_idchar)

lemma lex_id:
  \<open>is_idstart c \<Longrightarrow> list_all is_idchar cs \<Longrightarrow> \<not> starts is_idchar tail \<Longrightarrow>
   lex_token st (c # cs @ tail) = Some (classify_id (c # cs), c # cs, tail)\<close>
  by (simp add: Let_def takeWhile_run dropWhile_run)

lemma lex_sym:
  \<open>is_symchar c \<Longrightarrow> list_all is_symchar cs \<Longrightarrow> \<not> starts is_symchar tail \<Longrightarrow>
   \<not> (c = dash \<and> cs = [] \<and> starts is_digit tail \<and> \<not> after_operand st) \<Longrightarrow>
   lex_token st (c # cs @ tail) = Some (classify_sym (c # cs), c # cs, tail)\<close>
proof -
  assume h: \<open>is_symchar c\<close> \<open>list_all is_symchar cs\<close> \<open>\<not> starts is_symchar tail\<close>
    \<open>\<not> (c = dash \<and> cs = [] \<and> starts is_digit tail \<and> \<not> after_operand st)\<close>
  have tw: \<open>takeWhile is_symchar (cs @ tail) = cs\<close> \<open>dropWhile is_symchar (cs @ tail) = tail\<close>
    using takeWhile_run[of is_symchar cs tail] dropWhile_run[of is_symchar cs tail] h by simp_all
  have nd: \<open>\<not> (c = dash \<and> starts is_digit (cs @ tail) \<and> \<not> after_operand st)\<close>
  proof (cases cs)
    case Nil
    then show ?thesis using h by simp
  next
    case (Cons d ds)
    with h have \<open>is_symchar d\<close> by simp
    then show ?thesis using Cons cls_sym[of d] by (simp add: starts_def)
  qed
  show ?thesis using h(1) cls_sym[of c] nd tw by (simp add: Let_def) blast
qed

lemma classify_id_key: \<open>(u, t) \<in> set keyword_table \<Longrightarrow> classify_id u = t\<close>
  by (simp add: classify_id_def map_of_is_SomeI[OF keyword_table_distinct])

lemma classify_id_non:
  \<open>\<not> is_keyword (c # cs) \<Longrightarrow> classify_id (c # cs) = (if is_upper c then UId else LId)\<close>
proof -
  assume \<open>\<not> is_keyword (c # cs)\<close>
  then have \<open>map_of keyword_table (c # cs) = None\<close> by (simp add: map_of_eq_None_iff)
  then show ?thesis by (simp add: classify_id_def)
qed

lemma classify_sym_tab: \<open>(u, t) \<in> set symbol_table \<Longrightarrow> classify_sym u = t\<close>
  by (simp add: classify_sym_def map_of_is_SomeI[OF symbol_table_distinct])

lemma classify_sym_non: \<open>\<not> is_symbol u \<Longrightarrow> classify_sym u = Op\<close>
proof -
  assume \<open>\<not> is_symbol u\<close>
  then have \<open>map_of symbol_table u = None\<close> by (simp add: map_of_eq_None_iff)
  then show ?thesis by (simp add: classify_sym_def)
qed

lemma lex_num:
  assumes \<open>read_num (u @ tail) = Some (n, tail)\<close> \<open>neg_ok st u\<close>
  shows \<open>lex_token st (u @ tail) = scan_num (u @ tail)\<close>
proof -
  from read_num_suffix[OF assms(1)] have \<open>u \<noteq> []\<close> by auto
  then obtain c cs where u: \<open>u = c # cs\<close> by (cases u) auto
  show ?thesis
  proof (cases \<open>c = dash\<close>)
    case True
    with assms(1) u obtain m where \<open>read_unsigned (cs @ tail) = Some m\<close>
      by (auto simp: read_num_def)
    from read_unsigned_starts[OF this] have \<open>starts is_digit (cs @ tail)\<close> .
    moreover from assms(2) True u have \<open>\<not> after_operand st\<close> by (simp add: neg_ok_def)
    ultimately show ?thesis using True u by (simp add: class_dash)
  next
    case False
    with assms(1) u obtain m where \<open>read_unsigned (c # cs @ tail) = Some m\<close>
      by (auto simp: read_num_def)
    from read_unsigned_starts[OF this] have \<open>is_digit c\<close> by simp
    then show ?thesis using False u cls_digit[of c] by simp
  qed
qed
(*>*)

lemma match_token_lex:
  \<open>TOKEN(st, u, tail) \<leadsto> t \<Longrightarrow> lex_token st (u @ tail) = Some (t, u, tail)\<close>
proof (induction rule: match_token.induct)
  case (Key u t tail st)
  from Key obtain c cs where u: \<open>u = c # cs\<close> \<open>is_lower c\<close> \<open>list_all is_idchar cs\<close>
    by (auto dest!: keyword_table_form)
  with Key show ?case by (simp add: lex_id cls_lower classify_id_key del: lex_token.simps)
next
  case (LId c cs tail st)
  have \<open>\<not> is_upper c\<close> using LId by (auto dest: class_disjoint(7))
  with LId show ?case by (simp add: lex_id cls_lower classify_id_non del: lex_token.simps)
next
  case (UId c cs tail st)
  have \<open>\<not> is_keyword (c # cs)\<close> using UId by (auto dest!: keyword_lower dest: class_disjoint(7))
  with UId show ?case by (simp add: lex_id cls_upper classify_id_non del: lex_token.simps)
next
  case (Sym u t tail st)
  from Sym obtain c cs where u: \<open>u = c # cs\<close> \<open>is_symchar c\<close> \<open>list_all is_symchar cs\<close>
    \<open>c = dash \<longrightarrow> cs \<noteq> []\<close>
    by (auto dest!: symbol_table_form)
  have nd: \<open>\<not> (c = dash \<and> cs = [] \<and> starts is_digit tail \<and> \<not> after_operand st)\<close>
    using u by blast
  have e: \<open>lex_token st (c # cs @ tail) = Some (classify_sym (c # cs), c # cs, tail)\<close>
    by (rule lex_sym[OF u(2) u(3) Sym(2) nd])
  have ct: \<open>classify_sym (c # cs) = t\<close> using classify_sym_tab[OF Sym(1)] u(1) by simp
  show ?case using e ct u(1) by simp
next
  case (Op u tail st)
  from Op obtain c cs where u: \<open>u = c # cs\<close> by (cases u) auto
  with Op have h: \<open>is_symchar c\<close> \<open>list_all is_symchar cs\<close> by simp_all
  from Op u have nd: \<open>\<not> (c = dash \<and> cs = [] \<and> starts is_digit tail \<and> \<not> after_operand st)\<close>
    by auto
  have e: \<open>lex_token st (c # cs @ tail) = Some (classify_sym (c # cs), c # cs, tail)\<close>
    by (rule lex_sym[OF h(1) h(2) _ nd]) (use Op u in simp)
  have ct: \<open>classify_sym (c # cs) = Op\<close> using classify_sym_non Op u by simp
  show ?case using e ct u by simp
next
  case (Delim c t tail st)
  then show ?case
  proof -
    from Delim have k: \<open>(c, t) \<in> set delim_table\<close> by simp
    from delim_table_class[OF k] have n: \<open>\<not> is_idstart c\<close> \<open>c \<noteq> dash\<close> \<open>\<not> is_symchar c\<close>
      \<open>\<not> is_digit c\<close> by simp_all
    from k have d: \<open>is_delim c\<close> by (force simp: is_delim_table image_iff)
    from k have \<open>classify_delim c = t\<close>
      by (simp add: classify_delim_def map_of_is_SomeI[OF delim_table_distinct])
    with n d Delim show ?thesis by simp
  qed
next
  case (Wild tail st)
  then show ?case by (simp add: class_defs)
next
  case (Tick c cs tail st)
  then show ?case
    by (simp add: class_tick scan_tick_def Let_def takeWhile_run dropWhile_run class_idchar
        class_defs)
next
  case (Int u v sfx tail st)
  then show ?case by (simp add: lex_num scan_num_def)
next
  case (Float u tail st)
  then show ?case by (simp add: lex_num scan_num_def)
next
  case (Sel c cs tail st)
  then show ?case
    by (simp add: class_dot scan_sel_def takeWhile_run dropWhile_run class_disjoint)
next
  case (SelN c cs tail st)
  have \<open>\<not> starts is_digit tail\<close> using SelN by (cases tail) (auto simp: cls_digit_idchar)
  with SelN show ?case
    by (simp add: class_dot scan_sel_def takeWhile_run dropWhile_run)
next
  case (Str cs tail ps st)
  then show ?case by (simp add: class_qt scan_str_def)
next
  case (Char cs tail c st)
  then show ?case by (simp add: class_cq scan_char_def)
qed

lemma token_deterministic:
  \<open>TOKEN(st, u, tail) \<leadsto> t \<Longrightarrow> TOKEN(st, u, tail) \<leadsto> t' \<Longrightarrow> t = t'\<close>
  by (drule match_token_lex)+ simp

text \<open>The token relation is deterministic and rejects the empty string, so
  the CaraML tokens with the lexer state form a token language.\<close>

global_interpretation token_lang match_trivia is_newline match_token lex_step lex_init
  \<open>\<lambda>_. True\<close> no_bidi
  by unfold_locales
     (auto dest: tr_deterministic match_trivia_nonempty token_deterministic match_token_nonempty)

text \<open>The longest token match at any input is the scan result.\<close>

lemma longest_ctx_lex:
  \<open>longest_ctx (match_token st) s = map_option (\<lambda>(t, u, _). (t, u)) (lex_token st s)\<close>
proof (cases \<open>lex_token st s\<close>)
  case None
  have \<open>lexemes st s = {}\<close>
  proof (rule ccontr)
    assume \<open>lexemes st s \<noteq> {}\<close>
    then obtain t u where \<open>(t, u) \<in> lexemes st s\<close> by auto
    then have \<open>TOKEN(st, u, drop (length u) s) \<leadsto> t\<close> \<open>prefix u s\<close>
      by (auto simp: lexemes_def match_ctx_def match_def)
    then have \<open>lex_token st s = Some (t, u, drop (length u) s)\<close>
      using match_token_lex[of st u \<open>drop (length u) s\<close> t] by (auto simp: prefix_def)
    with None show False by simp
  qed
  with None show ?thesis by (simp add: lexemes_longest_None_iff)
next
  case (Some x)
  then obtain t u r where x: \<open>x = (t, u, r)\<close> by (cases x) auto
  with Some lex_token_sound have s: \<open>s = u @ r\<close> and tok: \<open>TOKEN(st, u, r) \<leadsto> t\<close> by blast+
  have mem: \<open>(t, u) \<in> lexemes st s\<close>
    using s tok by (auto simp: lexemes_def match_ctx_def match_def)
  have \<open>length (snd y) \<le> length u\<close> if \<open>y \<in> lexemes st s\<close> for y
  proof -
    obtain t' u' where y: \<open>y = (t', u')\<close> by (cases y)
    with that have \<open>TOKEN(st, u', drop (length u') s) \<leadsto> t'\<close> \<open>prefix u' s\<close>
      by (auto simp: lexemes_def match_ctx_def match_def)
    then have \<open>lex_token st s = Some (t', u', drop (length u') s)\<close>
      using match_token_lex[of st u' \<open>drop (length u') s\<close> t'] by (auto simp: prefix_def)
    with Some x y show ?thesis by simp
  qed
  with mem Some x show ?thesis by (simp add: lexemes_longest_Some_iff)
qed

subsection \<open>The body scanner against the readings\<close>

lemma lex_body_sound:
  \<open>lex_body st line col off acc cs = Some (result, []) \<Longrightarrow>
   \<exists>body. result = rev acc @ body \<and> lexed_body st line col off cs body\<close>
proof (induction st line col off acc cs arbitrary: result rule: lex_body.induct)
  case (1 st line col off acc)
  then show ?case by (auto intro: lexed_body.intros)
next
  case (2 st line col off acc c cs)
  from "2.prems" obtain t u cs\<^sub>1 trs line\<^sub>2 col\<^sub>2 off\<^sub>2 cs\<^sub>2 where
    LT: \<open>lex_token st (c # cs) = Some (t, u, cs\<^sub>1)\<close> and
    LTR: \<open>lex_trivia (advance_line line u) (advance_col col u) (off + length u) cs\<^sub>1
            = Some (trs, line\<^sub>2, col\<^sub>2, off\<^sub>2, cs\<^sub>2)\<close> and
    REC: \<open>lex_body (lex_step st t (trs = [])) line\<^sub>2 col\<^sub>2 off\<^sub>2
            (mk_lexed_token line col off t u trs # acc) cs\<^sub>2 = Some (result, [])\<close>
    by (auto split: option.splits prod.splits)
  from "2.IH"[OF LT refl refl LTR refl refl refl refl REC] obtain body where
    body: \<open>result = rev (mk_lexed_token line col off t u trs # acc) @ body\<close> and
    LB: \<open>lexed_body (lex_step st t (trs = [])) line\<^sub>2 col\<^sub>2 off\<^sub>2 cs\<^sub>2 body\<close>
    by blast
  from lex_token_sound[OF LT] have cs\<^sub>1: \<open>cs\<^sub>1 = drop (length u) (c # cs)\<close> by simp
  have LM: \<open>longest_ctx (match_token st) (c # cs) = Some (t, u)\<close>
    unfolding longest_ctx_lex LT by simp
  from lex_trivia_sound[OF LTR] have
    STR: \<open>strip_trivia (advance_line line u) (advance_col col u) (off + length u) cs\<^sub>1 trs cs\<^sub>2\<close> and
    L2: \<open>line\<^sub>2 = advance_line (advance_line line u) (consumed trs)\<close> and
    C2: \<open>col\<^sub>2 = advance_col (advance_col col u) (consumed trs)\<close> and
    O2: \<open>off\<^sub>2 = off + length u + length (consumed trs)\<close>
    by auto
  have \<open>lexed_body st line col off (c # cs) (mk_lexed_token line col off t u trs # body)\<close>
    by (rule lexed_body.lexed_body_Step[OF LM]) (use STR LB in \<open>simp_all add: cs\<^sub>1 L2 C2 O2\<close>)
  with body show ?case by (intro exI[where x = \<open>mk_lexed_token line col off t u trs # body\<close>]) simp
qed

lemma lex_body_complete:
  \<open>lexed_body st line col off cs body \<Longrightarrow>
   lex_body st line col off acc cs = Some (rev acc @ body, [])\<close>
proof (induction arbitrary: acc rule: lexed_body.induct)
  case (lexed_body_Nil st line col off)
  then show ?case by simp
next
  case (lexed_body_Step st c cs t u line col off tsp rem r)
  from lexed_body_Step.hyps(1) obtain cs\<^sub>1 where LT: \<open>lex_token st (c # cs) = Some (t, u, cs\<^sub>1)\<close>
    by (auto simp: longest_ctx_lex)
  from lex_token_sound[OF LT] have cs\<^sub>1: \<open>cs\<^sub>1 = drop (length u) (c # cs)\<close> by simp
  from lex_trivia_ex_Some obtain trs line\<^sub>2 col\<^sub>2 off\<^sub>2 cs\<^sub>2 where
    LTR: \<open>lex_trivia (advance_line line u) (advance_col col u) (off + length u) cs\<^sub>1
            = Some (trs, line\<^sub>2, col\<^sub>2, off\<^sub>2, cs\<^sub>2)\<close>
    by blast
  from lex_trivia_sound[OF LTR] have
    STR: \<open>strip_trivia (advance_line line u) (advance_col col u) (off + length u) cs\<^sub>1 trs cs\<^sub>2\<close> and
    L2: \<open>line\<^sub>2 = advance_line (advance_line line u) (consumed trs)\<close> and
    C2: \<open>col\<^sub>2 = advance_col (advance_col col u) (consumed trs)\<close> and
    O2: \<open>off\<^sub>2 = off + length u + length (consumed trs)\<close>
    by auto
  from longests_deterministic[OF STR[unfolded cs\<^sub>1] lexed_body_Step.hyps(2)]
  have trs: \<open>trs = tsp\<close> \<open>cs\<^sub>2 = rem\<close> by auto
  from lexed_body_Step.IH[of \<open>mk_lexed_token line col off t u tsp # acc\<close>]
  have REC: \<open>lex_body (lex_step st t (tsp = [])) line\<^sub>2 col\<^sub>2 off\<^sub>2
               (mk_lexed_token line col off t u tsp # acc) rem
             = Some (rev acc @ mk_lexed_token line col off t u tsp # r, [])\<close>
    by (simp add: L2 C2 O2 trs)
  show ?case using LT LTR REC trs by simp
qed

subsection \<open>Soundness and completeness\<close>

text \<open>Every result of \<^const>\<open>caraml_lex\<close> is a reading of the source, and
  every reading is its result: \<^const>\<open>caraml_lex\<close> is a lexer for the CaraML
  token language.\<close>

lemma caraml_lex_sound:
  \<open>caraml_lex s = Some (header, body) \<Longrightarrow> lexed 0 0 0 s (header, body)\<close>
proof -
  assume \<open>caraml_lex s = Some (header, body)\<close>
  then obtain line col off cs' where
    bidi: \<open>no_bidi s\<close> and
    trivia: \<open>lex_trivia 0 0 0 s = Some (header, line, col, off, cs')\<close> and
    body: \<open>lex_body lex_init line col off [] cs' = Some (body, [])\<close>
    by (auto simp: caraml_lex_def bind_eq_Some_conv split: if_splits)
  from lex_trivia_sound[OF trivia] lex_body_sound[OF body] bidi show ?thesis
    by (auto intro: lexed.intros)
qed

lemma caraml_lex_complete:
  \<open>lexed 0 0 0 s (header, body) \<Longrightarrow> caraml_lex s = Some (header, body)\<close>
proof -
  assume \<open>lexed 0 0 0 s (header, body)\<close>
  then obtain tail where
    bidi: \<open>no_bidi s\<close> and
    STR: \<open>strip_trivia 0 0 0 s header tail\<close> and
    LB: \<open>lexed_body lex_init (advance_line 0 (consumed header)) (advance_col 0 (consumed header))
           (length (consumed header)) tail body\<close>
    by (auto elim: lexed.cases)
  from lex_trivia_ex_Some obtain header' line col off tail' where
    LT: \<open>lex_trivia 0 0 0 s = Some (header', line, col, off, tail')\<close>
    by blast
  from lex_trivia_sound[OF LT] STR have
    eq: \<open>header' = header\<close> \<open>tail' = tail\<close> and
    cur: \<open>line = advance_line 0 (consumed header)\<close> \<open>col = advance_col 0 (consumed header)\<close>
         \<open>off = length (consumed header)\<close>
    by (auto dest: longests_deterministic)
  from lex_body_complete[OF LB, of \<open>[]\<close>] LT bidi show ?thesis
    by (simp add: caraml_lex_def eq cur)
qed

global_interpretation lexer match_trivia is_newline match_token lex_step lex_init \<open>\<lambda>_. True\<close>
  no_bidi caraml_lex
  by unfold_locales (auto intro: caraml_lex_sound caraml_lex_complete)

subsection \<open>The decoders\<close>

text \<open>The readers of \<^theory>\<open>CaraML_Parser.Literals_Correct\<close> decode a lexeme on its own
  as the token relation read it in context.\<close>

text \<open>Every token of a reading is a token of the relation in some state.\<close>

lemma lexed_body_tokens:
  \<open>lexed_body st line col off cs body \<Longrightarrow> x \<in> set body \<Longrightarrow>
   \<exists>st' tail. TOKEN(st', s_txt (span x), tail) \<leadsto> tok x\<close>
proof (induction rule: lexed_body.induct)
  case (lexed_body_Step st c cs t u line col off tsp rem r)
  then show ?case by (fastforce dest!: lexemes_longest_SomeD)
qed simp

(*<*)
lemma table_toks:
  \<open>(u, t) \<in> set keyword_table \<Longrightarrow> t \<notin> {IntL, FloatL, StrL, StrI, CharL}\<close>
  \<open>(u, t) \<in> set symbol_table \<Longrightarrow> t \<notin> {IntL, FloatL, StrL, StrI, CharL}\<close>
  \<open>(c, t) \<in> set delim_table \<Longrightarrow> t \<notin> {IntL, FloatL, StrL, StrI, CharL}\<close>
  \<open>sel_tok st c \<noteq> IntL \<and> sel_tok st c \<noteq> FloatL \<and> sel_tok st c \<noteq> StrL \<and> sel_tok st c \<noteq> StrI \<and>
   sel_tok st c \<noteq> CharL\<close>
  by (auto simp: keyword_table_def symbol_table_def delim_table_def sel_tok_def)
(*>*)

text \<open>So the decoders are defined on every literal token the lexer produces:
  the reader accepts the whole lexeme, the integer value is in range, and the
  string token says whether the string has holes.\<close>

lemma decoders_defined:
  assumes \<open>caraml_lex s = Some (header, body)\<close> \<open>x \<in> set body\<close>
  defines \<open>u \<equiv> s_txt (span x)\<close>
  shows \<open>tok x = IntL \<Longrightarrow>
           read_num u = Some (NInt (fst (int_of_lexeme u)) (snd (int_of_lexeme u)), []) \<and>
           in_range (snd (int_of_lexeme u)) (fst (int_of_lexeme u))\<close>
    and \<open>tok x = FloatL \<Longrightarrow> read_num u = Some (NFloat, [])\<close>
    and \<open>tok x = StrL \<or> tok x = StrI \<Longrightarrow>
           read_str (tl u) = Some (str_pieces u, []) \<and> (tok x = StrI \<longleftrightarrow> has_hole (str_pieces u))\<close>
    and \<open>tok x = CharL \<Longrightarrow> read_char (tl u) = Some (char_value u, [])\<close>
proof -
  from caraml_lex_sound[OF assms(1)] obtain tail where
    \<open>lexed_body lex_init (advance_line 0 (consumed header)) (advance_col 0 (consumed header))
       (length (consumed header)) tail body\<close>
    by (auto elim: lexed.cases)
  from lexed_body_tokens[OF this assms(2)] obtain st' tail' where
    tok: \<open>TOKEN(st', u, tail') \<leadsto> tok x\<close>
    by (auto simp: u_def)
  show \<open>tok x = IntL \<Longrightarrow>
          read_num u = Some (NInt (fst (int_of_lexeme u)) (snd (int_of_lexeme u)), []) \<and>
          in_range (snd (int_of_lexeme u)) (fst (int_of_lexeme u))\<close>
  proof -
    assume \<open>tok x = IntL\<close>
    with tok obtain v sfx where \<open>read_num (u @ tail') = Some (NInt v sfx, tail')\<close> \<open>in_range sfx v\<close>
      by (cases rule: match_token.cases)
         (auto dest: table_toks(1-3) simp: table_toks(4) split: if_splits)
    then show ?thesis by (auto simp: int_of_lexeme_def dest!: read_num_lexeme)
  qed
  show \<open>tok x = FloatL \<Longrightarrow> read_num u = Some (NFloat, [])\<close>
  proof -
    assume \<open>tok x = FloatL\<close>
    with tok have \<open>read_num (u @ tail') = Some (NFloat, tail')\<close>
      by (cases rule: match_token.cases)
         (auto dest: table_toks(1-3) simp: table_toks(4) split: if_splits)
    then show ?thesis by (rule read_num_lexeme)
  qed
  show \<open>tok x = StrL \<or> tok x = StrI \<Longrightarrow>
          read_str (tl u) = Some (str_pieces u, []) \<and> (tok x = StrI \<longleftrightarrow> has_hole (str_pieces u))\<close>
  proof -
    assume \<open>tok x = StrL \<or> tok x = StrI\<close>
    with tok obtain cs ps where \<open>u = qt # cs\<close> \<open>read_str (cs @ tail') = Some (ps, tail')\<close>
      \<open>tok x = (if has_hole ps then StrI else StrL)\<close>
      by (cases rule: match_token.cases)
         (auto dest: table_toks(1-3) simp: table_toks(4) split: if_splits)
    then show ?thesis by (auto simp: str_pieces_def dest!: read_str_lexeme)
  qed
  show \<open>tok x = CharL \<Longrightarrow> read_char (tl u) = Some (char_value u, [])\<close>
  proof -
    assume \<open>tok x = CharL\<close>
    with tok obtain cs c where \<open>u = cq # cs\<close> \<open>read_char (cs @ tail') = Some (c, tail')\<close>
      by (cases rule: match_token.cases)
         (auto dest: table_toks(1-3) simp: table_toks(4) split: if_splits)
    then show ?thesis by (auto simp: char_value_def dest!: read_char_lexeme)
  qed
qed

end
