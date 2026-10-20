theory Trivia_Correct
  imports Trivia
begin

section \<open>Correctness of the trivia scanner\<close>

text \<open>\<^const>\<open>lex_trivia\<close> computes the \<^const>\<open>strip_trivia\<close> relation: each
  scanner step is the longest trivia match, which the per-kind lemmas of the
  first subsection establish, and the scanner never fails.\<close>

subsection \<open>Longest-match specifications of the scanners\<close>

lemma is_whitespace_not_dash: \<open>is_whitespace c \<Longrightarrow> c \<noteq> dash\<close>
  by (auto simp: is_whitespace_def)

lemma is_whitespace_not_curlyo: \<open>is_whitespace c \<Longrightarrow> c \<noteq> curlyo\<close>
  by (auto simp: is_whitespace_def)

lemma takeWhile_prefix_iff:
  \<open>prefix u xs \<Longrightarrow> list_all P u \<Longrightarrow> length u \<le> length (takeWhile P xs)\<close>
  by (induction u arbitrary: xs) (auto simp: prefix_def)

lemma longest_trivia_whitespace:
  assumes wsp: \<open>is_whitespace c\<close>
  shows \<open>longest_ctx match_trivia (c # cs) =
         Some (Space, c # takeWhile is_whitespace cs)\<close>
proof -
  let ?u = \<open>c # takeWhile is_whitespace cs\<close>
  have Space: \<open>(Space, ?u) \<in> trivia (c # cs)\<close>
    using wsp
    by (auto simp: trivia_def list_all_iff dest: set_takeWhileD
             intro!: match_ctxI[where tail = \<open>dropWhile is_whitespace cs\<close>] match_trivia.Space)

  have \<open>\<forall>y \<in> trivia (c # cs). length (snd y) \<le> length (snd (Space, ?u))\<close>
  proof (intro ballI)
    fix y assume \<open>y \<in> trivia (c # cs)\<close>
    then obtain t u where y: \<open>y = (t, u)\<close> by (cases y)
    with \<open>y \<in> trivia (c # cs)\<close> obtain tail where
      s_eq: \<open>c # cs = u @ tail\<close> and mt: \<open>match_trivia u tail t\<close>
      by (auto simp: trivia_def elim: match_ctxE)
    have pfx: \<open>prefix u (c # cs)\<close> using s_eq by (auto simp: prefix_def)

    from mt show \<open>length (snd y) \<le> length (snd (Space, ?u))\<close>
    proof (cases rule: match_trivia.cases)
      case Space
      then obtain u' where u: \<open>u = c # u'\<close>
        using pfx wsp by (cases u) (auto simp: prefix_def)
      with Space have \<open>prefix u' cs\<close> \<open>list_all is_whitespace u'\<close>
        using pfx by (auto simp: prefix_def)
      from takeWhile_prefix_iff[OF this] show ?thesis
        by (simp add: u y)
    next
      case (Line n)
      with pfx wsp is_whitespace_not_dash show ?thesis
        by (cases u) (auto simp: prefix_def split: if_splits)
    next
      case Block
      with pfx wsp is_whitespace_not_curlyo show ?thesis
        by (auto simp: prefix_def Cons_eq_append_conv)
    qed
  qed

  with Space show ?thesis
    by (simp add: longest_ctx_trivia_Some_iff)
qed

lemma is_symchar_dash: \<open>is_symchar dash\<close>
  by (simp add: is_symchar_def)

lemma dash_not_newline: \<open>\<not> is_newline dash\<close>
  by (simp add: is_newline_def)

lemma longest_trivia_line:
  assumes cc: \<open>[c\<^sub>1, c\<^sub>2] = cp ''--''\<close>
      and u_def: \<open>u = takeWhile ((=) dash) cs\<close>
      and after_def: \<open>after = drop (length u) cs\<close>
      and body_def: \<open>body = takeWhile (\<lambda>c. \<not> is_newline c) after\<close>
      and cnd: \<open>after = [] \<or> \<not> is_symchar (hd after)\<close>
  shows \<open>longest_ctx match_trivia (c\<^sub>1 # c\<^sub>2 # cs) =
         Some (LineComment, c\<^sub>1 # c\<^sub>2 # u @ body)\<close>
proof -
  from cc have cc: \<open>c\<^sub>1 = dash\<close> \<open>c\<^sub>2 = dash\<close> by auto

  have cs_eq: \<open>cs = u @ after\<close>
    using u_def after_def by (metis append_take_drop_id takeWhile_eq_take)

  have u_dashes: \<open>\<forall>d \<in> set u. d = dash\<close>
    using u_def by (auto dest: set_takeWhileD)

  have u_no_nl: \<open>\<forall>c \<in> set u. \<not> is_newline c\<close>
    using u_dashes dash_not_newline by metis

  have body_no_nl: \<open>\<forall>c \<in> set body. \<not> is_newline c\<close>
    using body_def by (auto dest: set_takeWhileD)

  have hd_body_eq: \<open>body \<noteq> [] \<Longrightarrow> hd body = hd after\<close>
    by (metis body_def hd_append2 takeWhile_dropWhile_id)

  have body_after_ne: \<open>body \<noteq> [] \<Longrightarrow> after \<noteq> []\<close>
    by (auto simp: body_def)

  have body_head_not_dash: \<open>body \<noteq> [] \<Longrightarrow> hd body \<noteq> dash\<close>
    using cnd hd_body_eq body_after_ne is_symchar_dash
    by auto

  have tw_dash_ubody: \<open>takeWhile (\<lambda>c. c = dash) (u @ body) = u\<close>
    using u_dashes body_head_not_dash
    by (cases body) simp_all

  have tw_nl_cs: \<open>takeWhile (\<lambda>c. \<not> is_newline c) cs = u @ body\<close>
    using cs_eq u_no_nl body_def by simp

  have body_tail_eq: \<open>c\<^sub>1 # c\<^sub>2 # cs = (c\<^sub>1 # c\<^sub>2 # u @ body) @ drop (length body) after\<close>
    using cs_eq body_def by (metis append_Cons append_assoc append_take_drop_id takeWhile_eq_take)

  have tail_ok: \<open>drop (length body) after = [] \<or> \<not> is_symchar (hd (drop (length body) after))\<close>
  proof -
    have eq: \<open>drop (length body) after = dropWhile (\<lambda>c. \<not> is_newline c) after\<close>
      by (simp add: body_def dropWhile_eq_drop)
    show ?thesis
      unfolding eq
    proof (cases \<open>dropWhile (\<lambda>c. \<not> is_newline c) after\<close>)
      case (Cons a as)
      with hd_dropWhile[of \<open>\<lambda>c. \<not> is_newline c\<close> after] have \<open>is_newline a\<close> by auto
      with Cons show
        \<open>dropWhile (\<lambda>c. \<not> is_newline c) after = [] \<or>
         \<not> is_symchar (hd (dropWhile (\<lambda>c. \<not> is_newline c) after)) \<close>
        by (auto simp: is_newline_def is_symchar_def)
    qed simp
  qed

  have LineComment: \<open>(LineComment, c\<^sub>1 # c\<^sub>2 # u @ body) \<in> trivia (c\<^sub>1 # c\<^sub>2 # cs)\<close>
    unfolding trivia_def
  proof (intro match_ctxI[where tail = \<open>drop (length body) after\<close>])
    show \<open>c\<^sub>1 # c\<^sub>2 # cs = (c\<^sub>1 # c\<^sub>2 # u @ body) @ drop (length body) after\<close>
      by (rule body_tail_eq)
    show \<open>match_trivia (c\<^sub>1 # c\<^sub>2 # u @ body) (drop (length body) after) LineComment\<close>
    proof (rule match_trivia.Line[of \<open>2 + length u\<close>])
      show \<open>2 + length u = length (takeWhile (\<lambda>c. c = dash) (c\<^sub>1 # c\<^sub>2 # u @ body))\<close>
        using cc tw_dash_ubody by simp
      show \<open>2 \<le> 2 + length u\<close> by simp
      show \<open>drop (2 + length u) (c\<^sub>1 # c\<^sub>2 # u @ body) = [] \<or>
             \<not> is_symchar (hd (drop (2 + length u) (c\<^sub>1 # c\<^sub>2 # u @ body)))\<close>
        using cnd hd_body_eq body_after_ne
        by (cases \<open>body = []\<close>) auto
      show \<open>list_all (Not \<circ> is_newline) (c\<^sub>1 # c\<^sub>2 # u @ body)\<close>
        using cc u_no_nl body_no_nl dash_not_newline
        by (auto simp: list_all_iff)
      show \<open>drop (length body) after = [] \<or> \<not> is_symchar (hd (drop (length body) after))\<close>
        by (rule tail_ok)
    qed
  qed

  have \<open>\<And>y. y \<in> trivia (c\<^sub>1 # c\<^sub>2 # cs) \<Longrightarrow> length (snd y) \<le> length (c\<^sub>1 # c\<^sub>2 # u @ body)\<close>
  proof -
    fix y assume \<open>y \<in> trivia (c\<^sub>1 # c\<^sub>2 # cs)\<close>
    then obtain t v where y: \<open>y = (t, v)\<close> by (cases y)
    with \<open>y \<in> trivia (c\<^sub>1 # c\<^sub>2 # cs)\<close> obtain vtail where
      s_eq: \<open>c\<^sub>1 # c\<^sub>2 # cs = v @ vtail\<close> and mt: \<open>match_trivia v vtail t\<close>
      by (auto simp: trivia_def elim: match_ctxE)
    have pfx: \<open>prefix v (c\<^sub>1 # c\<^sub>2 # cs)\<close> using s_eq by (auto simp: prefix_def)
    with mt show \<open>length (snd y) \<le> length (c\<^sub>1 # c\<^sub>2 # u @ body)\<close>
    proof (cases rule: match_trivia.cases)
      case (Line n)
      then have \<open>length v \<le> length (takeWhile (\<lambda>c. \<not> is_newline c) (c\<^sub>1 # c\<^sub>2 # cs))\<close>
        by (intro takeWhile_prefix_iff[OF pfx])
           (auto simp: list_all_iff cc dash_not_newline tw_nl_cs)
      with dash_not_newline show ?thesis
        by (simp add: y cc tw_nl_cs)
    qed (fastforce intro: pfx dest: is_whitespace_not_dash simp: cc list_all_Cons_iff prefix_Cons)+
  qed

  with LineComment show ?thesis
    by (simp add: longest_ctx_trivia_Some_iff)
qed

text \<open>Two invariants tie the executable block-comment scanner to the
  specification. \<^text>\<open>lex_block_cmt_body\<close> reads a successful scan back as a
  \<^const>\<open>comment_body\<close>-shaped prefix; \<^text>\<open>lex_block_cmt_body_max\<close> says the
  scanner picks the shortest \<^const>\<open>comment_body\<close> that closes the delimiter,
  which is the one that bounds the maximality obligation of
  \<^text>\<open>longest_trivia_block\<close>. The concatenation fact
  \<^text>\<open>lex_block_cmt_consumed\<close> below is the elementary building block: the
  scanner splits its input into the chars it walked past and the residual.\<close>

lemma lex_block_cmt_consumed:
  \<open>lex_block_cmt k acc cs = Some (tail, rest)
     \<Longrightarrow> \<exists>consumed. tail = rev acc @ consumed \<and> cs = consumed @ rest\<close>
proof (induction k acc cs arbitrary: tail rest rule: lex_block_cmt.induct)
  case (1 k acc c\<^sub>1 c\<^sub>2 cs)
  show ?case
  proof (cases \<open>[c\<^sub>1, c\<^sub>2] = cp ''{-''\<close>)
    case True
    with 1(4) have step: \<open>lex_block_cmt (k+1) (c\<^sub>2 # c\<^sub>1 # acc) cs = Some (tail, rest)\<close>
      by simp
    from 1(1)[OF True step] obtain c' where
      t: \<open>tail = rev (c\<^sub>2 # c\<^sub>1 # acc) @ c'\<close> and
      s: \<open>cs = c' @ rest\<close> by blast
    from t have \<open>tail = rev acc @ [c\<^sub>1, c\<^sub>2] @ c'\<close> by simp
    moreover from s have \<open>c\<^sub>1 # c\<^sub>2 # cs = ([c\<^sub>1, c\<^sub>2] @ c') @ rest\<close> by simp
    ultimately show ?thesis by blast
  next
    case not_open: False
    show ?thesis
    proof (cases \<open>[c\<^sub>1, c\<^sub>2] = cp ''-}''\<close>)
      case True
      show ?thesis
      proof (cases \<open>k = 1\<close>)
        case True2: True
        with True not_open 1(4)
        have \<open>tail = rev acc @ [c\<^sub>1, c\<^sub>2]\<close> \<open>rest = cs\<close> by auto
        thus ?thesis by (rule_tac x=\<open>[c\<^sub>1, c\<^sub>2]\<close> in exI) simp
      next
        case False2: False
        with True not_open 1(4)
        have step: \<open>lex_block_cmt (k-1) (c\<^sub>2 # c\<^sub>1 # acc) cs = Some (tail, rest)\<close>
          by simp
        from 1(2)[OF not_open True False2 step] obtain c' where
          t: \<open>tail = rev (c\<^sub>2 # c\<^sub>1 # acc) @ c'\<close> and
          s: \<open>cs = c' @ rest\<close> by blast
        from t have \<open>tail = rev acc @ [c\<^sub>1, c\<^sub>2] @ c'\<close> by simp
        moreover from s have \<open>c\<^sub>1 # c\<^sub>2 # cs = ([c\<^sub>1, c\<^sub>2] @ c') @ rest\<close> by simp
        ultimately show ?thesis by blast
      qed
    next
      case not_close: False
      have step: \<open>lex_block_cmt k (c\<^sub>1 # acc) (c\<^sub>2 # cs) = Some (tail, rest)\<close>
        using not_open not_close 1(4) by fastforce
      from 1(3)[OF not_open not_close step] obtain c' where
        t: \<open>tail = rev (c\<^sub>1 # acc) @ c'\<close> and
        s: \<open>c\<^sub>2 # cs = c' @ rest\<close> by blast
      from t have \<open>tail = rev acc @ [c\<^sub>1] @ c'\<close> by simp
      moreover from s have \<open>c\<^sub>1 # c\<^sub>2 # cs = ([c\<^sub>1] @ c') @ rest\<close> by simp
      ultimately show ?thesis by blast
    qed
  qed
qed auto

primrec depth_body :: \<open>nat \<Rightarrow> ustring \<Rightarrow> bool\<close> where
  \<open>depth_body 0 xs \<longleftrightarrow> (\<exists>b. xs = b @ cp ''-}'' \<and> comment_body b)\<close>
| \<open>depth_body (Suc n) xs \<longleftrightarrow>
     (\<exists>b ys. xs = b @ cp ''-}'' @ ys \<and> comment_body b \<and> depth_body n ys)\<close>

lemma lex_block_cmt_body_gen:
  \<open>lex_block_cmt K acc cs = Some (tail, rest) \<Longrightarrow> K = Suc n
     \<Longrightarrow> \<exists>consumed. tail = rev acc @ consumed
                  \<and> cs = consumed @ rest
                  \<and> depth_body n consumed\<close>
proof (induction K acc cs arbitrary: n tail rest rule: lex_block_cmt.induct)
  case (1 K acc c\<^sub>1 c\<^sub>2 cs)
  from \<open>K = Suc n\<close> have K_eq: \<open>K = Suc n\<close> .
  show ?case
  proof (cases \<open>[c\<^sub>1, c\<^sub>2] = cp ''{-''\<close>)
    case True
    with 1(4) have step: \<open>lex_block_cmt (K + 1) (c\<^sub>2 # c\<^sub>1 # acc) cs = Some (tail, rest)\<close>
      by simp
    have K1: \<open>K + 1 = Suc (Suc n)\<close> using K_eq by simp
    from 1(1)[OF True step K1] obtain consumed' where
      t: \<open>tail = rev (c\<^sub>2 # c\<^sub>1 # acc) @ consumed'\<close>
      and s: \<open>cs = consumed' @ rest\<close>
      and db: \<open>depth_body (Suc n) consumed'\<close> by blast
    from db obtain b\<^sub>1 ys where
      c'_eq: \<open>consumed' = b\<^sub>1 @ cp ''-}'' @ ys\<close>
      and cb\<^sub>1: \<open>comment_body b\<^sub>1\<close>
      and db_ys: \<open>depth_body n ys\<close> by auto
    let ?new = \<open>[c\<^sub>1, c\<^sub>2] @ consumed'\<close>
    show ?thesis
    proof (cases n)
      case 0
      from db_ys 0 obtain b\<^sub>2 where
        ys_eq: \<open>ys = b\<^sub>2 @ cp ''-}''\<close> and cb\<^sub>2: \<open>comment_body b\<^sub>2\<close> by auto
      let ?M = \<open>cp ''{-'' @ b\<^sub>1 @ cp ''-}'' @ b\<^sub>2\<close>
      have merged: \<open>?new = ?M @ cp ''-}''\<close> using True c'_eq ys_eq by simp
      have cb: \<open>comment_body ?M\<close> by (rule comment_body.Nest[OF cb\<^sub>1 cb\<^sub>2])
      from merged cb have \<open>depth_body 0 ?new\<close> by auto
      with 0 t s True show ?thesis by (rule_tac x = ?new in exI) simp
    next
      case (Suc j)
      from db_ys Suc obtain b\<^sub>2 ys' where
        ys_eq: \<open>ys = b\<^sub>2 @ cp ''-}'' @ ys'\<close>
        and cb\<^sub>2: \<open>comment_body b\<^sub>2\<close>
        and db': \<open>depth_body j ys'\<close> by auto
      let ?M = \<open>cp ''{-'' @ b\<^sub>1 @ cp ''-}'' @ b\<^sub>2\<close>
      have merged: \<open>?new = ?M @ cp ''-}'' @ ys'\<close> using True c'_eq ys_eq by simp
      have cb: \<open>comment_body ?M\<close> by (rule comment_body.Nest[OF cb\<^sub>1 cb\<^sub>2])
      from merged cb db' have \<open>depth_body (Suc j) ?new\<close>
        by (simp only: depth_body.simps(2)) blast
      with Suc t s True show ?thesis by (rule_tac x = ?new in exI) simp
    qed
  next
    case not_open: False
    show ?thesis
    proof (cases \<open>[c\<^sub>1, c\<^sub>2] = cp ''-}''\<close>)
      case is_close: True
      show ?thesis
      proof (cases \<open>K = 1\<close>)
        case True
        with is_close not_open 1(4) K_eq
        have tail_val: \<open>tail = rev acc @ [c\<^sub>1, c\<^sub>2]\<close> and rest_val: \<open>rest = cs\<close>
             and n0: \<open>n = 0\<close> by auto
        have \<open>depth_body 0 [c\<^sub>1, c\<^sub>2]\<close>
          using is_close comment_body.Nil by auto
        with tail_val rest_val n0 show ?thesis
          by (rule_tac x = \<open>[c\<^sub>1, c\<^sub>2]\<close> in exI) simp
      next
        case False
        with is_close not_open 1(4)
        have step: \<open>lex_block_cmt (K - 1) (c\<^sub>2 # c\<^sub>1 # acc) cs = Some (tail, rest)\<close>
          by simp
        from K_eq False obtain j where n_eq: \<open>n = Suc j\<close> by (cases n) auto
        with K_eq have K1: \<open>K - 1 = Suc j\<close> by simp
        from 1(2)[OF not_open is_close False step K1] obtain consumed' where
          t: \<open>tail = rev (c\<^sub>2 # c\<^sub>1 # acc) @ consumed'\<close>
          and s: \<open>cs = consumed' @ rest\<close>
          and db: \<open>depth_body j consumed'\<close> by blast
        have merged: \<open>[c\<^sub>1, c\<^sub>2] @ consumed' = [] @ cp ''-}'' @ consumed'\<close>
          using is_close by simp
        with db comment_body.Nil n_eq
        have \<open>depth_body n ([c\<^sub>1, c\<^sub>2] @ consumed')\<close> by auto
        with t s is_close show ?thesis
          by (rule_tac x = \<open>[c\<^sub>1, c\<^sub>2] @ consumed'\<close> in exI) simp
      qed
    next
      case not_close: False
      have step: \<open>lex_block_cmt K (c\<^sub>1 # acc) (c\<^sub>2 # cs) = Some (tail, rest)\<close>
        using not_open not_close 1(4) by auto
      from 1(3)[OF not_open not_close step K_eq] obtain consumed' where
        t: \<open>tail = rev (c\<^sub>1 # acc) @ consumed'\<close>
        and s: \<open>c\<^sub>2 # cs = consumed' @ rest\<close>
        and db: \<open>depth_body n consumed'\<close> by blast
      \<comment>\<open>Extract the first comment-body segment of \<open>consumed'\<close>, common shape
        across the two \<open>depth_body\<close> constructors.\<close>
      obtain b tl where
        c'_eq: \<open>consumed' = b @ cp ''-}'' @ tl\<close>
        and cb: \<open>comment_body b\<close>
        and tl_ok: \<open>tl = [] \<and> n = 0 \<or> (\<exists>j. n = Suc j \<and> depth_body j tl)\<close>
      proof (cases n)
        case 0
        with db obtain b where \<open>consumed' = b @ cp ''-}''\<close> \<open>comment_body b\<close> by auto
        thus ?thesis using 0 by (auto intro: that[of b \<open>[]\<close>])
      next
        case (Suc j)
        with db obtain b tl where
          \<open>consumed' = b @ cp ''-}'' @ tl\<close> \<open>comment_body b\<close> \<open>depth_body j tl\<close> by auto
        thus ?thesis using Suc by (auto intro: that[of b tl])
      qed
      have not_delim: \<open>\<not> comment_delim (c\<^sub>1 # b)\<close>
      proof (cases b)
        case Nil
        thus ?thesis by (auto simp: prefix_def)
      next
        case (Cons a as)
        have \<open>c\<^sub>2 = a\<close>
          using s c'_eq Cons by simp
        with Cons not_open not_close show ?thesis
          by (auto simp: prefix_def)
      qed
      have not_final: \<open>\<not> (c\<^sub>1 = curlyo \<and> b = [])\<close>
      proof (rule notI, elim conjE)
        assume \<open>c\<^sub>1 = curlyo\<close> and b_nil: \<open>b = []\<close>
        from b_nil c'_eq s have \<open>c\<^sub>2 = dash\<close> by simp
        with \<open>c\<^sub>1 = curlyo\<close> have \<open>[c\<^sub>1, c\<^sub>2] = cp ''{-''\<close> by simp
        with not_open show False by simp
      qed
      have cb_new: \<open>comment_body ([c\<^sub>1] @ b)\<close>
        using cb not_delim not_final by (auto intro: comment_body.Chr)
      have new_eq: \<open>[c\<^sub>1] @ consumed' = ([c\<^sub>1] @ b) @ cp ''-}'' @ tl\<close>
        using c'_eq by simp
      have \<open>depth_body n ([c\<^sub>1] @ consumed')\<close>
      proof (cases n)
        case 0
        with tl_ok have \<open>tl = []\<close> by auto
        with new_eq cb_new 0 show ?thesis by auto
      next
        case (Suc j)
        with tl_ok have db_tl: \<open>depth_body j tl\<close> by auto
        have \<open>depth_body (Suc j) ([c\<^sub>1] @ consumed')\<close>
          using new_eq cb_new db_tl by (simp only: depth_body.simps(2)) blast
        with Suc show ?thesis by simp
      qed
      with t s show ?thesis
        by (rule_tac x = \<open>[c\<^sub>1] @ consumed'\<close> in exI) simp
    qed
  qed
qed auto

lemma lex_block_cmt_body:
  assumes \<open>lex_block_cmt 1 [] cs = Some (tail, rest)\<close>
  obtains b where
    \<open>comment_body b\<close>
    \<open>tail = b @ cp ''-}''\<close>
    \<open>cs = b @ cp ''-}'' @ rest\<close>
proof -
  from lex_block_cmt_body_gen[OF assms, of 0]
  obtain consumed where
    \<open>tail = consumed\<close>
    \<open>cs = consumed @ rest\<close>
    \<open>depth_body 0 consumed\<close> by auto
  then obtain b where
    \<open>consumed = b @ cp ''-}''\<close>
    \<open>comment_body b\<close> by auto
  thus thesis using \<open>tail = consumed\<close> \<open>cs = consumed @ rest\<close>
    by (auto intro: that)
qed

lemma lex_block_cmt_shift_eq:
  \<open>lex_block_cmt k acc cs =
     (case lex_block_cmt k [] cs of None \<Rightarrow> None
      | Some (t, r) \<Rightarrow> Some (rev acc @ t, r))\<close>
proof (induction \<open>length cs\<close> arbitrary: k acc cs rule: less_induct)
  case less
  show ?case
  proof (cases cs)
    case Nil thus ?thesis by simp
  next
    case (Cons c\<^sub>1 cs\<^sub>1)
    show ?thesis
    proof (cases cs\<^sub>1)
      case Nil
      with Cons show ?thesis by simp
    next
      case (Cons c\<^sub>2 cs\<^sub>2)
      have cs_eq: \<open>cs = c\<^sub>1 # c\<^sub>2 # cs\<^sub>2\<close> using \<open>cs = c\<^sub>1 # cs\<^sub>1\<close> Cons by simp
      hence len_lt: \<open>length cs\<^sub>2 < length cs\<close> by simp
      show ?thesis
      proof (cases \<open>[c\<^sub>1, c\<^sub>2] = cp ''{-''\<close>)
        case True
        have L: \<open>lex_block_cmt k acc cs =
                 (case lex_block_cmt (k+1) [] cs\<^sub>2 of None \<Rightarrow> None
                  | Some (t, r) \<Rightarrow> Some (rev (c\<^sub>2 # c\<^sub>1 # acc) @ t, r))\<close>
          using True cs_eq less.hyps[OF len_lt, of \<open>k+1\<close> \<open>c\<^sub>2 # c\<^sub>1 # acc\<close>] by simp
        have R: \<open>lex_block_cmt k [] cs =
                 (case lex_block_cmt (k+1) [] cs\<^sub>2 of None \<Rightarrow> None
                  | Some (t, r) \<Rightarrow> Some (rev [c\<^sub>2, c\<^sub>1] @ t, r))\<close>
          using True cs_eq less.hyps[OF len_lt, of \<open>k+1\<close> \<open>[c\<^sub>2, c\<^sub>1]\<close>] by simp
        show ?thesis using L R by (auto split: option.split)
      next
        case not_open: False
        show ?thesis
        proof (cases \<open>[c\<^sub>1, c\<^sub>2] = cp ''-}''\<close>)
          case is_close: True
          show ?thesis
          proof (cases \<open>k = 1\<close>)
            case True
            show ?thesis
              using is_close True not_open cs_eq by simp
          next
            case False
            have L: \<open>lex_block_cmt k acc cs =
                     (case lex_block_cmt (k-1) [] cs\<^sub>2 of None \<Rightarrow> None
                      | Some (t, r) \<Rightarrow> Some (rev (c\<^sub>2 # c\<^sub>1 # acc) @ t, r))\<close>
              using is_close False not_open cs_eq
                    less.hyps[OF len_lt, of \<open>k-1\<close> \<open>c\<^sub>2 # c\<^sub>1 # acc\<close>] by simp
            have R: \<open>lex_block_cmt k [] cs =
                     (case lex_block_cmt (k-1) [] cs\<^sub>2 of None \<Rightarrow> None
                      | Some (t, r) \<Rightarrow> Some (rev [c\<^sub>2, c\<^sub>1] @ t, r))\<close>
              using is_close False not_open cs_eq
                    less.hyps[OF len_lt, of \<open>k-1\<close> \<open>[c\<^sub>2, c\<^sub>1]\<close>] by simp
            show ?thesis using L R by (auto split: option.split)
          qed
        next
          case not_close: False
          have len_lt': \<open>length (c\<^sub>2 # cs\<^sub>2) < length cs\<close> by (simp add: cs_eq)
          have L: \<open>lex_block_cmt k acc cs =
                   (case lex_block_cmt k [] (c\<^sub>2 # cs\<^sub>2) of None \<Rightarrow> None
                    | Some (t, r) \<Rightarrow> Some (rev (c\<^sub>1 # acc) @ t, r))\<close>
            using not_open not_close cs_eq
                  less.hyps[OF len_lt', of k \<open>c\<^sub>1 # acc\<close>] by fastforce
          have R: \<open>lex_block_cmt k [] cs =
                   (case lex_block_cmt k [] (c\<^sub>2 # cs\<^sub>2) of None \<Rightarrow> None
                    | Some (t, r) \<Rightarrow> Some (rev [c\<^sub>1] @ t, r))\<close>
            using not_open not_close cs_eq
                  less.hyps[OF len_lt', of k \<open>[c\<^sub>1]\<close>] by fastforce
          show ?thesis using L R by (auto split: option.split)
        qed
      qed
    qed
  qed
qed

lemma lex_block_cmt_acc_shift:
  assumes \<open>lex_block_cmt k acc cs = Some (tail, rest)\<close>
  shows \<open>\<exists>tail\<^sub>0. tail = rev acc @ tail\<^sub>0 \<and> lex_block_cmt k [] cs = Some (tail\<^sub>0, rest)\<close>
  using lex_block_cmt_shift_eq[of k acc cs] assms
  by (auto split: option.splits)

lemma lex_block_cmt_step:
  assumes \<open>comment_body b\<close>
  shows \<open>lex_block_cmt (Suc (Suc k)) acc (b @ cp ''-}'' @ rest)
           = lex_block_cmt (Suc k) (rev (b @ cp ''-}'') @ acc) rest\<close>
  using assms
proof (induction b arbitrary: k acc rest rule: comment_body.induct)
  case Nil
  show ?case by simp
next
  case (Chr c cs\<^sub>b)
  from Chr.hyps have not_delim: \<open>\<not> comment_delim (c # cs\<^sub>b)\<close>
                and not_final: \<open>\<not> (c = curlyo \<and> cs\<^sub>b = [])\<close> by simp_all
  show ?case
  proof (cases cs\<^sub>b)
    case Nil
    with not_final have c_ne: \<open>c \<noteq> curlyo\<close> by simp
    hence not_open: \<open>[c, dash] \<noteq> cp ''{-''\<close> by simp
    have not_close: \<open>[c, dash] \<noteq> cp ''-}''\<close> by simp
    from Nil not_open not_close
    have \<open>lex_block_cmt (Suc (Suc k)) acc ((c # cs\<^sub>b) @ cp ''-}'' @ rest)
            = lex_block_cmt (Suc (Suc k)) (c # acc) (cp ''-}'' @ rest)\<close>
      by simp
    also have \<open>\<dots> = lex_block_cmt (Suc k) ([curlyc, dash, c] @ acc) rest\<close>
      by simp
    finally show ?thesis using Nil by simp
  next
    case (Cons c\<^sub>b cs\<^sub>b')
    with not_delim have not_open: \<open>[c, c\<^sub>b] \<noteq> cp ''{-''\<close>
                    and not_close: \<open>[c, c\<^sub>b] \<noteq> cp ''-}''\<close>
      by (auto simp: prefix_def)
    from Cons not_open not_close
    have \<open>lex_block_cmt (Suc (Suc k)) acc ((c # cs\<^sub>b) @ cp ''-}'' @ rest)
            = lex_block_cmt (Suc (Suc k)) (c # acc) (cs\<^sub>b @ cp ''-}'' @ rest)\<close>
      by fastforce
    also from Chr.IH
    have \<open>\<dots> = lex_block_cmt (Suc k) (rev (cs\<^sub>b @ cp ''-}'') @ (c # acc)) rest\<close>
      by simp
    finally show ?thesis by fastforce
  qed
next
  case (Nest inner tail\<^sub>b)
  have \<open>lex_block_cmt (Suc (Suc k)) acc
            ((cp ''{-'' @ inner @ cp ''-}'' @ tail\<^sub>b) @ cp ''-}'' @ rest)
          = lex_block_cmt (Suc (Suc (Suc k))) ([dash, curlyo] @ acc)
              (inner @ cp ''-}'' @ tail\<^sub>b @ cp ''-}'' @ rest)\<close>
    by simp
  also from Nest.IH(1)
  have \<open>\<dots> = lex_block_cmt (Suc (Suc k))
                (rev (inner @ cp ''-}'') @ [dash, curlyo] @ acc)
                (tail\<^sub>b @ cp ''-}'' @ rest)\<close>
    by simp
  also from Nest.IH(2)
  have \<open>\<dots> = lex_block_cmt (Suc k)
                (rev (tail\<^sub>b @ cp ''-}'') @ rev (inner @ cp ''-}'') @
                 [dash, curlyo] @ acc) rest\<close>
    by simp
  also have \<open>\<dots> = lex_block_cmt (Suc k)
                    (rev ((cp ''{-'' @ inner @ cp ''-}'' @ tail\<^sub>b) @ cp ''-}'') @ acc)
                    rest\<close>
    by simp
  finally show ?case .
qed

lemma lex_block_cmt_body_max:
  assumes \<open>lex_block_cmt 1 [] cs = Some (tail, rest)\<close>
      and \<open>comment_body b'\<close>
      and \<open>cs = b' @ cp ''-}'' @ rest'\<close>
  shows \<open>length b' + 2 \<le> length tail\<close>
  using assms(2,3,1)
proof (induction b' arbitrary: cs tail rest rest' rule: comment_body.induct)
  case Nil
  from Nil have cs_eq: \<open>cs = cp ''-}'' @ rest'\<close> by simp
  have step: \<open>lex_block_cmt 1 [] cs = Some (cp ''-}'', rest')\<close>
    by (simp add: cs_eq)
  with Nil.prems(2) have \<open>tail = cp ''-}''\<close> \<open>rest = rest'\<close> by auto
  thus ?case by simp
next
  case (Chr c cs\<^sub>b)
  from Chr.hyps(1) have not_delim: \<open>\<not> comment_delim (c # cs\<^sub>b)\<close> .
  from Chr.prems(1) have cs_eq: \<open>cs = c # cs\<^sub>b @ cp ''-}'' @ rest'\<close> by simp
  show ?case
  proof (cases cs\<^sub>b)
    case Nil
    with cs_eq have cs_short: \<open>cs = c # cp ''-}'' @ rest'\<close> by simp
    show ?thesis
    proof (cases \<open>c = curlyo\<close>)
      case True
      \<comment>\<open>\<open>c = curlyo\<close>: scanner sees \<^text>\<open>{-\<close> and opens; the emitted tail
        must therefore extend past the initial \<^text>\<open>{-\<close>. If \<open>|tail| \<le> 2\<close>
        then \<^text>\<open>lex_block_cmt_body\<close> forces \<open>tail = cp ''-}''\<close>, so \<open>cs\<close>
        would have to start with \<open>dash\<close>, contradicting \<open>c = curlyo\<close>.\<close>
      from Chr.prems(2) cs_short have lex_full:
        \<open>lex_block_cmt 1 [] (c # cp ''-}'' @ rest') = Some (tail, rest)\<close> by simp
      have \<open>length tail \<ge> 3\<close>
      proof (rule ccontr)
        assume \<open>\<not> length tail \<ge> 3\<close>
        hence lt: \<open>length tail \<le> 2\<close> by simp
        obtain b where tail_eq: \<open>tail = b @ cp ''-}''\<close>
          and cs_eq_body: \<open>c # cp ''-}'' @ rest' = b @ cp ''-}'' @ rest\<close>
          by (rule lex_block_cmt_body[OF lex_full])
        from tail_eq lt have \<open>length b = 0\<close> by simp
        hence \<open>b = []\<close> by simp
        with cs_eq_body have \<open>c # cp ''-}'' @ rest' = cp ''-}'' @ rest\<close> by simp
        hence \<open>c = dash\<close> by simp
        with True show False by simp
      qed
      thus ?thesis by (simp add: Nil)
    next
      case False
      \<comment>\<open>\<open>c \<noteq> curlyo\<close>: the pair \<^text>\<open>[c, dash]\<close> is neither \<^text>\<open>{-\<close> nor
        \<^text>\<open>-}\<close> (the second character is \<open>dash\<close>, not \<open>curlyc\<close>). The
        scanner advances one step and immediately emits on the following
        \<^text>\<open>-}\<close>.\<close>
      have not_open: \<open>[c, dash] \<noteq> cp ''{-''\<close> using False by simp
      have not_close: \<open>[c, dash] \<noteq> cp ''-}''\<close> by simp
      have \<open>lex_block_cmt 1 [] (c # cp ''-}'' @ rest')
              = lex_block_cmt 1 [c] (cp ''-}'' @ rest')\<close>
        using not_open not_close by simp
      also have \<open>\<dots> = Some (rev [c] @ cp ''-}'', rest')\<close> by simp
      finally have \<open>lex_block_cmt 1 [] cs = Some ([c] @ cp ''-}'', rest')\<close>
        by (simp add: cs_short)
      with Chr.prems(2) have \<open>tail = [c] @ cp ''-}''\<close> by simp
      thus ?thesis by (simp add: Nil)
    qed
  next
    case (Cons c\<^sub>b\<^sub>1 cs\<^sub>b')
    with not_delim have \<open>[c, c\<^sub>b\<^sub>1] \<noteq> cp ''{-''\<close> \<open>[c, c\<^sub>b\<^sub>1] \<noteq> cp ''-}''\<close>
      by (auto simp: prefix_def)
    hence \<open>lex_block_cmt 1 [] cs
             = lex_block_cmt 1 [c] (cs\<^sub>b @ cp ''-}'' @ rest')\<close>
      using cs_eq Cons by fastforce
    with Chr.prems(2) have
      lex_shift: \<open>lex_block_cmt 1 [c] (cs\<^sub>b @ cp ''-}'' @ rest') = Some (tail, rest)\<close>
      by simp
    from lex_block_cmt_acc_shift[OF lex_shift] obtain tail\<^sub>0 where
      tail_eq: \<open>tail = rev [c] @ tail\<^sub>0\<close>
      and lex_0: \<open>lex_block_cmt 1 [] (cs\<^sub>b @ cp ''-}'' @ rest') = Some (tail\<^sub>0, rest)\<close>
      by blast
    from Chr.IH[of \<open>cs\<^sub>b @ cp ''-}'' @ rest'\<close> rest' tail\<^sub>0 rest] lex_0
    have \<open>length cs\<^sub>b + 2 \<le> length tail\<^sub>0\<close> by simp
    with tail_eq show ?thesis by simp
  qed
next
  case (Nest b\<^sub>i cs\<^sub>t)
  \<comment>\<open>Apply \<^text>\<open>lex_block_cmt_step\<close> on \<open>b\<^sub>i\<close> to peel the outer
    \<^text>\<open>{-\<close> and inner \<^text>\<open>-}\<close>, reducing the depth-2 scan to a
    depth-1 scan on \<open>cs\<^sub>t @ cp ''-}'' @ rest'\<close>; then \<^text>\<open>Nest.IH(2)\<close>
    bounds the resulting tail.\<close>
  from Nest.prems(1) have cs_eq:
    \<open>cs = cp ''{-'' @ b\<^sub>i @ cp ''-}'' @ cs\<^sub>t @ cp ''-}'' @ rest'\<close>
    by simp
  from Nest.prems(2) cs_eq have
    lex_open: \<open>lex_block_cmt 2 [dash, curlyo]
                 (b\<^sub>i @ cp ''-}'' @ cs\<^sub>t @ cp ''-}'' @ rest') = Some (tail, rest)\<close>
    by (simp add: Suc_1[unfolded One_nat_def])

  have step_eq:
    \<open>lex_block_cmt 2 [dash, curlyo] (b\<^sub>i @ cp ''-}'' @ cs\<^sub>t @ cp ''-}'' @ rest') =
     lex_block_cmt 1 (rev (b\<^sub>i @ cp ''-}'') @ [dash, curlyo]) (cs\<^sub>t @ cp ''-}'' @ rest')\<close>
    using lex_block_cmt_step[OF Nest.hyps(1),
                             of 0 \<open>[dash, curlyo]\<close> \<open>cs\<^sub>t @ cp ''-}'' @ rest'\<close>]
    by (simp add: numeral_2_eq_2)

  with lex_open have
    lex_shift: \<open>lex_block_cmt 1 (rev (b\<^sub>i @ cp ''-}'') @ [dash, curlyo])
                  (cs\<^sub>t @ cp ''-}'' @ rest') = Some (tail, rest)\<close>
    by presburger
  from lex_block_cmt_acc_shift[OF lex_shift] obtain tail\<^sub>0 where
    tail_eq: \<open>tail = rev (rev (b\<^sub>i @ cp ''-}'') @ [dash, curlyo]) @ tail\<^sub>0\<close>
    and lex_t: \<open>lex_block_cmt 1 [] (cs\<^sub>t @ cp ''-}'' @ rest') = Some (tail\<^sub>0, rest)\<close>
    by blast
  from Nest.IH(2)[of \<open>cs\<^sub>t @ cp ''-}'' @ rest'\<close> rest' tail\<^sub>0 rest] lex_t
  have t_bound: \<open>length cs\<^sub>t + 2 \<le> length tail\<^sub>0\<close> by simp
  have tail_len: \<open>length tail = length b\<^sub>i + 4 + length tail\<^sub>0\<close>
    using tail_eq by simp
  show ?case using t_bound tail_len by simp
qed

lemma longest_trivia_block:
  assumes cc: \<open>[c\<^sub>1, c\<^sub>2] = cp ''{-''\<close>
      and lex: \<open>lex_block_cmt 1 [] cs = Some (tail, rest)\<close>
  shows \<open>longest_ctx match_trivia (c\<^sub>1 # c\<^sub>2 # cs) =
         Some (BlockComment, cp ''{-'' @ tail)\<close>
proof -
  from lex obtain b where
    body_ok: \<open>comment_body b\<close>
    and tail_eq: \<open>tail = b @ cp ''-}''\<close>
    and cs_eq: \<open>cs = b @ cp ''-}'' @ rest\<close>
    by (rule lex_block_cmt_body)

  have c_eq: \<open>c\<^sub>1 = curlyo\<close> \<open>c\<^sub>2 = dash\<close> using cc by auto

  have v_eq: \<open>cp ''{-'' @ tail = cp ''{-'' @ b @ cp ''-}''\<close>
    using tail_eq by simp
  have concat_eq: \<open>c\<^sub>1 # c\<^sub>2 # cs = (cp ''{-'' @ tail) @ rest\<close>
  proof -
    have \<open>c\<^sub>1 # c\<^sub>2 # cs = curlyo # dash # b @ cp ''-}'' @ rest\<close>
      using cs_eq c_eq by simp
    also have \<open>\<dots> = (cp ''{-'') @ tail @ rest\<close>
      using tail_eq by simp
    finally show ?thesis by simp
  qed

  have block_match: \<open>match_trivia (cp ''{-'' @ tail) rest BlockComment\<close>
    using match_trivia.Block[OF body_ok, of rest]
    by (subst v_eq) simp

  have member: \<open>(BlockComment, cp ''{-'' @ tail) \<in> trivia (c\<^sub>1 # c\<^sub>2 # cs)\<close>
    unfolding trivia_def
    using concat_eq block_match by (rule match_ctxI)

  have max: \<open>\<forall>y \<in> trivia (c\<^sub>1 # c\<^sub>2 # cs).
              length (snd y) \<le> length (cp ''{-'' @ tail)\<close>
  proof
    fix y assume \<open>y \<in> trivia (c\<^sub>1 # c\<^sub>2 # cs)\<close>
    then obtain t v where y_eq: \<open>y = (t, v)\<close> by (cases y) auto
    with \<open>y \<in> _\<close> obtain vtail where
      s_eq: \<open>c\<^sub>1 # c\<^sub>2 # cs = v @ vtail\<close>
      and mt: \<open>match_trivia v vtail t\<close>
      by (auto simp: trivia_def elim: match_ctxE)
    have pfx: \<open>prefix v (c\<^sub>1 # c\<^sub>2 # cs)\<close>
      using s_eq by (auto simp: prefix_def)
    from mt show \<open>length (snd y) \<le> length (cp ''{-'' @ tail)\<close>
    proof (cases rule: match_trivia.cases)
      case Space
      have \<open>v \<noteq> []\<close> using Space by simp
      then obtain vh vt where v_form: \<open>v = vh # vt\<close> by (cases v) auto
      then have \<open>c\<^sub>1 = vh\<close> using pfx by (auto simp: prefix_def)
      with v_form Space have \<open>is_whitespace c\<^sub>1\<close> by (auto simp: list_all_iff)
      with c_eq is_whitespace_not_curlyo have False by simp
      then show ?thesis ..
    next
      case (Line n)
      have tw_len: \<open>2 \<le> length (takeWhile (\<lambda>c. c = dash) v)\<close>
        using Line by simp
      then have v_ne: \<open>v \<noteq> []\<close> by (cases v) simp_all
      then obtain vh vt where v_form: \<open>v = vh # vt\<close> by (cases v) auto
      have vh_dash: \<open>vh = dash\<close>
        using tw_len v_form by (cases \<open>vh = dash\<close>) simp_all
      have vh_eq: \<open>vh = c\<^sub>1\<close> using pfx v_form by (auto simp: prefix_def)
      with vh_dash c_eq have False by simp
      then show ?thesis ..
    next
      case (Block b')
      then have v_shape: \<open>v = cp ''{-'' @ b' @ cp ''-}''\<close>
        and body_b': \<open>comment_body b'\<close>
        by simp+
      from v_shape s_eq cc have \<open>cs = b' @ cp ''-}'' @ vtail\<close>
        by simp
      then have \<open>length b' + 2 \<le> length tail\<close>
        using lex body_b' lex_block_cmt_body_max by blast
      then show ?thesis
        using v_shape tail_eq y_eq by simp
    qed
  qed

  show ?thesis using member max
    by (simp add: longest_ctx_trivia_Some_iff)
qed

text \<open>Any balanced body followed by the closer is found by
  \<^const>\<open>lex_block_cmt\<close>, by induction on \<^const>\<open>comment_body\<close>. This is
  the block-comment case of \<^text>\<open>longest_trivia_None\<close>.\<close>

lemma lex_block_cmt_complete:
  assumes \<open>comment_body b\<close>
      and \<open>cs = b @ cp ''-}'' @ rest\<close>
  shows \<open>lex_block_cmt 1 [] cs \<noteq> None\<close>
proof -
  have \<open>\<forall>acc rest. lex_block_cmt 1 acc (b @ cp ''-}'' @ rest) \<noteq> None\<close>
    using assms(1)
  proof (induction b rule: comment_body.induct)
    case (Chr c cs\<^sub>b)
    from Chr.hyps have not_delim: \<open>\<not> comment_delim (c # cs\<^sub>b)\<close>
                  and not_final: \<open>\<not> (c = curlyo \<and> cs\<^sub>b = [])\<close> by simp_all
    show ?case
    proof (intro allI)
      fix acc rest
      show \<open>lex_block_cmt 1 acc ((c # cs\<^sub>b) @ cp ''-}'' @ rest) \<noteq> None\<close>
      proof (cases cs\<^sub>b)
        case Nil
        with not_final have c_ne: \<open>c \<noteq> curlyo\<close> by simp
        hence not_open: \<open>[c, dash] \<noteq> cp ''{-''\<close> by simp
        have not_close: \<open>[c, dash] \<noteq> cp ''-}''\<close> by simp
        from Nil not_open not_close
        have \<open>lex_block_cmt 1 acc ((c # cs\<^sub>b) @ cp ''-}'' @ rest)
                = lex_block_cmt 1 (c # acc) (cp ''-}'' @ rest)\<close>
          by simp
        also have \<open>\<dots> = Some (rev (c # acc) @ cp ''-}'', rest)\<close> by simp
        finally show ?thesis by simp
      next
        case (Cons c\<^sub>b cs\<^sub>b')
        with not_delim have not_open: \<open>[c, c\<^sub>b] \<noteq> cp ''{-''\<close>
                        and not_close: \<open>[c, c\<^sub>b] \<noteq> cp ''-}''\<close>
          by (auto simp: prefix_def)
        from Cons not_open not_close
        have \<open>lex_block_cmt 1 acc ((c # cs\<^sub>b) @ cp ''-}'' @ rest)
                = lex_block_cmt 1 (c # acc) (cs\<^sub>b @ cp ''-}'' @ rest)\<close>
          by fastforce
        with Chr.IH show ?thesis by simp
      qed
    qed
  next
    case (Nest inner tail\<^sub>b)
    show ?case
    proof (intro allI)
      fix acc rest
      have \<open>lex_block_cmt 1 acc ((cp ''{-'' @ inner @ cp ''-}'' @ tail\<^sub>b) @ cp ''-}'' @ rest)
              = lex_block_cmt 2 ([dash, curlyo] @ acc)
                  (inner @ cp ''-}'' @ tail\<^sub>b @ cp ''-}'' @ rest)\<close>
        by (simp add: Suc_1[unfolded One_nat_def])
      also from lex_block_cmt_step[OF Nest.hyps(1)]
      have \<open>\<dots> = lex_block_cmt 1
                    (rev (inner @ cp ''-}'') @ [dash, curlyo] @ acc)
                    (tail\<^sub>b @ cp ''-}'' @ rest)\<close>
        by (simp add: numeral_2_eq_2)
      also from Nest.IH(2) have \<open>\<dots> \<noteq> None\<close> by blast
      finally show \<open>lex_block_cmt 1 acc
          ((cp ''{-'' @ inner @ cp ''-}'' @ tail\<^sub>b) @ cp ''-}'' @ rest)
                     \<noteq> None\<close> .
    qed
  qed simp
  with assms(2) show ?thesis by simp
qed

lemma longest_trivia_None:
  assumes not_ws: \<open>\<not> is_whitespace c\<^sub>1\<close>
      and not_line: \<open>[c\<^sub>1, c\<^sub>2] \<noteq> cp ''--'' \<or>
           (let u = takeWhile ((=) dash) cs;
                after = drop (length u) cs
            in after \<noteq> [] \<and> is_symchar (hd after))\<close>
      and not_block: \<open>[c\<^sub>1, c\<^sub>2] \<noteq> cp ''{-'' \<or> lex_block_cmt 1 [] cs = None\<close>
  shows \<open>longest_ctx match_trivia (c\<^sub>1 # c\<^sub>2 # cs) = None\<close>
proof -
  have \<open>trivia (c\<^sub>1 # c\<^sub>2 # cs) = {}\<close>
    unfolding trivia_def
  proof (rule ccontr)
    assume \<open>match_ctx match_trivia (c\<^sub>1 # c\<^sub>2 # cs) \<noteq> {}\<close>
    then obtain t v vtail where
      s_eq: \<open>c\<^sub>1 # c\<^sub>2 # cs = v @ vtail\<close> and mt: \<open>match_trivia v vtail t\<close>
      by (auto elim!: match_ctxE)
    have v_ne: \<open>v \<noteq> []\<close>
      using mt by (cases rule: match_trivia.cases) auto
    then obtain v' where v_form: \<open>v = c\<^sub>1 # v'\<close>
      using s_eq by (cases v) auto
    from mt show False
    proof (cases rule: match_trivia.cases)
      case Space
      with v_form have \<open>is_whitespace c\<^sub>1\<close> by (auto simp: list_all_iff)
      with not_ws show False by simp
    next
      case (Line n)
      then have n_dashes: \<open>n = length (takeWhile (\<lambda>c. c = dash) v)\<close>
        and n_ge: \<open>2 \<le> n\<close>
        and drop_cnd: \<open>drop n v = [] \<or> \<not> is_symchar (hd (drop n v))\<close>
        and tail_cnd: \<open>vtail = [] \<or> \<not> is_symchar (hd vtail)\<close>
        by auto

      have v_len_ge: \<open>2 \<le> length v\<close>
        using n_ge n_dashes length_takeWhile_le[of \<open>\<lambda>c. c = dash\<close> v] by linarith
      then obtain v'' where v_form2: \<open>v = c\<^sub>1 # c\<^sub>2 # v''\<close>
        using v_form s_eq by (cases v') auto

      have c_dash: \<open>c\<^sub>1 = dash\<close> \<open>c\<^sub>2 = dash\<close>
        using n_dashes n_ge v_form2 by (auto split: if_splits)
      hence cc_eq: \<open>[c\<^sub>1, c\<^sub>2] = cp ''--''\<close> by simp

      let ?u = \<open>takeWhile ((=) dash) cs\<close>
      let ?after = \<open>drop (length ?u) cs\<close>

      from cc_eq not_line have after_ok:
        \<open>?after \<noteq> [] \<and> is_symchar (hd ?after)\<close>
        by (simp add: Let_def)
      have after_ne: \<open>?after \<noteq> []\<close>
        and after_sym: \<open>is_symchar (hd ?after)\<close>
        using after_ok by auto

      have cs_split: \<open>cs = ?u @ ?after\<close>
        by (metis append_take_drop_id takeWhile_eq_take)

      have cs_v'': \<open>cs = v'' @ vtail\<close>
        using s_eq v_form2 by simp

      show False
      proof (cases \<open>length v'' \<le> length ?u\<close>)
        case True
        \<comment>\<open>v ends inside or at end of the leading dashes.\<close>
        have vtail_split: \<open>vtail = drop (length v'') ?u @ ?after\<close>
        proof -
          have \<open>vtail = drop (length v'') cs\<close>
            using cs_v'' by (metis append_eq_conv_conj)
          also have \<open>\<dots> = drop (length v'') (?u @ ?after)\<close>
            using cs_split by simp
          also have \<open>\<dots> = drop (length v'') ?u @ ?after\<close>
            using True by simp
          finally show ?thesis .
        qed
        show False
        proof (cases \<open>length v'' = length ?u\<close>)
          case True
          hence \<open>drop (length v'') ?u = []\<close> by simp
          hence \<open>vtail = ?after\<close> using vtail_split by simp
          with after_ne after_sym tail_cnd show False by auto
        next
          case False
          with \<open>length v'' \<le> length ?u\<close> have lt: \<open>length v'' < length ?u\<close> by simp
          have drop_u_ne: \<open>drop (length v'') ?u \<noteq> []\<close> using lt by simp
          have hd_dash: \<open>hd (drop (length v'') ?u) = dash\<close>
          proof -
            have \<open>hd (drop (length v'') ?u) \<in> set (drop (length v'') ?u)\<close>
              using drop_u_ne by (rule hd_in_set)
            hence \<open>hd (drop (length v'') ?u) \<in> set ?u\<close>
              by (auto dest: in_set_dropD)
            thus ?thesis by (auto dest: set_takeWhileD)
          qed
          have vtail_ne: \<open>vtail \<noteq> []\<close>
            using vtail_split drop_u_ne by simp
          have hd_vtail_eq: \<open>hd vtail = hd (drop (length v'') ?u)\<close>
            using vtail_split drop_u_ne by simp
          with hd_dash have \<open>hd vtail = dash\<close> by simp
          with vtail_ne tail_cnd is_symchar_dash show False by auto
        qed
      next
        case False
        \<comment>\<open>v extends into \<open>?after\<close>. Then \<open>n = 2 + length ?u\<close> and \<open>drop n v\<close> starts at \<open>hd ?after\<close>.\<close>
        hence long: \<open>length ?u < length v''\<close> by simp
        have take_u_v'': \<open>take (length ?u) v'' = ?u\<close>
        proof -
          have \<open>?u = take (length ?u) cs\<close> by (metis takeWhile_eq_take)
          also have \<open>\<dots> = take (length ?u) (v'' @ vtail)\<close>
            using cs_v'' by simp
          also have \<open>\<dots> = take (length ?u) v''\<close>
            using long by simp
          finally show ?thesis by simp
        qed
        have v''_form: \<open>v'' = ?u @ drop (length ?u) v''\<close>
          using take_u_v'' by (metis append_take_drop_id)
        have drop_v''_ne: \<open>drop (length ?u) v'' \<noteq> []\<close> using long by simp

        have hd_drop_v'': \<open>hd (drop (length ?u) v'') = hd ?after\<close>
        proof -
          have v_eq_take: \<open>v'' = take (length v'') cs\<close>
            using cs_v'' by (metis append_eq_conv_conj)
          have \<open>drop (length ?u) v'' = drop (length ?u) (take (length v'') cs)\<close>
            using v_eq_take by simp
          also have \<open>\<dots> = take (length v'' - length ?u) (drop (length ?u) cs)\<close>
            by (simp add: drop_take)
          finally have eq:
            \<open>drop (length ?u) v'' = take (length v'' - length ?u) ?after\<close> .
          from eq show ?thesis
            using long after_ne
            by (cases \<open>length v'' - length ?u\<close>; cases ?after) auto
        qed

        have u_all_dash: \<open>list_all ((=) dash) ?u\<close>
          by (auto simp: list_all_iff dest: set_takeWhileD)
        have hd_after_ne_dash: \<open>hd ?after \<noteq> dash\<close>
        proof -
          have \<open>?after = dropWhile ((=) dash) cs\<close>
            by (simp add: dropWhile_eq_drop)
          with after_ne show ?thesis by (metis (full_types) hd_dropWhile)
        qed
        have hd_drop_ne_dash: \<open>hd (drop (length ?u) v'') \<noteq> dash\<close>
          using hd_drop_v'' hd_after_ne_dash by simp

        have takeWhile_v'': \<open>takeWhile ((=) dash) v'' = ?u\<close>
        proof -
          have tw_zero: \<open>takeWhile ((=) dash) (drop (length ?u) v'') = []\<close>
            using hd_drop_ne_dash drop_v''_ne
            by (cases \<open>drop (length ?u) v''\<close>) auto
          have \<open>takeWhile ((=) dash) v'' = takeWhile ((=) dash) (?u @ drop (length ?u) v'')\<close>
            using v''_form by simp
          also have \<open>\<dots> = ?u @ takeWhile ((=) dash) (drop (length ?u) v'')\<close>
            using u_all_dash by (simp add: list_all_iff)
          also have \<open>\<dots> = ?u\<close> using tw_zero by simp
          finally show ?thesis .
        qed
        have takeWhile_v: \<open>takeWhile (\<lambda>c. c = dash) v = c\<^sub>1 # c\<^sub>2 # ?u\<close>
        proof -
          have h1: \<open>takeWhile (\<lambda>c. c = dash) v = c\<^sub>1 # c\<^sub>2 # takeWhile (\<lambda>c. c = dash) v''\<close>
            using c_dash v_form2 by simp
          have h2: \<open>takeWhile (\<lambda>c. c = dash) v'' = takeWhile ((=) dash) v''\<close>
            by (rule takeWhile_cong) auto
          from h1 h2 takeWhile_v'' show ?thesis by metis
        qed
        have n_eq: \<open>n = 2 + length ?u\<close>
          using n_dashes takeWhile_v by simp

        have \<open>drop n v = drop (length ?u) v''\<close>
          using n_eq v_form2 by simp
        with drop_v''_ne hd_drop_v'' after_sym drop_cnd show False by auto
      qed
    next
      case (Block b)
      from Block have v_shape: \<open>v = cp ''{-'' @ b @ cp ''-}''\<close> by simp
      hence hd_v: \<open>hd v = curlyo\<close> by simp
      have \<open>hd v = c\<^sub>1\<close> using v_form by simp
      with hd_v have c1_curly: \<open>c\<^sub>1 = curlyo\<close> by simp
      from v_shape have v_form3: \<open>v = curlyo # dash # (b @ cp ''-}'')\<close> by simp
      hence \<open>c\<^sub>2 = dash\<close> using v_form s_eq by simp
      with c1_curly have cc_curly: \<open>[c\<^sub>1, c\<^sub>2] = cp ''{-''\<close> by simp
      with not_block have lex_none: \<open>lex_block_cmt 1 [] cs = None\<close> by simp

      have b_pfx_cs: \<open>cs = b @ cp ''-}'' @ (drop (length v) (c\<^sub>1 # c\<^sub>2 # cs))\<close>
      proof -
        have \<open>v @ vtail = cp ''{-'' @ b @ cp ''-}'' @ vtail\<close>
          using v_shape by simp
        with s_eq have \<open>c\<^sub>1 # c\<^sub>2 # cs = cp ''{-'' @ b @ cp ''-}'' @ vtail\<close> by simp
        hence \<open>cs = b @ cp ''-}'' @ vtail\<close> by simp
        moreover from s_eq have \<open>vtail = drop (length v) (c\<^sub>1 # c\<^sub>2 # cs)\<close>
          by (metis append_eq_conv_conj)
        ultimately show ?thesis by simp
      qed

      from Block(3) b_pfx_cs lex_block_cmt_complete[of b cs \<open>drop (length v) (c\<^sub>1 # c\<^sub>2 # cs)\<close>]
      have \<open>lex_block_cmt 1 [] cs \<noteq> None\<close> by simp
      with lex_none show False by simp
    qed
  qed
  thus ?thesis by (simp add: longest_ctx_trivia_None_iff)
qed


lemma longest_trivia_empty [simp]:
  \<open>longest_ctx match_trivia [] = None\<close>
  by (auto simp: longest_ctx_trivia_None_iff trivia_def match_ctx_def match_def prefix_def)

lemma prefix_singleton: \<open>prefix u [c] \<longleftrightarrow> u = [] \<or> u = [c]\<close>
  by (auto simp: prefix_def Cons_eq_append_conv)

lemma longest_trivia_singleton:
  \<open>longest_ctx match_trivia [c] =
     (if is_whitespace c then Some (Space, [c]) else None)\<close>
  by (auto simp: longest_ctx_trivia_Some_iff longest_ctx_trivia_None_iff trivia_def match_ctx_def
                 match_def prefix_singleton list_all_iff
           intro: match_trivia.Space elim!: match_trivia.cases split: if_splits)


subsection \<open>Soundness of the executable scanners\<close>

text \<open>\<^const>\<open>lex_trivia'\<close> agrees with \<^const>\<open>strip_trivia\<close> on the trivia it
  emits, and its returned cursor equals \<^const>\<open>advance_line\<close> /
  \<^const>\<open>advance_col\<close> / \<^text>\<open>+ length\<close> of the consumed characters. Both
  facts come from one induction.\<close>

lemma singleton_strip:
  assumes \<open>is_whitespace v\<close>
  shows \<open>strip_trivia line col off [v] [(Space, span_of line col off [v])] []\<close>
proof -
  have L: \<open>longest_ctx match_trivia [v] = Some (Space, [v])\<close>
    using assms by (simp add: longest_trivia_singleton)
  have S: \<open>strip_trivia (advance_line line [v]) (advance_col col [v]) (off + length [v])
           (drop (length [v]) [v]) [] []\<close>
    by (simp add: strip_trivia.strip_Stop)
  from strip_trivia.strip_Step[OF L S] show ?thesis by simp
qed

lemma lex_trivia'_sound:
  assumes \<open>lex_trivia' line col off acc s = Some (result, line', col', off', cs')\<close>
  obtains header where
    \<open>result = header @ acc\<close>
    \<open>strip_trivia line col off s (rev header) cs'\<close>
    \<open>line' = advance_line line (consumed (rev header))\<close>
    \<open>col'  = advance_col  col (consumed (rev header))\<close>
    \<open>off'  = off + length (consumed (rev header))\<close>
  apply (atomize_elim)
  using assms
proof (induction line col off acc s arbitrary: result line' col' off' cs'
    rule: lex_trivia'.induct[case_names more empty singleton])
  case (more line col off acc c\<^sub>1 c\<^sub>2 cs)
  let ?s = \<open>c\<^sub>1 # c\<^sub>2 # cs\<close>
  show ?case
  proof (cases \<open>is_whitespace c\<^sub>1\<close>)
    case ws: True
    let ?u = \<open>c\<^sub>1 # takeWhile is_whitespace (c\<^sub>2 # cs)\<close>
    let ?rest = \<open>drop (length ?u) ?s\<close>
    let ?line = \<open>advance_line line ?u\<close>
    let ?col = \<open>advance_col col ?u\<close>
    let ?off = \<open>off + length ?u\<close>
    let ?trivia = \<open>(Space, span_of line col off ?u)\<close>
    let ?acc = \<open>?trivia # acc\<close>

    from ws more.prems have
      \<open>lex_trivia' ?line ?col ?off ?acc ?rest = Some (result, line', col', off', cs')\<close>
      by (simp add: Let_def)

    then obtain header' where
      IH1: \<open>result = header' @ ?acc\<close> and
      IH2: \<open>strip_trivia ?line ?col ?off ?rest (rev header') cs'\<close> and
      IH3: \<open>line' = advance_line ?line (consumed (rev header'))\<close> and
      IH4: \<open>col'  = advance_col  ?col (consumed (rev header'))\<close> and
      IH5: \<open>off'  = ?off + length (consumed (rev header'))\<close>
      using more.IH(1) ws by blast

    have strip: \<open>strip_trivia line col off ?s (?trivia # rev header') cs'\<close>
      using strip_trivia.strip_Step[OF _ IH2] longest_trivia_whitespace[OF ws]
      by blast

    show ?thesis
      using IH1 IH3 IH4 IH5 strip
      by (intro exI[where x=\<open>header' @ [?trivia]\<close>] conjI) (simp_all flip: advance_append)
  next
    case notws: False
    show ?thesis
    proof (cases \<open>[c\<^sub>1, c\<^sub>2] = cp ''--''\<close>)
      case line_eq: True
      let ?u = \<open>takeWhile ((=) dash) cs\<close>
      let ?after = \<open>drop (length ?u) cs\<close>
      show ?thesis
      proof (cases \<open>?after = [] \<or> \<not> is_symchar (hd ?after)\<close>)
        case cnd: True
        let ?body = \<open>takeWhile (\<lambda>c. \<not> is_newline c) ?after\<close>
        let ?consume = \<open>c\<^sub>1 # c\<^sub>2 # (?u @ ?body)\<close>
        let ?rest = \<open>drop (length ?body) ?after\<close>
        let ?line = \<open>advance_line line ?consume\<close>
        let ?col = \<open>advance_col col ?consume\<close>
        let ?off = \<open>off + length ?consume\<close>
        let ?trivia = \<open>(LineComment, span_of line col off ?consume)\<close>
        let ?acc = \<open>?trivia # acc\<close>

        from notws line_eq cnd more.prems have
          \<open>lex_trivia' ?line ?col ?off ?acc ?rest = Some (result, line', col', off', cs')\<close>
          by (simp add: Let_def)

        then obtain header' where
          IH1: \<open>result = header' @ ?acc\<close>
           and IH2: \<open>strip_trivia ?line ?col ?off ?rest (rev header') cs'\<close>
           and IH3: \<open>line' = advance_line ?line (consumed (rev header'))\<close>
           and IH4: \<open>col'  = advance_col  ?col (consumed (rev header'))\<close>
           and IH5: \<open>off'  = ?off + length (consumed (rev header'))\<close>
          using more.IH(2) notws line_eq cnd
          by meson

        from IH2 have strip: \<open>strip_trivia line col off ?s (?trivia # rev header') cs'\<close>
          using strip_trivia.strip_Step[OF longest_trivia_line[OF line_eq refl refl refl cnd]]
          by (simp add: add.commute)

        show ?thesis
          using IH1 IH3 IH4 IH5 strip
          by (intro exI[where x=\<open>header' @ [?trivia]\<close>] conjI) (simp_all flip: advance_append)
      next
        case cnd_no: False
        from notws line_eq cnd_no more.prems have res:
          \<open>result = acc\<close> \<open>line' = line\<close> \<open>col' = col\<close> \<open>off' = off\<close> \<open>cs' = ?s\<close>
          by (auto simp: Let_def)

        have \<open>[c\<^sub>1, c\<^sub>2] \<noteq> cp ''--'' \<or>
             (let u = takeWhile ((=) dash) cs; 
                  after = drop (length u) cs
               in after \<noteq> [] \<and> is_symchar (hd after))\<close>
          using cnd_no by (auto simp: Let_def)
        moreover have \<open>[c\<^sub>1, c\<^sub>2] \<noteq> cp ''{-'' \<or> lex_block_cmt 1 [] cs = None\<close>
          using line_eq by simp
        ultimately have \<open>longest_ctx match_trivia ?s = None\<close>
          by (intro longest_trivia_None[OF notws])

        with res show ?thesis
          by (auto simp: advance_line_def advance_col_def intro: strip_trivia.strip_Stop)
      qed
    next
      case notline: False
      show ?thesis
      proof (cases \<open>[c\<^sub>1, c\<^sub>2] = cp ''{-''\<close>)
        case blk_eq: True
        show ?thesis
        proof (cases \<open>lex_block_cmt 1 [] cs\<close>)
          case None
          from notws notline blk_eq None more.prems have res:
            \<open>result = acc\<close> \<open>line' = line\<close> \<open>col' = col\<close> \<open>off' = off\<close> \<open>cs' = ?s\<close>
            by (auto simp: Let_def)

          have \<open>[c\<^sub>1, c\<^sub>2] \<noteq> cp ''--'' \<or>
             (let u = takeWhile ((=) dash) cs;
                  after = drop (length u) cs
               in after \<noteq> [] \<and> is_symchar (hd after))\<close>
            using notline by simp
          moreover have \<open>[c\<^sub>1, c\<^sub>2] \<noteq> cp ''{-'' \<or> lex_block_cmt 1 [] cs = None\<close>
            using None by simp
          ultimately have \<open>longest_ctx match_trivia ?s = None\<close>
            by (intro longest_trivia_None[OF notws])

          with res show ?thesis
            by (auto simp: advance_line_def advance_col_def intro: strip_trivia.strip_Stop)
        next
          case (Some val)
          then obtain tail rest\<^sub>0 where
            val_eq: \<open>val = (tail, rest\<^sub>0)\<close> and
            Some': \<open>lex_block_cmt 1 [] cs = Some (tail, rest\<^sub>0)\<close>
            by (cases val) auto

          let ?consume = \<open>cp ''{-'' @ tail\<close>
          let ?line = \<open>advance_line line ?consume\<close>
          let ?col = \<open>advance_col col ?consume\<close>
          let ?off = \<open>off + length ?consume\<close>
          let ?trivia = \<open>(BlockComment, span_of line col off ?consume)\<close>
          let ?acc = \<open>?trivia # acc\<close>

          from notws notline blk_eq Some' more.prems have
            \<open>lex_trivia' ?line ?col ?off ?acc rest\<^sub>0 = Some (result, line', col', off', cs')\<close>
            by (simp add: Let_def)

          then obtain header' where
            IH1: \<open>result = header' @ ?acc\<close>
             and IH2: \<open>strip_trivia ?line ?col ?off rest\<^sub>0 (rev header') cs'\<close>
             and IH3: \<open>line' = advance_line ?line (consumed (rev header'))\<close>
             and IH4: \<open>col'  = advance_col  ?col (consumed (rev header'))\<close>
             and IH5: \<open>off'  = ?off + length (consumed (rev header'))\<close>
            using more.IH(3) notws notline blk_eq Some' by fastforce

          have \<open>rest\<^sub>0 = drop (length ?consume) ?s\<close>
            using lex_block_cmt_consumed[OF Some'] by auto
          moreover have \<open>longest_ctx match_trivia ?s = Some (BlockComment, ?consume)\<close>
            by (rule longest_trivia_block[OF blk_eq Some'])
          ultimately have strip: \<open>strip_trivia line col off ?s (?trivia # rev header') cs'\<close>
            using IH2 strip_trivia.strip_Step
            by blast

          show ?thesis
            using IH1 IH3 IH4 IH5 strip
            by (intro exI[where x=\<open>header' @ [?trivia]\<close>] conjI) (simp_all flip: advance_append)
        qed
      next
        case False
        with notws notline more.prems have
          \<open>result = acc\<close> \<open>line' = line\<close> \<open>col' = col\<close> \<open>off' = off\<close> \<open>cs' = ?s\<close>
          by (auto simp: Let_def)
        moreover have \<open>longest_ctx match_trivia ?s = None\<close>
          using longest_trivia_None[OF notws] notline False
          by blast
        ultimately show ?thesis
          by (auto simp: advance_line_def advance_col_def intro: strip_trivia.strip_Stop)
      qed
    qed
  qed
next
  case (empty line col off acc)
  then show ?case
    by (auto simp: advance_line_def advance_col_def intro: strip_trivia.strip_Stop)
next
  case (singleton line col off acc v)
  with singleton_strip show ?case
    by (cases \<open>is_whitespace v\<close>)
      (auto simp: advance_line_def advance_col_def longest_trivia_singleton
        intro: strip_trivia.strip_Stop)
qed

lemma lex_trivia_sound:
  assumes \<open>lex_trivia line\<^sub>0 col\<^sub>0 off\<^sub>0 s = Some (header, line, col, off, cs')\<close>
  shows \<open>strip_trivia line\<^sub>0 col\<^sub>0 off\<^sub>0 s header cs' \<and>
         line = advance_line line\<^sub>0 (consumed header) \<and>
         col  = advance_col  col\<^sub>0 (consumed header) \<and>
         off  = off\<^sub>0 + length (consumed header)\<close>
proof -
  from assms obtain acc where
    acc: \<open>lex_trivia' line\<^sub>0 col\<^sub>0 off\<^sub>0 [] s = Some (acc, line, col, off, cs')\<close> and
     hd: \<open>header = rev acc\<close>
    by (auto simp: lex_trivia_def split: option.splits)

  from lex_trivia'_sound[OF acc] obtain h where
     \<open>acc = h @ []\<close>
     \<open>strip_trivia line\<^sub>0 col\<^sub>0 off\<^sub>0 s (rev h) cs'\<close>
     \<open>line = advance_line line\<^sub>0 (consumed (rev h))\<close>
     \<open>col  = advance_col  col\<^sub>0 (consumed (rev h))\<close>
     \<open>off  = off\<^sub>0 + length (consumed (rev h))\<close>
    by auto

  with hd show ?thesis by simp
qed

end
