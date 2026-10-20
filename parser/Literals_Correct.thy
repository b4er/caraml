theory Literals_Correct
  imports Literals
begin

section \<open>The literal readers stop where the lexer stops\<close>

text \<open>The lexer hands a decoder the text of a lexeme alone, while the token
  relation and the scanner run the same reader on the lexeme followed by the
  rest of the input. The lemmas \<open>read_num_lexeme\<close>, \<open>read_str_lexeme\<close> and
  \<open>read_char_lexeme\<close> bridge the two: a reader that consumes exactly a
  prefix \<open>u\<close> of \<open>u @ r\<close> consumes exactly \<open>u\<close> on its own. Strings and
  characters are delimited, so only the numeral case needs the boundary
  condition the lexer imposes: the character after a numeral is neither a
  digit, an underscore nor a letter.\<close>

subsection \<open>Numerals\<close>

(*<*)

lemma rs_i8: \<open>read_suffix (cp ''i8'') = (Some I8, [])\<close> by code_simp
lemma rs_i16: \<open>read_suffix (cp ''i16'') = (Some I16, [])\<close> by code_simp
lemma rs_i32: \<open>read_suffix (cp ''i32'') = (Some I32, [])\<close> by code_simp
lemma rs_i64: \<open>read_suffix (cp ''i64'') = (Some I64, [])\<close> by code_simp
lemma rs_u8: \<open>read_suffix (cp ''u8'') = (Some U8, [])\<close> by code_simp
lemma rs_u16: \<open>read_suffix (cp ''u16'') = (Some U16, [])\<close> by code_simp
lemma rs_u32: \<open>read_suffix (cp ''u32'') = (Some U32, [])\<close> by code_simp
lemma rs_u64: \<open>read_suffix (cp ''u64'') = (Some U64, [])\<close> by code_simp

lemma read_suffix_table:
  \<open>(u, s) \<in> set suffix_table \<Longrightarrow> read_suffix u = (Some s, []) \<and> hd u \<noteq> uscore\<close>
  unfolding suffix_table_def
  by (auto simp: rs_i8[simplified] rs_i16[simplified] rs_i32[simplified] rs_i64[simplified]
      rs_u8[simplified] rs_u16[simplified] rs_u32[simplified] rs_u64[simplified])

lemma rs_nil: \<open>read_suffix [] = (None, [])\<close> by code_simp

lemma scan_more_ctx:
  \<open>scan_more D (y @ z @ r) = (y, z @ r) \<Longrightarrow> z = [] \<or> hd z \<noteq> uscore \<Longrightarrow> scan_more D (y @ z) = (y, z)\<close>
proof (induction y arbitrary: z r)
  case Nil
  then show ?case
    by (cases z; cases \<open>tl z\<close>)
       (auto simp: apfst_def map_prod_def split: if_splits list.splits prod.splits)
next
  case (Cons a y)
  show ?case
  proof (cases \<open>D a\<close>)
    case True
    with Cons show ?thesis by (auto simp: apfst_def map_prod_def split: prod.splits)
  next
    case False
    with Cons.prems obtain d y' where y: \<open>y = d # y'\<close> \<open>a = uscore\<close> \<open>D d\<close>
      by (cases y; cases z)
         (auto simp: apfst_def map_prod_def split: list.splits if_splits prod.splits)
    from Cons.prems(1) False y have h: \<open>scan_more D (y @ z @ r) = (y, z @ r)\<close>
      by (auto simp: apfst_def map_prod_def split: prod.splits)
    from Cons.IH[OF h Cons.prems(2)] False y
    show ?thesis by (auto simp: apfst_def map_prod_def split: prod.splits)
  qed
qed

lemma scan_digits_ctx:
  \<open>scan_digits D (y @ z @ r) = Some (y, z @ r) \<Longrightarrow> z = [] \<or> hd z \<noteq> uscore
   \<Longrightarrow> scan_digits D (y @ z) = Some (y, z)\<close>
  by (cases y) (auto simp: scan_digits_def apfst_def map_prod_def
      split: if_splits prod.splits list.splits
      dest: scan_more_ctx)

lemma read_suffix_ctx:
  \<open>read_suffix (x @ r) = (sfx, r) \<Longrightarrow> read_suffix x = (sfx, []) \<and> (x = [] \<or> hd x \<noteq> uscore)\<close>
proof (cases \<open>find (\<lambda>(u, _). prefix u (x @ r)) suffix_table\<close>)
  case None
  assume h: \<open>read_suffix (x @ r) = (sfx, r)\<close>
  with None have \<open>x @ r = r\<close> by (simp add: read_suffix_def)
  then have \<open>x = []\<close> by simp
  moreover from h None have \<open>sfx = None\<close> by (simp add: read_suffix_def)
  ultimately show ?thesis using rs_nil by simp
next
  case (Some p)
  obtain u s where p: \<open>p = (u, s)\<close> by (cases p)
  assume h: \<open>read_suffix (x @ r) = (sfx, r)\<close>
  from Some p have mem: \<open>(u, s) \<in> set suffix_table\<close> and pre: \<open>prefix u (x @ r)\<close>
    by (metis find_Some_iff nth_mem, metis (mono_tags, lifting) find_Some_iff case_prod_conv)
  from pre obtain v where v: \<open>x @ r = u @ v\<close> by (auto simp: prefix_def)
  from h Some p v have \<open>v = r\<close> by (simp add: read_suffix_def)
  with v have \<open>x = u\<close> by simp
  moreover from h Some p v have \<open>sfx = Some s\<close> by (simp add: read_suffix_def)
  ultimately show ?thesis using read_suffix_table[OF mem] by (cases u) auto
qed

lemma suffix_split:
  \<open>suffix t (x @ r) \<Longrightarrow> suffix r t \<Longrightarrow> \<exists>p t0. x = p @ t0 \<and> t = t0 @ r\<close>
  by (auto simp: suffix_def append_eq_append_conv2)

lemma suffix_cut: \<open>suffix (t @ r) (x @ r) \<Longrightarrow> \<exists>p. x = p @ t\<close>
  by (auto simp: suffix_def)

lemma read_radix_ctx:
  \<open>read_radix (x @ z @ r) = Some (v, z @ r) \<Longrightarrow> z = [] \<or> hd z \<noteq> uscore \<Longrightarrow>
   read_radix (x @ z) = Some (v, z)\<close>
proof -
  assume h: \<open>read_radix (x @ z @ r) = Some (v, z @ r)\<close> and z: \<open>z = [] \<or> hd z \<noteq> uscore\<close>
  from h obtain a b w ds where
    s: \<open>x @ z @ r = a # b # w\<close> and
    sd: \<open>scan_digits (if a = 0x30 \<and> b = 0x78 then is_hexdigit else is_bindigit) w
        = Some (ds, z @ r)\<close> and
    ab: \<open>a = 0x30 \<and> (b = 0x78 \<or> b = 0x62)\<close>
    and v: \<open>v = (if b = 0x78 then digits_value 16 ds else digits_value 2 ds)\<close>
    by (auto simp: read_radix_def apfst_def map_prod_def
         split: list.splits if_splits prod.splits option.splits)
  from scan_digits_split[OF sd] have w: \<open>w = ds @ z @ r\<close> and ds: \<open>ds \<noteq> []\<close> by auto
  with s have \<open>x = a # b # ds\<close> by simp
  from scan_digits_ctx[OF sd[unfolded w] z]
  show ?thesis using ab v \<open>x = a # b # ds\<close>
    by (auto simp: read_radix_def apfst_def map_prod_def)
qed

lemma drop_dash_app: \<open>x \<noteq> [] \<Longrightarrow> drop_dash (x @ r) = drop_dash x @ r\<close>
  by (cases x) (auto simp: drop_dash_def)

lemma read_frac_ctx:
  \<open>read_frac (x @ z @ r) = Some (z @ r) \<Longrightarrow> z = [] \<or> hd z \<noteq> uscore \<Longrightarrow> read_frac (x @ z) = Some z\<close>
proof -
  assume h: \<open>read_frac (x @ z @ r) = Some (z @ r)\<close> and z: \<open>z = [] \<or> hd z \<noteq> uscore\<close>
  from h obtain d w ds where s: \<open>x @ z @ r = d # w\<close> and d: \<open>d = dot\<close>
    and sd: \<open>scan_digits is_digit w = Some (ds, z @ r)\<close>
    by (auto simp: read_frac_def split: list.splits if_splits option.splits)
  from read_frac_suffix[OF h] have \<open>x \<noteq> []\<close> by auto
  then obtain x' where x: \<open>x = d # x'\<close> using s by (cases x) auto
  with s have w: \<open>w = x' @ z @ r\<close> by simp
  from scan_digits_split[OF sd] w have xd: \<open>x' = ds\<close> by simp
  from sd have sd': \<open>scan_digits is_digit (x' @ z @ r) = Some (x', z @ r)\<close> by (simp add: w xd)
  from scan_digits_ctx[OF sd' z] show ?thesis using x d
    by (simp add: read_frac_def xd)
qed

lemma read_exp_ctx:
  \<open>read_exp (x @ z @ r) = Some (z @ r) \<Longrightarrow> z = [] \<or> hd z \<noteq> uscore \<Longrightarrow> read_exp (x @ z) = Some z\<close>
proof -
  assume h: \<open>read_exp (x @ z @ r) = Some (z @ r)\<close> and z: \<open>z = [] \<or> hd z \<noteq> uscore\<close>
  from h obtain e t ds where s: \<open>x @ z @ r = e # t\<close> and e: \<open>e = 0x65 \<or> e = 0x45\<close>
    and sd: \<open>scan_digits is_digit (drop_dash t) = Some (ds, z @ r)\<close>
    by (auto simp: read_exp_def split: list.splits if_splits option.splits)
  from read_exp_suffix[OF h] have \<open>x \<noteq> []\<close> by auto
  then obtain x' where x: \<open>x = e # x'\<close> using s by (cases x) auto
  with s have t: \<open>t = x' @ z @ r\<close> by simp
  from scan_digits_split[OF sd] have dd: \<open>drop_dash t = ds @ z @ r\<close> and ds: \<open>ds \<noteq> []\<close> by auto
  have \<open>x' \<noteq> []\<close>
  proof
    assume \<open>x' = []\<close>
    with t dd drop_dash_suffix[of t] ds show False
      by (auto dest: suffix_length_le)
  qed
  with dd t have \<open>drop_dash x' @ z @ r = ds @ z @ r\<close> by (simp add: drop_dash_app)
  then have \<open>drop_dash x' = ds\<close> by simp
  moreover from scan_digits_ctx[OF sd[unfolded dd] z]
    have \<open>scan_digits is_digit (ds @ z) = Some (ds, z)\<close> .
  ultimately show ?thesis using x e \<open>x' \<noteq> []\<close> by (simp add: read_exp_def drop_dash_app)
qed

lemma scan_digits_app: \<open>scan_digits D s \<noteq> None \<Longrightarrow> scan_digits D (s @ r) \<noteq> None\<close>
  by (auto simp: scan_digits_def split: list.splits if_splits)

lemma read_radix_app: \<open>read_radix x \<noteq> None \<Longrightarrow> read_radix (x @ r) \<noteq> None\<close>
  by (use scan_digits_app[of _ _ r] in
      \<open>fastforce simp: read_radix_def split: list.splits if_splits option.splits\<close>)

lemma read_frac_app: \<open>read_frac x \<noteq> None \<Longrightarrow> read_frac (x @ r) \<noteq> None\<close>
  by (use scan_digits_app[of _ _ r] in
      \<open>fastforce simp: read_frac_def split: list.splits if_splits option.splits\<close>)

lemma read_exp_app: \<open>read_exp x \<noteq> None \<Longrightarrow> read_exp (x @ r) \<noteq> None\<close>
proof -
  assume \<open>read_exp x \<noteq> None\<close>
  then obtain e t where x: \<open>x = e # t\<close> and \<open>e = 0x65 \<or> e = 0x45\<close>
    and sd: \<open>scan_digits is_digit (drop_dash t) \<noteq> None\<close>
    by (auto simp: read_exp_def split: list.splits if_splits option.splits)
  from sd have \<open>t \<noteq> []\<close> by (auto simp: drop_dash_def scan_digits_def)
  from scan_digits_app[OF sd, of r] drop_dash_app[OF this]
  show ?thesis using x \<open>e = 0x65 \<or> e = 0x45\<close> by (auto simp: read_exp_def)
qed

lemma read_frac_hd: \<open>read_frac s = Some a \<Longrightarrow> s \<noteq> [] \<and> hd s = dot\<close>
  by (auto simp: read_frac_def split: list.splits if_splits)

lemma read_exp_hd: \<open>read_exp s = Some a \<Longrightarrow> s \<noteq> [] \<and> (hd s = 0x65 \<or> hd s = 0x45)\<close>
  by (auto simp: read_exp_def split: list.splits if_splits)

lemma cond_of: \<open>\<rho> = t @ r \<Longrightarrow> \<rho> \<noteq> [] \<Longrightarrow> hd \<rho> \<noteq> uscore \<Longrightarrow> t = [] \<or> hd t \<noteq> uscore\<close>
  by (cases t) auto

lemma digits_ctx:
  \<open>scan_digits is_digit (x @ r) = Some (ds, t0 @ r) \<Longrightarrow> t0 = [] \<or> hd t0 \<noteq> uscore \<Longrightarrow>
   x = ds @ t0 \<and> scan_digits is_digit x = Some (ds, t0)\<close>
proof -
  assume sd: \<open>scan_digits is_digit (x @ r) = Some (ds, t0 @ r)\<close> and z: \<open>t0 = [] \<or> hd t0 \<noteq> uscore\<close>
  from scan_digits_split[OF sd] have \<open>x = ds @ t0\<close> by simp
  with sd have \<open>scan_digits is_digit (ds @ t0 @ r) = Some (ds, t0 @ r)\<close> by simp
  from scan_digits_ctx[OF this z] show ?thesis using \<open>x = ds @ t0\<close> by simp
qed

lemma read_unsigned_ctx:
  \<open>read_unsigned (x @ r) = Some (n, r) \<Longrightarrow> read_unsigned x = Some (n, [])\<close>
proof -
  assume h: \<open>read_unsigned (x @ r) = Some (n, r)\<close>
  show ?thesis
  proof (cases \<open>read_radix (x @ r)\<close>)
    case (Some p)
    obtain v r0 where p: \<open>p = (v, r0)\<close> by (cases p)
    obtain sfx r' where rs: \<open>read_suffix r0 = (sfx, r')\<close> by (cases \<open>read_suffix r0\<close>)
    from h Some p rs have n: \<open>n = NInt v sfx\<close> and r': \<open>r' = r\<close> by (simp_all add: read_unsigned_def)
    from rs r' have rs': \<open>read_suffix r0 = (sfx, r)\<close> by simp
    from read_radix_suffix[of \<open>x @ r\<close> v r0] Some p have s0: \<open>suffix r0 (x @ r)\<close> by simp
    from suffix_split[OF s0 read_suffix_suffix[OF rs']] obtain pp t0 where
      x: \<open>x = pp @ t0\<close> and r0: \<open>r0 = t0 @ r\<close> by blast
    from read_suffix_ctx[of t0 r sfx] rs' r0 have rs0: \<open>read_suffix t0 = (sfx, [])\<close>
      and c: \<open>t0 = [] \<or> hd t0 \<noteq> uscore\<close>
      by simp_all
    from Some p x r0 have \<open>read_radix (pp @ t0 @ r) = Some (v, t0 @ r)\<close> by simp
    from read_radix_ctx[OF this c] show ?thesis using x rs0 n by (simp add: read_unsigned_def)
  next
    case None
    with read_radix_app have rn: \<open>read_radix x = None\<close> by (metis)
    from h None obtain ds r0 where sd: \<open>scan_digits is_digit (x @ r) = Some (ds, r0)\<close>
      by (auto simp: read_unsigned_def split: option.splits)
    from scan_digits_split[OF sd] have xr: \<open>x @ r = ds @ r0\<close> by simp
    then have s0: \<open>suffix r0 (x @ r)\<close> by (simp add: suffix_def)
    show ?thesis
    proof (cases \<open>read_frac r0\<close>)
      case fr: (Some r1)
      from read_frac_suffix[OF fr] have s1: \<open>suffix r1 r0\<close> by simp
      from read_frac_hd[OF fr] have h0: \<open>r0 \<noteq> []\<close> \<open>hd r0 \<noteq> uscore\<close> by auto
      show ?thesis
      proof (cases \<open>read_exp r1\<close>)
        case ex: (Some r2)
        from h None sd fr ex have r2: \<open>r2 = r\<close> and n: \<open>n = NFloat\<close>
          by (simp_all add: read_unsigned_def)
        from read_exp_suffix[OF ex] r2 have sr1: \<open>suffix r r1\<close> by simp
        from suffix_trans[OF sr1 s1] have sr0: \<open>suffix r r0\<close> .
        from suffix_split[OF s0 sr0] obtain pp t0 where x: \<open>x = pp @ t0\<close> and r0: \<open>r0 = t0 @ r\<close>
          by blast
        from suffix_trans[OF s1 s0] have \<open>suffix r1 (x @ r)\<close> .
        from suffix_split[OF this sr1] obtain qq t1 where qx: \<open>x = qq @ t1\<close> and r1: \<open>r1 = t1 @ r\<close>
          by blast
        from s1 r0 r1 have \<open>suffix (t1 @ r) (t0 @ r)\<close> by simp
        from suffix_cut[OF this] obtain p1 where t0: \<open>t0 = p1 @ t1\<close> by blast
        from read_exp_hd[OF ex] have \<open>r1 \<noteq> []\<close> \<open>hd r1 \<noteq> uscore\<close> by auto
        from cond_of[OF r1 this] have c1: \<open>t1 = [] \<or> hd t1 \<noteq> uscore\<close> .
        from ex r1 r2 have \<open>read_exp (t1 @ [] @ r) = Some ([] @ r)\<close> by simp
        from read_exp_ctx[OF this] have ex0: \<open>read_exp t1 = Some []\<close> by simp
        from fr r0 r1 t0 have \<open>read_frac (p1 @ t1 @ r) = Some (t1 @ r)\<close> by simp
        from read_frac_ctx[OF this c1] have fr0: \<open>read_frac t0 = Some t1\<close> by (simp add: t0)
        from cond_of[OF r0 h0] have c0: \<open>t0 = [] \<or> hd t0 \<noteq> uscore\<close> .
        from digits_ctx[OF sd[unfolded r0] c0] have sd0: \<open>scan_digits is_digit x = Some (ds, t0)\<close>
          by blast
        show ?thesis using rn sd0 fr0 ex0 n by (simp add: read_unsigned_def)
      next
        case ex: None
        from h None sd fr ex have r1: \<open>r1 = r\<close> and n: \<open>n = NFloat\<close>
          by (simp_all add: read_unsigned_def)
        from s1 r1 have sr0: \<open>suffix r r0\<close> by simp
        from suffix_split[OF s0 sr0] obtain pp t0 where x: \<open>x = pp @ t0\<close> and r0: \<open>r0 = t0 @ r\<close>
          by blast
        from fr r0 r1 have \<open>read_frac (t0 @ [] @ r) = Some ([] @ r)\<close> by simp
        from read_frac_ctx[OF this] have fr0: \<open>read_frac t0 = Some []\<close> by simp
        from cond_of[OF r0 h0] have c0: \<open>t0 = [] \<or> hd t0 \<noteq> uscore\<close> .
        from digits_ctx[OF sd[unfolded r0] c0] have sd0: \<open>scan_digits is_digit x = Some (ds, t0)\<close>
          by blast
        show ?thesis using rn sd0 fr0 n by (simp add: read_unsigned_def read_exp_def)
      qed
    next
      case fr: None
      show ?thesis
      proof (cases \<open>read_exp r0\<close>)
        case ex: (Some r2)
        from h None sd fr ex have r2: \<open>r2 = r\<close> and n: \<open>n = NFloat\<close>
          by (simp_all add: read_unsigned_def)
        from read_exp_suffix[OF ex] r2 have sr0: \<open>suffix r r0\<close> by simp
        from suffix_split[OF s0 sr0] obtain pp t0 where x: \<open>x = pp @ t0\<close> and r0: \<open>r0 = t0 @ r\<close>
          by blast
        from read_exp_hd[OF ex] have h0: \<open>r0 \<noteq> []\<close> \<open>hd r0 \<noteq> uscore\<close> by auto
        from cond_of[OF r0 h0] have c0: \<open>t0 = [] \<or> hd t0 \<noteq> uscore\<close> .
        from ex r0 r2 have \<open>read_exp (t0 @ [] @ r) = Some ([] @ r)\<close> by simp
        from read_exp_ctx[OF this] have ex0: \<open>read_exp t0 = Some []\<close> by simp
        from digits_ctx[OF sd[unfolded r0] c0] have sd0: \<open>scan_digits is_digit x = Some (ds, t0)\<close>
          by blast
        from fr r0 have \<open>read_frac (t0 @ r) = None\<close> by simp
        with read_frac_app have fr0: \<open>read_frac t0 = None\<close> by metis
        show ?thesis using rn sd0 fr0 ex0 n by (simp add: read_unsigned_def)
      next
        case ex: None
        obtain sfx r' where rs: \<open>read_suffix r0 = (sfx, r')\<close> by (cases \<open>read_suffix r0\<close>)
        from h None sd fr ex rs have n: \<open>n = NInt (digits_value 10 ds) sfx\<close> and r': \<open>r' = r\<close>
          by (simp_all add: read_unsigned_def)
        from rs r' have rs': \<open>read_suffix r0 = (sfx, r)\<close> by simp
        from suffix_split[OF s0 read_suffix_suffix[OF rs']] obtain pp t0 where
          x: \<open>x = pp @ t0\<close> and r0: \<open>r0 = t0 @ r\<close> by blast
        from read_suffix_ctx[of t0 r sfx] rs' r0 have rs0: \<open>read_suffix t0 = (sfx, [])\<close>
          and c0: \<open>t0 = [] \<or> hd t0 \<noteq> uscore\<close>
          by simp_all
        from digits_ctx[OF sd[unfolded r0] c0] have sd0: \<open>scan_digits is_digit x = Some (ds, t0)\<close>
          by blast
        from fr r0 have \<open>read_frac (t0 @ r) = None\<close> by simp
        with read_frac_app have fr0: \<open>read_frac t0 = None\<close> by metis
        from ex r0 have \<open>read_exp (t0 @ r) = None\<close> by simp
        with read_exp_app have ex0: \<open>read_exp t0 = None\<close> by metis
        show ?thesis using rn sd0 fr0 ex0 rs0 n by (simp add: read_unsigned_def)
      qed
    qed
  qed
qed
(*>*)

lemma read_num_lexeme:
  \<open>read_num (u @ r) = Some (n, r) \<Longrightarrow> read_num u = Some (n, [])\<close>
proof (cases u)
  case Nil
  assume \<open>read_num (u @ r) = Some (n, r)\<close>
  from read_num_suffix[OF this[unfolded Nil append_Nil]] show ?thesis by simp
next
  case (Cons c u')
  assume h: \<open>read_num (u @ r) = Some (n, r)\<close>
  show ?thesis
  proof (cases \<open>c = dash\<close>)
    case True
    with h Cons obtain n' where \<open>read_unsigned (u' @ r) = Some (n', r)\<close> and \<open>n = negate n'\<close>
      by (auto simp: read_num_def split: option.splits prod.splits)
    from read_unsigned_ctx[OF this(1)] show ?thesis using True Cons \<open>n = negate n'\<close>
      by (simp add: read_num_def)
  next
    case False
    with h Cons have \<open>read_unsigned (u @ r) = Some (n, r)\<close> by (simp add: read_num_def)
    from read_unsigned_ctx[OF this] show ?thesis using False Cons by (simp add: read_num_def)
  qed
qed

subsection \<open>Strings and characters\<close>

(*<*)
lemma tw_ctx:
  \<open>drop (length (takeWhile p (y @ r))) (y @ r) = k # r \<Longrightarrow>
   \<exists>hs. y = hs @ [k] \<and> (\<forall>r'. takeWhile p (y @ r') = hs)\<close>
proof (induction y)
  case Nil
  then show ?case using length_drop[of _ r]
    by (metis append_Nil length_Cons length_drop nat_le_linear not_less_eq_eq diff_le_self)
next
  case (Cons a y)
  show ?case
  proof (cases \<open>p a\<close>)
    case True
    with Cons.prems have \<open>drop (length (takeWhile p (y @ r))) (y @ r) = k # r\<close> by simp
    from Cons.IH[OF this] True show ?thesis by auto
  next
    case False
    with Cons.prems show ?thesis by auto
  qed
qed

lemma read_escape_ctx:
  \<open>read_escape (x @ r) = Some (c, r) \<Longrightarrow> read_escape (x @ r') = Some (c, r')\<close>
proof (cases x)
  case Nil
  assume h: \<open>read_escape (x @ r) = Some (c, r)\<close>
  from read_escape_suffix[OF h] Nil show ?thesis by simp
next
  case xc: (Cons a y)
  assume h: \<open>read_escape (x @ r) = Some (c, r)\<close>
  then have h': \<open>read_escape (a # (y @ r)) = Some (c, r)\<close> using xc by simp
  show ?thesis
  proof (cases \<open>a = 0x75\<close>)
    case False
    with h' show ?thesis using xc by (auto simp: read_escape_def split: if_splits)
  next
    case True
    show ?thesis
    proof (cases y)
      case Nil
      with h' True have h2: \<open>read_escape (117 # r) = Some (c, r)\<close> by simp
      show ?thesis
      proof (cases r)
        case Nil
        with h2 show ?thesis by (simp add: read_escape_def)
      next
        case (Cons b r1)
        with h2 have \<open>\<exists>k. drop (length (takeWhile is_hexdigit r1)) r1 = k # r\<close>
          by (auto simp: read_escape_def Let_def split: list.splits if_splits)
        then obtain k where \<open>drop (length (takeWhile is_hexdigit r1)) r1 = k # r\<close> ..
        from arg_cong[where f=length, OF this] Cons show ?thesis by simp
      qed
    next
      case (Cons b y1)
      with h' True have cb: \<open>b = curlyo\<close>
        by (auto simp: read_escape_def Let_def split: list.splits if_splits)
      from h' Cons True cb
        have \<open>\<exists>k. drop (length (takeWhile is_hexdigit (y1 @ r))) (y1 @ r) = k # r\<close>
        by (auto simp: read_escape_def Let_def split: list.splits if_splits)
      then obtain k where dr: \<open>drop (length (takeWhile is_hexdigit (y1 @ r))) (y1 @ r) = k # r\<close> ..
      from tw_ctx[OF dr] obtain hs where y1: \<open>y1 = hs @ [k]\<close>
        and tw: \<open>\<forall>r'. takeWhile is_hexdigit (y1 @ r') = hs\<close> by blast
      have tw': \<open>\<And>r'. takeWhile is_hexdigit (hs @ k # r') = hs\<close> using tw y1 by auto
      from h' xc Cons True cb y1 have kc: \<open>k = curlyc\<close>
        by (auto simp: read_escape_def Let_def tw' split: if_splits)
      from tw' kc have tw'': \<open>\<And>r'. takeWhile is_hexdigit (hs @ curlyc # r') = hs\<close> by simp
      from h' xc Cons True cb y1 kc show ?thesis
        by (auto simp: read_escape_def Let_def tw'' split: if_splits)
    qed
  qed
qed

lemma app_eq_Cons_self: \<open>y @ r = q # r \<Longrightarrow> y = [q]\<close>
  by (cases y) auto

lemma scan_path_ctx:
  \<open>scan_path acc nm (x @ r) = Some (p, r) \<Longrightarrow> scan_path acc nm (x @ r') = Some (p, r')\<close>
proof (induction x arbitrary: acc nm)
  case Nil
  then show ?case using scan_path_suffix[of acc nm r p r] by simp
next
  case (Cons c x)
  then show ?case by (auto split: if_splits)
qed

lemma read_str_ctx:
  \<open>read_str (x @ r) = Some (ps, r) \<Longrightarrow> read_str (x @ r') = Some (ps, r')\<close>
proof (induction x arbitrary: ps rule: length_induct)
  case (1 x)
  show ?case
  proof (cases x)
    case Nil
    with "1.prems" have \<open>read_str r = Some (ps, r)\<close> by simp
    from read_str_suffix[OF this] show ?thesis by simp
  next
    case xc: (Cons c x1)
    have rs: \<open>read_str (c # (x1 @ r)) = Some (ps, r)\<close> using "1.prems" xc by simp
    have x1ne: \<open>x1 = [] \<Longrightarrow> False\<close> if \<open>read_str (x1 @ r) = Some (qs, r)\<close> for qs
      using read_str_suffix[of \<open>x1 @ r\<close> qs r] that by simp
    show ?thesis
    proof (cases \<open>c = qt\<close>)
      case True
      with rs have \<open>x1 @ r = r\<close> by simp
      then have \<open>x1 = []\<close> by simp
      with True xc rs show ?thesis by simp
    next
      case qt: False
      show ?thesis
      proof (cases \<open>is_newline c\<close>)
        case True
        with rs qt show ?thesis by simp
      next
        case nl: False
        show ?thesis
        proof (cases \<open>c = bslash\<close>)
          case True
          with rs qt nl obtain d r1 qs where e: \<open>read_escape (x1 @ r) = Some (d, r1)\<close>
            and rr: \<open>read_str r1 = Some (qs, r)\<close> and ps: \<open>ps = add_char d qs\<close>
            by (auto split: option.splits)
          from suffix_split[OF read_escape_suffix[THEN conjunct1, OF e]
              read_str_suffix[THEN conjunct1, OF rr]]
          obtain p t0 where x1: \<open>x1 = p @ t0\<close> and r1: \<open>r1 = t0 @ r\<close> by blast
          from e r1 x1 have e2: \<open>read_escape (p @ (t0 @ r)) = Some (d, t0 @ r)\<close> by simp
          from read_escape_ctx[OF e2, of \<open>t0 @ r'\<close>] x1
            have e3: \<open>read_escape (x1 @ r') = Some (d, t0 @ r')\<close> by simp
          have len: \<open>length t0 < length x\<close> using x1 xc by simp
          from "1.IH"[rule_format, OF len, of qs] rr r1
            have rr': \<open>read_str (t0 @ r') = Some (qs, r')\<close> by simp
          show ?thesis using True xc qt nl e3 rr' ps by simp
        next
          case nb: False
          show ?thesis
          proof (cases \<open>c = dollar \<and> (case x1 @ r of b # _ \<Rightarrow> b = curlyo | [] \<Rightarrow> False)\<close>)
            case True
            with rs qt nl nb obtain p r1 qs where e: \<open>scan_path [] [] (tl (x1 @ r)) = Some (p, r1)\<close>
              and rr: \<open>read_str r1 = Some (qs, r)\<close> and ps: \<open>ps = Hole p # qs\<close>
              by (auto split: option.splits)
            have x1ne': \<open>x1 \<noteq> []\<close>
            proof
              assume \<open>x1 = []\<close>
              with scan_path_suffix[OF e] read_str_suffix[OF rr] show False
                by (cases r) auto
            qed
            then obtain b x2 where xb: \<open>x1 = b # x2\<close> by (cases x1) auto
            with True have cd: \<open>c = dollar\<close> and bc: \<open>b = curlyo\<close> by auto
            from e xb have e1: \<open>scan_path [] [] (x2 @ r) = Some (p, r1)\<close> by simp
            from suffix_split[OF scan_path_suffix[THEN conjunct1, OF e1]
                read_str_suffix[THEN conjunct1, OF rr]]
            obtain p' t0 where x2: \<open>x2 = p' @ t0\<close> and r1: \<open>r1 = t0 @ r\<close> by blast
            from e1 r1 x2 have e2: \<open>scan_path [] [] (p' @ (t0 @ r)) = Some (p, t0 @ r)\<close> by simp
            from scan_path_ctx[OF e2, of \<open>t0 @ r'\<close>] x2
              have e3: \<open>scan_path [] [] (x2 @ r') = Some (p, t0 @ r')\<close> by simp
            have len: \<open>length t0 < length x\<close> using x2 xb xc by simp
            from "1.IH"[rule_format, OF len, of qs] rr r1
              have rr': \<open>read_str (t0 @ r') = Some (qs, r')\<close> by simp
            show ?thesis using xc xb cd bc e3 rr' ps qt nl nb by simp
          next
            case False
            with rs qt nl nb obtain qs where rr: \<open>read_str (x1 @ r) = Some (qs, r)\<close>
              and ps: \<open>ps = add_char c qs\<close>
              by (auto split: option.splits)
            from x1ne[OF rr] obtain b x2 where xb: \<open>x1 = b # x2\<close> by (cases x1) auto
            have len: \<open>length x1 < length x\<close> using xc by simp
            from "1.IH"[rule_format, OF len, of qs] rr
              have rr': \<open>read_str (x1 @ r') = Some (qs, r')\<close> by simp
            from False xb have \<open>\<not> (c = dollar \<and> (case x1 @ r' of b # _ \<Rightarrow> b = curlyo | [] \<Rightarrow> False))\<close>
              by simp
            then show ?thesis using xc xb qt nl nb rr' ps by (simp, blast)
          qed
        qed
      qed
    qed
  qed
qed
(*>*)

lemma read_str_lexeme:
  \<open>read_str (u @ r) = Some (ps, r) \<Longrightarrow> read_str u = Some (ps, [])\<close>
  using read_str_ctx[of u r ps \<open>[]\<close>] by simp

lemma read_char_lexeme:
  \<open>read_char (u @ r) = Some (c, r) \<Longrightarrow> read_char u = Some (c, [])\<close>
proof -
  assume h: \<open>read_char (u @ r) = Some (c, r)\<close>
  show ?thesis
  proof (cases u)
    case Nil
    with read_char_suffix[OF h] show ?thesis by simp
  next
    case (Cons c0 u1)
    show ?thesis
    proof (cases \<open>c0 = bslash\<close>)
      case True
      with h Cons obtain d r1 where e: \<open>read_escape (u1 @ r) = Some (d, r1)\<close>
        and r1: \<open>r1 = cq # r\<close> and cd: \<open>c = d\<close>
        by (auto simp: read_char_def Let_def split: option.splits list.splits if_splits)
      have \<open>suffix r r1\<close> using r1 by (auto simp: suffix_def)
      from suffix_split[OF read_escape_suffix[THEN conjunct1, OF e] this]
      obtain p t0 where u1: \<open>u1 = p @ t0\<close> and t0: \<open>r1 = t0 @ r\<close> by blast
      from t0 r1 have \<open>t0 @ r = cq # r\<close> by simp
      then have t0': \<open>t0 = [cq]\<close> by (rule app_eq_Cons_self)
      from e u1 t0' r1 have e2: \<open>read_escape (p @ (cq # r)) = Some (d, cq # r)\<close> by simp
      from read_escape_ctx[OF e2, of \<open>[cq]\<close>] have \<open>read_escape (p @ [cq]) = Some (d, [cq])\<close> by simp
      then show ?thesis using Cons True u1 t0' cd
        by (simp add: read_char_def Let_def is_newline_def)
    next
      case nb: False
      with h Cons have nq: \<open>c0 \<noteq> cq \<and> \<not> is_newline c0\<close> and cl: \<open>c = c0 \<and> u1 @ r = cq # r\<close>
        by (auto simp: read_char_def Let_def split: option.splits list.splits if_splits)
      from app_eq_Cons_self[of u1 r cq] cl have \<open>u1 = [cq]\<close> by simp
      then show ?thesis using Cons nb nq cl by (simp add: read_char_def Let_def)
    qed
  qed
qed

end
