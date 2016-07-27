theory frac
imports AutoCorres
  GCD "~~/src/HOL/Number_Theory/Primes" 
begin

install_C_file "frac.c"

context frac
begin

  thm abs_body_def

end


autocorres [ ts_force pure = , ts_force nondet =  abs add gcd, unsigned_word_abs = gcd ] "frac.c"

context frac
begin

  thm abs'_def
  thm add'_def
  thm frac'_def
  thm gcd'_def

  section "the abs function"

  thm abs'_def

  term "abs'" 

  lemma "\<lbrace> %s. True \<rbrace> func \<lbrace> % rv s. rv = 0 \<rbrace>!"
    oops

  lemma "\<lbrace> %s. abs a \<le> INT_MAX   \<rbrace> abs' a  \<lbrace> %r s. r = abs a \<rbrace>!"
    unfolding abs'_def 
    apply wp 
    apply simp
    apply safe
    proof -
      fix a
      assume A: "\<bar>a\<bar> \<le> INT_MAX"
      assume al0: "a < 0"
      have "-a = \<bar>a\<bar>" using al0 by auto  
    also
      have "\<dots> \<le> INT_MAX" by fact
    finally
      show "-a \<le> INT_MAX" .

      have "- INT_MAX - 1 \<le> - INT_MAX" by simp
    also
      have "- INT_MAX \<le> - \<bar>a\<bar>" using A by fastforce
    also
      have " - \<bar>a\<bar> = a" using al0 by simp
    also
      have "a \<le> -a" using al0 by simp
    finally       
      show "- INT_MAX - 1 \<le> - a" .
    qed 
    
    thm abs'_def
  lemma abs_wp: (* [wp] *)
    "\<lbrace> %s. INT_MIN < a \<and> a \<le> INT_MAX  \<rbrace> abs' a  \<lbrace> %r s. r = abs a  \<rbrace>!"
    unfolding abs'_def 
    apply wp by (auto simp add: INT_MAX_def INT_MIN_def)


  section "the gcd function"

  thm gcd'_def

  text " a suggested correctness property of gcd"
  lemma gcd_wp: (* [wp]: *)
    "\<lbrace> P (gcd a b) \<rbrace> gcd' a b \<lbrace> P \<rbrace>!" sorry

  
  section "the frac function"

  thm frac'_def

  term frac_t_C (* a constructor for the frac structure, but it takes two '32 signed word' not ints! *)
 
  lemma frac_wp: 
    "\<lbrace> %s. True \<rbrace> frac' a b \<lbrace> %rv s. (\<exists>x y.  y>0 \<and> gcd x y = 1 \<and> a*y=b*x \<and> rv = frac_t_C (of_int x) (of_int y) ) \<rbrace>!" sorry

  

  section "the add function"


  thm add'_def

  (* TODO: formulate correctness properties of add *)




end

end