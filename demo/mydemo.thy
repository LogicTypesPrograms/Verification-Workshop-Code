
theory mydemo
imports
  "AutoCorres" 
begin

(* Parse the input file. *)
install_C_file  "mydemo.c"

find_theorems name: "body_def"

context mydemo begin

  thm f_body_def
  thm g_body_def


end

(* Abstract the input file. *)
autocorres [ts_force nondet = g] "mydemo.c"

(*   [ts_rules = nondet|pure|option] *)

context mydemo begin

  thm f'_def
  thm g'_def

  lemma "f' 3 = 0" by(simp add: f'_def)
  term ovalidNF
 
  thm whileLoop_add_inv[where M="\<lambda>(a, s). a"]
  term abs
  lemma returns0: "INT_MIN < a \<Longrightarrow> a < INT_MAX \<Longrightarrow>
        \<lbrace> \<lambda>s. True \<rbrace>
           g' a
        \<lbrace> \<lambda>r s. r=0 \<rbrace>!"
     unfolding g'_def
     apply(subst whileLoop_add_inv[where I="\<lambda>a s. INT_MIN < a \<and> a < INT_MAX" and M="\<lambda>(a,s). nat (abs a)"])
     apply(wp)
      by (auto simp add: INT_MIN_def INT_MAX_def) 

end


end
