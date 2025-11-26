theory Example_Programs
  imports "UTP_IMP"
begin

declare [[literal_variables]]

alphabet st = 
  x :: int
  y :: int

record_default st

subsection \<open> Toy Programs \<close>

definition myprog1 :: "st prog" where
"myprog1 = x := 0 ; while x < 10 do x := x + 1 od"

definition myprog2 :: "st prog" where
"myprog2 = (x := 0) \<sqinter> (x := 3) \<sqinter> (x := 1)"

execute myprog1

value "final_states myprog1 default"

value "exec_prog myprog1"

lemma "H{True} myprog1 {x = 10}"
  unfolding myprog1_def
  apply (sequence "x = 0")
   apply assign
   apply subst_eval'
  apply simp
  apply (while "x \<le> 10")
    apply simp
   apply assign
   apply subst_eval'
   apply simp
  apply simp
  done

value "final_states myprog2 default"

value "exec_prog myprog2"

subsection \<open> Euclidean algorithm \<close>

program Eucl "(X :: int, Y :: int)" over st =
"x := X; 
 y := Y; 
 while x \<noteq> y 
 do if x < y 
    then y := y - x 
    else x := x - y 
    fi 
 od"

execute "Eucl(21, 15)"

lemma Eucl_correct: "H{True} Eucl(X, Y) {\<bar>x\<bar> = gcd X Y}"
  apply (simp add: Eucl_def)
  apply (sequence "x = X")
   apply assign
   apply subst_eval'
   apply simp
  apply (sequence "x = X \<and> y = Y")
   apply assign
     apply subst_eval'
   apply simp
  apply (while "gcd x y = gcd X Y")
    apply simp
   apply if_then_else
    apply assign
  apply subst_eval
    apply (metis (no_types, lifting) SEXP_def gcd.commute gcd_diff1 tautI)
   apply assign
  apply subst_eval
   apply (metis (no_types, lifting) SEXP_def gcd_diff1 tautI)
  apply expr_simp
  done

program Eucl_ann "(X :: int, Y :: int)" over st =
"x := X; 
 y := Y; 
 while x \<noteq> y 
 invariant gcd X Y = gcd x y 
 do 
    if x < y 
    then y := y - x 
    else x := x - y 
    fi 
 od"

lemma Eucl_correct': "H{True} Eucl_ann(X, Y) {\<bar>x\<bar> = gcd X Y}"
  apply vcg
  apply (metis gcd.commute gcd_diff1)
  apply (simp add: gcd_diff1)
  done

end