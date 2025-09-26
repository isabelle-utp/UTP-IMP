theory Example_Programs
  imports "UTP_IMP"
begin

declare [[literal_variables]]

alphabet st = 
  x :: int
  y :: int

record_default st

definition myprog1 :: "st prog" where
"myprog1 = x := 0 ;; while x < 10 do x := x + 1 od"

definition myprog2 :: "st prog" where
"myprog2 = (x := 0) + (x := 3) + (x := 1)"

definition Eucl :: "int \<Rightarrow> int \<Rightarrow> st prog" where
"Eucl X Y = (x := X ;; y := Y ;; while x \<noteq> y do if x < y then y := y - x else x := x - y fi od)"

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

value "final_states (Eucl 21 15) default"

value "exec_prog (Eucl 21 15)"

end