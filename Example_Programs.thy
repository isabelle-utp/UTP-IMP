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

value "final_states myprog2 default"

value "final_states (Eucl 21 15) default"

end