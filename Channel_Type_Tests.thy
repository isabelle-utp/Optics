theory Channel_Type_Tests
  imports Channel_Type
begin

(* Create a very large channel type (50 channels) to test proof and instantiation *)

ML \<open> val chans = map (fn n => ("a" ^ Int.toString n, "int")) (0 upto 49); \<close>

setup \<open> Channel_Type.compile_chantype ("ch_big", chans) \<close>

print_theorems

thm ch_big.prism_chanreps

end