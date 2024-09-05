theory Channel_Type_Example
  imports Channel_Type
begin

chantype ch_single =
  chnat :: nat

chantype ch_two =
  chbool :: bool
  chint :: int

chantype ct =
  a1 :: int
  a2 :: int
  a3 :: int
  a4 :: int
  a5 :: int
  a6 :: int
  a7 :: int
  a8 :: int

thm ct.prism_chanreps

chantype ch_buffer =
  inp :: unit
  outp :: nat
  modif :: bool

thm ch_buffer.inp_wb_prism

thm ch_buffer.codeps

thm ch_buffer.prism_chanreps

chantype ch_buffer2 =
  inp2 :: unit
  outp2 :: nat
  mod2 :: bool

chantype chbig =
  a1 :: int
  a2 :: int
  a3 :: int
  a4 :: int
  a5 :: int
  a6 :: bool
  a7 :: bool
  a8 :: unit
  a9 :: nat

chantype ('a, 'b) ty =
  p1 :: "'a list"
  p2 :: "nat"
  p3 :: bool

end