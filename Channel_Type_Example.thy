theory Channel_Type_Example
  imports Channel_Type
begin

chantype ch_single =
  chnat :: nat

chantype ch_two =
  chbool :: bool
  chint :: int

chantype ch_buffer =
  inp :: unit
  outp :: nat
  mod :: bool

thm ch_buffer.inp_wb_prism

thm ch_buffer.codeps

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

end