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

end