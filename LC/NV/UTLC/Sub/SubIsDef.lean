import MathlibExtra.Fresh

import LC.NV.UTLC.Sub.ReplaceFree
import LC.NV.UTLC.Sub.Rename
import LC.NV.UTLC.Alpha


set_option autoImplicit false


open Term_


-- sub_is_def M x N means M [ x := N ] is defined
inductive sub_is_def : Term_ → Symbol_ → Term_ → Prop

-- y [ x := N ] is defined
| var
  (y : Symbol_)
  (x : Symbol_)
  (N : Term_) :
  sub_is_def (var_ y) x N

-- P [ x := N ] is defined → Q [ x := N ] is defined → (P Q) [ x := N ] is defined
| app
  (P : Term_)
  (Q : Term_)
  (x : Symbol_)
  (N : Term_) :
  sub_is_def P x N →
  sub_is_def Q x N →
  sub_is_def (app_ P Q) x N

-- x = y → ( λ y . P ) [ x := N ] is defined
| abs_same
  (y : Symbol_)
  (P : Term_)
  (x : Symbol_)
  (N : Term_) :
  x = y →
  sub_is_def (abs_ y P) x N

| abs_diff_nel
  (y : Symbol_)
  (P : Term_)
  (x : Symbol_)
  (N : Term_) :
  ¬ x = y →
  x ∉ P.free_var_set →
  sub_is_def (abs_ y P) x N

| abs_diff
  (y : Symbol_)
  (P : Term_)
  (x : Symbol_)
  (N : Term_) :
  ¬ x = y →
  y ∉ N.free_var_set →
  sub_is_def P x N →
  sub_is_def (abs_ y P) x N
