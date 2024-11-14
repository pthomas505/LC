import MathlibExtra.Fresh

import LC.NV.UTLC.Alpha

import LC.NV.UTLC.Sub.ReplaceFree
import LC.NV.UTLC.Sub.Rename
import LC.NV.UTLC.Sub.SubIsDef


set_option autoImplicit false


open Term_


-- [1]


-- is_sub M x N L means M [ x := N ] = L
inductive is_sub : Term_ → Symbol_ → Term_ → Term_ → Prop

-- if x = y then y [ x := N ] = N
| var_same
  (y : Symbol_)
  (x : Symbol_)
  (N : Term_) :
  x = y →
  is_sub (var_ y) x N N

-- if x ≠ y then y [ x := N ] = y
| var_diff
  (y : Symbol_)
  (x : Symbol_)
  (N : Term_) :
  ¬ x = y →
  is_sub (var_ y) x N (var_ y)

-- (P Q) [ x := N ] = (P [ x := N ] Q [ x := N ])
| app
  (P : Term_)
  (Q : Term_)
  (x : Symbol_)
  (N : Term_)
  (P' : Term_)
  (Q' : Term_) :
  is_sub P x N P' →
  is_sub Q x N Q' →
  is_sub (app_ P Q) x N (app_ P' Q')

-- if x = y then ( λ y . P ) [ x := N ] = ( λ y . P )
| abs_same
  (y : Symbol_)
  (P : Term_)
  (x : Symbol_)
  (N : Term_) :
  x = y →
  is_sub (abs_ y P) x N (abs_ y P)

| abs_diff_nel
  (y : Symbol_)
  (P : Term_)
  (x : Symbol_)
  (N : Term_)
  (P' : Term_) :
  ¬ x = y →
  x ∉ P.free_var_set →
  is_sub P x N P' →
  is_sub (abs_ y P) x N (abs_ y P')

| abs_diff
  (y : Symbol_)
  (P : Term_)
  (x : Symbol_)
  (N : Term_)
  (P' : Term_) :
  ¬ x = y →
  y ∉ N.free_var_set →
  is_sub P x N P' →
  is_sub (abs_ y P) x N (abs_ y P')


-------------------------------------------------------------------------------


-- [2]

inductive is_sub_alt : Term_ → Symbol_ → Term_ → Term_ → Prop

| var_same
  (y : Symbol_)
  (x : Symbol_)
  (N : Term_) :
  x = y →
  is_sub_alt (var_ y) x N N

| var_diff
  (y : Symbol_)
  (x : Symbol_)
  (N : Term_) :
  ¬ x = y →
  is_sub_alt (var_ y) x N (var_ y)

| app
  (P : Term_)
  (Q : Term_)
  (x : Symbol_)
  (N : Term_)
  (P' : Term_)
  (Q' : Term_) :
  is_sub_alt P x N P' →
  is_sub_alt Q x N Q' →
  is_sub_alt (app_ P Q) x N (app_ P' Q')

| abs
  (y : Symbol_)
  (P : Term_)
  (x : Symbol_)
  (N : Term_)
  (P' : Term_)
  (z : Symbol_) :
  z ∉ N.free_var_set →
  are_alpha_equiv_alt (abs_ y P) (abs_ z (replace_free y (var_ z) P)) →
  is_sub_alt (replace_free y (var_ z) P) x N P' →
  is_sub_alt (abs_ y P) x N (abs_ z P')


-------------------------------------------------------------------------------


example
  (y : Symbol_)
  (P : Term_)
  (x : Symbol_)
  (N : Term_)
  (P' : Term_)
  (h1 : is_sub_alt P x N P')
  (h2 : y ∉ N.free_var_set) :
  is_sub_alt (abs_ y P) x N (abs_ y P') :=
  by
    apply is_sub_alt.abs
    · exact h2
    · rw [replace_free_self]
      apply are_alpha_equiv_alt.refl
    · rw [replace_free_self]
      exact h1


example
  (y : Symbol_)
  (P : Term_)
  (x : Symbol_)
  (N : Term_)
  (P' : Term_)
  (h1 : is_sub_alt P x N P')
  (h2 : x ∉ P.free_var_set) :
  is_sub_alt (abs_ y P) x N (abs_ y P') :=
  by
    sorry
