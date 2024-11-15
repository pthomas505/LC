import MathlibExtra.Fresh

import LC.NV.UTLC.Alpha

import LC.NV.UTLC.Sub.ReplaceFree
import LC.NV.UTLC.Sub.ReplaceVar
import LC.NV.UTLC.Sub.SubIsDef


set_option autoImplicit false


open Term_


inductive is_sub_v0 : Term_ → Symbol_ → Term_ → Term_ → Prop

-- if x = y then y [ x := N ] = N
| var_same
  (y : Symbol_)
  (x : Symbol_)
  (N : Term_) :
  x = y →
  is_sub_v0 (var_ y) x N N

-- if x ≠ y then y [ x := N ] = y
| var_diff
  (y : Symbol_)
  (x : Symbol_)
  (N : Term_) :
  ¬ x = y →
  is_sub_v0 (var_ y) x N (var_ y)

-- (P Q) [ x := N ] = (P [ x := N ] Q [ x := N ])
| app
  (P : Term_)
  (Q : Term_)
  (x : Symbol_)
  (N : Term_)
  (P' : Term_)
  (Q' : Term_) :
  is_sub_v0 P x N P' →
  is_sub_v0 Q x N Q' →
  is_sub_v0 (app_ P Q) x N (app_ P' Q')

| abs_diff_nel
  (y : Symbol_)
  (P : Term_)
  (x : Symbol_)
  (N : Term_) :
  x ∉ (abs_ y P).free_var_set →
  is_sub_v0 (abs_ y P) x N (abs_ y P)

| abs_diff
  (y : Symbol_)
  (P : Term_)
  (x : Symbol_)
  (N : Term_)
  (P' : Term_) :
  ¬ x = y →
  y ∉ N.free_var_set →
  is_sub_v0 P x N P' →
  is_sub_v0 (abs_ y P) x N (abs_ y P')


-------------------------------------------------------------------------------


inductive is_sub_v1 : Term_ → Symbol_ → Term_ → Term_ → Prop

-- if x = y then y [ x := N ] = N
| var_same
  (y : Symbol_)
  (x : Symbol_)
  (N : Term_) :
  x = y →
  is_sub_v1 (var_ y) x N N

-- if x ≠ y then y [ x := N ] = y
| var_diff
  (y : Symbol_)
  (x : Symbol_)
  (N : Term_) :
  ¬ x = y →
  is_sub_v1 (var_ y) x N (var_ y)

-- (P Q) [ x := N ] = (P [ x := N ] Q [ x := N ])
| app
  (P : Term_)
  (Q : Term_)
  (x : Symbol_)
  (N : Term_)
  (P' : Term_)
  (Q' : Term_) :
  is_sub_v1 P x N P' →
  is_sub_v1 Q x N Q' →
  is_sub_v1 (app_ P Q) x N (app_ P' Q')

-- if x = y then ( λ y . P ) [ x := N ] = ( λ y . P )
| abs_same
  (y : Symbol_)
  (P : Term_)
  (x : Symbol_)
  (N : Term_) :
  x = y →
  is_sub_v1 (abs_ y P) x N (abs_ y P)

| abs_diff_nel
  (y : Symbol_)
  (P : Term_)
  (x : Symbol_)
  (N : Term_) :
  ¬ x = y →
  x ∉ P.free_var_set →
  is_sub_v1 (abs_ y P) x N (abs_ y P)

| abs_diff
  (y : Symbol_)
  (P : Term_)
  (x : Symbol_)
  (N : Term_)
  (P' : Term_) :
  ¬ x = y →
  y ∉ N.free_var_set →
  is_sub_v1 P x N P' →
  is_sub_v1 (abs_ y P) x N (abs_ y P')


-------------------------------------------------------------------------------


-- [1]

/--
  is_sub_v3 M x N L := True if and only if L is the result of replacing each free occurrence of x in M by N and no free occurrence of a variable in N becomes a bound occurrence in L.
  M [ x := N ] = L
-/
inductive is_sub_v3 : Term_ → Symbol_ → Term_ → Term_ → Prop

-- if x = y then y [ x := N ] = N
| var_same
  (y : Symbol_)
  (x : Symbol_)
  (N : Term_) :
  x = y →
  is_sub_v3 (var_ y) x N N

-- if x ≠ y then y [ x := N ] = y
| var_diff
  (y : Symbol_)
  (x : Symbol_)
  (N : Term_) :
  ¬ x = y →
  is_sub_v3 (var_ y) x N (var_ y)

-- (P Q) [ x := N ] = (P [ x := N ] Q [ x := N ])
| app
  (P : Term_)
  (Q : Term_)
  (x : Symbol_)
  (N : Term_)
  (P' : Term_)
  (Q' : Term_) :
  is_sub_v3 P x N P' →
  is_sub_v3 Q x N Q' →
  is_sub_v3 (app_ P Q) x N (app_ P' Q')

-- if x = y then ( λ y . P ) [ x := N ] = ( λ y . P )
| abs_same
  (y : Symbol_)
  (P : Term_)
  (x : Symbol_)
  (N : Term_) :
  x = y →
  is_sub_v3 (abs_ y P) x N (abs_ y P)

| abs_diff_nel
  (y : Symbol_)
  (P : Term_)
  (x : Symbol_)
  (N : Term_)
  (P' : Term_) :
  ¬ x = y →
  x ∉ P.free_var_set →
  is_sub_v3 P x N P' →
  is_sub_v3 (abs_ y P) x N (abs_ y P')

| abs_diff
  (y : Symbol_)
  (P : Term_)
  (x : Symbol_)
  (N : Term_)
  (P' : Term_) :
  ¬ x = y →
  y ∉ N.free_var_set →
  is_sub_v3 P x N P' →
  is_sub_v3 (abs_ y P) x N (abs_ y P')


-------------------------------------------------------------------------------


-- [2]

inductive is_sub_v4 : Term_ → Symbol_ → Term_ → Term_ → Prop

| var_same
  (y : Symbol_)
  (x : Symbol_)
  (N : Term_) :
  x = y →
  is_sub_v4 (var_ y) x N N

| var_diff
  (y : Symbol_)
  (x : Symbol_)
  (N : Term_) :
  ¬ x = y →
  is_sub_v4 (var_ y) x N (var_ y)

| app
  (P : Term_)
  (Q : Term_)
  (x : Symbol_)
  (N : Term_)
  (P' : Term_)
  (Q' : Term_) :
  is_sub_v4 P x N P' →
  is_sub_v4 Q x N Q' →
  is_sub_v4 (app_ P Q) x N (app_ P' Q')

| abs
  (y : Symbol_)
  (P : Term_)
  (x : Symbol_)
  (N : Term_)
  (P' : Term_)
  (z : Symbol_) :
  z ∉ N.free_var_set →
  are_alpha_equiv_v2 (abs_ y P) (abs_ z (replace_free y (var_ z) P)) →
  is_sub_v4 (replace_free y (var_ z) P) x N P' →
  is_sub_v4 (abs_ y P) x N (abs_ z P')


-------------------------------------------------------------------------------
