import MathlibExtra.Fresh

import LC.NV.UTLC.Alpha

import LC.NV.UTLC.Sub.ReplaceFree
import LC.NV.UTLC.Sub.Rename
import LC.NV.UTLC.Sub.SubIsDef


set_option autoImplicit false


open Term_


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

-- if x ≠ y then ( λ y . P ) [ x := N ] = ( λ y . P [ x := N ] )

| abs_diff_nel
  (y : Symbol_)
  (P : Term_)
  (x : Symbol_)
  (N : Term_)
  (P' : Term_) :
  ¬ x = y →
  x ∉ (abs_ y P).free_var_set →
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


-- is_sub_fresh M x N L means M [ x := N ] = L
inductive is_sub_fresh : Term_ → Symbol_ → Term_ → Term_ → Prop

| var_same
  (y : Symbol_)
  (x : Symbol_)
  (N : Term_) :
  x = y →
  is_sub_fresh (var_ y) x N N

| var_diff
  (y : Symbol_)
  (x : Symbol_)
  (N : Term_) :
  ¬ x = y →
  is_sub_fresh (var_ y) x N (var_ y)

| app
  (P : Term_)
  (Q : Term_)
  (x : Symbol_)
  (N : Term_)
  (P' : Term_)
  (Q' : Term_) :
  is_sub_fresh P x N P' →
  is_sub_fresh Q x N Q' →
  is_sub_fresh (app_ P Q) x N (app_ P' Q')

| abs_same
  (y : Symbol_)
  (P : Term_)
  (x : Symbol_)
  (N : Term_) :
  x = y →
  is_sub_fresh (abs_ y P) x N (abs_ y P)

| abs_diff
  (y : Symbol_)
  (P : Term_)
  (x : Symbol_)
  (N : Term_)
  (P' : Term_) :
  ¬ x = y →
  y ∉ N.free_var_set →
  is_sub_fresh P x N P' →
  is_sub_fresh (abs_ y P) x N (abs_ y P')

| abs_diff_fresh
  (y : Symbol_)
  (P : Term_)
  (x : Symbol_)
  (N : Term_)
  (y' : Symbol_)
  (P' : Term_) :
  ¬ x = y →
  y ∈ N.free_var_set →
  y' ∉ P.var_set →
  y' ∉ N.var_set →
  is_sub_fresh (rename y y' P) x N P' →
  is_sub_fresh (abs_ y P) x N (abs_ y' P')


-------------------------------------------------------------------------------


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
  are_alpha_equiv (abs_ z (replace_free y (var_ z) P)) (abs_ y P) →
  is_sub_alt (replace_free y (var_ z) P) x N P' →
  is_sub_alt (abs_ y P) x N (abs_ z P')


-------------------------------------------------------------------------------
