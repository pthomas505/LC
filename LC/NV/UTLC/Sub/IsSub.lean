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


-- is_sub_ M x N L means M [ x := N ] = L
inductive is_sub_ : Term_ → Symbol_ → Term_ → Term_ → Prop

-- if x = y then y [ x := N ] = N
| var_same
  (y : Symbol_)
  (x : Symbol_)
  (N : Term_) :
  x = y →
  is_sub_ (var_ y) x N N

-- if x ≠ y then y [ x := N ] = y
| var_diff
  (y : Symbol_)
  (x : Symbol_)
  (N : Term_) :
  ¬ x = y →
  is_sub_ (var_ y) x N (var_ y)

-- (P Q) [ x := N ] = (P [ x := N ] Q [ x := N ])
| app
  (P : Term_)
  (Q : Term_)
  (x : Symbol_)
  (N : Term_)
  (P' : Term_)
  (Q' : Term_) :
  is_sub_ P x N P' →
  is_sub_ Q x N Q' →
  is_sub_ (app_ P Q) x N (app_ P' Q')

-- if x = y then ( λ y . P ) [ x := N ] = ( λ y . P )
| abs_same
  (y : Symbol_)
  (P : Term_)
  (x : Symbol_)
  (N : Term_) :
  x = y →
  is_sub_ (abs_ y P) x N (abs_ y P)

-- if x ≠ y then ( λ y . P ) [ x := N ] = ( λ y . P [ x := N ] )

| abs_diff_nel
  (y : Symbol_)
  (P : Term_)
  (x : Symbol_)
  (N : Term_)
  (P' : Term_) :
  ¬ x = y →
  x ∉ P.free_var_set →
  is_sub_ P x N P' →
  is_sub_ (abs_ y P) x N (abs_ y P')

| abs_diff
  (y : Symbol_)
  (P : Term_)
  (x : Symbol_)
  (N : Term_)
  (P' : Term_) :
  ¬ x = y →
  y ∉ N.free_var_set →
  is_sub_ P x N P' →
  is_sub_ (abs_ y P) x N (abs_ y P')


example
  (e1 e2 e3 : Term_)
  (v : Symbol_)
  (h1 : is_sub e1 v e2 e3) :
  is_sub_ e1 v e2 e3 :=
  by
    induction h1
    case var_same y x N ih =>
      apply is_sub_.var_same
      exact ih
    case var_diff y x N ih =>
      apply is_sub_.var_diff
      exact ih
    case app P Q x N P' Q' ih_1 ih_2 ih_3 ih_4 =>
      apply is_sub_.app
      · exact ih_3
      · exact ih_4
    case abs_same y P x N ih_1 =>
      apply is_sub_.abs_same
      · exact ih_1
    case abs_diff_nel y P x N P' ih_1 ih_2 ih_3 ih_4 =>
      unfold free_var_set at ih_2
      simp at ih_2
      have s1 : x ∉ P.free_var_set := by tauto
      apply is_sub_.abs_diff_nel
      · exact ih_1
      · exact s1
      · exact ih_4
    case abs_diff y P x N P' ih_1 ih_2 ih_3 ih_4 =>
      apply is_sub_.abs_diff
      · exact ih_1
      · exact ih_2
      · exact ih_4


example
  (e1 e2 e3 : Term_)
  (v : Symbol_)
  (h1 : is_sub_ e1 v e2 e3) :
  is_sub e1 v e2 e3 :=
  by
    induction h1
    case var_same y x N ih =>
      apply is_sub.var_same
      exact ih
    case var_diff y x N ih =>
      apply is_sub.var_diff
      exact ih
    case app P Q x N P' Q' ih_1 ih_2 ih_3 ih_4 =>
      apply is_sub.app
      · exact ih_3
      · exact ih_4
    case abs_same y P x N ih_1 =>
      apply is_sub.abs_same
      · exact ih_1
    case abs_diff_nel y P x N P' ih_1 ih_2 ih_3 ih_4 =>
      apply is_sub.abs_diff_nel
      · exact ih_1
      · unfold free_var_set
        simp
        intro a1
        contradiction
      · exact ih_4
    case abs_diff y P x N P' ih_1 ih_2 ih_3 ih_4 =>
      apply is_sub.abs_diff
      · exact ih_1
      · exact ih_2
      · exact ih_4


-------------------------------------------------------------------------------


-- https://faculty.iiit.ac.in/~venkatesh.choppella/popl/current-topics/lambda-calculus-1/index.html#org6f14feb

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
  (z : Symbol_)
  (P' : Term_) :
  ¬ x = y →
  y ∈ N.free_var_set →
  z ∉ P.var_set →
  z ∉ N.var_set →
  ¬ z = x →
  ¬ z = y →
  is_sub_fresh (rename y z P) x N P' →
  is_sub_fresh (abs_ y P) x N (abs_ z P')


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
