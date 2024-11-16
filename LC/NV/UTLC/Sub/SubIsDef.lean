import LC.NV.UTLC.Binders
import LC.NV.UTLC.Sub.ReplaceFree


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


-------------------------------------------------------------------------------


-- [1]
lemma lemma_1_2_5_i_a
  (M : Term_)
  (x : Symbol_)
  (N : Term_)
  (h1 : x ∉ M.free_var_set) :
  sub_is_def M x N :=
  by
  induction M
  case var_ y =>
    exact sub_is_def.var y x N

  case app_ P Q ih_P ih_Q =>
    unfold Term_.free_var_set at h1
    simp at h1
    obtain ⟨h1_left, h1_right⟩ := h1
    specialize ih_P h1_left
    specialize ih_Q h1_right
    exact sub_is_def.app P Q x N ih_P ih_Q

  case abs_ y P _ =>
    by_cases h_xy : x = y
    · exact sub_is_def.abs_same y P x N h_xy
    · apply sub_is_def.abs_diff_nel y P x N h_xy
      unfold free_var_set at h1
      simp at h1
      tauto


-- [1]
lemma lemma_1_2_5_ii_right
(M : Term_)
(x : Symbol_)
(N : Term_)
(z : Symbol_)
(h1 : sub_is_def M x N)
(h2 : z ∈ (replace_free x N M).free_var_set) :
(z ∈ M.free_var_set ∧ x ≠ z) ∨ (z ∈ N.free_var_set ∧ x ∈ M.free_var_set) := sorry


-- [1]
lemma lemma_1_2_5_ii_left
(M : Term_)
(x : Symbol_)
(N : Term_)
(z : Symbol_)
(h1 : sub_is_def M x N)
(h2 : (z ∈ M.free_var_set ∧ x ≠ z) ∨ (z ∈ N.free_var_set ∧ x ∈ M.free_var_set)) :
z ∈ (replace_free x N M).free_var_set := sorry


-- [1]
lemma lemma_1_2_5_ii
{M : Term_}
{x : Symbol_}
{N : Term_}
{z : Symbol_}
(H1 : sub_is_def M x N) :
z ∈ (replace_free x N M).free_var_set ↔
  (z ∈ M.free_var_set ∧ x ≠ z) ∨ (z ∈ N.free_var_set ∧ x ∈ M.free_var_set) :=
sorry


-- [1]
lemma lemma_1_2_5_iii_a
{M : Term_}
{x : Symbol_} :
sub_is_def M x (var_ x) := sorry


-- [1]
lemma lemma_1_2_6_a_left
(M N L : Term_)
(x y : Symbol_)
(h1 : sub_is_def M x N)
(h2 : sub_is_def N y L)
(h3 : sub_is_def (replace_free x N M) y L)
(h4 : x ≠ y)
(h5 : x ∉ L.free_var_set ∨ y ∉ M.free_var_set) :
sub_is_def M y L := sorry


-- [1]
lemma lemma_1_2_6_a_right
(M N L : Term_)
(x y : Symbol_)
(h1 : sub_is_def M x N)
(h2 : sub_is_def N y L)
(h3 : sub_is_def (replace_free x N M) y L)
(h4 : x ≠ y)
(h5 : x ∉ L.free_var_set ∨ y ∉ M.free_var_set) :
sub_is_def (replace_free y L M) x (replace_free y L N) := sorry


-- [1]
lemma lemma_1_2_6_b
(M N L : Term_)
(x y : Symbol_)
(h1 : sub_is_def M x N)
(h2 : sub_is_def N y L)
(h3 : sub_is_def (replace_free x N M) y L)
(h4 : x ≠ y)
(h5 : x ∉ L.free_var_set ∨ y ∉ M.free_var_set) :
replace_free y L (replace_free x N M) =
  replace_free x (replace_free y L M) (replace_free y L N) := sorry
