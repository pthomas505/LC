import LC.NV.UTLC.Binders
import LC.NV.UTLC.Sub.ReplaceFree


set_option autoImplicit false


open Term_


-- sub_is_def_v3 M x N means M [ x := N ] is defined
inductive sub_is_def_v3 : Term_ → Symbol_ → Term_ → Prop

-- y [ x := N ] is defined
| var
  (y : Symbol_)
  (x : Symbol_)
  (N : Term_) :
  sub_is_def_v3 (var_ y) x N

-- P [ x := N ] is defined → Q [ x := N ] is defined → (P Q) [ x := N ] is defined
| app
  (P : Term_)
  (Q : Term_)
  (x : Symbol_)
  (N : Term_) :
  sub_is_def_v3 P x N →
  sub_is_def_v3 Q x N →
  sub_is_def_v3 (app_ P Q) x N

-- x = y → ( λ y . P ) [ x := N ] is defined
| abs_same
  (y : Symbol_)
  (P : Term_)
  (x : Symbol_)
  (N : Term_) :
  x = y →
  sub_is_def_v3 (abs_ y P) x N

| abs_diff_1
  (y : Symbol_)
  (P : Term_)
  (x : Symbol_)
  (N : Term_) :
  ¬ x = y →
  x ∉ P.free_var_set →
  sub_is_def_v3 (abs_ y P) x N

| abs_diff_2
  (y : Symbol_)
  (P : Term_)
  (x : Symbol_)
  (N : Term_) :
  ¬ x = y →
  y ∉ N.free_var_set →
  sub_is_def_v3 P x N →
  sub_is_def_v3 (abs_ y P) x N


-------------------------------------------------------------------------------


-- [1]
lemma lemma_1_2_5_i_a
  (M : Term_)
  (x : Symbol_)
  (N : Term_)
  (h1 : x ∉ M.free_var_set) :
  sub_is_def_v3 M x N :=
  by
  induction M
  case var_ y =>
    exact sub_is_def_v3.var y x N

  case app_ P Q ih_P ih_Q =>
    unfold Term_.free_var_set at h1
    simp at h1
    obtain ⟨h1_left, h1_right⟩ := h1
    specialize ih_P h1_left
    specialize ih_Q h1_right
    exact sub_is_def_v3.app P Q x N ih_P ih_Q

  case abs_ y P _ =>
    by_cases h_xy : x = y
    · exact sub_is_def_v3.abs_same y P x N h_xy
    · apply sub_is_def_v3.abs_diff_1 y P x N h_xy
      unfold free_var_set at h1
      simp at h1
      tauto


-- [1]
lemma lemma_1_2_5_ii_right
  (e1 : Term_)
  (v : Symbol_)
  (e2 : Term_)
  (z : Symbol_)
  (h1 : sub_is_def_v3 e1 v e2)
  (h2 : z ∈ (replace_free v e2 e1).free_var_set) :
  (z ∈ e1.free_var_set ∧ ¬ v = z) ∨ (z ∈ e2.free_var_set ∧ v ∈ e1.free_var_set) :=
  by
    induction h1
    case var y x N =>
      simp only [free_var_set]
      simp

      unfold replace_free at h2
      split_ifs at h2
      case pos c1 =>
        right
        exact ⟨h2, c1⟩
      case neg c1 =>
        unfold free_var_set at h2
        simp at h2
        left
        rw [h2]
        exact ⟨rfl, c1⟩
    case app P Q x N ih_1 ih_2 ih_3 ih_4 =>
      simp only [free_var_set]
      simp

      unfold replace_free at h2
      simp only [free_var_set] at h2
      simp at h2
      cases h2
      case inl h2_left =>
        tauto
      case inr h2_right =>
        tauto
    case abs_same y P x N ih =>
      unfold replace_free at h2
      split_ifs at h2
      unfold free_var_set at h2
      simp at h2

      left
      simp only [free_var_set]
      simp
      rw [ih]
      tauto
    case abs_diff_1 y P x N ih_1 ih_2 =>
      unfold replace_free at h2
      split_ifs at h2
      unfold free_var_set at h2
      simp at h2

      left
      simp only [free_var_set]
      simp

      have s1 : (replace_free x N P) = P := lemma_1_2_5_i_b P x N ih_2
      rw [s1] at h2

      constructor
      · exact h2
      · intro contra
        rw [← contra] at h2
        tauto
    case abs_diff_2 y P x N ih_1 ih_2 ih_3 ih_4 =>
      unfold replace_free at h2
      split_ifs at h2
      unfold free_var_set at h2
      simp at h2

      simp only [free_var_set]
      simp
      tauto


-- [1]
lemma lemma_1_2_5_ii_left
  (M : Term_)
  (x : Symbol_)
  (N : Term_)
  (z : Symbol_)
  (h1 : sub_is_def_v3 M x N)
  (h2 : (z ∈ M.free_var_set ∧ ¬ x = z) ∨ (z ∈ N.free_var_set ∧ x ∈ M.free_var_set)) :
  z ∈ (replace_free x N M).free_var_set := sorry


-- [1]
lemma lemma_1_2_5_ii
  (M : Term_)
  (x : Symbol_)
  (N : Term_)
  (z : Symbol_)
  (H1 : sub_is_def_v3 M x N) :
  z ∈ (replace_free x N M).free_var_set ↔
    (z ∈ M.free_var_set ∧ ¬ x = z) ∨ (z ∈ N.free_var_set ∧ x ∈ M.free_var_set) :=
sorry


-- [1]
lemma lemma_1_2_5_iii_a
  (e : Term_)
  (v : Symbol_) :
  sub_is_def_v3 e v (var_ v) :=
  by
    induction e
    case var_ x =>
      apply sub_is_def_v3.var
    case app_ P Q ih_1 ih_2 =>
      apply sub_is_def_v3.app
      · exact ih_1
      · exact ih_2
    case abs_ x P ih =>
      by_cases c1 : v = x
      case pos =>
        rw [c1]
        apply sub_is_def_v3.abs_same
        rfl
      case neg =>
        apply sub_is_def_v3.abs_diff_2
        · exact c1
        · unfold free_var_set
          simp
          intro contra
          apply c1
          rw [contra]
        · exact ih


-- [1]
lemma lemma_1_2_6_a_left
  (M N L : Term_)
  (x y : Symbol_)
  (h1 : sub_is_def_v3 M x N)
  (h2 : sub_is_def_v3 N y L)
  (h3 : sub_is_def_v3 (replace_free x N M) y L)
  (h4 : ¬ x = y)
  (h5 : x ∉ L.free_var_set ∨ y ∉ M.free_var_set) :
  sub_is_def_v3 M y L := sorry


-- [1]
lemma lemma_1_2_6_a_right
  (M N L : Term_)
  (x y : Symbol_)
  (h1 : sub_is_def_v3 M x N)
  (h2 : sub_is_def_v3 N y L)
  (h3 : sub_is_def_v3 (replace_free x N M) y L)
  (h4 : ¬ x = y)
  (h5 : x ∉ L.free_var_set ∨ y ∉ M.free_var_set) :
  sub_is_def_v3 (replace_free y L M) x (replace_free y L N) := sorry


-- [1]
lemma lemma_1_2_6_b
  (M N L : Term_)
  (x y : Symbol_)
  (h1 : sub_is_def_v3 M x N)
  (h2 : sub_is_def_v3 N y L)
  (h3 : sub_is_def_v3 (replace_free x N M) y L)
  (h4 : ¬ x = y)
  (h5 : x ∉ L.free_var_set ∨ y ∉ M.free_var_set) :
  replace_free y L (replace_free x N M) =
    replace_free x (replace_free y L M) (replace_free y L N) := sorry
