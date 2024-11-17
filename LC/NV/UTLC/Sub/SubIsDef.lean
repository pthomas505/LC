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
| abs_1
  (y : Symbol_)
  (P : Term_)
  (x : Symbol_)
  (N : Term_) :
  x = y →
  sub_is_def_v3 (abs_ y P) x N

| abs_2
  (y : Symbol_)
  (P : Term_)
  (x : Symbol_)
  (N : Term_) :
  ¬ x = y →
  x ∉ P.free_var_set →
  sub_is_def_v3 (abs_ y P) x N

| abs_3
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
  (e1 : Term_)
  (v : Symbol_)
  (e2 : Term_)
  (h1 : v ∉ e1.free_var_set) :
  sub_is_def_v3 e1 v e2 :=
  by
  induction e1
  case var_ x =>
    exact sub_is_def_v3.var x v e2

  case app_ P Q ih_1 ih_2 =>
    unfold Term_.free_var_set at h1
    simp at h1
    obtain ⟨h1_left, h1_right⟩ := h1
    specialize ih_1 h1_left
    specialize ih_2 h1_right
    exact sub_is_def_v3.app P Q v e2 ih_1 ih_2

  case abs_ x P _ =>
    by_cases c1 : v = x
    · exact sub_is_def_v3.abs_1 x P v e2 c1
    · apply sub_is_def_v3.abs_2 x P v e2 c1
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
    case abs_1 y P x N ih =>
      unfold replace_free at h2
      split_ifs at h2
      unfold free_var_set at h2
      simp at h2

      left
      simp only [free_var_set]
      simp
      rw [ih]
      tauto
    case abs_2 y P x N ih_1 ih_2 =>
      unfold replace_free at h2
      split_ifs at h2
      unfold free_var_set at h2
      simp at h2

      left
      simp only [free_var_set]
      simp

      have s1 : (replace_free x N P) = P := replace_free_not_mem x N P ih_2
      rw [s1] at h2

      constructor
      · exact h2
      · intro contra
        rw [← contra] at h2
        tauto
    case abs_3 y P x N ih_1 ih_2 ih_3 ih_4 =>
      unfold replace_free at h2
      split_ifs at h2
      unfold free_var_set at h2
      simp at h2

      simp only [free_var_set]
      simp
      tauto


-- [1]
lemma lemma_1_2_5_ii_left
  (e1 : Term_)
  (v : Symbol_)
  (e2 : Term_)
  (z : Symbol_)
  (h1 : sub_is_def_v3 e1 v e2)
  (h2 : (z ∈ e1.free_var_set ∧ ¬ v = z) ∨ (z ∈ e2.free_var_set ∧ v ∈ e1.free_var_set)) :
  z ∈ (replace_free v e2 e1).free_var_set :=
  by
    induction h1
    all_goals
      simp only [free_var_set] at h2

      unfold replace_free
    case var y x N =>
      simp at h2

      split_ifs
      case pos c1 =>
        rw [c1] at h2
        tauto
      case neg c1 =>
        unfold free_var_set
        simp
        tauto
    case app P Q x N ih_1 ih_2 ih_3 ih_4 =>
      simp at h2

      unfold free_var_set
      simp
      tauto
    case abs_1 y P x N ih =>
      simp at h2

      split_ifs
      unfold free_var_set
      simp
      tauto
    case abs_2 y P x N ih_1 ih_2 =>
      simp at h2

      split_ifs
      unfold free_var_set
      simp

      have s1 : replace_free x N P = P := replace_free_not_mem x N P ih_2
      rw [s1]

      tauto
    case abs_3 y P x N ih_1 ih_2 ih_3 ih_4 =>
      simp at h2

      split_ifs
      unfold free_var_set
      simp
      cases h2
      case inl c1 =>
        tauto
      case inr c1 =>
        constructor
        · apply ih_4
          tauto
        · obtain ⟨c1_left, c1_right⟩ := c1
          intro contra
          apply ih_2
          rw [contra] at c1_left
          exact c1_left


-- [1]
lemma lemma_1_2_5_ii
  (e1 : Term_)
  (v : Symbol_)
  (e2 : Term_)
  (z : Symbol_)
  (h1 : sub_is_def_v3 e1 v e2) :
  z ∈ (replace_free v e2 e1).free_var_set ↔
    (z ∈ e1.free_var_set ∧ ¬ v = z) ∨ (z ∈ e2.free_var_set ∧ v ∈ e1.free_var_set) :=
  by
    induction h1
    case var y x N =>
      unfold replace_free
      split_ifs
      case pos c1 =>
        simp only [free_var_set]
        simp
        rw [c1]
        tauto
      case neg c1 =>
        simp only [free_var_set]
        simp
        constructor
        · intro a1
          rw [a1]
          tauto
        · intro a1
          tauto
    case app P Q x N ih_1 ih_2 ih_3 ih_4 =>
      unfold replace_free
      simp only [free_var_set]
      simp
      tauto
    case abs_1 y P x N ih =>
      unfold replace_free
      split_ifs
      simp only [free_var_set]
      simp
      rw [ih]
      tauto
    case abs_2 y P x N ih_1 ih_2 =>
      unfold replace_free
      split_ifs
      simp only [free_var_set]
      simp

      have s1 : replace_free x N P = P := replace_free_not_mem x N P ih_2
      rw [s1]

      constructor
      · intro a1
        obtain ⟨a1_left, a1_right⟩ := a1

        have s1 : ¬ x = z :=
        by
          intro contra
          apply ih_2
          rw [contra]
          exact a1_left

        tauto
      · tauto
    case abs_3 y P x N ih_1 ih_2 ih_3 ih_4 =>
      unfold replace_free
      split_ifs
      simp only [free_var_set]
      simp

      constructor
      · intro a1
        tauto
      · intro a1
        cases a1
        case _ c1 =>
          tauto
        case _ c2 =>
          constructor
          · rw [ih_4]
            tauto
          · intro contra
            apply ih_2
            rw [contra] at c2
            tauto


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
        apply sub_is_def_v3.abs_1
        rfl
      case neg =>
        apply sub_is_def_v3.abs_3
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
