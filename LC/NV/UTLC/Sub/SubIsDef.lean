import LC.NV.UTLC.Sub.ReplaceFree


set_option autoImplicit false


open Term_


/--
  `sub_is_def_v3 M x N` := True if and only if `M [ x := N ]` is defined
-/
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
  (M : Term_)
  (x : Symbol_)
  (N : Term_)
  (h1 : x ∉ M.free_var_set) :
  sub_is_def_v3 M x N :=
  by
    induction M
    case var_ x_ =>
      exact sub_is_def_v3.var x_ x N

    case app_ P_ Q_ ih_1 ih_2 =>
      unfold Term_.free_var_set at h1
      simp at h1
      obtain ⟨h1_left, h1_right⟩ := h1
      specialize ih_1 h1_left
      specialize ih_2 h1_right
      exact sub_is_def_v3.app P_ Q_ x N ih_1 ih_2

    case abs_ x_ P_ _ =>
      by_cases c1 : x = x_
      · exact sub_is_def_v3.abs_1 x_ P_ x N c1
      · apply sub_is_def_v3.abs_2 x_ P_ x N c1
        unfold free_var_set at h1
        simp at h1
        tauto


-- [1]
lemma lemma_1_2_5_ii_right
  (M : Term_)
  (x : Symbol_)
  (N : Term_)
  (y : Symbol_)
  (h1 : sub_is_def_v3 M x N)
  (h2 : y ∈ (replace_free x N M).free_var_set) :
  (y ∈ M.free_var_set ∧ ¬ x = y) ∨ (y ∈ N.free_var_set ∧ x ∈ M.free_var_set) :=
  by
    induction h1
    case var y_ x_ N_ =>
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
    case app P_ Q_ x_ N_ ih_1 ih_2 ih_3 ih_4 =>
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
    case abs_1 y_ P_ x_ N_ ih =>
      unfold replace_free at h2
      split_ifs at h2
      unfold free_var_set at h2
      simp at h2

      left
      simp only [free_var_set]
      simp
      rw [ih]
      tauto
    case abs_2 y_ P_ x_ N_ ih_1 ih_2 =>
      unfold replace_free at h2
      split_ifs at h2
      unfold free_var_set at h2
      simp at h2

      left
      simp only [free_var_set]
      simp

      have s1 : (replace_free x_ N_ P_) = P_ := by apply replace_free_not_mem; exact ih_2
      rw [s1] at h2

      constructor
      · exact h2
      · intro contra
        rw [← contra] at h2
        tauto
    case abs_3 y_ P_ x_ N_ ih_1 ih_2 ih_3 ih_4 =>
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
  (y : Symbol_)
  (h1 : sub_is_def_v3 M x N)
  (h2 : (y ∈ M.free_var_set ∧ ¬ x = y) ∨ (y ∈ N.free_var_set ∧ x ∈ M.free_var_set)) :
  y ∈ (replace_free x N M).free_var_set :=
  by
    induction h1
    all_goals
      simp only [free_var_set] at h2

      unfold replace_free
    case var y_ x_ N_ =>
      simp at h2

      split_ifs
      case pos c1 =>
        rw [c1] at h2
        tauto
      case neg c1 =>
        unfold free_var_set
        simp
        tauto
    case app P_ Q_ x_ N_ ih_1 ih_2 ih_3 ih_4 =>
      simp at h2

      unfold free_var_set
      simp
      tauto
    case abs_1 y_ P_ x_ N_ ih =>
      simp at h2

      split_ifs
      unfold free_var_set
      simp
      tauto
    case abs_2 y_ P_ x_ N_ ih_1 ih_2 =>
      simp at h2

      split_ifs
      unfold free_var_set
      simp

      have s1 : replace_free x_ N_ P_ = P_ := by apply replace_free_not_mem; exact ih_2
      rw [s1]

      tauto
    case abs_3 y_ P_ x_ N_ ih_1 ih_2 ih_3 ih_4 =>
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
  (M : Term_)
  (x : Symbol_)
  (N : Term_)
  (y : Symbol_)
  (h1 : sub_is_def_v3 M x N) :
  y ∈ (replace_free x N M).free_var_set ↔
    (y ∈ M.free_var_set ∧ ¬ x = y) ∨ (y ∈ N.free_var_set ∧ x ∈ M.free_var_set) :=
  by
    induction h1
    case var y_ x_ N_ =>
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
    case app P_ Q_ x_ N_ ih_1 ih_2 ih_3 ih_4 =>
      unfold replace_free
      simp only [free_var_set]
      simp
      tauto
    case abs_1 y_ P_ x_ N_ ih =>
      unfold replace_free
      split_ifs
      simp only [free_var_set]
      simp
      rw [ih]
      tauto
    case abs_2 y_ P_ x_ N_ ih_1 ih_2 =>
      unfold replace_free
      split_ifs
      simp only [free_var_set]
      simp

      have s1 : replace_free x_ N_ P_ = P_ := by apply replace_free_not_mem; exact ih_2
      rw [s1]

      constructor
      · intro a1
        obtain ⟨a1_left, a1_right⟩ := a1

        have s1 : ¬ x_ = y :=
        by
          intro contra
          apply ih_2
          rw [contra]
          exact a1_left

        tauto
      · tauto
    case abs_3 y_ P_ x_ N_ ih_1 ih_2 ih_3 ih_4 =>
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
  (M : Term_)
  (x : Symbol_) :
  sub_is_def_v3 M x (var_ x) :=
  by
    induction M
    case var_ x_ =>
      apply sub_is_def_v3.var
    case app_ P_ Q_ ih_1 ih_2 =>
      apply sub_is_def_v3.app
      · exact ih_1
      · exact ih_2
    case abs_ x_ P_ ih =>
      by_cases c1 : x = x_
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
  (h2 : sub_is_def_v3 (replace_free x N M) y L)
  (h3 : ¬ x = y)
  (h4 : x ∉ L.free_var_set ∨ y ∉ M.free_var_set) :
  sub_is_def_v3 M y L :=
  by
    induction M
    case var_ x_ =>
      apply sub_is_def_v3.var
    case app_ P_ Q_ ih_1 ih_2 =>
      cases h1
      case app h1_left h1_right =>
        unfold replace_free at h2
        cases h2
        case app h3_left h3_right =>
          simp only [free_var_set] at h4
          simp at h4
          apply sub_is_def_v3.app
          · tauto
          · tauto
    case abs_ x_ P_ ih =>
      cases h1
      case abs_1 c1 =>
        unfold replace_free at h2
        split_ifs at h2
        exact h2
      case abs_2 c1 c2 =>
        unfold replace_free at h2
        split_ifs at h2

        have s1 : replace_free x N P_ = P_ := by apply replace_free_not_mem; exact c2
        rw [s1] at h2
        exact h2
      case abs_3 c1 c2 c3 =>
        unfold replace_free at h2
        split_ifs at h2

        simp only [free_var_set] at h4
        simp at h4

        cases h2
        case abs_1 c4 =>
          apply sub_is_def_v3.abs_1
          exact c4
        case abs_2 c4 c5 =>
          apply sub_is_def_v3.abs_2
          · exact c4
          · intro contra
            apply c5
            exact replace_free_mem_free_var_set P_ x N y contra h3
        case abs_3 c4 c5 c6 =>
          apply sub_is_def_v3.abs_3
          · exact c4
          · exact c5
          · apply ih c3 c6
            tauto


-- [1]
lemma lemma_1_2_6_a_right
  (M N L : Term_)
  (x y : Symbol_)
  (h1 : sub_is_def_v3 M x N)
  (h2 : sub_is_def_v3 N y L)
  (h3 : sub_is_def_v3 (replace_free x N M) y L)
  (h4 : ¬ x = y)
  (h5 : x ∉ L.free_var_set ∨ y ∉ M.free_var_set) :
  sub_is_def_v3 (replace_free y L M) x (replace_free y L N) :=
  by
    induction M
    case var_ x_ =>
      simp only [free_var_set] at h5
      simp at h5

      cases h5
      case inl h5_left =>
        simp only [replace_free]
        split_ifs
        case pos c1 =>
          exact lemma_1_2_5_i_a L x (replace_free y L N) h5_left
        case neg c1 =>
          exact sub_is_def_v3.var x_ x (replace_free y L N)
      case inr h5_right =>
        simp only [replace_free]
        split_ifs
        exact sub_is_def_v3.var x_ x (replace_free y L N)
    case app_ P_ Q_ ih_1 ih_2 =>
      cases h1
      case app c1 c2 =>
        cases h3
        case app c3 c4 =>
          simp only [free_var_set] at h5
          simp at h5

          apply sub_is_def_v3.app
          · tauto
          · tauto
    case abs_ x_ P_ ih =>
      simp only [free_var_set] at h5
      simp at h5

      cases h1
      case abs_1 c1 =>
        simp only [replace_free]
        split_ifs
        case pos c2 =>
          apply sub_is_def_v3.abs_1
          exact c1
        case neg c2 =>
          apply sub_is_def_v3.abs_1
          exact c1
      case abs_2 c1 c2 =>
        simp only [replace_free] at h3
        split_ifs at h3

        simp only [replace_free]
        split_ifs
        case pos c3 =>
          apply sub_is_def_v3.abs_2
          · exact c1
          · exact c2
        case neg c3 =>
          apply sub_is_def_v3.abs_2
          · exact c1
          · cases h5
            case _ h5_left =>
              apply replace_free_not_mem_either_free_var_set; exact c2; exact h5_left
            case _ h5_right =>
              simp only [free_var_set] at h5_right
              have s1 : y ∉ P_.free_var_set := by tauto
              have s2 : replace_free y L P_ = P_ := replace_free_not_mem P_ y L s1
              rw [s2]
              exact c2
      case abs_3 c1 c2 c3 =>
        simp only [replace_free] at h3
        split_ifs at h3

        simp only [replace_free]
        split_ifs
        case pos c4 =>
          rw [c4]
          have s1 : replace_free x_ L N = N := replace_free_not_mem N x_ L c2
          rw [s1]
          apply sub_is_def_v3.abs_3; exact c1; exact c2; exact c3
        case neg c4 =>
          sorry


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


#lint
