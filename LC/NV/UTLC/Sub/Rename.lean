import LC.NV.UTLC.Binders


set_option autoImplicit false


open Term_


/--
  replace_var u v e := The simultaneous replacement of each occurrence of the variable `u` by the variable `v` in the term `e`.
  (`u -> v` in `e`)
-/
def replace_var
  (u v : Symbol_) :
  Term_ → Term_
  | var_ x =>
    if u = x
    then var_ v
    else var_ x
  | app_ M N =>
    app_ (replace_var u v M) (replace_var u v N)
  | abs_ x M =>
    if u = x
    then abs_ v (replace_var u v M)
    else abs_ x (replace_var u v M)


-------------------------------------------------------------------------------


theorem replace_var_same
  (u : Symbol_)
  (e : Term_) :
  replace_var u u e = e :=
  by
    induction e
    all_goals
      unfold replace_var
    case var_ x =>
      split_ifs
      case pos c1 =>
        rw [c1]
      case neg c1 =>
        rfl
    case app_ M N ih_1 ih_2 =>
      rw [ih_1]
      rw [ih_2]
    case abs_ x M ih =>
      split_ifs
      case pos c1 =>
        rw [ih]
        rw [c1]
      case neg c1 =>
        rw [ih]


theorem replace_var_diff
  (u v : Symbol_)
  (e : Term_)
  (h1 : ¬ u = v) :
  ¬ occurs_in u (replace_var u v e) :=
  by
    induction e
    case var_ x =>
      unfold replace_var
      split_ifs
      case pos c1 =>
        unfold occurs_in
        exact h1
      case neg c1 =>
        unfold occurs_in
        exact c1
    case app_ M N ih_1 ih_2 =>
      unfold replace_var
      unfold occurs_in
      simp
      exact ⟨ih_1, ih_2⟩
    case abs_ x M ih =>
      unfold replace_var
      split_ifs
      case pos c1 =>
        unfold occurs_in
        simp
        exact ⟨h1, ih⟩
      case neg c1 =>
        unfold occurs_in
        simp
        exact ⟨c1, ih⟩


theorem replace_var_from_not_occurs_in
  (u v : Symbol_)
  (e : Term_)
  (h1 : ¬ occurs_in u e) :
  replace_var u v e = e :=
  by
    induction e
    all_goals
      unfold occurs_in at h1
    case var_ x =>
      unfold replace_var
      split_ifs
      rfl
    case app_ M N ih_1 ih_2 =>
      simp at h1
      obtain ⟨h1_left, h1_right⟩ := h1

      unfold replace_var
      rw [ih_1 h1_left]
      rw [ih_2 h1_right]
    case abs_ x M ih =>
      simp at h1
      obtain ⟨h1_left, h1_right⟩ := h1

      unfold replace_var
      split_ifs
      rw [ih h1_right]


theorem replace_var_to_not_occurs_in
  (u v : Symbol_)
  (e : Term_)
  (h1 : ¬ occurs_in v e) :
  replace_var v u (replace_var u v e) = e :=
  by
    induction e
    all_goals
      unfold occurs_in at h1
    case var_ x =>
      simp only [replace_var]
      split_ifs
      case pos c1 =>
        rw [c1]
        unfold replace_var
        simp
      case neg c1 =>
        unfold replace_var
        split_ifs
        rfl
    case app_ M N ih_1 ih_2 =>
      simp at h1
      obtain ⟨h1_left, h1_right⟩ := h1

      simp only [replace_var]
      rw [ih_1 h1_left]
      rw [ih_2 h1_right]
    case abs_ x M ih =>
      simp at h1
      obtain ⟨h1_left, h1_right⟩ := h1

      simp only [replace_var]
      split_ifs
      case pos c1 =>
        simp only [replace_var]
        simp
        exact ⟨c1, ih h1_right⟩
      case neg c1 =>
        simp only [replace_var]
        split_ifs
        congr
        exact ih h1_right


theorem replace_var_free_var_set_sdiff
  (u v : Symbol_)
  (e : Term_)
  (h1 : v ∉ e.var_set) :
  e.free_var_set \ {u} = (replace_var u v e).free_var_set \ {v} :=
  by
    induction e
    case var_ x =>
      unfold var_set at h1
      simp at h1

      unfold replace_var
      split_ifs
      case pos c1 =>
        unfold free_var_set
        rw [c1]
        simp
      case neg c1 =>
        unfold free_var_set
        simp only [Finset.sdiff_singleton_eq_erase]

        have s1 : Finset.erase {x} u = ({x} : Finset Symbol_) :=
        by
          apply Finset.erase_eq_of_not_mem
          simp
          exact c1
        rw [s1]

        have s2 : Finset.erase {x} v = ({x} : Finset Symbol_) :=
        by
          apply Finset.erase_eq_of_not_mem
          simp
          exact h1
        rw [s2]
    case app_ M N ih_1 ih_2 =>
      unfold var_set at h1
      simp at h1
      obtain ⟨h1_left, h1_right⟩ := h1

      unfold replace_var
      unfold free_var_set
      simp only [Finset.union_sdiff_distrib]
      rw [ih_1 h1_left]
      rw [ih_2 h1_right]
    case abs_ x M ih =>
      unfold var_set at h1
      simp at h1
      obtain ⟨h1_left, _⟩ := h1

      unfold replace_var
      split_ifs
      case pos c1 =>
        rw [← c1]
        unfold free_var_set
        simp
        exact ih h1_left
      case neg c1 =>
        unfold free_var_set
        simp only [sdiff_sdiff_comm]
        congr 1
        exact ih h1_left


#lint
