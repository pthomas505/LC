import LC.NV.UTLC.Binders


set_option autoImplicit false


open Term_


/--
  `replace_free u N M` := The simultaneous replacement of each occurrence of the variable `u` by the term `N` in the term `M`.
  `M [ u := N ]`
  (`u` -> `N` in `M`)
-/
def replace_free
  (u : Symbol_)
  (N : Term_) :
  Term_ → Term_
  | var_ x =>
    if u = x
    then N
    else var_ x

  | app_ P Q => app_ (replace_free u N P) (replace_free u N Q)

  | abs_ x P =>
    if u = x
    then abs_ x P
    else abs_ x (replace_free u N P)


-------------------------------------------------------------------------------


-- [1] lemma_1_2_5_iii_b
lemma replace_free_id
  (u : Symbol_)
  (M : Term_) :
  replace_free u (var_ u) M = M :=
  by
    induction M
    all_goals
      unfold replace_free
    case var_ x =>
      split_ifs
      case pos c1 =>
        rw [c1]
      case neg c1 =>
        rfl
    case app_ P Q ih_1 ih_2 =>
      rw [ih_1]
      rw [ih_2]
    case abs_ x P ih =>
      split_ifs
      case pos c1 =>
        rfl
      case neg c1 =>
        rw [ih]


-- [1] lemma_1_2_5_i_b
lemma replace_free_not_mem
  (u : Symbol_)
  (N : Term_)
  (M : Term_)
  (h1 : u ∉ M.free_var_set) :
  replace_free u N M = M :=
  by
    induction M
    all_goals
      unfold free_var_set at h1
      unfold replace_free
    case var_ x =>
      simp at h1

      split_ifs
      rfl
    case app_ P Q ih_1 ih_2 =>
      simp at h1
      obtain ⟨h1_left, h1_right⟩ := h1

      rw [ih_1 h1_left]
      rw [ih_2 h1_right]
    case abs_ x P ih =>
      simp at h1

      split_ifs
      case pos c1 =>
        rfl
      case neg c1 =>
        have s1 : u ∉ P.free_var_set := by tauto
        specialize ih s1
        rw [ih]


lemma replace_free_inverse
  (u v : Symbol_)
  (M : Term_)
  (h1 : v ∉ M.var_set) :
  replace_free v (var_ u) (replace_free u (var_ v) M) = M :=
  by
    induction M
    all_goals
      unfold var_set at h1
      simp only [replace_free]
    case var_ x =>
      simp at h1

      split_ifs
      case pos c1 =>
        rw [c1]
        unfold replace_free
        simp
      case neg c1 =>
        unfold replace_free
        split_ifs
        rfl
    case app_ P Q ih_1 ih_2 =>
      simp at h1
      obtain ⟨h1_left, h1_right⟩ := h1

      rw [ih_1 h1_left]
      rw [ih_2 h1_right]
    case abs_ x P ih =>
      simp at h1
      obtain ⟨h1_left, h1_right⟩ := h1
      specialize ih h1_left

      split_ifs
      case pos c1 =>
        unfold replace_free
        split_ifs
        congr
        have s1 : v ∉ P.free_var_set :=
        by
          exact not_mem_var_set_imp_not_mem_free_var_set v P h1_left
        exact replace_free_not_mem v (var_ u) P s1
      case neg c1 =>
        unfold replace_free
        split_ifs
        rw [ih]


lemma replace_free_not_mem_free_var_set
  (u v : Symbol_)
  (M : Term_)
  (h1 : ¬ u = v) :
  u ∉ (replace_free u (var_ v) M).free_var_set :=
  by
    induction M
    case var_ x =>
      unfold replace_free
      split_ifs
      case pos c1 =>
        unfold free_var_set
        simp
        exact h1
      case neg c1 =>
        unfold free_var_set
        simp
        exact c1
    case app_ P Q ih_1 ih_2 =>
      unfold replace_free
      unfold free_var_set
      simp
      exact ⟨ih_1, ih_2⟩
    case abs_ x P ih =>
      unfold replace_free
      split_ifs
      case pos c1 =>
        unfold free_var_set
        simp
        intro contra
        exact c1
      case neg c1 =>
        unfold free_var_set
        simp
        intro a1
        contradiction


#lint
