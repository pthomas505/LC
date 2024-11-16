import LC.NV.UTLC.Binders


set_option autoImplicit false


open Term_


-- replace_free u N M := M [ u := N ]
-- u -> N in M
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


lemma replace_free_self
  (u : Symbol_)
  (M : Term_) :
  replace_free u (var_ u) M = M :=
  by
    induction M
    case var_ x =>
      unfold replace_free
      split_ifs
      case pos c1 =>
        rw [c1]
      case neg c1 =>
        rfl
    case app_ P Q ih_1 ih_2 =>
      unfold replace_free
      rw [ih_1]
      rw [ih_2]
    case abs_ x P ih =>
      unfold replace_free
      split_ifs
      case pos c1 =>
        rfl
      case neg c1 =>
        rw [ih]


-- [1]
lemma lemma_1_2_5_iii_b
  (v : Symbol_)
  (e : Term_) :
  replace_free v (var_ v) e = e := replace_free_self v e


lemma not_free_in_replace_free_self
  (u : Symbol_)
  (N : Term_)
  (M : Term_)
  (h1 : ¬ is_free_in u M) :
  replace_free u N M = M :=
  by
    induction M
    case var_ x =>
      unfold is_free_in at h1
      unfold replace_free
      split_ifs
      rfl
    case app_ P Q ih_1 ih_2 =>
      unfold is_free_in at h1
      simp at h1
      obtain ⟨h1_left, h1_right⟩ := h1

      unfold replace_free
      rw [ih_1 h1_left]
      rw [ih_2 h1_right]
    case abs_ x P ih =>
      unfold is_free_in at h1
      simp at h1

      unfold replace_free
      split_ifs
      case pos c1 =>
        rfl
      case neg c1 =>
        specialize h1 c1
        specialize ih h1
        rw [ih]


-- [1]
lemma lemma_1_2_5_i_b
  (M : Term_)
  (x : Symbol_)
  (N : Term_)
  (h1 : x ∉ M.free_var_set) :
  replace_free x N M = M :=
  by
    apply not_free_in_replace_free_self
    intro contra
    apply h1
    rw [← is_free_in_iff_mem_free_var_set x M]
    exact contra


lemma replace_free_inverse
  (u v : Symbol_)
  (M : Term_)
  (h1 : ¬ occurs_in v M) :
  replace_free v (var_ u) (replace_free u (var_ v) M) = M :=
  by
    induction M
    case var_ x =>
      unfold occurs_in at h1

      simp only [replace_free]
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
      unfold occurs_in at h1
      simp at h1
      obtain ⟨h1_left, h1_right⟩ := h1

      simp only [replace_free]
      rw [ih_1 h1_left]
      rw [ih_2 h1_right]
    case abs_ x P ih =>
      unfold occurs_in at h1
      simp at h1
      obtain ⟨h1_left, h1_right⟩ := h1
      specialize ih h1_right

      simp only [replace_free]
      split_ifs
      case pos c1 =>
        unfold replace_free
        split_ifs
        have s1 : ¬ is_free_in v P :=
        by
          intro contra
          apply h1_right
          exact is_free_in_imp_occurs_in v P contra
        obtain s2 := not_free_in_replace_free_self v (var_ u) P s1
        rw [s2]
      case neg c1 =>
        unfold replace_free
        split_ifs
        rw [ih]


lemma not_is_free_in_replace_free
  (u v : Symbol_)
  (M : Term_)
  (h1 : ¬ u = v) :
  ¬ is_free_in u (replace_free u (var_ v) M) :=
  by
    induction M
    case var_ x =>
      unfold replace_free
      split_ifs
      case pos c1 =>
        unfold is_free_in
        exact h1
      case neg c1 =>
        unfold is_free_in
        exact c1
    case app_ P Q ih_1 ih_2 =>
      unfold replace_free
      unfold is_free_in
      simp
      exact ⟨ih_1, ih_2⟩
    case abs_ x P ih =>
      unfold replace_free
      split_ifs
      case pos c1 =>
        unfold is_free_in
        simp
        intro contra
        contradiction
      case neg c1 =>
        unfold is_free_in
        simp
        intro a1
        exact ih


lemma misc_5'
(x : Symbol_)
(y : Symbol_)
(P : Term_)
(N : Term_)
(h1 : x ∉ P.free_var_set) :
replace_free x N (abs_ y P) = abs_ y P :=
by
  apply lemma_1_2_5_i_b
  unfold Term_.free_var_set
  simp
  intro a1
  contradiction


lemma misc_7'
(x : Symbol_)
(y : Symbol_)
(P : Term_)
(N : Term_)
(h1 : x ∉ (abs_ y P).free_var_set)
(h2 : ¬ x = y) :
replace_free x N P = P :=
by
  unfold Term_.free_var_set at h1
  simp at h1
  apply lemma_1_2_5_i_b
  intro contra
  apply h2
  exact h1 contra
