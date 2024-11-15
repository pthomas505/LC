import MathlibExtra.Fresh

import LC.NV.UTLC.Sub.Alpha
import LC.NV.UTLC.Sub.ReplaceFree
import LC.NV.UTLC.Sub.ReplaceVar
import LC.NV.UTLC.Sub.SubIsDef


set_option autoImplicit false


open Term_


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

| abs_diff_nel
  (y : Symbol_)
  (P : Term_)
  (x : Symbol_)
  (N : Term_) :
  x ∉ (abs_ y P).free_var_set →
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


inductive is_sub_v2 : Term_ → Symbol_ → Term_ → Term_ → Prop

-- if x = y then y [ x := N ] = N
| var_same
  (y : Symbol_)
  (x : Symbol_)
  (N : Term_) :
  x = y →
  is_sub_v2 (var_ y) x N N

-- if x ≠ y then y [ x := N ] = y
| var_diff
  (y : Symbol_)
  (x : Symbol_)
  (N : Term_) :
  ¬ x = y →
  is_sub_v2 (var_ y) x N (var_ y)

-- (P Q) [ x := N ] = (P [ x := N ] Q [ x := N ])
| app
  (P : Term_)
  (Q : Term_)
  (x : Symbol_)
  (N : Term_)
  (P' : Term_)
  (Q' : Term_) :
  is_sub_v2 P x N P' →
  is_sub_v2 Q x N Q' →
  is_sub_v2 (app_ P Q) x N (app_ P' Q')

-- if x = y then ( λ y . P ) [ x := N ] = ( λ y . P )
| abs_same
  (y : Symbol_)
  (P : Term_)
  (x : Symbol_)
  (N : Term_) :
  x = y →
  is_sub_v2 (abs_ y P) x N (abs_ y P)

| abs_diff_nel
  (y : Symbol_)
  (P : Term_)
  (x : Symbol_)
  (N : Term_) :
  ¬ x = y →
  x ∉ P.free_var_set →
  is_sub_v2 (abs_ y P) x N (abs_ y P)

| abs_diff
  (y : Symbol_)
  (P : Term_)
  (x : Symbol_)
  (N : Term_)
  (P' : Term_) :
  ¬ x = y →
  y ∉ N.free_var_set →
  is_sub_v2 P x N P' →
  is_sub_v2 (abs_ y P) x N (abs_ y P')


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


lemma lemma_1_2_5_i_b
  (M : Term_)
  (x : Symbol_)
  (N : Term_)
  (h1 : x ∉ M.free_var_set) :
  replace_free x N M = M :=
  by
    induction M
    case var_ y =>
      unfold Term_.free_var_set at h1
      simp at h1

      unfold replace_free
      split_ifs
      rfl
    case app_ P Q P_ih Q_ih =>
      unfold Term_.free_var_set at h1
      simp at h1
      obtain ⟨h1_left, h1_right⟩ := h1

      specialize P_ih h1_left
      specialize Q_ih h1_right
      unfold replace_free
      rw [P_ih]
      rw [Q_ih]
    case abs_ y P ih =>
      unfold Term_.free_var_set at h1
      simp at h1

      unfold replace_free
      split_ifs
      case pos c1 =>
        rfl
      case neg c1 =>
        have s1 : replace_free x N P = P :=
        by
          apply ih
          intro contra
          apply c1
          apply h1
          exact contra
        rw [s1]


lemma lemma_1_2_5_i
  (M : Term_)
  (x : Symbol_)
  (N : Term_)
  (h1 : x ∉ M.free_var_set) :
  is_sub_v3 M x N M :=
  by
  induction M
  case var_ y =>
    unfold Term_.free_var_set at h1
    simp at h1
    exact is_sub_v3.var_diff y x N h1
  case app_ P Q ih_P ih_Q =>
    unfold Term_.free_var_set at h1
    simp at h1
    obtain ⟨h1_left, h1_right⟩ := h1
    specialize ih_P h1_left
    specialize ih_Q h1_right
    exact is_sub_v3.app P Q x N P Q ih_P ih_Q
  case abs_ y P ih =>
    by_cases c1 : x = y
    · apply is_sub_v3.abs_same y P x N c1
    · apply is_sub_v3.abs_diff_nel
      · exact c1
      · unfold free_var_set at h1
        simp at h1
        tauto
      · apply ih
        unfold Term_.free_var_set at h1
        simp at h1
        intro contra
        apply c1
        exact h1 contra


example
  (M : Term_)
  (x : Symbol_)
  (N : Term_)
  (L : Term_)
  (h1 : is_sub_v3 M x N L) :
  replace_free x N M = L :=
  by
    induction h1
    case var_same y' x' N' ih =>
      unfold replace_free
      split_ifs
      rfl
    case var_diff y' x' N' ih =>
      unfold replace_free
      split_ifs
      rfl
    case app P' Q' x' N' P'' Q'' P_ih_1 Q_ih_1 P_ih_2 Q_ih_2 =>
      unfold replace_free
      rw [P_ih_2]
      rw [Q_ih_2]
    case abs_same y' P' x' N' ih =>
      unfold replace_free
      split_ifs
      rfl
    case abs_diff_nel y' P' x' N' P'' ih_1 ih_2 ih_3 ih_4 =>
      unfold replace_free
      split_ifs
      rw [ih_4]
    case abs_diff y' P' x' N' P'' ih_1 ih_2 ih_3 ih_4 =>
      unfold replace_free
      split_ifs
      rw [ih_4]


example
(M : Term_)
(x : Symbol_)
(N : Term_)
(h1 : ∃ (L : Term_), is_sub_v3 M x N L) :
sub_is_def M x N :=
by
  obtain ⟨L, h1⟩ := h1
  induction h1
  case var_same h1_y h1_x _ _ =>
    apply sub_is_def.var
  case var_diff h1_y h1_x h1_N _ =>
    apply sub_is_def.var
  case app h1_P h1_Q h1_x h1_N _ _ _ _ ih_3 ih_4 =>
    apply sub_is_def.app; exact ih_3; exact ih_4
  case abs_same h1_y h1_P h1_x h1_N ih =>
    apply sub_is_def.abs_same; exact ih
  case abs_diff_nel h1_y h1_P h1_x h1_N _ ih_1 ih_2 _ _ =>
    apply sub_is_def.abs_diff_nel; exact ih_1; exact ih_2
  case abs_diff h1_y h1_P h1_x h1_N _ ih_1 ih_2 _ ih_4 =>
    apply sub_is_def.abs_diff; exact ih_1; exact ih_2; exact ih_4


example
(M : Term_)
(x : Symbol_)
(N : Term_)
(h1 : sub_is_def M x N) :
is_sub_v3 M x N (replace_free x N M) :=
by
  induction h1
  case var h1_y h1_x h1_N =>
    unfold replace_free
    split_ifs
    case pos c1 =>
      apply is_sub_v3.var_same; exact c1
    case neg c1 =>
      apply is_sub_v3.var_diff; exact c1
  case app h1_M h1_P h1_Q ih_1 _ _ ih_4 ih_5 =>
    apply is_sub_v3.app; exact ih_4; exact ih_5
  case abs_same h1_y h1_P h1_x ih_1 ih_2 =>
    unfold replace_free
    split_ifs
    apply is_sub_v3.abs_same; exact ih_2
  case abs_diff_nel h1_y h1_P h1_x h1_N _ ih_2 =>
    have s1 : replace_free h1_x h1_N (abs_ h1_y h1_P) = abs_ h1_y h1_P :=
    by
      apply lemma_1_2_5_i_b;
      unfold free_var_set
      simp
      tauto
    rw [s1]
    apply lemma_1_2_5_i
    unfold free_var_set
    simp
    tauto
  case abs_diff h1_y h1_P h1_x h1_N ih_1 ih_2 ih_3 ih_4 =>
    unfold replace_free
    split_ifs
    apply is_sub_v3.abs_diff
    · exact ih_1
    · exact ih_2
    · exact ih_4


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


lemma lemma_1_2_5_ii_right
(M : Term_)
(x : Symbol_)
(N : Term_)
(z : Symbol_)
(h1 : sub_is_def M x N)
(h2 : z ∈ (replace_free x N M).free_var_set) :
(z ∈ M.free_var_set ∧ x ≠ z) ∨ (z ∈ N.free_var_set ∧ x ∈ M.free_var_set) := sorry

lemma lemma_1_2_5_ii_left
(M : Term_)
(x : Symbol_)
(N : Term_)
(z : Symbol_)
(h1 : sub_is_def M x N)
(h2 : (z ∈ M.free_var_set ∧ x ≠ z) ∨ (z ∈ N.free_var_set ∧ x ∈ M.free_var_set)) :
z ∈ (replace_free x N M).free_var_set := sorry

lemma lemma_1_2_5_ii
{M : Term_}
{x : Symbol_}
{N : Term_}
{z : Symbol_}
(H1 : sub_is_def M x N) :
z ∈ (replace_free x N M).free_var_set ↔
  (z ∈ M.free_var_set ∧ x ≠ z) ∨ (z ∈ N.free_var_set ∧ x ∈ M.free_var_set) :=
sorry

lemma lemma_1_2_5_iii_a
{M : Term_}
{x : Symbol_} :
sub_is_def M x (var_ x) := sorry

lemma lemma_1_2_5_iii_b
{M : Term_}
{x : Symbol_} :
replace_free x (var_ x) M = M := sorry

lemma lemma_1_2_5_iii
{M : Term_}
{x : Symbol_} :
is_sub_v3 M x (var_ x) M := sorry

lemma lemma_1_2_6_a_left
(M N L : Term_)
(x y : Symbol_)
(h1 : sub_is_def M x N)
(h2 : sub_is_def N y L)
(h3 : sub_is_def (replace_free x N M) y L)
(h4 : x ≠ y)
(h5 : x ∉ L.free_var_set ∨ y ∉ M.free_var_set) :
sub_is_def M y L := sorry

lemma lemma_1_2_6_a_right
(M N L : Term_)
(x y : Symbol_)
(h1 : sub_is_def M x N)
(h2 : sub_is_def N y L)
(h3 : sub_is_def (replace_free x N M) y L)
(h4 : x ≠ y)
(h5 : x ∉ L.free_var_set ∨ y ∉ M.free_var_set) :
sub_is_def (replace_free y L M) x (replace_free y L N) := sorry

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


-------------------------------------------------------------------------------


example
  (e1 e2 e3 : Term_)
  (v : Symbol_)
  (h1 : is_sub_v1 e1 v e2 e3) :
  is_sub_v2 e1 v e2 e3 :=
  by
    induction h1
    case var_same y x N ih =>
      apply is_sub_v2.var_same
      exact ih
    case var_diff y x N ih =>
      apply is_sub_v2.var_diff
      exact ih
    case app P Q x N P' Q' ih_1 ih_2 ih_3 ih_4 =>
      apply is_sub_v2.app
      · exact ih_3
      · exact ih_4
    case abs_diff_nel y P x N ih =>
      unfold free_var_set at ih
      simp at ih
      by_cases c1 : x = y
      case pos =>
        apply is_sub_v2.abs_same
        exact c1
      case neg =>
        apply is_sub_v2.abs_diff_nel
        · exact c1
        · tauto
    case abs_diff y P x N P' ih_1 ih_2 ih_3 ih_4 =>
      apply is_sub_v2.abs_diff
      · exact ih_1
      · exact ih_2
      · exact ih_4


example
  (e1 e2 e3 : Term_)
  (v : Symbol_)
  (h1 : is_sub_v2 e1 v e2 e3) :
  is_sub_v1 e1 v e2 e3 :=
  by
    induction h1
    case var_same y x N ih =>
      apply is_sub_v1.var_same
      exact ih
    case var_diff y x N ih =>
      apply is_sub_v1.var_diff
      exact ih
    case app P Q x N P' Q' ih_1 ih_2 ih_3 ih_4 =>
      apply is_sub_v1.app
      · exact ih_3
      · exact ih_4
    case abs_same y P x N ih =>
      apply is_sub_v1.abs_diff_nel
      unfold free_var_set
      simp
      intro a1
      exact ih
    case abs_diff_nel y P x N ih_1 ih_2 =>
      apply is_sub_v1.abs_diff_nel
      unfold free_var_set
      simp
      intro contra
      contradiction
    case abs_diff y P x N P' ih_1 ih_2 ih_3 ih_4 =>
      apply is_sub_v1.abs_diff
      · exact ih_1
      · exact ih_2
      · exact ih_4


-------------------------------------------------------------------------------


example
  (e1 e2 e3 : Term_)
  (v : Symbol_)
  (h1 : is_sub_v2 e1 v e2 e3) :
  is_sub_v3 e1 v e2 e3 :=
  by
    induction h1
    case var_same y x N ih =>
      apply is_sub_v3.var_same
      exact ih
    case var_diff y x N ih =>
      apply is_sub_v3.var_diff
      exact ih
    case app P Q x N P' Q' ih_1 ih_2 ih_3 ih_4 =>
      apply is_sub_v3.app
      · exact ih_3
      · exact ih_4
    case abs_same y P x N ih_1 =>
      apply is_sub_v3.abs_same
      exact ih_1
    case abs_diff_nel y P x N ih_1 ih_2 =>
      apply lemma_1_2_5_i
      unfold free_var_set
      simp
      intro
      contradiction
    case abs_diff y P x N P' ih_1 ih_2 ih_3 ih_4 =>
      apply is_sub_v3.abs_diff
      · exact ih_1
      · exact ih_2
      · exact ih_4


theorem extracted_1
  (e1 : Term_)
  (v : Symbol_)
  (e2 e3 : Term_)
  (h1: v ∉ e1.free_var_set)
  (h2 : is_sub_v2 e1 v e2 e3) :
  e1 = e3 :=
  by
    induction h2
    case var_same y x N ih =>
      unfold free_var_set at h1
      simp at h1
      contradiction
    case var_diff y x N ih =>
      rfl
    case app P Q x N P' Q' ih_1 ih_2 ih_3 ih_4 =>
      unfold free_var_set at h1
      simp at h1
      obtain ⟨h1_left, h1_right⟩ := h1
      specialize ih_3 h1_left
      specialize ih_4 h1_right
      rw [ih_3]
      rw [ih_4]
    case abs_same y P x N ih_1 =>
      rfl
    case abs_diff_nel y P x N ih_1 ih_2 =>
      rfl
    case abs_diff y P x N P' ih_1 ih_2 ih_3 ih_4 =>
      unfold free_var_set at h1
      simp at h1
      have s1 : P = P' := by tauto
      rw [s1]


example
  (e1 e2 e3 : Term_)
  (v : Symbol_)
  (h1 : is_sub_v3 e1 v e2 e3) :
  is_sub_v2 e1 v e2 e3 :=
  by
    induction h1
    case var_same y x N ih =>
      apply is_sub_v2.var_same
      exact ih
    case var_diff y x N ih =>
      apply is_sub_v2.var_diff
      exact ih
    case app P Q x N P' Q' ih_1 ih_2 ih_3 ih_4 =>
      apply is_sub_v2.app
      · exact ih_3
      · exact ih_4
    case abs_same y P x N ih =>
      apply is_sub_v2.abs_same
      exact ih
    case abs_diff_nel y P x N P' ih_1 ih_2 ih_3 ih_4 =>
      have s1 : x ∉ (abs_ y P).free_var_set :=
      by
        unfold free_var_set
        simp
        intro contra
        contradiction
      have s2 : P = P' :=
      by
        apply extracted_1 P x N P' ih_2 ih_4
      subst s2
      apply is_sub_v2.abs_diff_nel
      · exact ih_1
      · exact ih_2
    case abs_diff y P x N P' ih_1 ih_2 ih_3 ih_4 =>
      apply is_sub_v2.abs_diff
      · exact ih_1
      · exact ih_2
      · exact ih_4


-------------------------------------------------------------------------------
