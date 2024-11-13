import LC.NV.UTLC.Sub.Rename
import LC.NV.UTLC.Sub.ReplaceFree


set_option autoImplicit false


open Term_


inductive are_alpha_equiv : Term_ → Term_ → Prop

| refl
  (M : Term_) :
  are_alpha_equiv M M

| symm
  (M N : Term_) :
  are_alpha_equiv M N →
  are_alpha_equiv N M

| trans
  (M N P : Term_) :
  are_alpha_equiv M N →
  are_alpha_equiv N P →
  are_alpha_equiv M P

| app
  (M M' N N' : Term_) :
  are_alpha_equiv M M' →
  are_alpha_equiv N N' →
  are_alpha_equiv (app_ M N) (app_ M' N')

| abs
  (x : Symbol_)
  (M M' : Term_) :
  are_alpha_equiv M M' →
  are_alpha_equiv (abs_ x M) (abs_ x M')

| alpha
  (x y : Symbol_)
  (M : Term_) :
  y ∉ M.var_set →
  are_alpha_equiv (abs_ x M) (abs_ y (rename x y M))


-------------------------------------------------------------------------------


-- [2]

inductive are_alpha_equiv_alt : Term_ → Term_ → Prop

| rename
  (x y : Symbol_)
  (M : Term_) :
  y ∉ M.var_set →
  are_alpha_equiv_alt (abs_ x M) (abs_ y (replace_free x (var_ y) M))

| compat_app_left
  (M N L : Term_) :
  are_alpha_equiv_alt M N →
  are_alpha_equiv_alt (app_ M L) (app_ N L)

| compat_app_right
  (M N L : Term_) :
  are_alpha_equiv_alt M N →
  are_alpha_equiv_alt (app_ L M) (app_ L N)

| compat_abs
  (x : Symbol_)
  (M N : Term_) :
  are_alpha_equiv_alt M N →
  are_alpha_equiv_alt (abs_ x M) (abs_ x N)

| refl
  (M : Term_) :
  are_alpha_equiv_alt M M

| symm
  (M N : Term_) :
  are_alpha_equiv_alt M N →
  are_alpha_equiv_alt N M

| trans
  (L M N : Term_) :
  are_alpha_equiv_alt L M →
  are_alpha_equiv_alt M N →
  are_alpha_equiv_alt L N


lemma are_alpha_equiv_rename_replace_free
  (u v : Symbol_)
  (e : Term_)
  (h1 : v ∉ e.var_set) :
  are_alpha_equiv (rename u v e) (replace_free u (var_ v) e) :=
  by
    induction e
    case var_ x =>
      unfold var_set at h1
      simp at h1
      unfold rename
      unfold replace_free
      split_ifs
      all_goals
        apply are_alpha_equiv.refl
    case app_ M N ih_1 ih_2 =>
      unfold var_set at h1
      simp at h1
      obtain ⟨h1_left, h1_right⟩ := h1
      specialize ih_1 h1_left
      specialize ih_2 h1_right
      unfold rename
      unfold replace_free
      apply are_alpha_equiv.app
      · exact ih_1
      · exact ih_2
    case abs_ x M ih =>
      unfold var_set at h1
      simp at h1
      obtain ⟨h1_left, h1_right⟩ := h1
      specialize ih h1_left
      unfold rename
      unfold replace_free
      split_ifs
      case pos c1 =>
        subst c1
        obtain s1 := are_alpha_equiv.alpha u v M h1_left
        apply are_alpha_equiv.symm
        exact s1
      case neg c1 =>
        apply are_alpha_equiv.abs
        exact ih


lemma are_alpha_equiv_alt_replace_free_rename
  (u v : Symbol_)
  (e : Term_)
  (h1 : v ∉ e.var_set) :
  are_alpha_equiv_alt (replace_free u (var_ v) e) (rename u v e) :=
  by
    induction e
    case var_ x =>
      unfold var_set at h1
      simp at h1
      unfold rename
      unfold replace_free
      split_ifs
      all_goals
        apply are_alpha_equiv_alt.refl
    case app_ M N ih_1 ih_2 =>
      unfold var_set at h1
      simp at h1
      obtain ⟨h1_left, h1_right⟩ := h1
      specialize ih_1 h1_left
      specialize ih_2 h1_right
      unfold rename
      unfold replace_free
      obtain s1 := are_alpha_equiv_alt.compat_app_right _ _ _ ih_2
      obtain s2 := are_alpha_equiv_alt.compat_app_left (replace_free u (var_ v) M) (rename u v M) (rename u v N) ih_1
      apply are_alpha_equiv_alt.trans _ _ _ s1 s2
    case abs_ x M ih =>
      unfold var_set at h1
      simp at h1
      obtain ⟨h1_left, h1_right⟩ := h1
      specialize ih h1_left
      unfold rename
      unfold replace_free
      split_ifs
      case pos c1 =>
        subst c1
        obtain s1 := are_alpha_equiv_alt.rename u v M h1_left
        apply are_alpha_equiv_alt.trans (abs_ u M) (abs_ v (replace_free u (var_ v) M)) (abs_ v (rename u v M)) s1
        apply are_alpha_equiv_alt.compat_abs
        exact ih
      case neg c1 =>
        apply are_alpha_equiv_alt.compat_abs
        exact ih


lemma are_alpha_equiv_imp_are_alpha_equiv_alt
  (e e' : Term_)
  (h1 : are_alpha_equiv e e') :
  are_alpha_equiv_alt e e' :=
  by
    induction h1
    case refl M =>
      exact are_alpha_equiv_alt.refl M
    case symm M N _ ih_2 =>
      exact are_alpha_equiv_alt.symm M N ih_2
    case trans M N P _ _ ih_3 ih_4 =>
      exact are_alpha_equiv_alt.trans M N P ih_3 ih_4
    case app M M' N N' _ _ ih_3 ih_4 =>
      obtain s1 := are_alpha_equiv_alt.compat_app_left M M' N ih_3
      obtain s2 := are_alpha_equiv_alt.compat_app_right N N' M' ih_4
      exact are_alpha_equiv_alt.trans (app_ M N) (app_ M' N) (app_ M' N') s1 s2
    case abs x M M' _ ih_2 =>
      exact are_alpha_equiv_alt.compat_abs x M M' ih_2
    case alpha x y M ih_1 =>
      obtain s1 := are_alpha_equiv_alt.rename x y M ih_1
      apply are_alpha_equiv_alt.trans (abs_ x M) (abs_ y (replace_free x (var_ y) M)) (abs_ y (rename x y M)) s1
      apply are_alpha_equiv_alt.compat_abs y (replace_free x (var_ y) M) (rename x y M)
      apply are_alpha_equiv_alt_replace_free_rename; exact ih_1


lemma are_alpha_equiv_alt_imp_are_alpha_equiv
  (e e' : Term_)
  (h1 : are_alpha_equiv_alt e e') :
  are_alpha_equiv e e' :=
  by
    induction h1
    case rename x y M ih_1 =>
      obtain s1 := are_alpha_equiv.alpha x y M ih_1
      apply are_alpha_equiv.trans _ _ _ s1
      apply are_alpha_equiv.abs
      apply are_alpha_equiv_rename_replace_free; exact ih_1
    case compat_app_left M N L _ ih_2 =>
      apply are_alpha_equiv.app M N L L
      · exact ih_2
      · exact are_alpha_equiv.refl L
    case compat_app_right M N L _ ih_2 =>
      apply are_alpha_equiv.app L L M N
      · exact are_alpha_equiv.refl L
      · exact ih_2
    case compat_abs x M N _ ih_2 =>
      exact are_alpha_equiv.abs x M N ih_2
    case refl M =>
      exact are_alpha_equiv.refl M
    case symm M N _ ih_2 =>
      exact are_alpha_equiv.symm M N ih_2
    case trans M N P _ _ ih_3 ih_4 =>
      exact are_alpha_equiv.trans M N P ih_3 ih_4


lemma are_alpha_equiv_iff_are_alpha_equiv_alt
  (e e' : Term_) :
  are_alpha_equiv e e' ↔ are_alpha_equiv_alt e e' :=
  by
    constructor
    · exact are_alpha_equiv_imp_are_alpha_equiv_alt e e'
    · exact are_alpha_equiv_alt_imp_are_alpha_equiv e e'


example
  (e e' : Term_)
  (h1 : are_alpha_equiv e e') :
  e.free_var_set = e'.free_var_set :=
  by
    induction h1
    case refl M =>
      exact Eq.refl M.free_var_set
    case symm M N _ ih_2 =>
      exact Eq.symm ih_2
    case trans M N P _ _ ih_3 ih_4 =>
      exact Eq.trans ih_3 ih_4
    case app M M' N N' ih_1 ih_2 ih_3 ih_4 =>
      unfold Term_.free_var_set
      congr
    case abs x M M' ih_1 ih_2 =>
      unfold Term_.free_var_set
      congr
    case alpha x y M ih =>
      unfold Term_.free_var_set
      exact rename_free_var_set_sdiff x y M ih
