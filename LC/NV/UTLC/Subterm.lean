import LC.NV.UTLC.Term

import Mathlib.Data.Multiset.Basic


set_option autoImplicit false


open Term_


/--
  `Term_.subterm_set e` := The set of all of the subterms of a term `e`.
  Definition 1.3.5
-/
def Term_.subterm_set :
  Term_ → Multiset Term_
  | var_ x => {var_ x}
  | app_ P Q => P.subterm_set ∪ Q.subterm_set ∪ {app_ P Q}
  | abs_ x P => P.subterm_set ∪ {abs_ x P}


-- reflexivity
lemma lemma_1_3_6_refl
  (e : Term_) :
  e ∈ e.subterm_set :=
  by
    cases e
    all_goals
      unfold subterm_set
    case var_ x =>
      simp
    case app_ P Q =>
      simp
    case abs_ x P =>
      simp


-- transitivity
lemma lemma_1_3_6_trans
  (e e' e'' : Term_)
  (h1 : e ∈ e'.subterm_set)
  (h2 : e' ∈ e''.subterm_set) :
  e ∈ e''.subterm_set :=
  by
    induction e''
    case var_ x'' =>
      unfold subterm_set at h2
      simp at h2
      rw [h2] at h1
      exact h1
    case app_ M'' N'' ih_1'' ih_2'' =>
      unfold subterm_set at h2
      simp at h2

      cases h2
      case inl h2 =>
        cases h2
        case inl h2 =>
          unfold subterm_set
          simp
          left
          left
          exact ih_1'' h2
        case inr h2 =>
          unfold subterm_set
          simp
          left
          right
          exact ih_2'' h2
      case inr h2 =>
        rw [h2] at h1
        exact h1
    case abs_ x'' M'' ih'' =>
      unfold subterm_set at h2
      simp at h2

      cases h2
      case inl h2 =>
        unfold subterm_set
        simp
        left
        exact ih'' h2
      case inr h2 =>
        rw [h2] at h1
        exact h1


/--
  Definition 1.3.8
-/
def is_proper_subterm
  (e e' : Term_) :
  Prop :=
  e ∈ e'.subterm_set ∧ ¬ e = e'


#lint
