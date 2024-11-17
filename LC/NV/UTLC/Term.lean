import Mathlib.Tactic


set_option autoImplicit false


-- untyped lambda calculus


/--
  The type of symbols.
-/
@[reducible]
def Symbol_ : Type := String
deriving Inhabited, DecidableEq, Repr


/--
  The type of terms.
-/
inductive Term_ : Type
  | var_ : Symbol_ → Term_
  | app_ : Term_ → Term_ → Term_
  | abs_ : Symbol_ → Term_ → Term_
deriving Inhabited, DecidableEq, Repr

compile_inductive% Term_

open Term_


/--
  The string representation of terms.
-/
def Term_.toString : Term_ → String
  | var_ x => x
  | app_ P Q => s! "({P.toString} {Q.toString})"
  | abs_ x P => s! "(fun {x}. {P.toString})"


instance :
  ToString Term_ :=
  { toString := fun (e : Term_) => e.toString }


/--
  `is_var e` := True if and only if `e` is a term variable.
-/
def Term_.is_var :
  Term_ → Prop
  | var_ _ => True
  | _ => False


instance
  (e : Term_) :
  Decidable e.is_var :=
  by
    cases e
    all_goals
      unfold is_var
      infer_instance


lemma is_var_iff_exists_var
  (e : Term_) :
  e.is_var ↔ ∃ (x : Symbol_), e = var_ x :=
  by
    constructor
    · intro a1
      cases e
      case var_ x =>
        apply Exists.intro x
        rfl
      all_goals
        unfold is_var at a1
        simp only at a1
    · intro a1
      obtain ⟨x, a1⟩ := a1
      rw [a1]
      unfold is_var
      simp only


/--
  `is_app e` := True if and only if `e` is a term application.
-/
def Term_.is_app :
  Term_ → Prop
  | app_ _ _ => True
  | _ => False


instance
  (e : Term_) :
  Decidable e.is_app :=
  by
    cases e
    all_goals
      unfold is_app
      infer_instance


lemma is_app_iff_exists_app
  (e : Term_) :
  e.is_app ↔∃ (P Q : Term_), e = app_ P Q :=
  by
    constructor
    · intro a1
      cases e
      case app_ P Q =>
        apply Exists.intro P
        apply Exists.intro Q
        rfl
      all_goals
        unfold is_app at a1
        simp only at a1
    · intro a1
      obtain ⟨P, Q, a1⟩ := a1
      rw [a1]
      unfold is_app
      simp only


/--
  `is_abs e` := True if and only if `e` is a term abstraction.
-/
def Term_.is_abs :
  Term_ → Prop
  | abs_ _ _ => True
  | _ => False


instance
  (e : Term_) :
  Decidable e.is_abs :=
  by
    cases e
    all_goals
      unfold is_abs
      infer_instance


lemma is_abs_iff_exists_abs
  (e : Term_) :
  e.is_abs ↔∃ (x : Symbol_) (P : Term_), e = abs_ x P :=
  by
    constructor
    · intro a1
      cases e
      case abs_ x P =>
        apply Exists.intro x
        apply Exists.intro P
        rfl
      all_goals
        unfold is_abs at a1
        simp only at a1
    · intro a1
      obtain ⟨P, Q, a1⟩ := a1
      rw [a1]
      unfold is_abs
      simp only


#lint
