import Mathlib.Tactic
import Mathlib.Util.CompileInductive


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
  The string representation of formulas.
-/
def Term_.toString : Term_ → String
  | var_ x => x
  | app_ M N => s! "({M.toString} {N.toString})"
  | abs_ x M => s! "(fun {x}. {M.toString})"


instance :
  ToString Term_ :=
  { toString := fun (e : Term_) => e.toString }


/--
  is_var e := True if and only if `e` is a term variable.
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
  is_app e := True if and only if `e` is a term application.
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
  e.is_app ↔∃ (M N : Term_), e = app_ M N :=
  by
    constructor
    · intro a1
      cases e
      case app_ M N =>
        apply Exists.intro M
        apply Exists.intro N
        rfl
      all_goals
        unfold is_app at a1
        simp only at a1
    · intro a1
      obtain ⟨M, N, a1⟩ := a1
      rw [a1]
      unfold is_app
      simp only


/--
  is_abs e := True if and only if `e` is a term abstraction.
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
  e.is_abs ↔∃ (x : Symbol_) (M : Term_), e = abs_ x M :=
  by
    constructor
    · intro a1
      cases e
      case abs_ x M =>
        apply Exists.intro x
        apply Exists.intro M
        rfl
      all_goals
        unfold is_abs at a1
        simp only at a1
    · intro a1
      obtain ⟨M, N, a1⟩ := a1
      rw [a1]
      unfold is_abs
      simp only


#lint
