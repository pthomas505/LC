import LC.NV.UTLC.Term

import Mathlib.Data.Finset.Basic


set_option autoImplicit false


open Term_


/--
  `Term_.var_set e` := The set of all of the variables that have an occurrence in the term `e`.
-/
def Term_.var_set :
  Term_ → Finset Symbol_
  | var_ x => {x}
  | app_ M N => M.var_set ∪ N.var_set
  | abs_ x M => M.var_set ∪ {x}


/--
  `occurs_in v e` := True if and only if there is an occurrence of the variable `v` in the term `e`.
-/
def occurs_in
  (v : Symbol_) :
  Term_ → Prop
  | var_ x => v = x
  | app_ M N => occurs_in v M ∨ occurs_in v N
  | abs_ x M => v = x ∨ occurs_in v M


instance
  (v : Symbol_)
  (e : Term_) :
  Decidable (occurs_in v e) :=
  by
  induction e
  all_goals
    simp only [occurs_in]
    infer_instance


/--
  `Term_.bound_var_set e` := The set of all of the variables that have a bound occurrence in the term `e`.
-/
def Term_.bound_var_set :
  Term_ → Finset Symbol_
  | var_ _ => ∅
  | app_ M N => M.bound_var_set ∪ N.bound_var_set
  | abs_ x M => M.bound_var_set ∪ {x}


/--
  `is_bound_in v e` := True if and only if there is a bound occurrence of the variable `v` in the term `e`.
-/
def is_bound_in
  (v : Symbol_) :
  Term_ → Prop
  | var_ _ => False
  | app_ M N => is_bound_in v M ∨ is_bound_in v N
  | abs_ x M => v = x ∨ is_bound_in v M


instance
  (v : Symbol_)
  (e : Term_) :
  Decidable (is_bound_in v e) :=
  by
  induction e
  all_goals
    simp only [is_bound_in]
    infer_instance


/--
  `Term_.free_var_set e` := The set of all of the variables that have a free occurrence in the term `e`.
-/
def Term_.free_var_set :
  Term_ → Finset Symbol_
  | var_ x => {x}
  | app_ M N => M.free_var_set ∪ N.free_var_set
  | abs_ x M => M.free_var_set \ {x}


/--
  `is_free_in v e` := True if and only if there is a free occurrence of the variable `v` in the term `e`.
-/
def is_free_in
  (v : Symbol_) :
  Term_ → Prop
  | var_ x => v = x
  | app_ M N => is_free_in v M ∨ is_free_in v N
  | abs_ x M => ¬ v = x ∧ is_free_in v M


instance
  (v : Symbol_)
  (e : Term_) :
  Decidable (is_free_in v e) :=
  by
  induction e
  all_goals
    simp only [is_free_in]
    infer_instance


/--
  `Term_.is_open e` := True if and only if the term `e` contains a free occurrence of a variable.
-/
def Term_.is_open
  (e : Term_) :
  Prop :=
  ¬ e.free_var_set = ∅


instance
  (e : Term_) :
  Decidable e.is_open :=
  by
  simp only [is_open]
  infer_instance


/--
  `Term_.is_closed e` := True if and only if the term `e` does not contain a free occurrence of a variable.
-/
def Term_.is_closed
  (e : Term_) :
  Prop :=
  e.free_var_set = ∅


instance
  (e : Term_) :
  Decidable e.is_closed :=
  by
  simp only [is_closed]
  infer_instance


-------------------------------------------------------------------------------


theorem occurs_in_iff_mem_var_set
  (v : Symbol_)
  (e : Term_) :
  occurs_in v e ↔ v ∈ e.var_set :=
  by
  induction e
  all_goals
    simp only [occurs_in]
    simp only [Term_.var_set]
  case var_ x =>
    simp
  case app_ M N ih_1 ih_2 =>
    rw [ih_1]
    rw [ih_2]
    simp
  case abs_ x M ih =>
    rw [ih]
    simp
    tauto


theorem is_bound_in_iff_mem_bound_var_set
  (v : Symbol_)
  (e : Term_) :
  is_bound_in v e ↔ v ∈ e.bound_var_set :=
  by
  induction e
  all_goals
    simp only [is_bound_in]
    simp only [Term_.bound_var_set]
  case var_ x =>
    simp
  case app_ M N ih_1 ih_2 =>
    rw [ih_1]
    rw [ih_2]
    simp
  case abs_ x M ih =>
    rw [ih]
    simp
    tauto


theorem is_free_in_iff_mem_free_var_set
  (v : Symbol_)
  (e : Term_) :
  is_free_in v e ↔ v ∈ e.free_var_set :=
  by
  induction e
  all_goals
    simp only [is_free_in]
    simp only [Term_.free_var_set]
  case var_ x =>
    simp
  case app_ M N ih_1 ih_2 =>
    rw [ih_1]
    rw [ih_2]
    simp
  case abs_ x M ih =>
    rw [ih]
    simp
    tauto


theorem is_bound_in_imp_occurs_in
  (v : Symbol_)
  (e : Term_)
  (h1 : is_bound_in v e) :
  occurs_in v e :=
  by
  induction e
  all_goals
    simp only [is_bound_in] at h1
  all_goals
    simp only [occurs_in]
    tauto


theorem is_free_in_imp_occurs_in
  (v : Symbol_)
  (e : Term_)
  (h1 : is_free_in v e) :
  occurs_in v e :=
  by
  induction e
  all_goals
    simp only [is_free_in] at h1
  all_goals
    simp only [occurs_in]
    tauto


#lint
