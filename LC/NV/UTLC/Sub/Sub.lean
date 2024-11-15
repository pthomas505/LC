import MathlibExtra.Fresh
import MathlibExtra.FunctionUpdateITE

import LC.NV.UTLC.Sub.Alpha
import LC.NV.UTLC.Sub.ReplaceFree
import LC.NV.UTLC.Sub.ReplaceVar
import LC.NV.UTLC.Sub.SubIsDef
import LC.NV.UTLC.Sub.IsSub


set_option autoImplicit false


open Term_


/--
  sub sigma c e := The simultaneous replacement of each free occurrence of any variable v in the expression e by sigma v. The character c is used to generate fresh binding variables as needed to avoid free variable capture.
-/
def sub
  (sigma : Symbol_ → Term_)
  (c : Char) :
  Term_ → Term_
  | var_ x => sigma x
  | app_ e1 e2 => app_ (sub sigma c e1) (sub sigma c e2)
  | abs_ x e =>
    let x' : Symbol_ :=
      if ∃ (y : Symbol_), y ∈ e.free_var_set \ {x} ∧ x ∈ (sigma y).free_var_set
      then fresh x c ((sub (Function.updateITE sigma x (var_ x)) c e).free_var_set)
      else x
    abs_ x' (sub (Function.updateITE sigma x (var_ x')) c e)


-- v -> t in e
def sub_single
  (v : Symbol_)
  (t : Term_)
  (e : Term_) :
  Term_ :=
  let sigma := Function.updateITE (fun x => var_ x) v t
  sub sigma '+' e


-- v -> t in e
def sub_var
  (v t : Symbol_)
  (e : Term_) :
  Term_ :=
  sub_single v (var_ t) e


#eval sub_var "x" "y" (abs_ "y" (var_ "x"))


-------------------------------------------------------------------------------

example
  (x y : Symbol_)
  (N P : Term_) :
  (sub_single x N (abs_ x P)) = abs_ x P :=
  by
    unfold sub_single
    simp
    unfold Function.updateITE
    simp
    unfold sub
    split_ifs
    case pos c1 =>
      obtain ⟨y', c1_left, c1_right⟩ := c1
      simp at c1_left
      obtain ⟨c1_left_left, c1_left_right⟩ := c1_left
      split_ifs at c1_right
      simp only [Term_.free_var_set] at c1_right
      simp at c1_right
      rw [c1_right] at c1_left_right
      contradiction
    case neg c1 =>
      simp at c1
      simp
      induction P
      case var_ x' =>
        unfold sub
        unfold Function.updateITE
        simp
        split_ifs
        case pos c2 =>
          rw [c2]
        case neg c2 =>
          rfl
      all_goals
        sorry


-------------------------------------------------------------------------------
