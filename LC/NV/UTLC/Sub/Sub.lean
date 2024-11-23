import MathlibExtra.Fresh
import MathlibExtra.FunctionUpdateITE

import LC.NV.UTLC.Sub.ReplaceFree


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
  | app_ P Q => app_ (sub sigma c P) (sub sigma c Q)
  | abs_ x P =>
    let x' : Symbol_ :=
      if ∃ (y : Symbol_), y ∈ P.free_var_set \ {x} ∧ x ∈ (sigma y).free_var_set
      then fresh x c ((sub (Function.updateITE sigma x (var_ x)) c P).free_var_set)
      else x
    abs_ x' (sub (Function.updateITE sigma x (var_ x')) c P)


-- x -> N in M
def sub_single
  (x : Symbol_)
  (N : Term_)
  (M : Term_)
  (c : Char) :
  Term_ :=
  let sigma := Function.updateITE (fun x => var_ x) x N
  sub sigma c M


-- x -> y in M
def sub_var
  (x y : Symbol_)
  (M : Term_)
  (c : Char) :
  Term_ :=
  sub_single x (var_ y) M c


#eval sub_var "x" "y" (abs_ "y" (var_ "x")) '+'


-------------------------------------------------------------------------------


lemma sub_id
  (M : Term_)
  (c : Char) :
  sub (fun x ↦ var_ x) c M = M :=
  by
    induction M
    case var_ x_ =>
      simp only [sub]
    case app_ P_ Q_ ih_1 ih_2 =>
      simp only [sub]
      rw [ih_1]
      rw [ih_2]
    case abs_ x_ P_ ih =>
      simp only [sub]
      simp
      constructor
      · intro x a1 a2 a3
        unfold free_var_set at a3
        simp at a3
        rw [a3] at a2
        contradiction
      · split_ifs
        case pos c1 =>
          simp at c1
          obtain ⟨y, ⟨c1_left_left, c1_left_right⟩, c1_right⟩ := c1
          unfold free_var_set at c1_right
          simp at c1_right
          rw [c1_right] at c1_left_right
          contradiction
        case neg c1 =>
          have s1 : Function.updateITE (fun x ↦ var_ x) x_ (var_ x_) = (fun x ↦ var_ x) :=
          by
            ext x
            unfold Function.updateITE
            split_ifs
            case pos c2 =>
              rw [c2]
            case neg c2 =>
              simp
          rw [s1]
          exact ih


example
  (x : Symbol_)
  (N : Term_)
  (M : Term_)
  (c : Char)
  (h1 : x ∉ M.free_var_set) :
  sub_single x N M c = M :=
  by
    induction M
    case var_ x_ =>
      unfold free_var_set at h1
      simp at h1

      simp only [sub_single]
      simp only [sub]
      simp only [Function.updateITE]
      split_ifs
      case pos c1 =>
        rw [c1] at h1
        contradiction
      case neg c1 =>
        rfl
    case app_ P_ Q_ ih_1 ih_2 =>
      simp only [sub_single] at ih_1

      unfold free_var_set at h1
      simp at h1


      simp only [sub_single]
      simp only [sub]
      congr
      · tauto
      · tauto
    case abs_ x_ P_ ih =>
      simp only [sub_single] at ih

      unfold free_var_set at h1
      simp at h1

      simp only [sub_single]
      simp only [sub]
      simp
      constructor
      · intro z a1 a2 a3
        simp only [Function.updateITE] at a3
        split_ifs at a3
        case pos c1 =>
          rw [c1] at a1
          rw [c1] at a2
          specialize h1 a1
          contradiction
        case neg c1 =>
          simp only [free_var_set] at a3
          simp at a3
          rw [a3] at a2
          contradiction
      · split_ifs
        case pos c1 =>
          simp at c1
          simp only [Function.updateITE] at c1
          obtain ⟨y, ⟨c1_left_left, c1_left_right⟩, c1_right⟩ := c1
          split_ifs at c1_right
          case pos c2 =>
            rw [c2] at c1_left_left
            specialize h1 c1_left_left
            rw [c2] at c1_left_right
            contradiction
          case neg c2 =>
            unfold free_var_set at c1_right
            simp at c1_right
            rw [c1_right] at c1_left_right
            contradiction
        case neg c1 =>
          simp at c1
          sorry


-------------------------------------------------------------------------------
