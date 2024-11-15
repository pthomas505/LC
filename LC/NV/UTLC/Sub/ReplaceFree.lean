import LC.NV.UTLC.Term


set_option autoImplicit false


open Term_


-- replace_free u e1 e2 := e2 [ u := e1 ]
-- u -> e1 in e2
def replace_free
(u : Symbol_)
(e : Term_) :
Term_ → Term_
| var_ x =>
  if u = x
  then e
  else var_ x

| app_ P Q => app_ (replace_free u e P) (replace_free u e Q)

| abs_ x P =>
  if u = x
  then abs_ x P
  else abs_ x (replace_free u e P)


-------------------------------------------------------------------------------


lemma replace_free_self
  (u : Symbol_)
  (e : Term_) :
  replace_free u (var_ u) e = e :=
  by
    induction e
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


/-
theorem fastReplaceFree_self
  (F : Formula)
  (v : VarName) :
  fastReplaceFree v v F = F :=

theorem not_free_in_fastReplaceFree_self
  (F : Formula)
  (v t : VarName)
  (h1 : ¬ isFreeIn v F) :
  fastReplaceFree v t F = F :=

  theorem fastReplaceFree_inverse
  (F : Formula)
  (v t : VarName)
  (h1 : ¬ occursIn t F) :
  fastReplaceFree t v (fastReplaceFree v t F) = F :=

  theorem not_isFreeIn_fastReplaceFree
  (F : Formula)
  (v t : VarName)
  (h1 : ¬ v = t) :
  ¬ isFreeIn v (fastReplaceFree v t F) :=


-/
