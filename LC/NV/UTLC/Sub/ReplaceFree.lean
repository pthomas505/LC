import LC.NV.UTLC.Term


set_option autoImplicit false


open Term_


-- replace_free x N M := M [ x := N ]
-- x -> N in M
def replace_free
(x : Symbol_)
(N : Term_) :
Term_ → Term_
| (var_ y) =>
  if x = y
  then N
  else var_ y

| (app_ P Q) => app_ (replace_free x N P) (replace_free x N Q)

| (abs_ y P) =>
  if x = y
  then abs_ y P
  else abs_ y (replace_free x N P)


lemma replace_free_self
  (v : Symbol_)
  (e : Term_) :
  replace_free v (var_ v) e = e :=
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
