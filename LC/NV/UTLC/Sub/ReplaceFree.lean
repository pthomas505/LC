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
