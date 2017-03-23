structure X :=
  (a : unit)
attribute [ematch] X.a
structure Y extends X
print Y.a