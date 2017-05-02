
def f ( x : ℕ ) := x + 1

lemma p : f 3 = 4 := begin unfold f, trivial end

structure X ( n : ℕ ) :=
  ( m : ℕ )

@[reducible] def g ( x : X (f 3) ) : X 4 :=
begin
  pose y := @X.mk (f 3) x.m, 
  refine (cast _ x),
  rewrite p
end

lemma h ( x : X (f 3) ) ( h : x.m = 0 ) : (g x).m = 0 :=
begin
-- https://groups.google.com/d/msg/lean-user/HVHlA4eXtxw/G0GUtjPGDAAJ
-- Jeremy suggests using:
  rewrite -h,
  reflexivity,
  
  -- I had tried:
--   dsimp,
--   unfold g._proof_1,
  -- What can I do with this?
  --   ⊢ (eq.rec x (eq.rec (eq.refl (X 4)) (eq.symm _root_.p))).m = 0
end