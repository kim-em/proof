-- Z : Type u,
-- a : Z,
-- _x α : Type u,
-- k : Z → α,
-- g f : α → _x,
-- w : (λ (x : Z), f (k x)) = λ (x : Z), g (k x)
-- ⊢ f (k a) = g (k a)

lemma {u} f
  ( Z : Type u ) 
  ( a : Z ) 
  ( α β  : Type u ) 
  ( k : Z → α ) 
  ( g f : α → β ) 
  ( w : (λ (x : Z), f (k x)) = λ (x : Z), g (k x) )
    : f (k a) = g (k a) := congr_fun w a
    -- begin
    --     -- I'd thought I could use:
    --     --   exact (congr_fun w a),
    --     -- this fails with:
    --     -- type mismatch at application
    --     --   congr_fun w
    --     -- term
    --     --   w
    --     -- has type
    --     --   (λ (x : Z), f (k x)) = λ (x : Z), g (k x)
    --     -- but is expected to have type
    --     --   f = g
    --   have p := congr_fun w a,
    --   exact p
    -- end