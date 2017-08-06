definition {u v} transport {A : Type u} { P : A → Type v} {x y : A} (p : x = y)
(u : P x) : P y :=
by induction p; exact u

definition {u v w} apdt011 
  {A : Type u} {Z : Type w} 
  {B : A → Type v} 
  (f : Πa, B a → Z) 
  {a a' : A} 
  {b : B a} 
  {b' : B a'} 
  (Ha : a = a') 
  (Hb : transport Ha b = b')
      : f a b = f a' b' :=
by cases Ha; cases Hb; reflexivity

set_option trace.check true




-- set_option pp.implicit true

-- @NaturalTransformation.components ?M_1 ?M_2 ?M_3 ?M_4 :
--   @NaturalTransformation ?M_1 ?M_2 ?M_3 ?M_4 → Π (X : ?M_1.Obj), ?M_2.Hom (⇑?M_3 X) (⇑?M_4 X)

-- α === Type (max u v)
-- a === (@NaturalTransformation (C × C) C (@MonoidalStructure.tensor C m)
--           (@FunctorComposition (C × C) (C × C) C (SwitchProductCategory C C)
--              (@FunctorComposition (C × C) (C × C) C (SwitchProductCategory C C) (@MonoidalStructure.tensor C m))))
-- T === (λ (_x : Type (max u v)), _x)
-- t : T a == a
-- t === (@vertical_composition_of_NaturalTransformations (C × C) C (@MonoidalStructure.tensor C m)
--           (@FunctorComposition (C × C) (C × C) C (SwitchProductCategory C C) (@MonoidalStructure.tensor C m))
--           (@FunctorComposition (C × C) (C × C) C (SwitchProductCategory C C)
--              (@FunctorComposition (C × C) (C × C) C (SwitchProductCategory C C) (@MonoidalStructure.tensor C m)))
--           (@isomorphism.Isomorphism.morphism (FunctorCategory (C × C) C) (@MonoidalStructure.tensor C m)
--              (@FunctorComposition (C × C) (C × C) C (SwitchProductCategory C C) (@MonoidalStructure.tensor C m))
--              (@braided_monoidal_category.Symmetry.braiding C m β))
--           (@whisker_on_left (C × C) (C × C) C (SwitchProductCategory C C) (@MonoidalStructure.tensor C m)
--              (@FunctorComposition (C × C) (C × C) C (SwitchProductCategory C C) (@MonoidalStructure.tensor C m))
--              (@isomorphism.Isomorphism.morphism (FunctorCategory (C × C) C) (@MonoidalStructure.tensor C m)
--                 (@FunctorComposition (C × C) (C × C) C (SwitchProductCategory C C) (@MonoidalStructure.tensor C m))
--                 (@braided_monoidal_category.Symmetry.braiding C m β)))) 
-- b === (@NaturalTransformation (C × C) C (@MonoidalStructure.tensor C m) (@MonoidalStructure.tensor C m))
-- e : a = b

-- @eq.rec α a T t b e : T b
-- T b == b

-- now we want to apply
--   f === @NaturalTransformation.components (C × C) C (@MonoidalStructure.tensor C m) (@MonoidalStructure.tensor C m)
-- to @eq.rec α a T b e.
-- actually, we're going to need to think of this as applying 
--   f' === @NaturalTransformation.components (C × C) C (@MonoidalStructure.tensor C m)
--      : Π (F : Functor (C × C) C), NaturalTransformation m.tensor F → Π (x : (C × C).Obj), C.Hom (m.tensor x) (F x)
-- and here we may as well introduce S : Functor (C × C) C → Type as S F = Π (x : (C × C).Obj), C.Hom (m.tensor x) (F x),
-- and then write f' : Π (F : Functor (C × C) C), NaturalTransformation m.tensor F → S F 
--
-- Thus we want to start with f' (@MonoidalStructure.tensor C m) (@eq.rec α a T t b e) : S (@MonoidalStructure.tensor C m)
-- and by application of the lemma we're designing obtain ...?
--   f' (@FunctorComposition (C × C) (C × C) C (SwitchProductCategory C C)
--              (@FunctorComposition (C × C) (C × C) C (SwitchProductCategory C C) (@MonoidalStructure.tensor C m)))
--      a 
-- Now this thing is of type S (@FunctorComposition (C × C) (C × C) C (SwitchProductCategory C C)
--              (@FunctorComposition (C × C) (C × C) C (SwitchProductCategory C C) (@MonoidalStructure.tensor C m)))
-- which is no good, so we're going to have to transport it through the type family S. But where do we obtain our 
-- path/equation to transport along? Somehow we take e : a = b, and think of that actually as e : R a' = R b' ... nope.

-------------

-- 20170508
--
-- (@NaturalTransformation.components (C × C) C
--        (@FunctorComposition (C × C) (C × C) C (SwitchProductCategory C C) (@MonoidalStructure.tensor C m))
--        (@MonoidalStructure.tensor C m)
--        (@eq.rec (Functor (C × C) C)
--           (@FunctorComposition (C × C) (C × C) C (IdentityFunctor (C × C)) (@MonoidalStructure.tensor C m))
--           (@NaturalTransformation (C × C) C
--              (@FunctorComposition (C × C) (C × C) C (SwitchProductCategory C C) (@MonoidalStructure.tensor C m)))
--           (t : NaturalTransformation (switch tensor) (id tensor))
--           (@MonoidalStructure.tensor C m)
--           (FunctorComposition.left_identity (C × C) C (@MonoidalStructure.tensor C m)))
--        X)

-- S = (@NaturalTransformation (C × C) C
-- f = @NaturalTransformation.components (C × C) C
-- f : Π a a' : A, Π t : S a a', Z a a'

-- Z a a' = Π X : (C × C).Obj, C.Hom (a X) (a' X)

-- a  = (@FunctorComposition (C × C) (C × C) C (SwitchProductCategory C C) (@MonoidalStructure.tensor C m))
-- a' = (@FunctorComposition (C × C) (C × C) C (IdentityFunctor (C × C)) (@MonoidalStructure.tensor C m))

-- A = (Functor (C × C) C)
-- a a' : A 

-- b = (@MonoidalStructure.tensor C m)
-- b : A

-- p : a' = b

-- t : S a a'

-- (@eq.rec A a' (S a) t b p) : S a b
-- f a b (@eq.rec A a' (S a) t b p) : Z a b
-- f a a' t : Z a a'
-- (@eq.rec A a' (Z a) (f a a' t) b p) : Z a b





lemma {u1 u2 u3 u4} v2 { α : Type u1 } { β : Type u2 } { S : α → β → Type u3 } { Z : α → β → Type u4 } { a : α } { b : β } { t : S a b } { b' : β } { p : b = b' } ( f : Π ( c : α ) ( d : β ) , S c d → Z c d ): 
  f a b' (@eq.rec β b (S a) t b' p) = (@eq.rec β b (Z a) (f a b t) b' p) :=
begin
induction p, reflexivity
end

lemma {u1 u2 u3} v1 { β : Type u1 } { S : β → Type u2 } { Z : β → Type u3 } { b : β } { t : S b } { b' : β } { p : b = b' } ( f : Π d : β, S d → Z d ) : 
  f b' (@eq.rec β b S t b' p) = (@eq.rec β b Z (f b t) b' p) :=
begin
induction p, reflexivity
end


      --  (@NaturalTransformation.components (C × C) C
      --     (@FunctorComposition (C × C) (C × C) C (SwitchProductCategory C C) (@MonoidalStructure.tensor C m))
      --     (@FunctorComposition (C × C) (C × C) C (IdentityFunctor (C × C)) (@MonoidalStructure.tensor C m))
      --     (@eq.rec (Functor (C × C) (C × C))
      --        (@FunctorComposition (C × C) (C × C) (C × C) (SwitchProductCategory C C) (SwitchProductCategory C C))
      --        (λ (a : Functor (C × C) (C × C)),
      --           @NaturalTransformation (C × C) C
      --             (@FunctorComposition (C × C) (C × C) C (SwitchProductCategory C C) (@MonoidalStructure.tensor C m))
      --             (@FunctorComposition (C × C) (C × C) C a (@MonoidalStructure.tensor C m)))
      --        (t : NaturalTransformation (switch tensor) (switch switch tensor))
      --        (IdentityFunctor (C × C))
      --        (switch_twice_is_the_identity C C)))

-- f  = @NaturalTransformation.components (C × C) C
-- α  = Functor (C × C) C 
-- a  : α
-- a  = (@FunctorComposition (C × C) (C × C) C (SwitchProductCategory C C) (@MonoidalStructure.tensor C m))
-- β  = Functor (C × C) C
-- f  : Π (a : α) (b : β), S a b → Z a b
-- γ  = (Functor (C × C) (C × C)
-- g  = switch switch
-- g' = id
-- p  : g = g'
-- R  : γ → β
--    = λ g, (g tensor)
-- S  = λ a b, NaturalTransformation a b
--
-- f a (R g') (@eq.rec γ g (S a) t g' p)


-- c' = (@FunctorComposition (C × C) (C × C) C (IdentityFunctor (C × C)) (@MonoidalStructure.tensor C m))
-- c'' = (@FunctorComposition (C × C) (C × C) C (@FunctorComposition (C × C) (C × C) (C × C) (SwitchProductCategory C C) (SwitchProductCategory C C)) (@MonoidalStructure.tensor C m))
-- eq.rec ... : NaturalTransformation c c'
-- γ = (Functor (C × C) (C × C)
-- g = switch switch
-- S = Π (a : α) (g : γ), NaturalTransformation a (R g)
-- t : NaturalTransformation a (R g)
-- t : S a g
-- g' = Identity (C × C)
-- p : g = g'

-- c' = R g'
-- c'' = R g
-- R = Π g : γ, (g tensor)
-- R : γ → β

-- f a c' t' : Z a c'

-- f a (R g') (@eq.rec γ g S t g' p)
-- f a (@eq.rec γ g R c'' g' p) (@eq.rec γ g S t g' p)
-- @eq.rec γ g (Z a (R g)) (f a (R g) t) g' p
-- @eq.rec γ g (Z a ???) (f a (@eq.rec γ g' R c' g (eq.symm p)) t) g' p



lemma {u1 u2 u3 u4 u5} w
  { α : Type u1 } { β : Type u2 } { γ : Type u3 }
  { S : α → β → Type u4 }
  { Z : α → β → Type u5 }
  { a : α } { g : γ } ( R : γ → β ) { t : S a (R g) } { g' : γ } { p : g = g' } ( f : Π (a : α) (b : β), S a b → Z a b ):
  f a (R g') (@eq.rec γ g (λ g, S a (R g)) t g' p) 
    = 
  @eq.rec γ g (λ g, Z a (R g)) (f a (R g) t) g' p
    := begin induction p, reflexivity end

--
-- (@eq.rec (Functor (C × C) C)
--                 (@FunctorComposition (C × C) (C × C) C (IdentityFunctor (C × C)) (@MonoidalStructure.tensor C m))
--                 (λ (G : Functor (C × C) C),
--                    Π (X : (C × C).Obj),
--                      C.Hom
--                        (@Functor.onObjects (C × C) C
--                           (@FunctorComposition (C × C) (C × C) C (IdentityFunctor (C × C))
--                              (@MonoidalStructure.tensor C m))
--                           X)
--                        (@Functor.onObjects (C × C) C G X))
--                 (λ (X : (C × C).Obj),
--                    C.identity
--                      (@Functor.onObjects (C × C) C
--                         (@FunctorComposition (C × C) (C × C) C (IdentityFunctor (C × C))
--                            (@MonoidalStructure.tensor C m))
--                         X))
--                 (@MonoidalStructure.tensor C m)
--                 (@squared_Braiding._proof_3 C m)
--                 X)
lemma {u1 u2 u3} b { α : Type u1 } { a : α } { β : Type u2 } { Z : α → β → Type u3 } { t : Π (b : β), Z a b } { a' : α } { p : a = a' } 
  : @eq.rec α a _ t a' p = λ b : β, @eq.rec α a (λ _a, Z _a b) (t b) a' p :=
begin
  induction p,
  reflexivity
end

--  (@eq.rec (Functor (C × C) C)
--                 (@FunctorComposition (C × C) (C × C) C (IdentityFunctor (C × C)) (@MonoidalStructure.tensor C m))
--                 (λ (_a : Functor (C × C) C),
--                    C.Hom
--                      (@Functor.onObjects (C × C) C
--                         (@FunctorComposition (C × C) (C × C) C (IdentityFunctor (C × C))
--                            (@MonoidalStructure.tensor C m))
--                         (X_1, X_2))
--                      (@Functor.onObjects (C × C) C _a (X_1, X_2)))
--                 (C.identity
--                    (@Functor.onObjects (C × C) C
--                       (@FunctorComposition (C × C) (C × C) C (IdentityFunctor (C × C))
--                          (@MonoidalStructure.tensor C m))
--                       (X_1, X_2)))
--                 (@MonoidalStructure.tensor C m)
--                 (@squared_Braiding._proof_3 C m))
-- α = (Functor (C × C) C)
-- a = (@FunctorComposition (C × C) (C × C) C (IdentityFunctor (C × C)) (@MonoidalStructure.tensor C m))
-- f = C.identity
--   : Π X : C.Obj, C.Hom X X
-- r = @Functor.onObjects (C × C) C
-- x : (C × C).Obj
-- r a x : C.Obj
-- t = f (r a x)
--   : C.Hom (r a x) (r a x)

lemma {u1 u2 u3 u4} pull_function_out
  { α : Type u1 } { a : α } { β : Type u2 } { Z : β → Type u3 } { γ : Type u4 } { r : Π a : α, γ → β } { x : γ } { a' : α } { p : a = a' } ( f : Π (b : β), Z b ) :
  @eq.rec α a _ (f (r a x)) a' p = f (r a' x) := 
begin
induction p, reflexivity
end

-- This seems sensible, but applies too often.
lemma {u} bar { α : Type u } { a : α } { b : α } ( p : a = b ) : @eq.rec α a (λ b: α, b = a) (eq.refl a) b p = eq.symm p :=
begin
  cases p,
  reflexivity
end

lemma {u} foo { α : Type u } { a b : α } { p : a = b } : eq.symm (eq.symm p) = p := by reflexivity

@[simp] lemma {u v w} function_of_eq.rec { α : Type u } { a : α } { T : α → Type v } { S : α → Type w } ( t : T a ) { b : α } ( e : a = b ) ( f : Π { c : α }, T c → S c ) :
  @f b ( @eq.rec α a T t b e ) = @eq.rec α a S (@f a t) b e :=
begin
  cases e,
  reflexivity
end
@[simp] lemma {u v w} function_of_eq.drec { α : Type u } { a : α } { T : Π b : α, a = b → Type v } { S : Π b : α, a = b → Type v } ( t : T a (eq.refl a)) { b : α } ( e : a = b ) ( f : Π { c : α } { p : a = c }, T c p → S c p ) :
  f ( @eq.drec α a T t b e ) = @eq.drec α a S (f t) b e :=
begin
  cases e,
  reflexivity
end

lemma z {A : Type} { X : A } : (eq.mpr (propext (eq_self_iff_true X)) trivial) = rfl :=
begin
  -- unfold trivial,
  reflexivity
end
