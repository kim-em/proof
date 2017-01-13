import standard

-- Lean's SMT tactic isn't yet hooked up by default. This snippet makes 'blast' available as an all purpose tactic.
meta def blast : tactic unit := using_smt $ return ()

-- This file develops Categories, Functors, and NaturalTransformations.

/-
-- As notational conventions, we denote
-- * Categories by capital latin letters near the begining of the alphabet (C, D, E, and then A, B when needed),
-- * Objects of categories by capital latin letters near the end of the alphabet,
-- * Morphisms by lower case latin letters,
-- * Functors by capital latin letters starting at F,
-- * NaturalTransformations by greek letters.
-/

/-
-- We've decided that Obj and Hom should be fields of Category, rather than parameters.
-- Mostly this is for the sake of simpler signatures, and it's possible that it is not the right choice.
-- Functor and NaturalTransformation are each parameterized by both their source and target.
-/

structure Category :=
  (Obj : Type)
  (Hom : Obj -> Obj -> Type)
  (identity : Π X : Obj, Hom X X)
  (compose  : Π ⦃X Y Z : Obj⦄, Hom X Y → Hom Y Z → Hom X Z)

  (left_identity  : Π ⦃X Y : Obj⦄ (f : Hom X Y), compose (identity _) f = f)
  (right_identity : Π ⦃X Y : Obj⦄ (f : Hom X Y), compose f (identity _) = f)
  (associativity  : Π ⦃W X Y Z : Obj⦄ (f : Hom W X) (g : Hom X Y) (h : Hom Y Z),
    compose (compose f g) h = compose f (compose g h))

attribute [class] Category
-- declaring it as a class from the beginning results in an insane
-- signature ... This really seems like it must be a bug, or at least
-- a rough edge.

instance ℕCategory : Category :=
  {
    Obj := unit,
    Hom := λ a b, ℕ,
    identity := λ a, 0,
    compose  := λ a b c, add,

    left_identity  := λ a b, zero_add,
      -- Sadly, "by blast" doesn't work here. I think this is because
      -- "by blast" checks if the heads of the expressions match,
      -- which is the case for right_identity and associativity, but
      -- not left_identity.
    right_identity := by blast, --λ a b, add_zero,
    associativity  := by blast  --λ a b c d, add_assoc
  }

structure Functor (C : Category) (D : Category) :=
  (onObjects   : C^.Obj → D^.Obj)
  (onMorphisms : Π ⦃X Y : C^.Obj⦄,
                C^.Hom X Y → D^.Hom (onObjects X) (onObjects Y))
  (identities : Π (X : C^.Obj),
    onMorphisms (C^.identity X) = D^.identity (onObjects X))
  (functoriality : Π ⦃X Y Z : C^.Obj⦄ (f : C^.Hom X Y) (g : C^.Hom Y Z),
    onMorphisms (C^.compose f g) = D^.compose (onMorphisms f) (onMorphisms g))

attribute [class] Functor

-- We define a coercion so that we can write `F X` for the functor `F` applied to the object `X`.
-- One can still write out `onObjects F X` when needed.
instance Functor_to_onObjects { C D : Category }: has_coe_to_fun (Functor C D) :=
{ F   := λ f, C^.Obj -> D^.Obj,
  coe := Functor.onObjects }

-- Unfortunately we haven't been able to set up similar notation for morphisms.
-- Instead we define notation so that `F <$> f` denotes the functor `F` applied to the morphism `f`.
-- One can still write out `onMorphisms F f` when needed, or even the very verbose `@Functor.onMorphisms C D F X Y f`.
namespace Functor
  -- Lean complains about the use of local variables in
  -- notation. There must be a way around that.
  infix `<$>`:50 := λ {C : Category} {D : Category}
                      (F : Functor C D) {X Y : C^.Obj} (f : C^.Hom X Y),
                      onMorphisms F f
end Functor

-- This defines a coercion allowing us to write `F f` for `onMorphisms F f`
-- but sadly it doesn't work if  to_onObjects is already in scope.
--instance Functor_to_onMorphisms { C D : Category } : has_coe_to_fun (Functor C D) :=
--{ F   := λ f, Π ⦃X Y : C^.Obj⦄, C^.Hom X Y → D^.Hom (f X) (f Y), -- contrary to usual use, `f` here denotes the Functor.
--  coe := Functor.onMorphisms }

instance IdentityFunctor ( C: Category ) : Functor C C :=
{
  onObjects     := λ X, X,
  onMorphisms   := λ X Y f, f,
  identities    := by blast,
  functoriality := by blast
}

instance FunctorComposition { C D E : Category } ( F : Functor C D ) ( G : Functor D E ) : Functor C E :=
{
  onObjects     := λ X, G (F X),
  onMorphisms   := λ _ _ f, G <$> (F <$> f),
  identities    := begin
                     intros,
                     rewrite [ - G^.identities, - F^.identities ]
                   end,
  functoriality := begin
                     intros,
                     rewrite [ - G^.functoriality, - F^.functoriality ]
                   end
}

instance DoublingAsFunctor : Functor ℕCategory ℕCategory :=
  { onObjects   := id,
    onMorphisms := (λ _ _ n, n + n),
      /-
      -- Sadly, "by blast" doesn't work below if we replace "n + n"
      -- with "2 * n".  Again, I think this is because the heads don't
      -- match. If you use "n * 2", then identities works by blast,
      -- but functoriality still doesn't.
      -/
    identities    := by blast,
    functoriality := by blast
  }

structure NaturalTransformation { C D : Category } ( F G : Functor C D ) :=
  (components: Π X : C^.Obj, D^.Hom (F X) (G X))
  (naturality: Π { X Y : C^.Obj }, Π f : C^.Hom X Y, D^.compose (F <$> f) (components Y) = D^.compose (components X) (G <$> f))

-- This defines a coercion so we can write `α X` for `components α X`.
instance NaturalTransformation_to_components { C D : Category } { F G : Functor C D } : has_coe_to_fun (NaturalTransformation F G) :=
{ F   := λ f, Π X : C^.Obj, D^.Hom (F X) (G X),
  coe := NaturalTransformation.components }

-- We'll want to be able to prove that two natural transformations are equal if they are componentwise equal.
lemma NaturalTransformations_componentwise_equal
  { C D : Category } 
  { F G : Functor C D } 
  ( α β : NaturalTransformation F G )
  ( w: Π X : C^.Obj, α X = β X ) : α = β :=
  begin
    induction α,
    induction β,
    -- Argh, how to complete this proof?
    exact sorry
  end

definition IdentityNaturalTransformation { C D : Category } (F : Functor C D) : NaturalTransformation F F :=
  {
    components := λ X, D^.identity (F X),
    naturality := begin
                    intros,
                    rewrite [ D^.left_identity, D^.right_identity ]
                  end
  }

definition vertical_composition_of_NaturalTransformations
  { C D : Category }
  { F G H : Functor C D }
  ( α : NaturalTransformation F G )
  ( β : NaturalTransformation G H ) : NaturalTransformation F H :=
  {
    components := λ X, D^.compose (α X) (β X),
    naturality := begin
                    intros,
                    /- this proof was written by a sufficient stupid process that I am confident a computer
                    -- could have done it! -/
                    rewrite D^.associativity,
                    rewrite - β^.naturality,
                    rewrite - D^.associativity,
                    rewrite α^.naturality,
                    rewrite D^.associativity
                  end
  }

definition horizontal_composition_of_NaturalTransformations
  { C D E : Category }
  { F G : Functor C D }
  { H I : Functor D E } 
  ( α : NaturalTransformation F G )
  ( β : NaturalTransformation H I ) : NaturalTransformation (FunctorComposition F H) (FunctorComposition G I) :=
  {
    components := λ X : C^.Obj, E^.compose (β (F X)) (I <$> (α X)),
    naturality := begin
                    intros,
                    rewrite - β^.naturality,
                    rewrite - β^.naturality,
                    exact sorry
                  end
  }

instance ProductCategory (C : Category) (D : Category) :
  Category :=
  {
    Obj := C^.Obj × D^.Obj,
    Hom := (λ X Y : C^.Obj × D^.Obj, C^.Hom (X^.fst) (Y^.fst) × D^.Hom (X^.snd) (Y^.snd)),
    identity := λ X, (C^.identity (X^.fst), D^.identity (X^.snd)),
    compose  := λ _ _ _ f g, (C^.compose (f^.fst) (g^.fst), D^.compose (f^.snd) (g^.snd)),

    left_identity  := begin
                        intros,
                        rewrite [ C^.left_identity, D^.left_identity ],
                        induction f,
                        simp
                      end,
    right_identity := begin
                        intros,
                        rewrite [ C^.right_identity, D^.right_identity],
                        induction f,
                        simp
                      end,
    associativity  := begin
                        intros,
                        rewrite [ C^.associativity, D^.associativity ]
                      end
  }

namespace ProductCategory
  notation C `×` D := ProductCategory C D
end ProductCategory

instance ProductFunctor { A B C D : Category } ( F : Functor A B ) ( G : Functor C D ) : Functor (A × C) (B × D) :=
{
  onObjects := λ X, (F X^.fst, G X^.snd),
  onMorphisms := λ _ _ f, (F <$> f^.fst, G <$> f^.snd),
  identities := begin
                  intros o,
                  induction o,
                  pose hF := F^.identities fst,
                  pose hG := G^.identities snd,                  
                  exact sorry
                end,
  functoriality := begin
                     intros,
                     exact sorry
                   end
}

check ProductFunctor

namespace ProductFunctor
  notation F `×` G := ProductFunctor F G
end ProductFunctor

def ℕTensorProduct : Functor (ℕCategory × ℕCategory) ℕCategory :=
  { onObjects     := prod.fst,
    onMorphisms   := λ _ _ n, n^.fst + n^.snd,
    identities    := by blast,
    functoriality := by blast
  }

instance SwitchProductCategory ( C D : Category ) : Functor (C × D) (D × C) :=
{
  onObjects     := λ X, (X^.snd, X^.fst),
  onMorphisms   := λ _ _ f, (f^.snd, f^.fst),
  identities    := by blast,
  functoriality := by blast
}

instance ProductCategoryAssociator ( C D E : Category ) : Functor ((C × D) × E) (C × (D × E)) :=
{
  onObjects     := λ X, (X^.fst^.fst, (X^.fst^.snd, X^.snd)),
  onMorphisms   := λ _ _ f, (f^.fst^.fst, (f^.fst^.snd, f^.snd)),
  identities    := by blast,
  functoriality := by blast
}

structure PreMonoidalCategory
  -- this is only for internal use: it has a tensor product, but no associator at all
  -- it's not interesting mathematically, but may allow us to introduce usable notation for the tensor product
  extends carrier : Category :=
  (tensor : Functor (carrier × carrier) carrier)
  (tensor_unit : Obj)
  (interchange: Π { A B C D E F: Obj }, Π f : Hom A B, Π g : Hom B C, Π h : Hom D E, Π k : Hom E F, 
    @Functor.onMorphisms _ _ tensor (A, D) (C, F) ((compose f g), (compose h k)) = compose (@Functor.onMorphisms _ _ tensor (A, D) (B, E) (f, h)) (@Functor.onMorphisms _ _ tensor (B, E) (C, F) (g, k)))

namespace PreMonoidalCategory
  infix `⊗`:70 := λ {C : PreMonoidalCategory} (X Y : C^.Obj),
                    Functor.onObjects C^.tensor (X, Y)
  infix `⊗m`:70 := λ {C : PreMonoidalCategory} {W X Y Z : C^.Obj}
                     (f : C^.Hom W X) (g : C^.Hom Y Z),
                     Functor.onMorphisms C^.tensor (f, g)
end PreMonoidalCategory


attribute [class] PreMonoidalCategory
attribute [instance] PreMonoidalCategory.to_Category
instance PreMonoidalCategory_coercion : has_coe PreMonoidalCategory Category := 
  ⟨PreMonoidalCategory.to_Category⟩

definition left_associated_triple_tensor ( C : PreMonoidalCategory ) : Functor ((C × C) × C) C :=
  FunctorComposition (C^.tensor × IdentityFunctor C) C^.tensor
definition right_associated_triple_tensor ( C : PreMonoidalCategory ) : Functor (C × (C × C)) C :=
  FunctorComposition (IdentityFunctor C × C^.tensor) C^.tensor

definition Associator ( C : PreMonoidalCategory ) := 
  NaturalTransformation 
    (left_associated_triple_tensor C) 
    (FunctorComposition (ProductCategoryAssociator C C C) (right_associated_triple_tensor C))

--print Associator
definition associator_components ( C : PreMonoidalCategory ) := Π X Y Z : C^.Obj, C^.Hom  (C^.tensor (C^.tensor (X, Y), Z)) (C^.tensor (X, C^.tensor (Y, Z)))

definition associator_to_components { C : PreMonoidalCategory } ( α : Associator C ) : associator_components C := 
begin
 blast,
 pose r := α^.components ((X, Y), Z),
 exact sorry
end

/- 
-- This should be impossible to prove in general, as of course the components might not
-- satisfy naturality. I'm imagining, however, that it might be possible to write a
-- tactic that, once it has seen the actual components, blasts naturality...
-/
definition associator_from_components { C: PreMonoidalCategory } ( α : associator_components C ) : Associator C :=
  begin
    exact sorry
  end

structure LaxMonoidalCategory
  extends carrier : PreMonoidalCategory :=
  --(associator' : Associator carrier)
  (associator : Π (X Y Z : Obj),
     Hom (tensor (tensor (X, Y), Z)) (tensor (X, tensor (Y, Z)))) 

-- Why can't we use notation here? It seems with slightly cleverer type checking it should work.
-- If we really can't make this work, remove PreMonoidalCategory, as it's useless.

-- TODO actually, express the associator as a natural transformation!
/- I tried writing the pentagon, but it doesn't type check. :-(
  (pentagon : Π (A B C D : Obj),
     -- we need to compare:
     -- ((AB)C)D ---> (A(BC))D ---> A((BC)D) ---> A(B(CD))
     -- ((AB)C)D ---> (AB)(CD) ---> A(B(CD))
     compose
       (compose
         (tensor <$> (associator A B C, identity D))
         (associator A (tensor (B, C)) D)
       ) (tensor <$> (identity A, associator B C D)) =
     compose
       (associator (tensor (A, B)) C D)
       (associator A B (tensor (C, D)))

  )
-/
/-
-- TODO(far future)
-- One should prove the first substantial result of this theory: that any two ways to reparenthesize are equal.
-- It requires introducing a representation of a reparathesization, but the proof should then be an easy induction.
-- It's a good example of something that is so easy for humans, that is better eventually be easy for the computer too!
-/

-- Notice that LaxMonoidalCategory.tensor has a horrible signature...
-- It sure would be nice if it read ... Functor (carrier × carrier) carrier
-- print LaxMonoidalCategory

attribute [class] LaxMonoidalCategory
attribute [instance] LaxMonoidalCategory.to_PreMonoidalCategory
instance LaxMonoidalCategory_coercion : has_coe LaxMonoidalCategory PreMonoidalCategory :=
  ⟨LaxMonoidalCategory.to_PreMonoidalCategory⟩


def ℕLaxMonoidalCategory : LaxMonoidalCategory :=
  { ℕCategory with
    tensor       := ℕTensorProduct,
    tensor_unit  := (),
    associator   := λ _ _ _, Category.identity ℕCategory (),
    interchange  := begin
                      exact sorry -- should be trivial, but how?
                    end
  }

structure OplaxMonoidalCategory
  extends carrier : PreMonoidalCategory :=
  -- TODO better name? unfortunately it doesn't yet make sense to say 'inverse_associator'.
  (backwards_associator : Π (X Y Z : Obj),
     Hom (tensor (X, tensor (Y, Z)))  (tensor (tensor (X, Y), Z)))

attribute [class] OplaxMonoidalCategory
attribute [instance] OplaxMonoidalCategory.to_PreMonoidalCategory
instance OplaxMonoidalCategory_coercion : has_coe OplaxMonoidalCategory PreMonoidalCategory :=
  ⟨OplaxMonoidalCategory.to_PreMonoidalCategory⟩

structure MonoidalCategory
  extends LaxMonoidalCategory, OplaxMonoidalCategory :=
  (associators_inverses_1: Π (X Y Z : Obj), compose (associator X Y Z) (backwards_associator X Y Z) = identity (tensor (tensor (X, Y), Z)))
  (associators_inverses_2: Π (X Y Z : Obj), compose (backwards_associator X Y Z) (associator X Y Z) = identity (tensor (X, tensor (Y, Z))))

attribute [class] MonoidalCategory
attribute [instance] MonoidalCategory.to_LaxMonoidalCategory
instance MonoidalCategory_coercion_to_LaxMonoidalCategory : has_coe MonoidalCategory LaxMonoidalCategory := ⟨MonoidalCategory.to_LaxMonoidalCategory⟩
--instance MonoidalCategory_coercion_to_OplaxMonoidalCategory : has_coe MonoidalCategory OplaxMonoidalCategory := ⟨MonoidalCategory.to_OplaxMonoidalCategory⟩

namespace MonoidalCategory
  infix `⊗`:70 := λ {C : MonoidalCategory} (X Y : Obj C),
                    tensor C (X, Y)
  infix `⊗`:70 := λ {C : MonoidalCategory} {W X Y Z : Obj C}
                     (f : Hom C W X) (g : Hom C Y Z),
                     C^.tensor <$> (f, g)
end MonoidalCategory


definition tensor_on_left (C: MonoidalCategory) (Z: C^.Obj) : Functor C C :=
  {
    onObjects := λ X, Z ⊗ X,
    onMorphisms := --λ _ _ f, (C^.identity Z) ⊗ f,
                   --λ _ _ f, C^.tensor <$> (C^.identity Z, f),
                   --λ _ _ f, onMorphisms (C^.tensor) (C^.identity Z f),
                   λ X Y f, @Functor.onMorphisms _ _ (C^.tensor) (Z, X) (Z, Y) (C^.identity Z, f),
    identities := begin
                    intros,
                    pose H := Functor.identities (C^.tensor) (Z, X),
                    -- these next two steps are ridiculous... surely we shouldn't have to do this.
                    assert ids : Category.identity C = MonoidalCategory.identity C, blast,
                    rewrite ids,
                    exact H -- blast doesn't work here?!
                  end,
    functoriality := begin
                       intros,
                       -- similarly here
                       assert composes : Category.compose C = MonoidalCategory.compose C, blast, 
                       rewrite composes,
                       rewrite - C^.interchange,
                       rewrite C^.left_identity
                     end
  }

structure Isomorphism ( C: Category ) ( X Y : C^.Obj ) :=
  (morphism : C^.Hom X Y)
  (inverse : C^.Hom Y X)
  (witness_1 : C^.compose morphism inverse = C^.identity X)
  (witness_2 : C^.compose inverse morphism = C^.identity Y)

instance Isomorphism_coercion_to_morphism { C : Category } { X Y : C^.Obj } : has_coe (Isomorphism C X Y) (C^.Hom X Y) :=
  { coe := Isomorphism.morphism }

-- To define a natural isomorphism, we'll define the functor category, and ask for an isomorphism there.
-- It's then a lemma that each component is an isomorphism, and vice versa.

instance FunctorCategory ( C D : Category ) : Category :=
{
  Obj := Functor C D,
  Hom := λ F G, NaturalTransformation F G,

  identity := λ F, IdentityNaturalTransformation F,
  compose := @vertical_composition_of_NaturalTransformations C D,

  left_identity := sorry, -- these facts all rely on NaturalTransformations_componentwise_equal above.
  right_identity := sorry,
  associativity := sorry
}

definition NaturalIsomorphism { C D : Category } ( F G : Functor C D ) := Isomorphism (FunctorCategory C D) F G

-- TODO I'm confused how to even say this!
--lemma components_of_NaturalIsomorphism_are_isomorphisms { C D : Category } { F G : Functor C D } ( α : NaturalIsomorphism F G ) ....?

structure BraidedMonoidalCategory
  extends parent: MonoidalCategory :=
  (braiding: NaturalIsomorphism (tensor) (FunctorComposition (SwitchProductCategory parent parent) tensor))

-- Coercion of a NaturalIsomorphism to a NaturalTransformation doesn't seem to work. :-(

structure SymmetricMonoidalCategory
  extends parent: BraidedMonoidalCategory :=
  (symmetry: vertical_composition_of_NaturalTransformations braiding braiding = IdentityNaturalTransformation (IdentityFunctor (parent × parent)))

structure EnrichedCategory :=
  (V: MonoidalCategory)
  (Obj : Type )
  (Hom : Obj -> Obj -> V^.Obj)
  (compose :  Π ⦃X Y Z : Obj⦄, V^.Hom ((Hom X Y) ⊗ (Hom Y Z)) (Hom X Z))
  -- TODO and so on

-- TODO How would we define an additive category, now? We don't want to say:
--   Hom : Obj -> Obj -> AdditiveGroup
-- instead we want to express something like:
--   Hom : Obj -> Obj -> [something coercible to AdditiveGroup]
