open tactic
open smt_tactic

def pointwise_attribute : user_attribute := {
  name := `pointwise,
  descr := "A lemma that proves things are equal using the fact they are pointwise equal."
}

run_command attribute.register `pointwise_attribute

/- Try to apply one of the given lemas, it succeeds if one of them succeeds. -/
meta def any_apply : list name → tactic unit
| []      := failed
| (c::cs) := (mk_const c >>= fapply) <|> any_apply cs

meta def smt_simp   : tactic unit := using_smt $ intros >> try simp
meta def smt_eblast : tactic unit := using_smt $ intros >> try simp >> try eblast
meta def smt_ematch : tactic unit := using_smt $ intros >> add_lemmas_from_facts >> try ematch

meta def pointwise (and_then : tactic unit) : tactic unit :=
do cs ← attribute.get_instances `pointwise,
   try (seq (any_apply cs) and_then)

attribute [pointwise] funext

meta def blast        : tactic unit := smt_eblast >> pointwise blast

-- In a timing test on 2017-02-18, I found that using `abstract { blast }` instead of just `blast` resulted in a 5x speed-up!
notation `♮` := by abstract { blast }

@[pointwise] lemma {u v} pair_equality {α : Type u} {β : Type v} { X: α × β }: (X^.fst, X^.snd) = X := begin induction X, blast end
@[pointwise] lemma {u v} pair_equality_1 {α : Type u} {β : Type v} { X: α × β } { A : α } ( p : A = X^.fst ) : (A, X^.snd) = X := begin induction X, blast end
@[pointwise] lemma {u v} pair_equality_2 {α : Type u} {β : Type v} { X: α × β } { B : β } ( p : B = X^.snd ) : (X^.fst, B) = X := begin induction X, blast end
attribute [pointwise] subtype.eq

def {u} auto_cast {α β : Type u} {h : α = β} (a : α) := cast h a
@[simp] lemma {u} auto_cast_identity {α : Type u} (a : α) : @auto_cast α α (by smt_ematch) a = a := ♮
notation `⟦` p `⟧` := @auto_cast _ _ (by smt_ematch) p
universe variables u v

structure Category :=
  (Obj : Type u)
  (Hom : Obj → Obj → Type v)
  (identity : Π X : Obj, Hom X X)
  (compose  : Π { X Y Z : Obj }, Hom X Y → Hom Y Z → Hom X Z)

  (left_identity  : ∀ { X Y : Obj } (f : Hom X Y), compose (identity _) f = f)
  (right_identity : ∀ { X Y : Obj } (f : Hom X Y), compose f (identity _) = f)
  (associativity  : ∀ { W X Y Z : Obj } (f : Hom W X) (g : Hom X Y) (h : Hom Y Z),
    compose (compose f g) h = compose f (compose g h))

attribute [simp] Category.left_identity
attribute [simp] Category.right_identity
attribute [ematch] Category.associativity

definition CategoryOfTypes : Category :=
{
    Obj := Type u,
    Hom := λ a b, a → b,

    identity := λ a, id,
    compose  := λ _ _ _ f g, g ∘ f,

    left_identity  := ♮,
    right_identity := ♮,
    associativity  := ♮
}

universe variables u1 v1 u2 v2 u3 v3

structure Functor (C : Category.{ u1 v1 }) (D : Category.{ u2 v2 }) :=
  (onObjects   : C^.Obj → D^.Obj)
  (onMorphisms : Π { X Y : C^.Obj },
                C^.Hom X Y → D^.Hom (onObjects X) (onObjects Y))
  (identities : ∀ (X : C^.Obj),
    onMorphisms (C^.identity X) = D^.identity (onObjects X))
  (functoriality : ∀ { X Y Z : C^.Obj } (f : C^.Hom X Y) (g : C^.Hom Y Z),
    onMorphisms (C^.compose f g) = D^.compose (onMorphisms f) (onMorphisms g))

attribute [simp] Functor.identities
attribute [simp] Functor.functoriality
attribute [ematch] Functor.functoriality

-- We define a coercion so that we can write `F X` for the functor `F` applied to the object `X`.
-- One can still write out `onObjects F X` when needed.
instance Functor_to_onObjects { C D : Category }: has_coe_to_fun (Functor C D) :=
{ F   := λ f, C^.Obj -> D^.Obj,
  coe := Functor.onObjects }

definition IdentityFunctor ( C: Category ) : Functor C C :=
{
  onObjects     := id,
  onMorphisms   := λ _ _ f, f,
  identities    := ♮,
  functoriality := ♮
}

definition FunctorComposition { C D E : Category } ( F : Functor C D ) ( G : Functor D E ) : Functor C E :=
{
  onObjects     := λ X, G (F X),
  onMorphisms   := λ _ _ f, G^.onMorphisms (F^.onMorphisms f),
  identities    := ♮,
  functoriality := ♮
}

-- namespace Functor
--   notation F `∘` G := FunctorComposition F G
-- end Functor

structure NaturalTransformation { C D : Category } ( F G : Functor C D ) :=
  (components: Π X : C^.Obj, D^.Hom (F X) (G X))
  (naturality: ∀ { X Y : C^.Obj } (f : C^.Hom X Y),
     D^.compose (F^.onMorphisms f) (components Y) = D^.compose (components X) (G^.onMorphisms f))

attribute [ematch] NaturalTransformation.naturality

-- This defines a coercion so we can write `α X` for `components α X`.
instance NaturalTransformation_to_components { C D : Category } { F G : Functor C D } : has_coe_to_fun (NaturalTransformation F G) :=
{ F   := λ f, Π X : C^.Obj, D^.Hom (F X) (G X),
  coe := NaturalTransformation.components }

-- We'll want to be able to prove that two natural transformations are equal if they are componentwise equal.
@[pointwise] lemma NaturalTransformations_componentwise_equal
  { C D : Category }
  { F G : Functor C D }
  ( α β : NaturalTransformation F G )
  ( w : ∀ X : C^.Obj, α X = β X ) : α = β :=
  begin
    induction α with αc,
    induction β with βc,
    have hc : αc = βc, from funext w,
    by subst hc
  end

definition IdentityNaturalTransformation { C D : Category } (F : Functor C D) : NaturalTransformation F F :=
  {
    components := λ X, D^.identity (F X),
    naturality := ♮
  }

definition vertical_composition_of_NaturalTransformations
  { C D : Category }
  { F G H : Functor C D }
  ( α : NaturalTransformation F G )
  ( β : NaturalTransformation G H ) : NaturalTransformation F H :=
  {
    components := λ X, D^.compose (α X) (β X),
    naturality := ♮
  }

definition horizontal_composition_of_NaturalTransformations
  { C D E : Category }
  { F G : Functor C D }
  { H I : Functor D E }
  ( α : NaturalTransformation F G )
  ( β : NaturalTransformation H I ) : NaturalTransformation (FunctorComposition F H) (FunctorComposition G I) :=
  {
    components := λ X : C^.Obj, E^.compose (β (F X)) (I^.onMorphisms (α X)),
    naturality := begin
                    blast,
                    unfold FunctorComposition, 
                    blast
                  end
  }

definition whisker_on_left
  { C D E : Category }
  ( F : Functor C D )
  { G H : Functor D E }
  ( α : NaturalTransformation G H ) :
  NaturalTransformation (FunctorComposition F G) (FunctorComposition F H) :=
  horizontal_composition_of_NaturalTransformations (IdentityNaturalTransformation F) α

definition whisker_on_right
  { C D E : Category }
  { F G : Functor C D }
  ( α : NaturalTransformation F G )
  ( H : Functor D E ) :
  NaturalTransformation (FunctorComposition F H) (FunctorComposition G H) :=
  horizontal_composition_of_NaturalTransformations α (IdentityNaturalTransformation H)

definition ProductCategory (C : Category.{u1 v1}) (D : Category.{u2 v2}) : Category :=
{
  Obj      := C^.Obj × D^.Obj,
  Hom      := (λ X Y : C^.Obj × D^.Obj, C^.Hom (X^.fst) (Y^.fst) × D^.Hom (X^.snd) (Y^.snd)),
  identity := λ X, (C^.identity (X^.fst), D^.identity (X^.snd)),
  compose  := λ _ _ _ f g, (C^.compose (f^.fst) (g^.fst), D^.compose (f^.snd) (g^.snd)),

  left_identity  := ♮,
  right_identity := ♮,
  associativity  := ♮
}

namespace ProductCategory
  notation C `×` D := ProductCategory C D
end ProductCategory

definition ProductFunctor { A B C D : Category } ( F : Functor A B ) ( G : Functor C D ) : Functor (A × C) (B × D) :=
{
  onObjects     := λ X, (F X^.fst, G X^.snd),
  onMorphisms   := λ _ _ f, (F^.onMorphisms f^.fst, G^.onMorphisms f^.snd),
  identities    := begin
                     blast,
                     unfold ProductCategory,
                     blast,
                   end,
  functoriality := begin
                     blast,
                     unfold ProductCategory,
                     blast
                   end
}

namespace ProductFunctor
  notation F `×` G := ProductFunctor F G
end ProductFunctor

definition ProductNaturalTransformation { A B C D : Category } { F G : Functor A B } { H I : Functor C D } (α : NaturalTransformation F G) (β : NaturalTransformation H I) : NaturalTransformation (F × H) (G × I) :=
{
  components := λ X, (α X^.fst, β X^.snd),
  naturality := begin
                  blast,
                  unfold ProductFunctor,
                  blast,
                  unfold ProductCategory,
                  blast
                end
}

namespace ProductNaturalTransformation
  notation α `×` β := ProductNaturalTransformation α β
end ProductNaturalTransformation

definition ProductCategoryAssociator
  ( C : Category.{ u1 v1 } )
  ( D : Category.{ u2 v2 } )
  ( E : Category.{ u3 v3 } )
  : Functor ((C × D) × E) (C × (D × E)) :=
{
  onObjects     := λ X, (X^.fst^.fst, (X^.fst^.snd, X^.snd)),
  onMorphisms   := λ _ _ f, (f^.fst^.fst, (f^.fst^.snd, f^.snd)),
  identities    := ♮,
  functoriality := ♮
}

@[reducible] definition TensorProduct ( C: Category ) := Functor ( C × C ) C

definition left_associated_triple_tensor ( C : Category.{ u v } ) ( tensor : TensorProduct C ) : Functor ((C × C) × C) C :=
  FunctorComposition (tensor × IdentityFunctor C) tensor
definition right_associated_triple_tensor ( C : Category.{ u v } ) ( tensor : TensorProduct C ) : Functor (C × (C × C)) C :=
  FunctorComposition (IdentityFunctor C × tensor) tensor

@[reducible] definition Associator { C : Category.{ u v } } ( tensor : TensorProduct C ) := 
  NaturalTransformation 
    (left_associated_triple_tensor C tensor) 
    (FunctorComposition (ProductCategoryAssociator C C C) (right_associated_triple_tensor C tensor))

definition Pentagon { C : Category } { tensor : TensorProduct C } ( associator : Associator tensor ) :=
  let α ( X Y Z : C^.Obj ) := associator ((X, Y), Z) in
  let tensorObjects ( X Y : C^.Obj ) := tensor^.onObjects (X, Y) in
  let tensorMorphisms { W X Y Z : C^.Obj } ( f : C^.Hom W X ) ( g : C^.Hom Y Z ) : C^.Hom (tensorObjects W Y) (tensorObjects X Z) := tensor^.onMorphisms (f, g) in
  ∀ W X Y Z : C^.Obj, 
    C^.compose (α (tensorObjects W X) Y Z) (α W X (tensorObjects Y Z))
  = C^.compose (C^.compose (tensorMorphisms (α W X Y) (C^.identity Z)) (α W (tensorObjects X Y) Z)) (tensorMorphisms (C^.identity W) (α X Y Z)) 

structure MonoidalCategory
  extends carrier : Category :=
  (tensor                    : TensorProduct carrier)
  (associator_transformation : Associator tensor)
  (pentagon                  : Pentagon associator_transformation)

instance MonoidalCategory_coercion : has_coe MonoidalCategory.{u v} Category.{u v} :=
  ⟨MonoidalCategory.to_Category⟩

@[reducible] definition MonoidalCategory.tensorObjects   ( C : MonoidalCategory ) ( X Y : C^.Obj )                                           : C^.Obj := C^.tensor (X, Y)
@[reducible] definition MonoidalCategory.tensorMorphisms ( C : MonoidalCategory ) { W X Y Z : C^.Obj } ( f : C^.Hom W X ) ( g : C^.Hom Y Z ) : C^.Hom (C^.tensor (W, Y)) (C^.tensor (X, Z)) := C^.tensor^.onMorphisms (f, g)
@[ematch] definition MonoidalCategory.interchange
  ( C : MonoidalCategory )
  { U V W X Y Z: C^.Obj }
  ( f : C^.Hom U V )( g : C^.Hom V W )( h : C^.Hom X Y )( k : C^.Hom Y Z ) :
  @Functor.onMorphisms _ _ C^.tensor (U, X) (W, Z) ((C^.compose f g), (C^.compose h k)) = C^.compose (@Functor.onMorphisms _ _ C^.tensor (U, X) (V, Y) (f, h)) (@Functor.onMorphisms _ _ C^.tensor (V, Y) (W, Z) (g, k)) :=
  @Functor.functoriality (C × C) C C^.tensor (U, X) (V, Y) (W, Z) (f, h) (g, k)

definition TensorProductOfTypes : TensorProduct CategoryOfTypes :=
{
  onObjects     := λ p, prod p.1 p.2,
  onMorphisms   := λ _ _ p, λ q, (p.1 q.1, p.2 q.2),
  identities    := ♮,
  functoriality := ♮
}

definition MonoidalCategoryOfTypes : MonoidalCategory :=
{
  CategoryOfTypes with
  tensor := TensorProductOfTypes,
  associator_transformation := {
    components := λ p, λ t, (t.1.1,(t.1.2, t.2)),
    naturality := ♮
  },
  pentagon := begin
                blast,
                unfold Pentagon,
                blast
              end
}

local attribute [reducible] lift_t coe_t coe_b

@[simp] lemma bifunctor_identities
  { C D E : Category }
  ( X : C^.Obj ) ( Y : D^.Obj )
  ( F : Functor (C × D) E ) : @Functor.onMorphisms _ _ F (X, Y) (X, Y) (C^.identity X, D^.identity Y) = E^.identity (F^.onObjects (X, Y)) :=
  begin
    blast,
    assert p : (C^.identity X, D^.identity Y) = (C × D)^.identity (X, Y), blast,
    rewrite p,
    blast
  end 


set_option pp.implicit true

definition tensor_on_left { C: MonoidalCategory.{u v} } ( Z: C^.Obj ) : Functor.{u v u v} C C :=
{
  onObjects := λ X, C^.tensorObjects Z X,
  onMorphisms := λ X Y f, C^.tensorMorphisms (C^.identity Z) f,
  identities := ♮,
  functoriality := begin
                      blast,
                      -- TODO I'd hope the blast could just do these steps: interchange has [ematch], and left_identity has [simp].
                      rewrite - C^.interchange,
                      rewrite C^.left_identity
                    end
}

-- @[reducible] definition pentagon_3step_1 ( C : MonoidalCategory.{ u v } ) :=
--   let α := C^.associator_transformation in
--   whisker_on_right
--     (α × IdentityNaturalTransformation (IdentityFunctor C))
--     C^.tensor

-- @[reducible] definition pentagon_3step_2 ( C : MonoidalCategory.{ u v } ) :=
--   let α := C^.associator_transformation in
--   whisker_on_left
--     (FunctorComposition
--       (ProductCategoryAssociator C C C × IdentityFunctor C)
--       ((IdentityFunctor C × C^.tensor) × IdentityFunctor C))
--     α

-- @[reducible] definition pentagon_3step_3 ( C : MonoidalCategory.{ u v } ) :=
--   let α := C^.associator_transformation in
--   whisker_on_left
--     (FunctorComposition
--       (ProductCategoryAssociator C C C × IdentityFunctor C)
--       (ProductCategoryAssociator C (C × C) C))
--     (whisker_on_right
--       (IdentityNaturalTransformation (IdentityFunctor C) × α)
--       C^.tensor)

-- @[reducible] definition pentagon_3step ( C : MonoidalCategory.{ u v } ) :=
--   vertical_composition_of_NaturalTransformations
--     (vertical_composition_of_NaturalTransformations
--       (pentagon_3step_1 C)
--       (pentagon_3step_2 C))
--     (pentagon_3step_3 C)

-- @[reducible] definition pentagon_2step_1 ( C : MonoidalCategory.{ u v } ) :=
--   let α := C^.associator_transformation in
--   whisker_on_left
--     ((C^.tensor × IdentityFunctor C) × IdentityFunctor C)
--     α

-- @[reducible] definition pentagon_2step_2 ( C : MonoidalCategory.{ u v } ) :=
--   let α := C^.associator_transformation in
--   whisker_on_left
--     (FunctorComposition
--       (ProductCategoryAssociator (C × C) C C)
--       (IdentityFunctor (C × C) × C^.tensor))
--     α

-- @[reducible] definition pentagon_2step ( C : MonoidalCategory.{ u v } ) :=
--   vertical_composition_of_NaturalTransformations
--     (pentagon_2step_1 C)
--     (pentagon_2step_2 C)

-- -- adding these attributes increased compile time from 1.5 minutes to 13 minutes. :-(
-- -- attribute [simp] MonoidalCategory.left_identity
-- -- attribute [simp] MonoidalCategory.right_identity

-- lemma pentagon_in_terms_of_natural_transformations
--   ( C : MonoidalCategory ) :
--   pentagon_2step C = pentagon_3step C :=
--   begin
--     blast, 
--     induction X with PQR S,
--     induction PQR with PQ R,
--     induction PQ with P Q,
--     pose p := C^.pentagon P Q R S,
--     -- notice that the hypothesis p is gross, until we blast!
--     blast,
--     -- I don't understand why this isn't being done by blast automatically: Functor.identities has [simp].
--     -- Moreover, I don't understand why `rewrite bifunctor_identities` doesn't apply here.
--     repeat { rewrite C^.tensor^.identities <|> rewrite C^.left_identity <|> rewrite C^.right_identity },
--     blast
--   end
