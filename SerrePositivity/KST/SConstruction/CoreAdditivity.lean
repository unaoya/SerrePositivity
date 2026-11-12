module
public import SerrePositivity.KST.SConstruction.ObjectAdditivity
public import SerrePositivity.KST.SConstruction.ObjectCoreWeakEquivalence

/-! # core S• 実現の加法性
概要：cofiber 図式の subobject・quotient の対は core S• の対角実現の後で弱同値。
方針：object 加法性を自然な object/core 比較と積の弱同値で移す。
規約：追加の加法性仮定を置かない。使われ方：反復 S• の delooping。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory CategoryTheory.MonoidalCategory SSet
open SerrePositivity.InfinityCategories SerrePositivity.SimplicialModel

/-- 一回の core S• の対角実現を安定な入力上の関手にする。 -/
def coreSRealizationFunctor : StableModel.{u} ⥤ SSet.{u} :=
  simplicialStableEndofunctor.flip ⋙
    (Functor.whiskeringRight SimplexCategoryᵒᵖ StableModel.{u} SSet.{u}).obj
      (stableModelForget ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor) ⋙ simplicialDiagonalFunctor

/-- object S• から core S• 実現への元の比較は完全関手について自然。 -/
def objectCoreRealizationComparison : objectSConstructionFunctor.{u} ⟶ coreSRealizationFunctor where
  app X := objectToCoreSRealization X.carrier
  naturality {_X _Y} f := objectToCoreSRealization_naturality
    (Functor.whiskerRight (simplicialStableEndofunctor.flip.map f) stableModelForget)

/-- core S• 実現の subobject・quotient からなる加法性の射。 -/
def coreSAdditivityMap (X : StableModel.{u}) :
    coreSRealizationFunctor.obj (cofiberStableModel X) ⟶
      coreSRealizationFunctor.obj X ⊗ coreSRealizationFunctor.obj X :=
  CartesianMonoidalCategory.lift
    (coreSRealizationFunctor.map (cofiberStableSubobject X))
    (coreSRealizationFunctor.map (cofiberStableQuotient X))

/-- 加法性の比較正方形は元の object/core 写像で厳密に可換。 -/
lemma objectCoreAdditivity_commute (X : StableModel.{u}) :
    objectSAdditivityMap X ≫
      (objectToCoreSRealization X.carrier ⊗ₘ objectToCoreSRealization X.carrier) =
    objectToCoreSRealization (cofiberStableModel X).carrier ≫ coreSAdditivityMap X := by
  change CartesianMonoidalCategory.lift
      (objectSConstructionFunctor.map (cofiberStableSubobject X))
      (objectSConstructionFunctor.map (cofiberStableQuotient X)) ≫
        (objectCoreRealizationComparison.app X ⊗ₘ objectCoreRealizationComparison.app X) =
    objectCoreRealizationComparison.app (cofiberStableModel X) ≫
      CartesianMonoidalCategory.lift
        (coreSRealizationFunctor.map (cofiberStableSubobject X))
        (coreSRealizationFunctor.map (cofiberStableQuotient X))
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, CartesianMonoidalCategory.tensorHom_fst,
      CartesianMonoidalCategory.lift_fst_assoc, CartesianMonoidalCategory.lift_fst]
    exact objectCoreRealizationComparison.naturality (cofiberStableSubobject X)
  · simp only [Category.assoc, CartesianMonoidalCategory.tensorHom_snd,
      CartesianMonoidalCategory.lift_snd_assoc, CartesianMonoidalCategory.lift_snd]
    exact objectCoreRealizationComparison.naturality (cofiberStableQuotient X)

/-- object/core 比較の積は局所化同型。 -/
lemma objectCoreComparison_tensor_localized_isIso (X : StableModel.{u}) :
    IsIso (AnodyneHomotopy.anodyneQ.map
      (objectToCoreSRealization X.carrier ⊗ₘ objectToCoreSRealization X.carrier)) := by
  have h := objectToCoreSRealization_localized_isIso X.carrier
  have := AnodyneHomotopy.whiskerRight_anodyneQ_isIso
    (objectToCoreSRealization X.carrier) h (objectSConstruction X.carrier)
  have := AnodyneHomotopy.whiskerLeft_anodyneQ_isIso
    (objectToCoreSRealization X.carrier) h
      (simplicialDiagonalFunctor.obj (simplicialCoreSConstruction X.carrier))
  rw [tensorHom_def, AnodyneHomotopy.anodyneQ.map_comp]
  infer_instance

/-- core S• 実現の加法性：subobject・quotient の射対は anodyne 局所化で同型。 -/
lemma coreSAdditivityMap_localized_isIso (X : StableModel.{u}) :
    IsIso (AnodyneHomotopy.anodyneQ.map (coreSAdditivityMap X)) := by
  let Q := AnodyneHomotopy.anodyneQ
  have := objectSAdditivityMap_localized_isIso X
  have := objectCoreComparison_tensor_localized_isIso X
  have := objectToCoreSRealization_localized_isIso (cofiberStableModel X).carrier
  have he := congrArg Q.map (objectCoreAdditivity_commute X)
  rw [Q.map_comp, Q.map_comp] at he
  have hi : IsIso (Q.map (objectToCoreSRealization (cofiberStableModel X).carrier) ≫
      Q.map (coreSAdditivityMap X)) := he ▸ inferInstance
  exact (isIso_comp_left_iff _ _).mp hi

end SerrePositivity.KST.SConstruction
