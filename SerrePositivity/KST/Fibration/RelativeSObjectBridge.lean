module
public import SerrePositivity.KST.Fibration.WeakStringCoreInclusionComparison
public import SerrePositivity.KST.Fibration.RelativeSKernelSquare

/-! # 元の object S 比較で相対 S の core 包含を厳密に保つ -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open SerrePositivity.KST.LocalizingInvariants
open SerrePositivity.KST.SConstruction
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration

/-- 元の object/core 比較と単回実現の座標同型の合成。 -/
def objectSingleRealizationComparison (X : StableModel.{u}) :
    objectSConstructionFunctor.obj X ⟶ (multiRealizationFunctor 1).obj X :=
  objectCoreRealizationComparison.app X ≫ (coreSingleRealizationIso X).hom

/-- 元の object と単回実現の比較は、同じ完全関手で厳密に自然。 -/
lemma objectSingleRealizationComparison_naturality {X Y : StableModel.{u}} (f : X ⟶ Y) :
    objectSConstructionFunctor.map f ≫ objectSingleRealizationComparison Y =
      objectSingleRealizationComparison X ≫ (multiRealizationFunctor 1).map f := by
  unfold objectSingleRealizationComparison
  rw [← Category.assoc, objectCoreRealizationComparison.naturality, Category.assoc,
    coreSingleRealizationIso_naturality, ← Category.assoc]

/-- object と単回実現の元の比較自体は局所化同型。 -/
theorem objectSingleRealizationComparison_localized_isIso (X : StableModel.{u}) :
    IsIso (AnodyneHomotopy.anodyneQ.map (objectSingleRealizationComparison X)) := by
  have : IsIso (AnodyneHomotopy.anodyneQ.map (objectCoreRealizationComparison.app X)) :=
    objectToCoreSRealization_localized_isIso X.carrier
  unfold objectSingleRealizationComparison
  rw [Functor.map_comp]
  infer_instance

/-- 元の object 比較を前合成した場合、相対 S と定数 W 列の比較は厳密に可換。 -/
theorem relativeSWeakStringMultiComparison_coreInclusion_object
    {B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C) :
    objectToCoreSRealization B.obj ≫ simplicialDiagonalFunctor.map
      (relativeSimplicialSConstructionCoreInclusion q.hom) ≫
        relativeSWeakStringMultiComparison q =
      objectSingleRealizationComparison (sInputModel B) ≫
        weakStringRealizationConstantDiagonal (multiRealizationFunctor 1) q := by
  let a : objectSConstructionFunctor.obj (sInputModel B) ⟶
      coreSRealizationFunctor.obj (sInputModel B) := objectToCoreSRealization B.obj
  let i : coreSRealizationFunctor.obj (sInputModel B) ⟶
      simplicialDiagonalFunctor.obj (relativeSimplicialSConstruction q.hom) :=
    simplicialDiagonalFunctor.map (relativeSimplicialSConstructionCoreInclusion q.hom)
  let c := relativeSWeakStringCoreComparison q
  let k := weakStringRealizationConstantDiagonal coreSRealizationFunctor q
  let j := simplicialDiagonalFunctor.map (weakStringCoreSingleRealizationIso q).hom
  let p := (coreSingleRealizationIso (sInputModel B)).hom
  let l := weakStringRealizationConstantDiagonal (multiRealizationFunctor 1) q
  have hc : a ≫ i ≫ c = a ≫ k :=
    relativeSWeakStringCoreComparison_coreInclusion_object q
  have hp : p ≫ l = k ≫ j := weakStringConstantDiagonal_coreSingle q
  change a ≫ i ≫ (c ≫ j) = (a ≫ p) ≫ l
  calc
    _ = (a ≫ i ≫ c) ≫ j := (Category.assoc _ _ _).symm
    _ = (a ≫ k) ≫ j := congrArg (fun m => m ≫ j) hc
    _ = _ := by rw [Category.assoc, ← hp, ← Category.assoc]

end SerrePositivity.KST.Fibration
