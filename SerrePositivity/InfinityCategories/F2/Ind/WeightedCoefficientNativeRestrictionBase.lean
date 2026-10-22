module

public import SerrePositivity.InfinityCategories.F2.Ind.WeightedCoefficientNativeReconstructionLarge
public import SerrePositivity.InfinityCategories.F2.Ind.WeightedCoefficientNativeImage

/-!
概要：元の native 評価復元と全評価の同型を、同じ始点固定族の底上で合成可能にする。
方針：同じ復元の射影と元の共同射影の可換式を使い、相対前合成の二つの射を定める。
規約：元の底の射を厳密に保持。使われ方：元の全評価の指定値写像への比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable (κ : Cardinal.{u}) {C : SSet.{u}} [Quasicategory C]
  {I : Type u} [SmallCategory I] (F : I ⥤ RightFibrationObject C) (i : I) (x : C _⦋0⦌)
local notation "H" => twistedElementsHomDiagram (weightedDensityProjection F)
local notation "G" => weightedDensityJointTargetDiagram F
local notation "D" => weightedCoefficientNativeEvaluationDiagram κ F i x
local notation "k" => CategoryTheory.Functor.map SSet.uliftFunctor
  (weightedCoefficientEvaluationBase F i x)

/-- 元の始点固定族から、元の係数全空間への同じ射影の持ち上げ。 -/
def weightedCoefficientNativeSourceBase :=
  (SSet.uliftFunctor.{u + 1, u}).map
    (pullback.fst (F.obj i).val.hom (twistedArrowSourceProjection x))

/-- 元の全評価を同じ始点固定族へ制限した同じ共同底。 -/
def weightedCoefficientNativeGlobalBase :=
  (SSet.uliftFunctor.{u + 1, u}).map (weightedCoefficientSourceIntoTotal F i x) ≫
    (SSet.uliftFunctor.{u + 1, u}).map
      (twistedElementsReconstruction (weightedDensityProjection F) ≫
        smallLeftUnstraighteningProjection H)

/-- 元の native 評価復元を、元の大きい全空間へ送る。 -/
def weightedCoefficientNativeReconstructionLift :=
  (SSet.uliftFunctor.{u + 1, u}).map (weightedCoefficientNativeReconstruction κ F i x) ≫
    (smallLeftUnstraighteningIso D).hom

/-- 元の共同底と元の始点固定の射影の正方形は、持ち上げても厳密に可換。 -/
lemma weightedCoefficientNativeSourceBase_global :
    weightedCoefficientNativeSourceBase F i x ≫ k = weightedCoefficientNativeGlobalBase F i x := by
  rw [weightedCoefficientNativeGlobalBase, twistedElementsReconstruction_projection,
    ← CategoryTheory.Functor.map_comp, weightedCoefficientSourceIntoTotal_projection,
    CategoryTheory.Functor.map_comp]
  rfl

/-- 同じ持ち上げた native 評価復元は、元の係数全空間成分を保つ。 -/
lemma weightedCoefficientNativeReconstructionLift_projection :
    weightedCoefficientNativeReconstructionLift κ F i x ≫ leftUnstraighteningProjection D =
      weightedCoefficientNativeSourceBase F i x := by
  rw [weightedCoefficientNativeReconstructionLift, Category.assoc,
    smallLeftUnstraighteningIso_projection, ← CategoryTheory.Functor.map_comp,
    weightedCoefficientNativeReconstruction_projection]
  rfl

/-- 元の native 評価復元で、同じ共同底上の全変換を制限する。 -/
def weightedCoefficientNativeReconstructionPre :=
  relativeFunctorOverPre (leftUnstraighteningProjection G)
    (Over.homMk (weightedCoefficientNativeReconstructionLift κ F i x) (by
      change weightedCoefficientNativeReconstructionLift κ F i x ≫
        (leftUnstraighteningProjection D ≫ k) = weightedCoefficientNativeGlobalBase F i x
      rw [← Category.assoc, weightedCoefficientNativeReconstructionLift_projection,
        weightedCoefficientNativeSourceBase_global]) :
      Over.mk (weightedCoefficientNativeGlobalBase F i x) ⟶
        Over.mk (leftUnstraighteningProjection D ≫ k))

/-- 元の全評価同型を、同じ共同底上で元の係数・始点族へ制限する。 -/
def weightedCoefficientNativeGlobalPre :=
  relativeFunctorOverPre (leftUnstraighteningProjection G)
    (Over.homMk ((SSet.uliftFunctor.{u + 1, u}).map (weightedCoefficientSourceIntoTotal F i x)) rfl :
      Over.mk (weightedCoefficientNativeGlobalBase F i x) ⟶
        Over.mk ((SSet.uliftFunctor.{u + 1, u}).map
          (twistedElementsReconstruction (weightedDensityProjection F) ≫
            smallLeftUnstraighteningProjection H)))

end SerrePositivity.InfinityCategories.F2.Ind
