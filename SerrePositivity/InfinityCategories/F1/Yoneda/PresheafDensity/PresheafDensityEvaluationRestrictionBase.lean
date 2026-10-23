module

public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.PresheafDensityEvaluationReconstructionNaturality
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.PresheafDensityEvaluationRelativeImage

/-!
概要：同じ始点固定の全族上で、評価復元射と大域評価の底の表示を揃える。
方針：元の共同射影の正方形と、評価復元射の射影公式を使う。
規約：底の射を厳密に保持し、相対 Hom 内の比較を可能にする。
使われ方：評価変換の像と大域評価の相対同型の合成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {C : SSet.{u}} [Quasicategory C]
  (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u}) (x : C _⦋0⦌)
local notation "p" => smallRightUnstraighteningProjection F
local notation "H" => twistedElementsHomDiagram p
local notation "G" => presheafTwistedElementsTargetDiagram F
local notation "Dx" => presheafDensityEvaluationDiagram F x

/-- 元の始点固定の全族から同じ終点の全空間への持ち上げた射影。 -/
def presheafDensityEvaluationSourceBase :=
  (SSet.uliftFunctor.{u + 1, u}).map (pullback.fst p (twistedArrowSourceProjection x))

/-- 元の大域評価同型を同じ始点固定の全族へ制限した底。 -/
def presheafDensityEvaluationGlobalBase :=
  (SSet.uliftFunctor.{u + 1, u}).map (twistedSourceElementsComparison p x) ≫
    (SSet.uliftFunctor.{u + 1, u}).map
      (twistedElementsReconstruction p ≫ smallLeftUnstraighteningProjection H)

/-- 同じ評価復元射を元の大きい評価図式の全空間へ送る。 -/
def presheafDensityEvaluationReconstructionLift :=
  (SSet.uliftFunctor.{u + 1, u}).map (presheafDensityEvaluationReconstruction F x) ≫
    (smallLeftUnstraighteningIso Dx).hom

/-- 元の共同射影と始点固定の射影の正方形は、持ち上げても厳密に可換。 -/
lemma presheafDensityEvaluationSourceBase_global :
    presheafDensityEvaluationSourceBase F x ≫
      (SSet.uliftFunctor.{u + 1, u}).map (presheafDensitySourceInclusion F x) =
        presheafDensityEvaluationGlobalBase F x := by
  rw [presheafDensityEvaluationGlobalBase, twistedElementsReconstruction_projection,
    ← Functor.map_comp, twistedSourceElementsComparison_projection, Functor.map_comp]
  rfl

/-- 同じ大きい評価復元射の射影は、元の終点の全空間への射影。 -/
lemma presheafDensityEvaluationReconstructionLift_projection :
    presheafDensityEvaluationReconstructionLift F x ≫ leftUnstraighteningProjection Dx =
      presheafDensityEvaluationSourceBase F x := by
  rw [presheafDensityEvaluationReconstructionLift, Category.assoc,
    smallLeftUnstraighteningIso_projection, ← Functor.map_comp,
    presheafDensityEvaluationReconstruction_projection]
  rfl

/-- 同じ底の上で評価復元射に沿って相対変換を制限する。 -/
def presheafDensityEvaluationReconstructionPre :=
  relativeFunctorOverPre (leftUnstraighteningProjection G)
    (Over.homMk (presheafDensityEvaluationReconstructionLift F x) (by
      change presheafDensityEvaluationReconstructionLift F x ≫
        (leftUnstraighteningProjection Dx ≫
          (SSet.uliftFunctor.{u + 1, u}).map (presheafDensitySourceInclusion F x)) =
            presheafDensityEvaluationGlobalBase F x
      rw [← Category.assoc, presheafDensityEvaluationReconstructionLift_projection,
        presheafDensityEvaluationSourceBase_global]) :
      Over.mk (presheafDensityEvaluationGlobalBase F x) ⟶
        Over.mk (leftUnstraighteningProjection Dx ≫
          (SSet.uliftFunctor.{u + 1, u}).map (presheafDensitySourceInclusion F x)))

/-- 同じ底の上で元の大域評価同型を始点固定の全族へ制限する。 -/
def presheafDensityEvaluationGlobalPre :=
  relativeFunctorOverPre (leftUnstraighteningProjection G)
    (Over.homMk ((SSet.uliftFunctor.{u + 1, u}).map (twistedSourceElementsComparison p x)) rfl :
      Over.mk (presheafDensityEvaluationGlobalBase F x) ⟶
        Over.mk ((SSet.uliftFunctor.{u + 1, u}).map
          (twistedElementsReconstruction p ≫ smallLeftUnstraighteningProjection H)))

end SerrePositivity.InfinityCategories.F2.Ind
