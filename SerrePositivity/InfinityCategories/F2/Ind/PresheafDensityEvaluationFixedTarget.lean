module

public import SerrePositivity.InfinityCategories.F2.Ind.PresheafDensityEvaluationGlobalComparison
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorIsPullbackIso

/-!
概要：同じ始点固定の全族上で、元の大域標的への相対 Hom を同じ定値標的へ戻す。
方針：元の unstraightening の底変換正方形の厳密な相対 Hom 同型を使う。
規約：同じ全族・底の図式・指定値を保つ。
使われ方：密度評価の実際の像を元の指定値への写像へ戻す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {C : SSet.{u}} [Quasicategory C]
  (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u}) (x : C _⦋0⦌)
local notation "G" => presheafTwistedElementsTargetDiagram F
local notation "Dx" => presheafDensityEvaluationDiagram F x
local notation "z" => presheafDensityEvaluationVertex F x

/-- 同じ底上の全変換を、元の大域標的から同じ評価の定値標的へ厳密に戻す同型。 -/
def presheafDensityEvaluationFixedTargetIso :
    relativeFunctorSpace (leftUnstraighteningProjection (SSet.const z))
      (presheafDensityEvaluationSourceBase F x) ≅
    relativeFunctorSpace (leftUnstraighteningProjection G)
      (presheafDensityEvaluationGlobalBase F x) :=
  relativeFunctorIsPullbackIso
    (leftUnstraighteningMap_isPullback (SSet.const z) G
      ((SSet.uliftFunctor.{u + 1, u}).map (presheafDensitySourceInclusion F x))
      (presheafDensitySourceInclusion_target F x))
    (presheafDensityEvaluationSourceBase F x) (presheafDensityEvaluationGlobalBase F x)
    (presheafDensityEvaluationSourceBase_global F x)

/-- 評価の同じ定値標的への変換を、同じ評価復元射へ制限する。 -/
def presheafDensityEvaluationConstantPre :=
  relativeFunctorOverPre (leftUnstraighteningProjection (SSet.const z))
    (Over.homMk (presheafDensityEvaluationReconstructionLift F x)
      (presheafDensityEvaluationReconstructionLift_projection F x) :
      Over.mk (presheafDensityEvaluationSourceBase F x) ⟶
        Over.mk (leftUnstraighteningProjection Dx))

/-- 同じ定値標的への変換の制限と、大域標的へ戻す厳密な同型は可換。 -/
lemma presheafDensityEvaluationFixedTargetIso_source_vertex
    (v : (relativeFunctorSpace (leftUnstraighteningProjection (SSet.const z))
      (leftUnstraighteningProjection Dx)) _⦋0⦌) :
    (presheafDensityEvaluationFixedTargetIso F x).hom.app (Opposite.op ⦋0⦌)
      ((presheafDensityEvaluationConstantPre F x).app (Opposite.op ⦋0⦌) v) =
    (presheafDensityEvaluationReconstructionPre F x).app (Opposite.op ⦋0⦌)
      ((presheafDensityEvaluationRelativeTargetMap F x).app (Opposite.op ⦋0⦌) v) := by
  obtain ⟨M, hM, rfl⟩ := exists_relativeFunctorVertex _ _ v
  apply Subtype.ext
  change functorVertex ((presheafDensityEvaluationReconstructionLift F x ≫ M) ≫
    leftUnstraighteningMap (SSet.const z) G
      ((SSet.uliftFunctor.{u + 1, u}).map (presheafDensitySourceInclusion F x))
      (presheafDensitySourceInclusion_target F x)) =
    functorVertex (presheafDensityEvaluationReconstructionLift F x ≫ M ≫
      leftUnstraighteningMap (SSet.const z) G
        ((SSet.uliftFunctor.{u + 1, u}).map (presheafDensitySourceInclusion F x))
        (presheafDensitySourceInclusion_target F x))
  rw [Category.assoc]

end SerrePositivity.InfinityCategories.F2.Ind
