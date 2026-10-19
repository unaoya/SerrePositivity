module

public import SerrePositivity.KST.Spectra.SpectrumCircleCompanionClasses
public import SerrePositivity.KST.Spectra.SphereMappingComponents

/-!
概要：元の companion 経路を基点付き円へ降ろし、元の普遍評価と基点固定で比較する。
方針：境界定数単体と円の射の標準同値を使い、基本群の類の等式を写像空間へ戻す。
規約：標準円の元の商と普遍評価を保持。使われ方：元の錐と BK 切断点の比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.OmegaSpectrum

local instance circleCompanionMappingHomKan (z : Sp.{u} _⦋0⦌) :
    KanComplex (circleEvaluationPointedHom z).right := by
  change KanComplex (mappingSpace
    (cotensor PointedSimplicialSet.circle (nativeCotensorInput PointedSimplicialSet.circle z).val)
      (nativeCotensorInput PointedSimplicialSet.circle z).val)
  infer_instance

/-- 元の companion の経路を、元の基点付き標準円からの射へ降ろしたもの。 -/
def circleEvaluationCompanionCircleMap (z : Sp.{u} _⦋0⦌) :
    PointedSimplicialSet.circle.{u} ⟶ circleEvaluationPointedHom z :=
  SphereSimplex.toMap (circleEvaluationPointedHom z) 1 (circleEvaluationCompanionSimplex z)

/-- 元の普遍評価を標準区間へ戻すと、元の生成 loop の同じ境界定数一単体。 -/
lemma circleEvaluationLoopSimplex_evaluation (z : Sp.{u} _⦋0⦌) :
    SphereSimplex.equiv (circleEvaluationPointedHom z) 1
      (cotensorEvaluation PointedSimplicialSet.circle
        (nativeCotensorInput PointedSimplicialSet.circle z).val) =
      circleEvaluationLoopSimplex z := by
  apply RelativeMorphism.ext
  change PointedObject.cofiberQuotient (boundary.{u} 1).ι ≫
    (cotensorEvaluation PointedSimplicialSet.circle
      (nativeCotensorInput PointedSimplicialSet.circle z).val).right =
        SSet.yonedaEquiv.symm
          (circleEvaluationHomEdge (nativeCotensorInput PointedSimplicialSet.circle z).val).edge
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, Equiv.apply_symm_apply]
  rfl

/-- 元の companion の円の射は、元の普遍評価と同じ写像空間の成分を表す。 -/
lemma circleEvaluationCompanionCircle_component (z : Sp.{u} _⦋0⦌) :
    π₀.mk (PointedMapping.familyVertex (circleEvaluationCompanionCircleMap z)) =
      π₀.mk (PointedMapping.familyVertex
        (cotensorEvaluation PointedSimplicialSet.circle
          (nativeCotensorInput PointedSimplicialSet.circle z).val)) := by
  apply (SphereSimplex.class_eq_iff_components (circleEvaluationPointedHom z) 0 _ _).mp
  have hc : SphereSimplex.equiv (circleEvaluationPointedHom z) 1
      (circleEvaluationCompanionCircleMap z) = circleEvaluationCompanionSimplex z :=
    Equiv.apply_symm_apply _ _
  rw [hc, circleEvaluationLoopSimplex_evaluation]
  exact circleEvaluationCompanion_loop_class z

/-- 元の companion の円の射と元の普遍評価の間には、基点を全時間で固定するホモトピー。 -/
lemma circleEvaluationCompanionCircle_pointedHomotopy (z : Sp.{u} _⦋0⦌) :
    ∃ H : SSet.Homotopy (circleEvaluationCompanionCircleMap z).right
      (cotensorEvaluation PointedSimplicialSet.circle
        (nativeCotensorInput PointedSimplicialSet.circle z).val).right,
      PointedSimplicialSet.circle.hom ▷ (Δ[1] : SSet.{u}) ≫ H.h =
        toUnit (𝟙_ SSet.{u} ⊗ (Δ[1] : SSet.{u})) ≫ (circleEvaluationPointedHom z).hom :=
  (PointedMapping.piZero_eq_iff_pointedHomotopy _ _).mp
    (circleEvaluationCompanionCircle_component z)

end SerrePositivity.KST.Spectra.OmegaSpectrum
