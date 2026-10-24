module
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorElementEvaluatedColumn
public import SerrePositivity.EInfinity.FrameHom.MixedNerveCoconePoint
public import SerrePositivity.EInfinity.ComplexLimits.OrdinaryDerivedSource
public import SerrePositivity.EInfinity.ComplexLimits.NormalizedTensorConeUnderSimplex

/-!
概要：元の通常評価の全余錐を、同じ複体 dg nerve の大域 join として表示する。
方針：元の混合宇宙の余錐を使い、全列制限・同じ自然変換円柱を回収する。
規約：元の終点 Y と全円柱を保持する。使われ方：大域評価三角形の第二辺。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.ComplexLimits
open CategoryTheory Limits MonoidalCategory SSet
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories DGNerve
open scoped Simplicial
variable (A : Type u) [CommRing A] (X Y : Complex A)

lemma normalizedTensorElementEvaluatedColumn_join {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n) :
    (joinStdSimplexIso n 0).hom ≫ (SSet.yonedaEquiv (X := nerve (Complex A))).symm
      (normalizedTensorElementEvaluatedColumn A X Y c) =
      joinMap (SSet.yonedaEquiv.symm c) (𝟙 (Δ[0] : SSet.{u + 1})) ≫
        FrameHom.MixedNerve.coconeJoin (normalizedTensorElementEvaluationCocone A X Y) := by
  let Γ := c ⋙ ULiftHom.up.{u, u + 1, u + 1}
  let L := normalizedTensorElementLiftedEvaluationCocone A X Y
  have h := FrameHom.TerminalCoconeSimplex.diagram_join L Γ
  have hd := congrArg (fun f => f ≫ FrameHom.MixedNerve.down (Complex A)) h
  simp only [Category.assoc, SSet.yonedaEquiv_symm_comp] at hd
  have hu : (SSet.yonedaEquiv (X := nerve (normalizedTensorElementIndex A X Y))).symm c ≫
      FrameHom.MixedNerve.up (normalizedTensorElementIndex A X Y) =
      (SSet.yonedaEquiv (X := nerve (ULiftHom.{u + 1}
        (normalizedTensorElementIndex A X Y)))).symm Γ := by
    rw [SSet.yonedaEquiv_symm_comp]
    rfl
  have hm : joinMap (SSet.yonedaEquiv.symm c) (𝟙 (Δ[0] : SSet.{u + 1})) ≫
      joinMap (FrameHom.MixedNerve.up (normalizedTensorElementIndex A X Y)) (𝟙 Δ[0]) =
      joinMap (SSet.yonedaEquiv.symm Γ) (𝟙 Δ[0]) := by
    rw [← joinMap_comp, hu, Category.id_comp]
  change _ = joinMap (SSet.yonedaEquiv.symm c) (𝟙 Δ[0]) ≫
    (joinMap (FrameHom.MixedNerve.up (normalizedTensorElementIndex A X Y)) (𝟙 Δ[0]) ≫
      (SerrePositivity.InfinityCategories.F1B.nerveCoconeEquiv L).val ≫ FrameHom.MixedNerve.down (Complex A))
  rw [← Category.assoc, hm]
  exact hd


def normalizedTensorElementEvaluationJoin :
    join (nerve (normalizedTensorElementIndex A X Y)) (Δ[0] : SSet.{u + 1}) ⟶
      dgNerve A (Complex A) :=
  FrameHom.MixedNerve.coconeJoin (normalizedTensorElementEvaluationCocone A X Y) ≫
    nerveMap (complexToClosed A) ≫ closedNerveInclusion A (Complex A)

lemma normalizedTensorElementEvaluationJoin_inr :
    joinInr (nerve (normalizedTensorElementIndex A X Y)) (Δ[0] : SSet.{u + 1}) ≫
      normalizedTensorElementEvaluationJoin A X Y = normalizedTensorConePoint A Y := by
  rw [normalizedTensorElementEvaluationJoin, ← Category.assoc, FrameHom.MixedNerve.coconeJoin_inr]
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp]
  simp only [nervePoint, normalizedTensorElementEvaluationCocone, normalizedTensorConePoint,
    Equiv.apply_symm_apply]
  change (nerveMap (complexToClosed A) ≫ closedNerveInclusion A (Complex A)).app
    (Opposite.op ⦋0⦌) (nerveVertex Y) = (dgNerve.vertexEquiv A (Complex A)).symm Y
  apply (dgNerve.vertexEquiv A (Complex A)).injective
  rfl

lemma normalizedTensorElementEvaluationJoin_restrict_simplex {n : ℕ}
    (c : ComposableArrows (normalizedTensorElementIndex A X Y) n) :
    joinMap (SSet.yonedaEquiv.symm c) (𝟙 (Δ[0] : SSet.{u + 1})) ≫
      normalizedTensorElementEvaluationJoin A X Y =
      (joinStdSimplexIso n 0).hom ≫ (SSet.yonedaEquiv (X := dgNerve A (Complex A))).symm
        (closedNerveSimplex
          (normalizedTensorElementEvaluatedColumn A X Y c ⋙ complexToClosed A)) := by
  have h := congrArg (fun f => f ≫ nerveMap (complexToClosed A) ≫
    closedNerveInclusion A (Complex A)) (normalizedTensorElementEvaluatedColumn_join A X Y c)
  simp only [Category.assoc, SSet.yonedaEquiv_symm_comp] at h
  exact h.symm

lemma normalizedTensorElementEvaluationJoin_prism :
    (β_ (nerve (normalizedTensorElementIndex A X Y)) (Δ[1] : SSet.{u + 1})).hom ≫
      rightMappingSpacePrism _ ≫ normalizedTensorElementEvaluationJoin A X Y =
      (FrameHom.MixedNerve.homotopy (normalizedTensorElementEvaluation A X Y)).h ≫
        nerveMap (complexToClosed A) ≫ closedNerveInclusion A (Complex A) := by
  have h := congrArg (fun f => f ≫ nerveMap (complexToClosed A) ≫
    closedNerveInclusion A (Complex A))
    (FrameHom.MixedNerve.coconePrism_eq_homotopy (normalizedTensorElementEvaluationCocone A X Y))
  simpa only [Category.assoc, normalizedTensorElementEvaluationJoin,
    normalizedTensorElementEvaluationCocone] using h

end SerrePositivity.EInfinity.ComplexLimits
