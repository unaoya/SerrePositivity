module

public import SerrePositivity.KST.Spectra.SpectrumCircleHomBKCentral
public import SerrePositivity.KST.Spectra.SpectrumCircleEvaluationHom

/-!
概要：BK パラメーターの二辺の向きと、元の円評価の生成 loop を厳密に照合する。
方針：BK 重みの逆同型を通し、左辺は商の生成辺、右辺は基点の定値辺と計算する。
規約：元の普遍評価を変えない。使われ方：実際の円評価錐と Hom–BK 比較の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum

/-- ホーン重みへ戻すと、指定した BK パラメーターは元の collapse と円への商の合成。 -/
lemma circleBKParameter_horn :
    cospanBKWeightIso.{u}.inv.app (AsSmall.up.obj .one) ≫ circleBKParameter =
      loopHornCollapse.app (AsSmall.up.obj .one) ≫
        PointedObject.cofiberQuotient (boundary.{u} 1).ι := by
  have h := NatTrans.congr_app cospanBKWeightIso.{u}.inv_hom_id (AsSmall.up.obj .one)
  change cospanBKWeightIso.inv.app (AsSmall.up.obj .one) ≫
    cospanBKWeightIso.hom.app (AsSmall.up.obj .one) = 𝟙 (horn 2 2 : SSet.{u}) at h
  change _ ≫ ((cospanBKWeightIso.hom.app (AsSmall.up.obj .one) ≫
    loopHornCollapse.app (AsSmall.up.obj .one)) ≫ _) = _
  simpa only [Category.assoc, Category.id_comp] using congrArg
    (fun f : (horn 2 2 : SSet.{u}) ⟶ horn 2 2 ↦
      f ≫ loopHornCollapse.app (AsSmall.up.obj .one) ≫
        PointedObject.cofiberQuotient (boundary.{u} 1).ι) h

/-- 指定した BK パラメーターの左辺は、標準円への元の商写像。 -/
lemma circleBKParameter_leftEdge :
    horn₂₂.ι₀₂ ≫ cospanBKWeightIso.{u}.inv.app (AsSmall.up.obj .one) ≫
        circleBKParameter = PointedObject.cofiberQuotient (boundary.{u} 1).ι := by
  rw [circleBKParameter_horn, ← Category.assoc, loopHornCollapse_leftEdge, Category.id_comp]

/-- 指定した BK パラメーターの右辺は、標準円の基点での定値辺。 -/
lemma circleBKParameter_rightEdge :
    horn₂₂.ι₁₂ ≫ cospanBKWeightIso.{u}.inv.app (AsSmall.up.obj .one) ≫
        circleBKParameter = SSet.const circleBasepoint := by
  rw [circleBKParameter_horn, ← Category.assoc, loopHornCollapse_rightEdge, SSet.const_comp]
  exact congrArg (fun x : PointedSimplicialSet.circle.{u}.right _⦋0⦌ ↦
    SSet.const (X := (Δ[1] : SSet.{u})) x) (circleQuotient_vertex 1)

/-- 左辺の元の普遍評価は、既存の円評価の生成 loop の同じ一単体。 -/
lemma circleBKParameter_evaluation_leftEdge (Y : OmegaSpectrum.{u}) :
    SSet.yonedaEquiv (horn₂₂.ι₀₂ ≫
      cospanBKWeightIso.{u}.inv.app (AsSmall.up.obj .one) ≫ circleBKParameter ≫
        (cotensorEvaluation PointedSimplicialSet.circle Y).right) =
      (circleEvaluationHomEdge Y).edge := by
  have h := congrArg (fun f : (Δ[1] : SSet.{u}) ⟶ PointedSimplicialSet.circle.right ↦
    f ≫ (cotensorEvaluation PointedSimplicialSet.circle Y).right) circleBKParameter_leftEdge
  have he : horn₂₂.ι₀₂ ≫ cospanBKWeightIso.inv.app (AsSmall.up.obj .one) ≫
      circleBKParameter ≫ (cotensorEvaluation PointedSimplicialSet.circle Y).right =
        PointedObject.cofiberQuotient (boundary.{u} 1).ι ≫
          (cotensorEvaluation PointedSimplicialSet.circle Y).right := by
    simpa only [Category.assoc] using h
  rw [he, SSet.yonedaEquiv_comp, circleEvaluationHomEdge_edge]
  rfl

/-- 右辺の元の普遍評価は、元の BF Hom の零写像で定数。 -/
lemma circleBKParameter_evaluation_rightEdge (Y : OmegaSpectrum.{u}) :
    horn₂₂.ι₁₂ ≫ cospanBKWeightIso.{u}.inv.app (AsSmall.up.obj .one) ≫
        circleBKParameter ≫ (cotensorEvaluation PointedSimplicialSet.circle Y).right =
      SSet.const ((RawSpectrumMapping.pointedSpace (cotensor PointedSimplicialSet.circle Y)
        Y.toKanSequence).hom.app (Opposite.op ⦋0⦌) PUnit.unit) := by
  have h := congrArg (fun f : (Δ[1] : SSet.{u}) ⟶ PointedSimplicialSet.circle.right ↦
    f ≫ (cotensorEvaluation PointedSimplicialSet.circle Y).right) circleBKParameter_rightEdge
  have he : horn₂₂.ι₁₂ ≫ cospanBKWeightIso.inv.app (AsSmall.up.obj .one) ≫
      circleBKParameter ≫ (cotensorEvaluation PointedSimplicialSet.circle Y).right =
        SSet.const circleBasepoint ≫ (cotensorEvaluation PointedSimplicialSet.circle Y).right := by
    simpa only [Category.assoc] using h
  rw [he, SSet.const_comp, circleEvaluationHom_basepoint]

end SerrePositivity.KST.Spectra.OmegaSpectrum
