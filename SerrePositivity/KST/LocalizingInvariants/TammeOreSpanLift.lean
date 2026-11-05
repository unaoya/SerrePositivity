module

public import SerrePositivity.KST.LocalizingInvariants.TammeSpanBaseChangeLift

/-!
概要：元の span と第二終点へ入る Tamme 分母から、普遍 Ore 正方形を保つ実 span lift を作る。
方針：指定二辺の普遍 pullback を選び、その底辺の分母性で第一脚を前合成する。
規約：普遍正方形と実 lift は構成するが、lift の cartesian 性はまだ主張しない。
使われ方：分母に沿う cartesian 輸送の存在部分とその高次判定への入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
variable {C D E : StableCategory.{u}} (p : ExactMap C E) (q : ExactMap D E)

lemma exists_tammeOreSpanLift
    (S : (horn 2 0 : SSet.{u}) ⟶ (laxCategory p q).obj)
    (hS : SSet.yonedaEquiv (horn₂₀.ι₀₁ ≫ S) ∈ tammeLocalizingEdges p q)
    {y : (laxCategory p q).obj _⦋0⦌}
    (s : Truncated.Edge (X := (truncation 2).obj (laxCategory p q).obj) y
      ((laxCategory p q).obj.δ 0 (SSet.yonedaEquiv (horn₂₀.ι₀₂ ≫ S))))
    (hs : s.edge ∈ tammeLocalizingEdges p q) :
    let X := (laxCategory p q).obj
    let W := tammeLocalizingEdges p q
    let x := (horn₂₀.ι₀₁ ≫ S).app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (1 : Fin 2))
    ∃ (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) (G : (Δ[1] : SSet.{u}) ⟶ markedSpanFamily X W x),
      IsPullbackSquare R ∧ squareTopEdge ≫ R = SSet.yonedaEquiv.symm s.edge ∧
      stdSimplex.δ (0 : Fin 2) ≫ G ≫ vertexFiberι (markedSpanSource X W) x ≫
        markedSpanInclusion X W = SSet.const (functorVertex S) ∧
      G ≫ markedSpanFamilyProjection X W x = SSet.yonedaEquiv.symm s.edge ∧
      G ≫ vertexFiberι (markedSpanSource X W) x ≫ markedSpanInclusion X W ≫
        (pre horn₂₀.ι₀₂).app X = _root_.SerrePositivity.InfinityCategories.Core.Quasicategory.squareArrowFamily R := by
  dsimp only
  let f := edgeOfSimplex (SSet.yonedaEquiv (horn₂₀.ι₀₂ ≫ S))
  obtain ⟨R, hR, hr, ht, hb⟩ := tammeLocalizingEdges_rightOre_pullback p q f s hs
  have hr' : squareRightEdge ≫ R = horn₂₀.ι₀₂ ≫ S :=
    hr.trans (SSet.yonedaEquiv.symm_apply_apply (horn₂₀.ι₀₂ ≫ S))
  have hb' : SSet.yonedaEquiv (squareBottomEdge ≫ R) ∈ tammeLocalizingEdges p q :=
    (squareBottomArrow_edge R) ▸ hb
  obtain ⟨G, hG₁, hGt, hGr⟩ := exists_tammeSpanBaseChangeLift p q S hS R hr' hb'
  exact ⟨R, G, hR, ht, hG₁, hGt.trans ht, hGr⟩

end SerrePositivity.KST.LocalizingInvariants
