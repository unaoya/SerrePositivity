module
public import SerrePositivity.KST.Fibration.WeakSpanBaseChangeLift

/-! # 元の W 分母上の普遍 Ore pullback を保つ span の実持ち上げ -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
  (h : IsVerdierSequence i q)

include h in
lemma exists_weakOreSpanLift
    (S : (horn 2 0 : SSet.{u}) ⟶ B.obj)
    (hS : SSet.yonedaEquiv (horn₂₀.ι₀₁ ≫ S) ∈ weakEquivalences i)
    {y : B.obj _⦋0⦌}
    (s : Truncated.Edge (X := (truncation 2).obj B.obj) y
      (B.obj.δ 0 (SSet.yonedaEquiv (horn₂₀.ι₀₂ ≫ S))))
    (hs : s.edge ∈ weakEquivalences i) :
    let X := B.obj
    let W := weakEquivalences i
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
  obtain ⟨R, hR, hr, ht, hb⟩ := weakEquivalences_rightOre_pullback h f s hs
  have hr' : squareRightEdge ≫ R = horn₂₀.ι₀₂ ≫ S :=
    hr.trans (SSet.yonedaEquiv.symm_apply_apply (horn₂₀.ι₀₂ ≫ S))
  have hb' : SSet.yonedaEquiv (squareBottomEdge ≫ R) ∈ weakEquivalences i :=
    (squareBottomArrow_edge R) ▸ hb
  obtain ⟨G, hG₁, hGt, hGr⟩ := exists_weakSpanBaseChangeLift h S hS R hr' hb'
  exact ⟨R, G, hR, ht, hG₁, hGt.trans ht, hGr⟩


end SerrePositivity.KST.Fibration
