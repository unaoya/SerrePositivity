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
variable {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
  (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q)

include h in
lemma exists_weakOreSpanLift
    (S : (horn 2 0 : SSet.{u}) ⟶ B.obj)
    (hS : SSet.yonedaEquiv (horn₂₀.ι₀₁ ≫ S) ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i)
    {y : B.obj _⦋0⦌}
    (s : Truncated.Edge (X := (truncation 2).obj B.obj) y
      (B.obj.δ 0 (SSet.yonedaEquiv (horn₂₀.ι₀₂ ≫ S))))
    (hs : s.edge ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) :
    let X := B.obj
    let W := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i
    let x := (horn₂₀.ι₀₁ ≫ S).app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (1 : Fin 2))
    ∃ (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ X) (G : (Δ[1] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.markedSpanFamily X W x),
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare R ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ R = SSet.yonedaEquiv.symm s.edge ∧
      stdSimplex.δ (0 : Fin 2) ≫ G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (markedSpanSource X W) x ≫
        markedSpanInclusion X W = SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex S) ∧
      G ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.markedSpanFamilyProjection X W x = SSet.yonedaEquiv.symm s.edge ∧
      G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (markedSpanSource X W) x ≫ markedSpanInclusion X W ≫
        (pre horn₂₀.ι₀₂).app X = _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.squareArrowFamily R := by
  dsimp only
  let f := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (SSet.yonedaEquiv (horn₂₀.ι₀₂ ≫ S))
  obtain ⟨R, hR, hr, ht, hb⟩ := weakEquivalences_rightOre_pullback h f s hs
  have hr' : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ R = horn₂₀.ι₀₂ ≫ S :=
    hr.trans (SSet.yonedaEquiv.symm_apply_apply (horn₂₀.ι₀₂ ≫ S))
  have hb' : SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ R) ∈ _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i :=
    (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareBottomArrow_edge R) ▸ hb
  obtain ⟨G, hG₁, hGt, hGr⟩ := exists_weakSpanBaseChangeLift h S hS R hr' hb'
  exact ⟨R, G, hR, ht, hG₁, hGt.trans ht, hGr⟩


end SerrePositivity.KST.Fibration
