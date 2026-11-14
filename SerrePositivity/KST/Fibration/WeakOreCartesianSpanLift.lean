module
public import SerrePositivity.KST.Fibration.WeakOreSpanLift
public import SerrePositivity.KST.LocalizingInvariants.MarkedSpanFamilyCartesianEdge

/-! # 元の W 分母上の Ore span lift の全外ホーンに関する cartesian 性 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
  (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q)

include h in
lemma exists_weakOreCartesianSpanLift
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
        (pre horn₂₀.ι₀₂).app X = _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.squareArrowFamily R ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.markedSpanFamilyProjection X W x) (SSet.yonedaEquiv G) := by
  dsimp only
  obtain ⟨R, G, hR, ht, hG₁, hGt, hGr⟩ := exists_weakOreSpanLift h S hS s hs
  refine ⟨R, G, hR, ht, hG₁, hGt, hGr, ?_⟩
  apply isCartesianEdge_markedSpanFamilyProjection_of_pullback
  rw [SSet.yonedaEquiv.symm_apply_apply, hGr, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.squareArrowFamily, uncurry_curry]
  exact (_root_.SerrePositivity.InfinityCategories.HA.Section6_1_1.isPullbackSquare_iff_transpose R).mp hR


end SerrePositivity.KST.Fibration
