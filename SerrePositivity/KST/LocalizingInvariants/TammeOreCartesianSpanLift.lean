module

public import SerrePositivity.KST.LocalizingInvariants.TammeOreSpanLift
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.MarkedSpanFamilyCartesianEdge

/-!
概要：指定 Tamme 分母上の実 Ore span lift は cartesian に選べる。
方針：保存済みの普遍正方形を右脚の族に同定し、全外ホーンの判定を適用する。
規約：同じ正方形・入力辺・終点 span を保持。使われ方：分数の族の局所 cartesian 輸送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
variable {C D E : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D E)

lemma exists_tammeOreCartesianSpanLift
    (S : (horn 2 0 : SSet.{u}) ⟶ (laxCategory p q).obj)
    (hS : SSet.yonedaEquiv (horn₂₀.ι₀₁ ≫ S) ∈ tammeLocalizingEdges p q)
    {y : (laxCategory p q).obj _⦋0⦌}
    (s : Truncated.Edge (X := (truncation 2).obj (laxCategory p q).obj) y
      ((laxCategory p q).obj.δ 0 (SSet.yonedaEquiv (horn₂₀.ι₀₂ ≫ S))))
    (hs : s.edge ∈ tammeLocalizingEdges p q) :
    let X := (laxCategory p q).obj
    let W := tammeLocalizingEdges p q
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
  obtain ⟨R, G, hR, ht, hG₁, hGt, hGr⟩ := exists_tammeOreSpanLift p q S hS s hs
  refine ⟨R, G, hR, ht, hG₁, hGt, hGr, ?_⟩
  apply isCartesianEdge_markedSpanFamilyProjection_of_pullback
  rw [SSet.yonedaEquiv.symm_apply_apply, hGr, _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.squareArrowFamily, uncurry_curry]
  exact (_root_.SerrePositivity.InfinityCategories.HA.Section6_1_1.isPullbackSquare_iff_transpose R).mp hR

end SerrePositivity.KST.LocalizingInvariants
