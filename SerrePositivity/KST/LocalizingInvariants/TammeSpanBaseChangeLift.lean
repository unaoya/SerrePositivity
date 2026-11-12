module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.MarkedSpanFamilies

public import SerrePositivity.KST.LocalizingInvariants.SpanBaseChangeFamily
public import SerrePositivity.KST.LocalizingInvariants.TammeUniversalOre

/-!
概要：Tamme 分母を底辺に持つ正方形から、第一終点固定の分母付き span の実持ち上げを作る。
方針：第一脚の合成二単体で二対三性を使い、正方形の右脚の全族と貼る。
規約：元の正方形・終点 span・入力辺を厳密に保持。cartesian 性は後続。
使われ方：普遍 Ore pullback からの局所 cartesian lift 候補。
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
variable {C D E : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (p : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap C E) (q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap D E)

lemma exists_tammeSpanBaseChangeLift
    (S : (horn 2 0 : SSet.{u}) ⟶ (laxCategory p q).obj)
    (hS : SSet.yonedaEquiv (horn₂₀.ι₀₁ ≫ S) ∈ tammeLocalizingEdges p q)
    (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ (laxCategory p q).obj)
    (hR : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ R = horn₂₀.ι₀₂ ≫ S)
    (hRb : SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ R) ∈ tammeLocalizingEdges p q) :
    let X := (laxCategory p q).obj
    let W := tammeLocalizingEdges p q
    let x := (horn₂₀.ι₀₁ ≫ S).app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (1 : Fin 2))
    ∃ G : (Δ[1] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.markedSpanFamily X W x,
      stdSimplex.δ (0 : Fin 2) ≫ G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (markedSpanSource X W) x ≫
        markedSpanInclusion X W = SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex S) ∧
      G ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.markedSpanFamilyProjection X W x = _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ R ∧
      G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (markedSpanSource X W) x ≫ markedSpanInclusion X W ≫
        (pre horn₂₀.ι₀₂).app X = _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.Quasicategory.squareArrowFamily R := by
  dsimp only
  let X := (laxCategory p q).obj
  let W := tammeLocalizingEdges p q
  let x := (horn₂₀.ι₀₁ ≫ S).app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (1 : Fin 2))
  obtain ⟨T, F, hT₂, hT₀, hF₁, hFl, hFr, hFs, hFt⟩ := exists_spanBaseChangeFamily S R hR
  have h₂ : SSet.yonedaEquiv (stdSimplex.δ (2 : Fin 3) ≫ T) ∈ W :=
    (congrArg (fun k : (Δ[1] : SSet.{u}) ⟶ X => SSet.yonedaEquiv k ∈ W) hT₂).mpr hRb
  have h₀ : SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 3) ≫ T) ∈ W :=
    (congrArg (fun k : (Δ[1] : SSet.{u}) ⟶ X => SSet.yonedaEquiv k ∈ W) hT₀).mpr hS
  have hnew : SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 3) ≫ T) ∈ W :=
    (tammeLocalizingEdges_twoOfThree p q T).1 h₂ h₀
  have hv : ∀ v : (Δ[1] : SSet.{u}) _⦋0⦌, spanLeftEdge (F.app (Opposite.op ⦋0⦌) v) ∈ W := by
    intro v
    obtain ⟨i, rfl⟩ := stdSimplex.obj₀Equiv.symm.surjective v
    have hh := congrArg (fun k => k.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm i)) hFl
    change ((pre horn₂₀.ι₀₁).app X).app (Opposite.op ⦋0⦌)
      (F.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm i)) =
      (intervalPrecompositionFamily T).app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm i) at hh
    unfold spanLeftEdge
    rw [hh]
    fin_cases i
    · exact (congrArg (fun a : X _⦋1⦌ => a ∈ W)
        (intervalPrecompositionFamily_edge_zero T)).mpr hnew
    · exact (congrArg (fun a : X _⦋1⦌ => a ∈ W)
        (intervalPrecompositionFamily_edge_one T)).mpr h₀
  let L : (Δ[1] : SSet.{u}) ⟶ markedSpans X W :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift (fun z => spanLeftEdge z ∈ W) F hv
  have hL : L ≫ markedSpanInclusion X W = F := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι _ _ _
  have hs : L ≫ markedSpanSource X W = SSet.const x := by
    change (L ≫ markedSpanInclusion X W) ≫ (pre horn₂₀.ι₀₁).app X ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt _ = _
    rw [hL]
    exact hFs
  let G : (Δ[1] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.markedSpanFamily X W x :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift (markedSpanSource X W) x L hs
  have hG : G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (markedSpanSource X W) x = L := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι _ _ _ _
  refine ⟨G, ?_, ?_, ?_⟩
  · change stdSimplex.δ (0 : Fin 2) ≫
      (G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (markedSpanSource X W) x) ≫ markedSpanInclusion X W = _
    simpa only [Category.assoc, hG, hL] using hF₁
  · change (G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (markedSpanSource X W) x) ≫ markedSpanInclusion X W ≫
      (pre horn₂₀.ι₀₂).app X ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt _ = _
    rw [hG, ← Category.assoc, hL]
    exact hFt
  · change (G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (markedSpanSource X W) x) ≫ markedSpanInclusion X W ≫
      (pre horn₂₀.ι₀₂).app X = _
    rw [hG, ← Category.assoc, hL]
    exact hFr

end SerrePositivity.KST.LocalizingInvariants
