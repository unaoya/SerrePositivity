module
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.MarkedSpanFamilies
public import SerrePositivity.KST.LocalizingInvariants.SpanBaseChangeFamily
public import SerrePositivity.KST.Fibration.WeakUniversalOre

/-! # 元の W 分母の基底変更による、第一終点を固定した全 span 族の実持ち上げ -/

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
lemma exists_weakSpanBaseChangeLift
    (S : (horn 2 0 : SSet.{u}) ⟶ B.obj)
    (hS : SSet.yonedaEquiv (horn₂₀.ι₀₁ ≫ S) ∈ weakEquivalences i)
    (R : (Δ[1] : SSet.{u}) ⊗ Δ[1] ⟶ B.obj)
    (hR : squareRightEdge ≫ R = horn₂₀.ι₀₂ ≫ S)
    (hRb : SSet.yonedaEquiv (squareBottomEdge ≫ R) ∈ weakEquivalences i) :
    let X := B.obj
    let W := weakEquivalences i
    let x := (horn₂₀.ι₀₁ ≫ S).app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (1 : Fin 2))
    ∃ G : (Δ[1] : SSet.{u}) ⟶ markedSpanFamily X W x,
      stdSimplex.δ (0 : Fin 2) ≫ G ≫ vertexFiberι (markedSpanSource X W) x ≫
        markedSpanInclusion X W = SSet.const (functorVertex S) ∧
      G ≫ markedSpanFamilyProjection X W x = squareTopEdge ≫ R ∧
      G ≫ vertexFiberι (markedSpanSource X W) x ≫ markedSpanInclusion X W ≫
        (pre horn₂₀.ι₀₂).app X = squareArrowFamily R := by
  dsimp only
  let X := B.obj
  let W := weakEquivalences i
  let x := (horn₂₀.ι₀₁ ≫ S).app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (1 : Fin 2))
  obtain ⟨T, F, hT₂, hT₀, hF₁, hFl, hFr, hFs, hFt⟩ := exists_spanBaseChangeFamily S R hR
  have h₂ : SSet.yonedaEquiv (stdSimplex.δ (2 : Fin 3) ≫ T) ∈ W :=
    (congrArg (fun k : (Δ[1] : SSet.{u}) ⟶ X => SSet.yonedaEquiv k ∈ W) hT₂).mpr hRb
  have h₀ : SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 3) ≫ T) ∈ W :=
    (congrArg (fun k : (Δ[1] : SSet.{u}) ⟶ X => SSet.yonedaEquiv k ∈ W) hT₀).mpr hS
  have hnew : SSet.yonedaEquiv (stdSimplex.δ (1 : Fin 3) ≫ T) ∈ W :=
    (weakEquivalences_twoOfThree h T).1 h₂ h₀
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
    fullSubcomplexLift (fun z => spanLeftEdge z ∈ W) F hv
  have hL : L ≫ markedSpanInclusion X W = F := fullSubcomplexLift_ι _ _ _
  have hs : L ≫ markedSpanSource X W = SSet.const x := by
    change (L ≫ markedSpanInclusion X W) ≫ (pre horn₂₀.ι₀₁).app X ≫ evaluateFunctorAt _ = _
    rw [hL]
    exact hFs
  let G : (Δ[1] : SSet.{u}) ⟶ markedSpanFamily X W x :=
    vertexFiberLift (markedSpanSource X W) x L hs
  have hG : G ≫ vertexFiberι (markedSpanSource X W) x = L := vertexFiberLift_ι _ _ _ _
  refine ⟨G, ?_, ?_, ?_⟩
  · change stdSimplex.δ (0 : Fin 2) ≫
      (G ≫ vertexFiberι (markedSpanSource X W) x) ≫ markedSpanInclusion X W = _
    simpa only [Category.assoc, hG, hL] using hF₁
  · change (G ≫ vertexFiberι (markedSpanSource X W) x) ≫ markedSpanInclusion X W ≫
      (pre horn₂₀.ι₀₂).app X ≫ evaluateFunctorAt _ = _
    rw [hG, ← Category.assoc, hL]
    exact hFt
  · change (G ≫ vertexFiberι (markedSpanSource X W) x) ≫ markedSpanInclusion X W ≫
      (pre horn₂₀.ι₀₂).app X = _
    rw [hG, ← Category.assoc, hL]
    exact hFr


end SerrePositivity.KST.Fibration
