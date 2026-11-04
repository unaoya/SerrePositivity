module
public import SerrePositivity.KST.LocalizingInvariants.MarkedSpanDiagrams
public import SerrePositivity.KST.LocalizingInvariants.MarkedSpanBoundary
public import SerrePositivity.KST.LocalizingInvariants.FixedSpanApexComparison

public import SerrePositivity.KST.LocalizingInvariants.SpanPostcompositionFamily

/-!
概要：分母付き span の第二終点の辺を、第一脚を固定して持ち上げる。
方針：元の span の右脚だけを合成し、左脚の厳密な定値性から分母性を全頂点に移す。
規約：第一脚と始点の評価を全区間で保持。使われ方：固定第一終点の族の lift。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

lemma exists_markedSpanPostcomposition {X : SSet.{u}} [Quasicategory X]
    (W : Set (X _⦋1⦌)) (v : (markedSpans X W) _⦋0⦌) (b : (Δ[1] : SSet.{u}) ⟶ X)
    (hb : stdSimplex.δ (1 : Fin 2) ≫ b =
      SSet.yonedaEquiv.symm ((markedSpanTarget X W).app (Opposite.op ⦋0⦌) v)) :
    ∃ G : (Δ[1] : SSet.{u}) ⟶ markedSpans X W,
      stdSimplex.δ (1 : Fin 2) ≫ G = SSet.const v ∧ G ≫ markedSpanTarget X W = b ∧
      G ≫ markedSpanSource X W =
        SSet.const ((markedSpanSource X W).app (Opposite.op ⦋0⦌) v) ∧
      G ≫ markedSpanApex X W = SSet.const ((markedSpanApex X W).app (Opposite.op ⦋0⦌) v) ∧
      G ≫ markedSpanInclusion X W ≫ (pre horn₂₀.ι₀₁).app X =
        SSet.const (((pre horn₂₀.ι₀₁).app X).app (Opposite.op ⦋0⦌) v.val) := by
  let p := (functorVertexEquiv (horn 2 0 : SSet.{u}) X).symm v.val
  have hp : functorVertex p = v.val := (functorVertexEquiv _ _).apply_symm_apply v.val
  have hbt : stdSimplex.δ (1 : Fin 2) ≫ b =
      stdSimplex.δ (0 : Fin 2) ≫ horn₂₀.ι₀₂ ≫ p := by
    apply SSet.yonedaEquiv.injective
    have hh := congrArg SSet.yonedaEquiv hb
    rw [Equiv.apply_symm_apply] at hh
    rw [hh]
    change ((pre horn₂₀.ι₀₂).app X ≫ evaluateFunctorAt
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2))).app (Opposite.op ⦋0⦌) v.val = _
    rw [← hp]
    change (evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2))).app
      (Opposite.op ⦋0⦌) (functorVertex (horn₂₀.ι₀₂ ≫ p)) = _
    rw [evaluateFunctorAt_functorVertex]
    exact (intervalMap_target (horn₂₀.ι₀₂ ≫ p)).symm.trans
      (SSet.yonedaEquiv_naturality (SimplexCategory.δ (0 : Fin 2)) (horn₂₀.ι₀₂ ≫ p))
  obtain ⟨F, hF₀, hFl, hFt⟩ := exists_spanPostcompositionFamily p b hbt
  have hl : ((pre horn₂₀.ι₀₁).app X).app (Opposite.op ⦋0⦌) v.val =
      functorVertex (horn₂₀.ι₀₁ ≫ p) := by rw [← hp]; rfl
  have hv : ∀ w : (Δ[1] : SSet.{u}) _⦋0⦌, spanLeftEdge (F.app (Opposite.op ⦋0⦌) w) ∈ W := by
    intro w
    have hh := congrArg (fun k => k.app (Opposite.op ⦋0⦌) w) hFl
    change ((pre horn₂₀.ι₀₁).app X).app (Opposite.op ⦋0⦌)
      (F.app (Opposite.op ⦋0⦌) w) = PinchedHom.constant (functorVertex (horn₂₀.ι₀₁ ≫ p)) 0 at hh
    rw [pinchedConstant_zero] at hh
    unfold spanLeftEdge
    rw [hh, ← hl]
    exact fullSubcomplexOnVertices_vertex v
  let G := fullSubcomplexLift (fun z => spanLeftEdge z ∈ W) F hv
  have hG : G ≫ markedSpanInclusion X W = F := fullSubcomplexLift_ι _ _ _
  have hGl : G ≫ markedSpanInclusion X W ≫ (pre horn₂₀.ι₀₁).app X =
      SSet.const (((pre horn₂₀.ι₀₁).app X).app (Opposite.op ⦋0⦌) v.val) := by
    rw [← Category.assoc, hG, hFl, hl]
  refine ⟨G, ?_, ?_, ?_, ?_, hGl⟩
  · have : Mono (markedSpanInclusion X W) := by dsimp [markedSpanInclusion]; infer_instance
    apply (cancel_mono (markedSpanInclusion X W)).mp
    rw [Category.assoc, hG, hF₀, SSet.const_comp, hp]
    rfl
  · change (G ≫ markedSpanInclusion X W) ≫ (pre horn₂₀.ι₀₂).app X ≫ evaluateFunctorAt _ = b
    rw [hG]
    exact hFt
  · change (G ≫ markedSpanInclusion X W ≫ (pre horn₂₀.ι₀₁).app X) ≫
      evaluateFunctorAt _ = _
    rw [hGl, SSet.const_comp]
    rfl
  · change (G ≫ markedSpanInclusion X W ≫ (pre horn₂₀.ι₀₁).app X) ≫
      evaluateFunctorAt _ = _
    rw [hGl, SSet.const_comp]
    rfl

end SerrePositivity.KST.LocalizingInvariants
