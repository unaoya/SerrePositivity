module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierSpanFamilyHomotopy
public import SerrePositivity.InfinityCategories.Core.HomotopyInvertibility

/-!
概要：元の分数評価の全比較四角形は、パラメータ関手圏で実際に可逆である。
方針：左経路の各成分は元の反転分母、右経路は同じ終点での恒等辺と検査する。
規約：パラメータに有限性・充填性は不要。既存の比較円柱を変更しない。
使われ方：回収した商の次辺族と前段比較の共有経路の貼合せ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.Derived.Verdier.Fractions
open SerrePositivity.KST.LocalizingInvariants

lemma spanConstantInterval_isInvertible {Y : SSet.{u}} [Quasicategory Y] (z : Y _⦋0⦌) :
    IsInvertibleEdge (edgeOfSimplex (SSet.yonedaEquiv (SSet.const z : (Δ[1] : SSet.{u}) ⟶ Y))) := by
  have hi : IsInvertibleEdge (Truncated.Edge.id (X := (truncation 2).obj Y) z) := by
    dsimp only [IsInvertibleEdge]
    rw [Truncated.HomotopyCategory.homMk_id]
    infer_instance
  apply (isInvertibleEdge_congr (e := edgeOfSimplex
    (SSet.yonedaEquiv (SSet.const z : (Δ[1] : SSet.{u}) ⟶ Y)))
    (f := Truncated.Edge.id (X := (truncation 2).obj Y) z) ?_).mpr hi
  exact pinchedConstant_one z

variable {X Q K : SSet.{u}} [Quasicategory Q] (F : X ⟶ Q) (W : Set (X _⦋1⦌))
  (hF : InvertsEdges F W) (r : K ⟶ markedSpans X W)

/-- 比較の終点経路は、元の同じ三角形の終点における恒等経路。 -/
lemma fractionFamilyComparison_target :
    (stdSimplex.δ (0 : Fin 2) ▷ (Δ[1] : SSet.{u})) ≫
      (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.spanSquareFamilyHomotopy (r ≫ fractionEvaluationSquare F W hF)).h =
    snd Δ[0] Δ[1] ≫ SSet.const
      ((internalHomFlipHomEquiv K Δ[2] Q (r ≫ fractionEvaluationTriangle F W hF)).app
        (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (2 : Fin 3))) := by
  rw [_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.spanSquareFamilyHomotopy_target]
  simp only [Category.assoc]
  rw [fractionEvaluationSquare_right, ← Category.assoc r,
    internalHomFlipHomEquiv_pre_app, SSet.const_comp]

/-- 分母を反転する関手の元の分数比較は、全パラメータ関手圏で可逆な比較辺。 -/
lemma fractionFamilyComparison_isInvertible :
    IsInvertibleEdge (functorEdgeOfSimplicialHomotopy
      (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.spanSquareFamilyHomotopy (r ≫ fractionEvaluationSquare F W hF))) := by
  let l := r ≫ markedSpanInclusion X W ≫ (ihom (horn 2 0 : SSet.{u})).map F ≫
    (pre horn₂₀.ι₀₁).app Q
  let a := edgeOfSimplex (SSet.yonedaEquiv (internalHomFlipHomEquiv K Δ[1] Q l))
  have ha : IsInvertibleEdge a := by
    let v₀ := ((ihom K).obj Q).δ 1
      (SSet.yonedaEquiv (internalHomFlipHomEquiv K Δ[1] Q l))
    let v₁ := ((ihom K).obj Q).δ 0
      (SSet.yonedaEquiv (internalHomFlipHomEquiv K Δ[1] Q l))
    let a' := (SSet.Edge.ofTruncated (X := (ihom K).obj Q) a).ofEq
      ((functorVertexEquiv K Q).apply_symm_apply v₀).symm
      ((functorVertexEquiv K Q).apply_symm_apply v₁).symm
    have ha' : IsInvertibleEdge a'.toTruncated := by
      apply (isInvertibleEdge_iff_evaluateFunctorAt a'.toTruncated).mpr
      intro k
      have hk := hF (fullSubcomplexOnVertices_vertex (r.app (Opposite.op ⦋0⦌) k))
      have he : (a'.toTruncated.map ((truncation 2).map (evaluateFunctorAt (Y := Q) k))).edge =
        ((edgeOfSimplex (spanLeftEdge ((r.app (Opposite.op ⦋0⦌) k).val))).map
          ((truncation 2).map F)).edge := by
        change (evaluateFunctorAt (Y := Q) k).app (Opposite.op ⦋1⦌)
          (SSet.yonedaEquiv (internalHomFlipHomEquiv K Δ[1] Q l)) = _
        rw [spanInternalHomFlip_interval_edge]
        have hl : l = r ≫ markedSpanInclusion X W ≫ (pre horn₂₀.ι₀₁).app X ≫
            (ihom (Δ[1] : SSet.{u})).map F := by
          dsimp only [l]
          rw [(pre horn₂₀.ι₀₁).naturality F]
        rw [hl]
        change intervalFunctorVertexEdge (((ihom (Δ[1] : SSet.{u})).map F).app
          (Opposite.op ⦋0⦌) (((pre horn₂₀.ι₀₁).app X).app (Opposite.op ⦋0⦌)
            (r.app (Opposite.op ⦋0⦌) k).val)) = _
        rw [intervalFunctorVertexEdge_postcomp]
        rfl
      exact (isInvertibleEdge_congr he).mpr hk
    exact (isInvertibleEdge_congr (e := a) (f := a'.toTruncated) rfl).mpr ha'
  let z := (internalHomFlipHomEquiv K Δ[2] Q (r ≫ fractionEvaluationTriangle F W hF)).app
    (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (2 : Fin 3))
  let b := edgeOfSimplex (SSet.yonedaEquiv (SSet.const z : (Δ[1] : SSet.{u}) ⟶ (ihom K).obj Q))
  have hb : IsInvertibleEdge b := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.spanConstantInterval_isInvertible z
  apply arrowHomotopy_isInvertible_of_endpointPaths
    (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.spanSquareFamilyHomotopy (r ≫ fractionEvaluationSquare F W hF)) a b ha hb
  · rw [_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.spanSquareFamilyHomotopy_source]
    simp only [Category.assoc]
    rw [fractionEvaluationSquare_left]
    change snd Δ[0] Δ[1] ≫ internalHomFlipHomEquiv K Δ[1] Q l =
      snd Δ[0] Δ[1] ≫ SSet.yonedaEquiv.symm (SSet.yonedaEquiv
        (internalHomFlipHomEquiv K Δ[1] Q l))
    rw [Equiv.symm_apply_apply]
  · rw [_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionFamilyComparison_target]
    change snd Δ[0] Δ[1] ≫ SSet.const z = snd Δ[0] Δ[1] ≫
      SSet.yonedaEquiv.symm (SSet.yonedaEquiv (SSet.const z : (Δ[1] : SSet.{u}) ⟶ _))
    rw [Equiv.symm_apply_apply]

/-- 元の全比較円柱の同じ辺から得る、パラメータ関手圏での実関手同型。 -/
def fractionFamilyComparisonIso : FunctorIso
    (internalHomFlipHomEquiv K Δ[1] Q
      ((r ≫ fractionEvaluationSquare F W hF) ≫ (pre squareBottomEdge).app Q))
    (internalHomFlipHomEquiv K Δ[1] Q
      ((r ≫ fractionEvaluationSquare F W hF) ≫ (pre squareTopEdge).app Q)) := by
  have := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionFamilyComparison_isInvertible F W hF r
  exact asIso (Truncated.HomotopyCategory.homMk (functorEdgeOfSimplicialHomotopy
    (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.spanSquareFamilyHomotopy (r ≫ fractionEvaluationSquare F W hF))))

end SerrePositivity.InfinityCategories.Derived.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionFamilyComparisonIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.fractionFamilyComparisonIso := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionFamilyComparisonIso

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.fractionFamilyComparison_isInvertible := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionFamilyComparison_isInvertible

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.fractionFamilyComparison_target := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionFamilyComparison_target

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.spanConstantInterval_isInvertible := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.spanConstantInterval_isInvertible
