module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierSpanFamilyHomotopy
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.HomotopyInvertibility

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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions
open _root_.SerrePositivity.KST.LocalizingInvariants

lemma spanConstantInterval_isInvertible {Y : SSet.{u}} [Quasicategory Y] (z : Y _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (SSet.yonedaEquiv (SSet.const z : (Δ[1] : SSet.{u}) ⟶ Y))) := by
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (Truncated.Edge.id (X := (truncation 2).obj Y) z) := by
    dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge]
    rw [Truncated.HomotopyCategory.homMk_id]
    infer_instance
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex
    (SSet.yonedaEquiv (SSet.const z : (Δ[1] : SSet.{u}) ⟶ Y)))
    (f := Truncated.Edge.id (X := (truncation 2).obj Y) z) ?_).mpr hi
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one z

variable {X Q K : SSet.{u}} [Quasicategory Q] (F : X ⟶ Q) (W : Set (X _⦋1⦌))
  (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InvertsEdges F W) (r : K ⟶ markedSpans X W)

/-- 比較の終点経路は、元の同じ三角形の終点における恒等経路。 -/
lemma fractionFamilyComparison_target :
    (stdSimplex.δ (0 : Fin 2) ▷ (Δ[1] : SSet.{u})) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.spanSquareFamilyHomotopy (r ≫ fractionEvaluationSquare F W hF)).h =
    snd Δ[0] Δ[1] ≫ SSet.const
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv K Δ[2] Q (r ≫ fractionEvaluationTriangle F W hF)).app
        (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (2 : Fin 3))) := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.spanSquareFamilyHomotopy_target]
  simp only [Category.assoc]
  rw [fractionEvaluationSquare_right, ← Category.assoc r,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv_pre_app, SSet.const_comp]

/-- 分母を反転する関手の元の分数比較は、全パラメータ関手圏で可逆な比較辺。 -/
lemma fractionFamilyComparison_isInvertible :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.spanSquareFamilyHomotopy (r ≫ fractionEvaluationSquare F W hF))) := by
  let l := r ≫ markedSpanInclusion X W ≫ (ihom (horn 2 0 : SSet.{u})).map F ≫
    (pre horn₂₀.ι₀₁).app Q
  let a := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv K Δ[1] Q l))
  have ha : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge a := by
    let v₀ := ((ihom K).obj Q).δ 1
      (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv K Δ[1] Q l))
    let v₁ := ((ihom K).obj Q).δ 0
      (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv K Δ[1] Q l))
    let a' := (SSet.Edge.ofTruncated (X := (ihom K).obj Q) a).ofEq
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv K Q).apply_symm_apply v₀).symm
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv K Q).apply_symm_apply v₁).symm
    have ha' : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge a'.toTruncated := by
      apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isInvertibleEdge_iff_evaluateFunctorAt a'.toTruncated).mpr
      intro k
      have hk := hF (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex (r.app (Opposite.op ⦋0⦌) k))
      have he : (a'.toTruncated.map ((truncation 2).map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := Q) k))).edge =
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (spanLeftEdge ((r.app (Opposite.op ⦋0⦌) k).val))).map
          ((truncation 2).map F)).edge := by
        change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := Q) k).app (Opposite.op ⦋1⦌)
          (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv K Δ[1] Q l)) = _
        rw [spanInternalHomFlip_interval_edge]
        have hl : l = r ≫ markedSpanInclusion X W ≫ (pre horn₂₀.ι₀₁).app X ≫
            (ihom (Δ[1] : SSet.{u})).map F := by
          dsimp only [l]
          rw [(pre horn₂₀.ι₀₁).naturality F]
        rw [hl]
        change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalFunctorVertexEdge (((ihom (Δ[1] : SSet.{u})).map F).app
          (Opposite.op ⦋0⦌) (((pre horn₂₀.ι₀₁).app X).app (Opposite.op ⦋0⦌)
            (r.app (Opposite.op ⦋0⦌) k).val)) = _
        rw [intervalFunctorVertexEdge_postcomp]
        rfl
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr he).mpr hk
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e := a) (f := a'.toTruncated) rfl).mpr ha'
  let z := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv K Δ[2] Q (r ≫ fractionEvaluationTriangle F W hF)).app
    (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (2 : Fin 3))
  let b := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (SSet.yonedaEquiv (SSet.const z : (Δ[1] : SSet.{u}) ⟶ (ihom K).obj Q))
  have hb : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge b := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.spanConstantInterval_isInvertible z
  apply _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.arrowHomotopy_isInvertible_of_endpointPaths
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.spanSquareFamilyHomotopy (r ≫ fractionEvaluationSquare F W hF)) a b ha hb
  · rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.spanSquareFamilyHomotopy_source]
    simp only [Category.assoc]
    rw [fractionEvaluationSquare_left]
    change snd Δ[0] Δ[1] ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv K Δ[1] Q l =
      snd Δ[0] Δ[1] ≫ SSet.yonedaEquiv.symm (SSet.yonedaEquiv
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv K Δ[1] Q l))
    rw [Equiv.symm_apply_apply]
  · rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionFamilyComparison_target]
    change snd Δ[0] Δ[1] ≫ SSet.const z = snd Δ[0] Δ[1] ≫
      SSet.yonedaEquiv.symm (SSet.yonedaEquiv (SSet.const z : (Δ[1] : SSet.{u}) ⟶ _))
    rw [Equiv.symm_apply_apply]

/-- 元の全比較円柱の同じ辺から得る、パラメータ関手圏での実関手同型。 -/
def fractionFamilyComparisonIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv K Δ[1] Q
      ((r ≫ fractionEvaluationSquare F W hF) ≫ (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge).app Q))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv K Δ[1] Q
      ((r ≫ fractionEvaluationSquare F W hF) ≫ (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge).app Q)) := by
  have := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionFamilyComparison_isInvertible F W hF r
  exact asIso (Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.spanSquareFamilyHomotopy (r ≫ fractionEvaluationSquare F W hF))))

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
