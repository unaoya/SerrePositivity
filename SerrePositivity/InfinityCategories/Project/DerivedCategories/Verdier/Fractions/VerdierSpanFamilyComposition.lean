module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.SimplexCoconeSquareComparison
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.FractionFamilyComparisonIso
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierSpanRecoveredArrows

/-!
概要：共通実分母・実次辺・元の分数評価の全族は、パラメータ関手圏で同じ合成関係を持つ。
方針：元の四角形の四辺を固定端点の実辺へ厳密照合し、同じ実二単体から合成整合を得る。
規約：合成整合を入力に残さず、元の評価と回収した固定端点比較から証明する。
使われ方：前段の指定分母経路と次辺比較の共有経路付き貼合せ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions
open _root_.SerrePositivity.KST.LocalizingInvariants

private lemma spanCancelPointPrism {Y : SSet.{u}} {f g : (Δ[1] : SSet.{u}) ⟶ Y}
    (h : snd (Δ[0] : SSet.{u}) Δ[1] ≫ f = snd Δ[0] Δ[1] ≫ g) : f = g := by
  let t := lift (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) (𝟙 (Δ[1] : SSet.{u}))
  have he := congrArg (fun f => t ≫ f) h
  simpa only [← Category.assoc, t, lift_snd, Category.id_comp] using he

variable {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}
  (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q) (x y : B.obj _⦋0⦌)
  (d : (verdierDenominatorOver i x : SSet.{u}) _⦋0⦌)
  {K : SSet.{u}} (g : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierDenominatorSpanProjection i x y) d)

/-- 同じ共通実分母族の元の分数評価。 -/
def verdierSpanEvaluatedMapping : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace
    (q.hom.app (Opposite.op ⦋0⦌) x) (q.hom.app (Opposite.op ⦋0⦌) y) :=
  g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierDenominatorSpanProjection i x y) d ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierDenominatorSpanCanonicalComparison i x y ≫
    fixedFractionEvaluation q.hom (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) h.inverts x y

/-- 元の全族の同じ合成関係。分母の後の元の分数評価が、実次辺の商像に一致する。 -/
lemma verdierSpanRecoveredArrows_comp :
    Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanMappedNumeratorEdge i q x y d g).toTruncated =
      Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanMappedDenominatorEdge i q x d K).toTruncated ≫
        Truncated.HomotopyCategory.homMk
          (intervalMappingFamilyEdge (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanEvaluatedMapping h x y d g)).toTruncated := by
  let r := g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierDenominatorSpanProjection i x y) d ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierDenominatorSpanCanonicalComparison i x y ≫
    fixedMarkedSpanInclusion B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) x y
  let U := r ≫ fractionEvaluationSquare q.hom (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) h.inverts
  let S := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv K (Δ[1] ⊗ Δ[1]) C.obj U
  have hfam : U ≫ (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge).app C.obj =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanMappedNumeratorFamily i q x y d g := by
    change (g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι _ _ ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanEvaluationSquare h x y) ≫ _ = _
    simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanEvaluationSquare_bottom,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanMappedNumeratorFamily, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierDenominatorSpanFiberArrow]
  have htfam : U ≫ (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge).app C.obj =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanEvaluatedMapping h x y d g ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι ((pre (boundary 1).ι).app C.obj)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingBoundary (q.hom.app (Opposite.op ⦋0⦌) x)
            (q.hom.app (Opposite.op ⦋0⦌) y))) := by
    change (g ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι _ _ ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanEvaluationSquare h x y) ≫ _ = _
    simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanEvaluationSquare_top, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanEvaluatedMapping]
  have hb : (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareBottomArrow S).edge = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanMappedNumeratorEdge i q x y d g).edge := by
    calc
      _ = SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge ≫ S) := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareBottomArrow_edge S
      _ = SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv K Δ[1] C.obj
          (U ≫ (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge).app C.obj)) :=
        congrArg SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv_pre_app _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareBottomEdge U).symm
      _ = _ := by rw [hfam, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanMappedNumeratorEdge_edge]
  have ht : (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareTopArrow S).edge =
      (intervalMappingFamilyEdge (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanEvaluatedMapping h x y d g)).edge := by
    calc
      _ = SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge ≫ S) := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareTopArrow_edge S
      _ = SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv K Δ[1] C.obj
          (U ≫ (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge).app C.obj)) :=
        congrArg SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv_pre_app _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareTopEdge U).symm
      _ = _ := by rw [htfam, intervalMappingFamilyEdge_edge]
  have hsource := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanFamilyHomotopy_source h x y d g
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.spanSquareFamilyHomotopy_source] at hsource
  have hlfam : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv K Δ[1] C.obj (U ≫ (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge).app C.obj) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanDenominatorDiagram i q x d ≫ curry (snd K C.obj) := by
    apply spanCancelPointPrism
    simpa only [U, r, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanEvaluationSquare, Category.assoc] using hsource
  have hl : (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareLeftArrow S).edge = (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanMappedDenominatorEdge i q x d K).edge := by
    calc
      _ = SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge ≫ S) := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.squareLeftArrow_edge S
      _ = SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv K Δ[1] C.obj
          (U ≫ (pre _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge).app C.obj)) :=
        congrArg SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv_pre_app _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareLeftEdge U).symm
      _ = _ := by rw [hlfam, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanMappedDenominatorEdge_edge]
  let z := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv K Δ[2] C.obj
    (r ≫ fractionEvaluationTriangle q.hom (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) h.inverts)).app
      (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (2 : Fin 3))
  have htarget := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionFamilyComparison_target q.hom (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) h.inverts r
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.spanSquareFamilyHomotopy_target] at htarget
  have hrfam : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ S = SSet.const z := by
    rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv_pre_app]
    exact spanCancelPointPrism htarget
  have hr : (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareRightArrow S).edge =
      (Truncated.Edge.id (X := (truncation 2).obj ((ihom K).obj C.obj)) z).edge := by
    calc
      _ = SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.squareRightEdge ≫ S) := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareRightArrow_edge S
      _ = SSet.yonedaEquiv (SSet.const z : (Δ[1] : SSet.{u}) ⟶ (ihom K).obj C.obj) :=
        congrArg SSet.yonedaEquiv hrfam
      _ = _ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_one z
  have hB := Truncated.HomotopyCategory.congr_arrowMk_homMk _ _ hb
  have hR := Truncated.HomotopyCategory.congr_arrowMk_homMk _ _ hr
  rw [Truncated.HomotopyCategory.homMk_id] at hR
  have hz : (HomotopyCategory.mk z : hoFunctor.obj ((ihom K).obj C.obj)) =
      HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex
        (SSet.const (q.hom.app (Opposite.op ⦋0⦌) y) : K ⟶ C.obj)) :=
    (congrArg Arrow.left hR).symm.trans (congrArg Arrow.right hB)
  have hR' := hR.trans (congrArg (fun v : hoFunctor.obj ((ihom K).obj C.obj) =>
    Arrow.mk (𝟙 v)) hz)
  have hc := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.spanSquare_homMk_comm_of_arrowMks S
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanMappedNumeratorEdge i q x y d g).toTruncated
    (intervalMappingFamilyEdge (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanEvaluatedMapping h x y d g)).toTruncated
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanMappedDenominatorEdge i q x d K).toTruncated
    (Truncated.Edge.id (X := (truncation 2).obj ((ihom K).obj C.obj))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (SSet.const (q.hom.app (Opposite.op ⦋0⦌) y) : K ⟶ C.obj)))
    hB (Truncated.HomotopyCategory.congr_arrowMk_homMk _ _ ht)
    (Truncated.HomotopyCategory.congr_arrowMk_homMk _ _ hl)
    (by
      rw [Truncated.HomotopyCategory.homMk_id]
      change Arrow.mk (Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareRightArrow S)) =
        Arrow.mk (𝟙 (HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex
          (SSet.const (q.hom.app (Opposite.op ⦋0⦌) y) : K ⟶ C.obj))))
      exact hR')
  simpa only [Truncated.HomotopyCategory.homMk_id, Category.comp_id] using hc

/-- 回収した固定端点比較を元の同じ合成関係へ代入する。 -/
lemma verdierSpanRecoveredArrows_comp_of_comparison
    (f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (q.hom.app (Opposite.op ⦋0⦌) x)
      (q.hom.app (Opposite.op ⦋0⦌) y))
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanEvaluatedMapping h x y d g) f) :
    Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanMappedNumeratorEdge i q x y d g).toTruncated =
      Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanMappedDenominatorEdge i q x d K).toTruncated ≫
        Truncated.HomotopyCategory.homMk (intervalMappingFamilyEdge f).toTruncated := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanRecoveredArrows_comp h x y d g, intervalMappingFamilyEdge_homMk_eq e]

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanEvaluatedMapping (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierSpanEvaluatedMapping := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanEvaluatedMapping

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierSpanRecoveredArrows_comp := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanRecoveredArrows_comp

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierSpanRecoveredArrows_comp_of_comparison := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanRecoveredArrows_comp_of_comparison

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierSpanEvaluatedMapping.congr_simp := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanEvaluatedMapping.congr_simp

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierSpanEvaluatedMapping.eq_1 := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierSpanEvaluatedMapping.eq_1
