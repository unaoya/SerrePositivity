module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Stable.Quasicategory.SimplexCoconeSquareComparison
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.FractionFamilyComparisonIso
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierSpanRecoveredArrows

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
namespace SerrePositivity.InfinityCategories.Derived.Verdier.Fractions
open SerrePositivity.KST.LocalizingInvariants

private lemma spanCancelPointPrism {Y : SSet.{u}} {f g : (Δ[1] : SSet.{u}) ⟶ Y}
    (h : snd (Δ[0] : SSet.{u}) Δ[1] ≫ f = snd Δ[0] Δ[1] ≫ g) : f = g := by
  let t := lift (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) (𝟙 (Δ[1] : SSet.{u}))
  have he := congrArg (fun f => t ≫ f) h
  simpa only [← Category.assoc, t, lift_snd, Category.id_comp] using he

variable {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
  (h : IsVerdierSequence i q) (x y : B.obj _⦋0⦌)
  (d : (verdierDenominatorOver i x : SSet.{u}) _⦋0⦌)
  {K : SSet.{u}} (g : K ⟶ vertexFiber (verdierDenominatorSpanProjection i x y) d)

/-- 同じ共通実分母族の元の分数評価。 -/
def verdierSpanEvaluatedMapping : K ⟶ intervalMappingSpace
    (q.hom.app (Opposite.op ⦋0⦌) x) (q.hom.app (Opposite.op ⦋0⦌) y) :=
  g ≫ vertexFiberι (verdierDenominatorSpanProjection i x y) d ≫
    verdierDenominatorSpanCanonicalComparison i x y ≫
    fixedFractionEvaluation q.hom (weakEquivalences i) h.inverts x y

/-- 元の全族の同じ合成関係。分母の後の元の分数評価が、実次辺の商像に一致する。 -/
lemma verdierSpanRecoveredArrows_comp :
    Truncated.HomotopyCategory.homMk (verdierSpanMappedNumeratorEdge i q x y d g).toTruncated =
      Truncated.HomotopyCategory.homMk (verdierSpanMappedDenominatorEdge i q x d K).toTruncated ≫
        Truncated.HomotopyCategory.homMk
          (intervalMappingFamilyEdge (verdierSpanEvaluatedMapping h x y d g)).toTruncated := by
  let r := g ≫ vertexFiberι (verdierDenominatorSpanProjection i x y) d ≫
    verdierDenominatorSpanCanonicalComparison i x y ≫
    fixedMarkedSpanInclusion B.obj (weakEquivalences i) x y
  let U := r ≫ fractionEvaluationSquare q.hom (weakEquivalences i) h.inverts
  let S := internalHomFlipHomEquiv K (Δ[1] ⊗ Δ[1]) C.obj U
  have hfam : U ≫ (pre squareBottomEdge).app C.obj =
      verdierSpanMappedNumeratorFamily i q x y d g := by
    change (g ≫ vertexFiberι _ _ ≫ verdierSpanEvaluationSquare h x y) ≫ _ = _
    simp only [Category.assoc, verdierSpanEvaluationSquare_bottom,
      verdierSpanMappedNumeratorFamily, verdierDenominatorSpanFiberArrow]
  have htfam : U ≫ (pre squareTopEdge).app C.obj =
      verdierSpanEvaluatedMapping h x y d g ≫
        vertexFiberι ((pre (boundary 1).ι).app C.obj)
          (functorVertex (intervalMappingBoundary (q.hom.app (Opposite.op ⦋0⦌) x)
            (q.hom.app (Opposite.op ⦋0⦌) y))) := by
    change (g ≫ vertexFiberι _ _ ≫ verdierSpanEvaluationSquare h x y) ≫ _ = _
    simp only [Category.assoc, verdierSpanEvaluationSquare_top, verdierSpanEvaluatedMapping]
  have hb : (squareBottomArrow S).edge = (verdierSpanMappedNumeratorEdge i q x y d g).edge := by
    calc
      _ = SSet.yonedaEquiv (squareBottomEdge ≫ S) := squareBottomArrow_edge S
      _ = SSet.yonedaEquiv (internalHomFlipHomEquiv K Δ[1] C.obj
          (U ≫ (pre squareBottomEdge).app C.obj)) :=
        congrArg SSet.yonedaEquiv (internalHomFlipHomEquiv_pre_app squareBottomEdge U).symm
      _ = _ := by rw [hfam, verdierSpanMappedNumeratorEdge_edge]
  have ht : (squareTopArrow S).edge =
      (intervalMappingFamilyEdge (verdierSpanEvaluatedMapping h x y d g)).edge := by
    calc
      _ = SSet.yonedaEquiv (squareTopEdge ≫ S) := squareTopArrow_edge S
      _ = SSet.yonedaEquiv (internalHomFlipHomEquiv K Δ[1] C.obj
          (U ≫ (pre squareTopEdge).app C.obj)) :=
        congrArg SSet.yonedaEquiv (internalHomFlipHomEquiv_pre_app squareTopEdge U).symm
      _ = _ := by rw [htfam, intervalMappingFamilyEdge_edge]
  have hsource := verdierSpanFamilyHomotopy_source h x y d g
  rw [spanSquareFamilyHomotopy_source] at hsource
  have hlfam : internalHomFlipHomEquiv K Δ[1] C.obj (U ≫ (pre squareLeftEdge).app C.obj) =
      verdierSpanDenominatorDiagram i q x d ≫ curry (snd K C.obj) := by
    apply spanCancelPointPrism
    simpa only [U, r, verdierSpanEvaluationSquare, Category.assoc] using hsource
  have hl : (squareLeftArrow S).edge = (verdierSpanMappedDenominatorEdge i q x d K).edge := by
    calc
      _ = SSet.yonedaEquiv (squareLeftEdge ≫ S) := squareLeftArrow_edge S
      _ = SSet.yonedaEquiv (internalHomFlipHomEquiv K Δ[1] C.obj
          (U ≫ (pre squareLeftEdge).app C.obj)) :=
        congrArg SSet.yonedaEquiv (internalHomFlipHomEquiv_pre_app squareLeftEdge U).symm
      _ = _ := by rw [hlfam, verdierSpanMappedDenominatorEdge_edge]
  let z := (internalHomFlipHomEquiv K Δ[2] C.obj
    (r ≫ fractionEvaluationTriangle q.hom (weakEquivalences i) h.inverts)).app
      (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (2 : Fin 3))
  have htarget := fractionFamilyComparison_target q.hom (weakEquivalences i) h.inverts r
  rw [spanSquareFamilyHomotopy_target] at htarget
  have hrfam : squareRightEdge ≫ S = SSet.const z := by
    rw [← internalHomFlipHomEquiv_pre_app]
    exact spanCancelPointPrism htarget
  have hr : (squareRightArrow S).edge =
      (Truncated.Edge.id (X := (truncation 2).obj ((ihom K).obj C.obj)) z).edge := by
    calc
      _ = SSet.yonedaEquiv (squareRightEdge ≫ S) := squareRightArrow_edge S
      _ = SSet.yonedaEquiv (SSet.const z : (Δ[1] : SSet.{u}) ⟶ (ihom K).obj C.obj) :=
        congrArg SSet.yonedaEquiv hrfam
      _ = _ := pinchedConstant_one z
  have hB := Truncated.HomotopyCategory.congr_arrowMk_homMk _ _ hb
  have hR := Truncated.HomotopyCategory.congr_arrowMk_homMk _ _ hr
  rw [Truncated.HomotopyCategory.homMk_id] at hR
  have hz : (HomotopyCategory.mk z : hoFunctor.obj ((ihom K).obj C.obj)) =
      HomotopyCategory.mk (functorVertex
        (SSet.const (q.hom.app (Opposite.op ⦋0⦌) y) : K ⟶ C.obj)) :=
    (congrArg Arrow.left hR).symm.trans (congrArg Arrow.right hB)
  have hR' := hR.trans (congrArg (fun v : hoFunctor.obj ((ihom K).obj C.obj) =>
    Arrow.mk (𝟙 v)) hz)
  have hc := spanSquare_homMk_comm_of_arrowMks S
    (verdierSpanMappedNumeratorEdge i q x y d g).toTruncated
    (intervalMappingFamilyEdge (verdierSpanEvaluatedMapping h x y d g)).toTruncated
    (verdierSpanMappedDenominatorEdge i q x d K).toTruncated
    (Truncated.Edge.id (X := (truncation 2).obj ((ihom K).obj C.obj))
      (functorVertex (SSet.const (q.hom.app (Opposite.op ⦋0⦌) y) : K ⟶ C.obj)))
    hB (Truncated.HomotopyCategory.congr_arrowMk_homMk _ _ ht)
    (Truncated.HomotopyCategory.congr_arrowMk_homMk _ _ hl)
    (by
      rw [Truncated.HomotopyCategory.homMk_id]
      change Arrow.mk (Truncated.HomotopyCategory.homMk (squareRightArrow S)) =
        Arrow.mk (𝟙 (HomotopyCategory.mk (functorVertex
          (SSet.const (q.hom.app (Opposite.op ⦋0⦌) y) : K ⟶ C.obj))))
      exact hR')
  simpa only [Truncated.HomotopyCategory.homMk_id, Category.comp_id] using hc

/-- 回収した固定端点比較を元の同じ合成関係へ代入する。 -/
lemma verdierSpanRecoveredArrows_comp_of_comparison
    (f : K ⟶ intervalMappingSpace (q.hom.app (Opposite.op ⦋0⦌) x)
      (q.hom.app (Opposite.op ⦋0⦌) y))
    (e : FunctorIso (verdierSpanEvaluatedMapping h x y d g) f) :
    Truncated.HomotopyCategory.homMk (verdierSpanMappedNumeratorEdge i q x y d g).toTruncated =
      Truncated.HomotopyCategory.homMk (verdierSpanMappedDenominatorEdge i q x d K).toTruncated ≫
        Truncated.HomotopyCategory.homMk (intervalMappingFamilyEdge f).toTruncated := by
  rw [verdierSpanRecoveredArrows_comp h x y d g, intervalMappingFamilyEdge_homMk_eq e]

end SerrePositivity.InfinityCategories.Derived.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanEvaluatedMapping (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierSpanEvaluatedMapping := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanEvaluatedMapping

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierSpanRecoveredArrows_comp := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanRecoveredArrows_comp

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierSpanRecoveredArrows_comp_of_comparison := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanRecoveredArrows_comp_of_comparison

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierSpanEvaluatedMapping.congr_simp := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanEvaluatedMapping.congr_simp

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.verdierSpanEvaluatedMapping.eq_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanEvaluatedMapping.eq_1
