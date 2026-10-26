module

public import SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredBoundaryPrefixPath
public import SerrePositivity.KST.LocalizingInvariants.VerdierChosenTerminalRefinementMap
public import SerrePositivity.KST.LocalizingInvariants.VerdierSpanRecoveredArrows
public import SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredQuotientCoconeCylinder

/-!
概要：保存済みの同じ一様補完から K 全体の始端前段比較と実分数比較の共有経路を構成する。
方針：同じ終端分母一次単体を前段へ持ち上げ、元の実分数二胞体の始点を全経路で照合する。
規約：前段補完・次辺全族・分数比較辺を選び直さず、共有経路を追加入力にしない。
使われ方：指定 S 境界を保つ K 始端全図式比較の実前段を供給する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.LocalizingInvariants

variable {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
  {h : IsVerdierSequence i q} {n : ℕ} {D : (Δ[n] : SSet.{u}) ⟶ B.obj}
  {z : B.obj _⦋0⦌} {K : SSet.{u}} {S : K.Subcomplex}
  {a : S.toSSet ⟶ verdierDenominatorSpanFamily i
    (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z}
  {f : K ⟶ intervalMappingSpace
    (q.hom.app (Opposite.op ⦋0⦌)
      (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))))
    (q.hom.app (Opposite.op ⦋0⦌) z)}

lemma exists_verdierRecoveredInitialPrefixPath
    (r : VerdierFiniteMappingCoconeRecovery h D z S a f) :
    ∃ t : Truncated.Edge (X := (truncation 2).obj ((ihom (Δ[n] : SSet.{u})).obj B.obj))
        (functorVertex (terminalRefinementSourceDiagram r.cylinder.single)) (functorVertex D),
      t.edge ∈ (relativeFirstRowSimplex q n).obj (Opposite.op ⦋1⦌) ∧
      t.edge = (squareLeftArrow (terminalRefinementSquare r.cylinder.single)).edge ∧
      IsInvertibleEdge (X := (ihom (Δ[n] : SSet.{u})).obj ((ihom K).obj C.obj))
        (spanConstantPrefixEdge K q.hom t).toTruncated ∧
      SSet.yonedaEquiv.symm (functorEdgeOfSimplicialHomotopy r.initialFractionHomotopy).edge ≫
        (pre (stdSimplex.δ (1 : Fin 2))).app ((ihom K).obj C.obj) =
      SSet.yonedaEquiv.symm (spanConstantPrefixEdge K q.hom t).edge ≫
        (pre (simplexLastPoint n)).app ((ihom K).obj C.obj) := by
  let x := D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))
  obtain ⟨t, ht, hlast, hraw⟩ :=
    exists_verdierChosenTerminalRefinementMap_with_edge h D r.denominator
    r.cylinder.single r.cylinder.single_projection r.cylinder.single_terminal
  have hai : IsInvertibleEdge (X := (ihom (Δ[n] : SSet.{u})).obj ((ihom K).obj C.obj))
      (spanConstantPrefixEdge K q.hom t).toTruncated := by
    apply spanConstantPrefixEdge_isInvertible
    change IsIso (simplexDenominatorImageIso q t ht).hom
    infer_instance
  refine ⟨t, ht, hraw, hai, ?_⟩
  let A₀ := spanConstantPrefixEdge K q.hom t
  have haL : (functorEdgeAt A₀ (SSet.yonedaEquiv (simplexLastPoint n))).edge =
      (verdierSpanMappedDenominatorEdge i q x r.denominator K).edge := by
    have he := spanConstantPrefixEdge_component K q.hom t
      (SSet.yonedaEquiv (simplexLastPoint n))
    have hk : SSet.yonedaEquiv (simplexLastPoint n) =
        stdSimplex.obj₀Equiv.symm (Fin.last n) := Equiv.apply_symm_apply _ _
    rw [hk, hlast] at he
    have hd : SSet.yonedaEquiv (verdierSpanDenominatorDiagram i q x r.denominator) =
        (verdierSpanMappedDenominator i q x r.denominator).edge :=
      (congrArg SSet.yonedaEquiv
        (verdierSpanMappedDenominator_diagram i q x r.denominator)).symm.trans
          (Equiv.apply_symm_apply _ _)
    have hden := verdierSpanMappedDenominatorEdge_edge i q x r.denominator K
    rw [SSet.yonedaEquiv_comp, hd] at hden
    exact he.trans hden.symm
  change SSet.yonedaEquiv.symm (SSet.yonedaEquiv (curry r.initialFractionHomotopy.h)) ≫ _ = _
  rw [Equiv.symm_apply_apply, curry_pre_app]
  have hs := verdierSpanFamilyHomotopy_source h x z r.denominator r.numerator
  change (stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u})) ≫ r.initialFractionHomotopy.h = _ at hs
  rw [hs]
  apply (cancel_mono (pointFunctorEvaluationIso ((ihom K).obj C.obj)).hom).mp
  change curry (snd (Δ[0] : SSet.{u}) Δ[1] ≫ _ ≫ _) ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) =
    (_ ≫ (pre (simplexLastPoint n)).app _) ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 1))
  rw [curry_evaluateFunctorAt_vertex, Category.assoc, stable_pre_evaluateFunctorAt]
  simp only [← Category.assoc, lift_snd, Category.id_comp]
  have hp : (simplexLastPoint n).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) = SSet.yonedaEquiv (simplexLastPoint n) := by
    have h₀ : stdSimplex.obj₀Equiv.symm (0 : Fin 1) =
        SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})) := by decide
    rw [h₀, ← SSet.yonedaEquiv_comp, Category.id_comp]
  rw [hp]
  have he : (evaluateFunctorAt (Y := (ihom K).obj C.obj)
      (SSet.yonedaEquiv (simplexLastPoint n))).app
      (Opposite.op ⦋1⦌) A₀.edge =
      SSet.yonedaEquiv (verdierSpanDenominatorDiagram i q x r.denominator ≫
        curry (snd K C.obj)) := by
    exact haL.trans (verdierSpanMappedDenominatorEdge_edge i q x r.denominator K)
  rw [SSet.yonedaEquiv_symm_comp]
  change _ = SSet.yonedaEquiv.symm
    ((evaluateFunctorAt (Y := (ihom K).obj C.obj)
      (SSet.yonedaEquiv (simplexLastPoint n))).app (Opposite.op ⦋1⦌) A₀.edge)
  rw [he, Equiv.symm_apply_apply]

lemma VerdierFiniteMappingCoconeRecovery.initialSource_prefix
    (r : VerdierFiniteMappingCoconeRecovery h D z S a f) :
    (r.cylinder.whole ≫ (ihom (join (Δ[n] : SSet.{u}) Δ[0])).map q.hom) ≫
      (pre (joinInl (Δ[n] : SSet.{u}) Δ[0])).app C.obj =
      SSet.const (functorVertex (terminalRefinementSourceDiagram r.cylinder.single ≫ q.hom)) := by
  rw [Category.assoc, (pre (joinInl (Δ[n] : SSet.{u}) Δ[0])).naturality q.hom,
    ← Category.assoc, r.cylinder.whole_prefix, SSet.const_comp]
  rfl

/-- 保存済み K 全族の次辺は、同じ始端分数二胞体の下辺に厳密に一致する。 -/
lemma VerdierFiniteMappingCoconeRecovery.initialSource_last
    (r : VerdierFiniteMappingCoconeRecovery h D z S a f) :
    (r.cylinder.whole ≫ (ihom (join (Δ[n] : SSet.{u}) Δ[0])).map q.hom) ≫
      (pre (joinMap (simplexLastPoint n) (𝟙 Δ[0]))).app C.obj =
      (r.numerator ≫ vertexFiberι (verdierDenominatorSpanProjection i
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z) r.denominator ≫
        verdierSpanEvaluationSquare h
          (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z ≫
        (pre squareBottomEdge).app C.obj) ≫ (pre (joinStdSimplexIso 0 0).hom).app C.obj := by
  rw [Category.assoc, (pre (joinMap (simplexLastPoint n) (𝟙 Δ[0]))).naturality q.hom,
    ← Category.assoc, r.cylinder.whole_next]
  have he := congrArg (fun g => r.numerator ≫ vertexFiberι (verdierDenominatorSpanProjection i
      (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z) r.denominator ≫
      g ≫ (pre (joinStdSimplexIso 0 0).hom).app C.obj)
    (verdierSpanEvaluationSquare_bottom h
      (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z)
  simp only [Category.assoc] at he ⊢
  rw [he]
  simp only [verdierSpanFamilyNumeratorArrow, Category.assoc]
  rw [(pre (joinStdSimplexIso 0 0).hom).naturality q.hom]

namespace VerdierRecoveredQuotientCoconeCylinder
variable {r : VerdierFiniteMappingCoconeRecovery h D z S a f}
  {G : K ⟶ (ihom (join (Δ[n] : SSet.{u}) Δ[0])).obj C.obj}
  (U : VerdierRecoveredQuotientCoconeCylinder r G)

/-- 同じ商全余錐円柱の K 全体の始端を、そのまま取り出す。 -/
def initialFamily : K ⟶ (ihom (join (Δ[n] : SSet.{u}) Δ[0])).obj C.obj :=
  (SSet.ι₀ : K ⟶ K ⊗ (Δ[1] : SSet.{u})) ≫ U.whole

lemma initialFamily_prefix : U.initialFamily ≫
    (pre (joinInl (Δ[n] : SSet.{u}) Δ[0])).app C.obj =
    SSet.const (functorVertex (D ≫ q.hom)) := by
  rw [initialFamily, Category.assoc, U.fixedPrefix, SSet.comp_const]

/-- 同じ商円柱始端の次辺は、保存済み実 K 全族の同じ分数二胞体の上辺。 -/
lemma initialFamily_last : U.initialFamily ≫
    (pre (joinMap (simplexLastPoint n) (𝟙 Δ[0]))).app C.obj =
    (r.numerator ≫ vertexFiberι (verdierDenominatorSpanProjection i
      (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z) r.denominator ≫
      verdierSpanEvaluationSquare h
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z ≫
      (pre squareTopEdge).app C.obj) ≫ (pre (joinStdSimplexIso 0 0).hom).app C.obj := by
  rw [initialFamily, Category.assoc, U.lastArrow]
  have he := congrArg (fun g => r.numerator ≫ vertexFiberι (verdierDenominatorSpanProjection i
      (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z) r.denominator ≫
      g ≫ (pre (joinStdSimplexIso 0 0).hom).app C.obj)
    (verdierSpanEvaluationSquare_top h
      (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z)
  simp only [Category.assoc] at he ⊢
  rw [he, ← Category.assoc (SSet.ι₀ : K ⟶ K ⊗ Δ[1]) r.comparison.h,
    r.comparison.h₀]
  simp only [Category.assoc]

end VerdierRecoveredQuotientCoconeCylinder

end SerrePositivity.KST.LocalizingInvariants
