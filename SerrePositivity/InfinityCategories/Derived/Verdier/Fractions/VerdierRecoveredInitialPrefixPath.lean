module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Stable.Quasicategory.CoconeFamilyTranspose
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierChosenTerminalRefinementMap
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierRecoveredBoundaryPrefixPath
public import SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredQuotientCoconeCylinder
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierSpanRecoveredArrows

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
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredQuotientCoconeCylinder
end SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredQuotientCoconeCylinder
namespace SerrePositivity.InfinityCategories.Derived.Verdier.Fractions
open SerrePositivity.KST.LocalizingInvariants

variable {A B C : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap B C}
  {h : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsVerdierSequence i q} {n : ℕ} {D : (Δ[n] : SSet.{u}) ⟶ B.obj}
  {z : B.obj _⦋0⦌} {K : SSet.{u}} {S : K.Subcomplex}
  {a : S.toSSet ⟶ _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanFamily i
    (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z}
  {f : K ⟶ intervalMappingSpace
    (q.hom.app (Opposite.op ⦋0⦌)
      (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))))
    (q.hom.app (Opposite.op ⦋0⦌) z)}

lemma exists_verdierRecoveredInitialPrefixPath
    (r : _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery h D z S a f) :
    ∃ t : Truncated.Edge (X := (truncation 2).obj ((ihom (Δ[n] : SSet.{u})).obj B.obj))
        (functorVertex (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.terminalRefinementSourceDiagram r.cylinder.single)) (functorVertex D),
      t.edge ∈ (relativeFirstRowSimplex q n).obj (Opposite.op ⦋1⦌) ∧
      t.edge = (squareLeftArrow (terminalRefinementSquare r.cylinder.single)).edge ∧
      IsInvertibleEdge (X := (ihom (Δ[n] : SSet.{u})).obj ((ihom K).obj C.obj))
        (_root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.spanConstantPrefixEdge K q.hom t).toTruncated ∧
      SSet.yonedaEquiv.symm (functorEdgeOfSimplicialHomotopy r.initialFractionHomotopy).edge ≫
        (pre (stdSimplex.δ (1 : Fin 2))).app ((ihom K).obj C.obj) =
      SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.spanConstantPrefixEdge K q.hom t).edge ≫
        (pre (_root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.simplexLastPoint n)).app ((ihom K).obj C.obj) := by
  let x := D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))
  obtain ⟨t, ht, hlast, hraw⟩ :=
    _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.exists_verdierChosenTerminalRefinementMap_with_edge h D r.denominator
    r.cylinder.single r.cylinder.single_projection r.cylinder.single_terminal
  have hai : IsInvertibleEdge (X := (ihom (Δ[n] : SSet.{u})).obj ((ihom K).obj C.obj))
      (_root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.spanConstantPrefixEdge K q.hom t).toTruncated := by
    apply _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.spanConstantPrefixEdge_isInvertible
    change IsIso (simplexDenominatorImageIso q t ht).hom
    infer_instance
  refine ⟨t, ht, hraw, hai, ?_⟩
  let A₀ := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.spanConstantPrefixEdge K q.hom t
  have haL : (functorEdgeAt A₀ (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.simplexLastPoint n))).edge =
      (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanMappedDenominatorEdge i q x r.denominator K).edge := by
    have he := _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.spanConstantPrefixEdge_component K q.hom t
      (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.simplexLastPoint n))
    have hk : SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.simplexLastPoint n) =
        stdSimplex.obj₀Equiv.symm (Fin.last n) := Equiv.apply_symm_apply _ _
    rw [hk, hlast] at he
    have hd : SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanDenominatorDiagram i q x r.denominator) =
        (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanMappedDenominator i q x r.denominator).edge :=
      (congrArg SSet.yonedaEquiv
        (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanMappedDenominator_diagram i q x r.denominator)).symm.trans
          (Equiv.apply_symm_apply _ _)
    have hden := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanMappedDenominatorEdge_edge i q x r.denominator K
    rw [SSet.yonedaEquiv_comp, hd] at hden
    exact he.trans hden.symm
  change SSet.yonedaEquiv.symm (SSet.yonedaEquiv (curry r.initialFractionHomotopy.h)) ≫ _ = _
  rw [Equiv.symm_apply_apply, curry_pre_app]
  have hs := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanFamilyHomotopy_source h x z r.denominator r.numerator
  change (stdSimplex.δ (1 : Fin 2) ▷ (Δ[1] : SSet.{u})) ≫ r.initialFractionHomotopy.h = _ at hs
  rw [hs]
  apply (cancel_mono (pointFunctorEvaluationIso ((ihom K).obj C.obj)).hom).mp
  change curry (snd (Δ[0] : SSet.{u}) Δ[1] ≫ _ ≫ _) ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) =
    (_ ≫ (pre (_root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.simplexLastPoint n)).app _) ≫
      evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 1))
  rw [curry_evaluateFunctorAt_vertex, Category.assoc, stable_pre_evaluateFunctorAt]
  simp only [← Category.assoc, lift_snd, Category.id_comp]
  have hp : (_root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.simplexLastPoint n).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 1)) = SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.simplexLastPoint n) := by
    have h₀ : stdSimplex.obj₀Equiv.symm (0 : Fin 1) =
        SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u})) := by decide
    rw [h₀, ← SSet.yonedaEquiv_comp, Category.id_comp]
  rw [hp]
  have he : (evaluateFunctorAt (Y := (ihom K).obj C.obj)
      (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.simplexLastPoint n))).app
      (Opposite.op ⦋1⦌) A₀.edge =
      SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanDenominatorDiagram i q x r.denominator ≫
        curry (snd K C.obj)) := by
    exact haL.trans (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanMappedDenominatorEdge_edge i q x r.denominator K)
  rw [SSet.yonedaEquiv_symm_comp]
  change _ = SSet.yonedaEquiv.symm
    ((evaluateFunctorAt (Y := (ihom K).obj C.obj)
      (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.simplexLastPoint n))).app (Opposite.op ⦋1⦌) A₀.edge)
  rw [he, Equiv.symm_apply_apply]

lemma VerdierFiniteMappingCoconeRecovery.initialSource_prefix
    (r : _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery h D z S a f) :
    (r.cylinder.whole ≫ (ihom (join (Δ[n] : SSet.{u}) Δ[0])).map q.hom) ≫
      (pre (joinInl (Δ[n] : SSet.{u}) Δ[0])).app C.obj =
      SSet.const (functorVertex (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.terminalRefinementSourceDiagram r.cylinder.single ≫ q.hom)) := by
  rw [Category.assoc, (pre (joinInl (Δ[n] : SSet.{u}) Δ[0])).naturality q.hom,
    ← Category.assoc, r.cylinder.whole_prefix, SSet.const_comp]
  rfl

/-- 保存済み K 全族の次辺は、同じ始端分数二胞体の下辺に厳密に一致する。 -/
lemma VerdierFiniteMappingCoconeRecovery.initialSource_last
    (r : _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery h D z S a f) :
    (r.cylinder.whole ≫ (ihom (join (Δ[n] : SSet.{u}) Δ[0])).map q.hom) ≫
      (pre (joinMap (_root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.simplexLastPoint n) (𝟙 Δ[0]))).app C.obj =
      (r.numerator ≫ vertexFiberι (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanProjection i
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z) r.denominator ≫
        _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanEvaluationSquare h
          (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z ≫
        (pre squareBottomEdge).app C.obj) ≫ (pre (joinStdSimplexIso 0 0).hom).app C.obj := by
  rw [Category.assoc, (pre (joinMap (_root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.simplexLastPoint n) (𝟙 Δ[0]))).naturality q.hom,
    ← Category.assoc, r.cylinder.whole_next]
  have he := congrArg (fun g => r.numerator ≫ vertexFiberι (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanProjection i
      (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z) r.denominator ≫
      g ≫ (pre (joinStdSimplexIso 0 0).hom).app C.obj)
    (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanEvaluationSquare_bottom h
      (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z)
  simp only [Category.assoc] at he ⊢
  rw [he]
  simp only [_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanFamilyNumeratorArrow, Category.assoc]
  rw [(pre (joinStdSimplexIso 0 0).hom).naturality q.hom]

namespace VerdierRecoveredQuotientCoconeCylinder
open SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredQuotientCoconeCylinder
variable {r : _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery h D z S a f}
  {G : K ⟶ (ihom (join (Δ[n] : SSet.{u}) Δ[0])).obj C.obj}
  (U : VerdierRecoveredQuotientCoconeCylinder r G)

/-- 同じ商全余錐円柱の K 全体の始端を、そのまま取り出す。 -/
def initialFamily : K ⟶ (ihom (join (Δ[n] : SSet.{u}) Δ[0])).obj C.obj :=
  (SSet.ι₀ : K ⟶ K ⊗ (Δ[1] : SSet.{u})) ≫ U.whole

lemma initialFamily_prefix : (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierRecoveredQuotientCoconeCylinder.initialFamily U) ≫
    (pre (joinInl (Δ[n] : SSet.{u}) Δ[0])).app C.obj =
    SSet.const (functorVertex (D ≫ q.hom)) := by
  rw [_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierRecoveredQuotientCoconeCylinder.initialFamily, Category.assoc, U.fixedPrefix, SSet.comp_const]

/-- 同じ商円柱始端の次辺は、保存済み実 K 全族の同じ分数二胞体の上辺。 -/
lemma initialFamily_last : (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierRecoveredQuotientCoconeCylinder.initialFamily U) ≫
    (pre (joinMap (_root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.simplexLastPoint n) (𝟙 Δ[0]))).app C.obj =
    (r.numerator ≫ vertexFiberι (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanProjection i
      (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z) r.denominator ≫
      _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanEvaluationSquare h
        (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z ≫
      (pre squareTopEdge).app C.obj) ≫ (pre (joinStdSimplexIso 0 0).hom).app C.obj := by
  rw [_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierRecoveredQuotientCoconeCylinder.initialFamily, Category.assoc, U.lastArrow]
  have he := congrArg (fun g => r.numerator ≫ vertexFiberι (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanProjection i
      (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z) r.denominator ≫
      g ≫ (pre (joinStdSimplexIso 0 0).hom).app C.obj)
    (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierSpanEvaluationSquare_top h
      (D.app (Opposite.op ⦋0⦌) (stdSimplex.obj₀Equiv.symm (Fin.last n))) z)
  simp only [Category.assoc] at he ⊢
  rw [he, ← Category.assoc (SSet.ι₀ : K ⟶ K ⊗ Δ[1]) r.comparison.h,
    r.comparison.h₀]
  simp only [Category.assoc]

end VerdierRecoveredQuotientCoconeCylinder

end SerrePositivity.InfinityCategories.Derived.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.exists_verdierRecoveredInitialPrefixPath := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.exists_verdierRecoveredInitialPrefixPath

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteMappingCoconeRecovery.initialSource_last := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery.initialSource_last

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierFiniteMappingCoconeRecovery.initialSource_prefix := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierFiniteMappingCoconeRecovery.initialSource_prefix

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierRecoveredQuotientCoconeCylinder.initialFamily (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredQuotientCoconeCylinder.initialFamily := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierRecoveredQuotientCoconeCylinder.initialFamily

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredQuotientCoconeCylinder.initialFamily_last := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierRecoveredQuotientCoconeCylinder.initialFamily_last

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredQuotientCoconeCylinder.initialFamily_prefix := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierRecoveredQuotientCoconeCylinder.initialFamily_prefix

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierRecoveredQuotientCoconeCylinder.initialFamily.eq_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierRecoveredQuotientCoconeCylinder.initialFamily.eq_1
