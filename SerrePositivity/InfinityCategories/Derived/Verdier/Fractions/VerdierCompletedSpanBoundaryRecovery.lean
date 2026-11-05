module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanRelativeRecovery
public import SerrePositivity.InfinityCategories.Derived.Localization.GroupoidCompletionFiniteBoundary

/-!
概要：完成分数の全族・完成境界・指定境界円柱を、一つの実分母の次辺族へ戻す。
方針：指定円柱と全族を有限写像円柱へ貼り、Sp-6 s4 の実回収を一度だけ適用する。
規約：境界が既に実分数族であるとは仮定せず、全比較は一つの円柱の制限とする。
使われ方：完成側有限境界を実分母・次辺族へ接続する入口。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.LocalizingInvariants
end SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanBoundaryRecovery
end SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanBoundaryRecovery
namespace SerrePositivity.InfinityCategories.Derived.Verdier.Fractions
open SerrePositivity.KST.LocalizingInvariants

variable {A B C : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.ExactMap B C}

/-- 指定完成境界円柱の全体を、同じ一つの実分母の fiber へ戻した証人。 -/
structure VerdierCompletedSpanBoundaryRecovery (h : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsVerdierSequence i q)
    (x y : B.obj _⦋0⦌) {S K : SSet.{u}} (j : S ⟶ K)
    (f : K ⟶ _root_.SerrePositivity.InfinityCategories.Derived.Localization.groupoidCompletion (fixedMarkedSpans B.obj (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) x y))
    {a : S ⟶ _root_.SerrePositivity.InfinityCategories.Derived.Localization.groupoidCompletion (fixedMarkedSpans B.obj (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) x y)}
    (H : SSet.Homotopy a (j ≫ f)) where
  denominator : (verdierDenominatorOver i x : SSet.{u}) _⦋0⦌
  whole : finiteMappingCylinder j ⟶
    vertexFiber (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanProjection i x y) _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanBoundaryRecovery.denominator
  comparison : SSet.Homotopy
    (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanBoundaryRecovery.whole ≫ vertexFiberι (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanProjection i x y) _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanBoundaryRecovery.denominator ≫
      _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanCanonicalComparison i x y ≫
      _root_.SerrePositivity.InfinityCategories.Derived.Localization.groupoidCompletionMap (fixedMarkedSpans B.obj (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) x y))
    (_root_.SerrePositivity.InfinityCategories.Derived.Localization.completedBoundaryCylinderMap j f H)

/-- 完成側の有限境界円柱全体から、実分母と実次辺族を新仮定なしに回収する。 -/
lemma exists_verdierCompletedSpanBoundaryRecovery (h : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsVerdierSequence i q)
    (x y : B.obj _⦋0⦌) {S K : SSet.{u}} [S.Finite] [K.Finite] (j : S ⟶ K)
    (f : K ⟶ _root_.SerrePositivity.InfinityCategories.Derived.Localization.groupoidCompletion (fixedMarkedSpans B.obj (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) x y))
    {a : S ⟶ _root_.SerrePositivity.InfinityCategories.Derived.Localization.groupoidCompletion (fixedMarkedSpans B.obj (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) x y)}
    (H : SSet.Homotopy a (j ≫ f)) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanBoundaryRecovery h x y j f H) := by
  let M := finiteMappingCylinder j
  let E := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanFamily i x y
  let b : ((⊥ : M.Subcomplex) : SSet.{u}) ⟶ E := {
    app := fun _ => TypeCat.ofHom (fun s => False.elim s.property)
    naturality := by intro n m v; ext s; exact False.elim s.property }
  have hb : b ≫ _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanCanonicalComparison i x y ≫
      _root_.SerrePositivity.InfinityCategories.Derived.Localization.groupoidCompletionMap (fixedMarkedSpans B.obj (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) x y) =
      (⊥ : M.Subcomplex).ι ≫ _root_.SerrePositivity.InfinityCategories.Derived.Localization.completedBoundaryCylinderMap j f H := by
    ext n s
    exact False.elim s.property
  obtain ⟨d, g, _, G, _⟩ := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierCompletedSpan_relative_finite_recovery h x y
    (⊥ : M.Subcomplex) b (_root_.SerrePositivity.InfinityCategories.Derived.Localization.completedBoundaryCylinderMap j f H) hb
  exact ⟨⟨d, g, G⟩⟩

namespace VerdierCompletedSpanBoundaryRecovery
open _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanBoundaryRecovery
variable {h : _root_.SerrePositivity.InfinityCategories.Stable.Verdier.IsVerdierSequence i q} {x y : B.obj _⦋0⦌} {S K : SSet.{u}} {j : S ⟶ K}
  {f : K ⟶ _root_.SerrePositivity.InfinityCategories.Derived.Localization.groupoidCompletion (fixedMarkedSpans B.obj (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) x y)}
  {a : S ⟶ _root_.SerrePositivity.InfinityCategories.Derived.Localization.groupoidCompletion (fixedMarkedSpans B.obj (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) x y)}
  {H : SSet.Homotopy a (j ≫ f)} (d : _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanBoundaryRecovery h x y j f H)

/-- 全 K 次辺族。境界と同じ実分母を共有する。 -/
def family : K ⟶ vertexFiber (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanProjection i x y) d.denominator :=
  pushout.inr (prismEndpoint 1 S) j ≫ d.whole

/-- 完成境界から回収された実 S 次辺族。 -/
def boundary : S ⟶ vertexFiber (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanProjection i x y) d.denominator :=
  finiteMappingCylinderSource j ≫ d.whole

/-- 実分母を全時刻で固定した、同じ実境界から全族の制限への円柱。 -/
def nativeHomotopy : SSet.Homotopy d.boundary (j ≫ d.family) := by
  let V := functorHomotopyPostcomp (finiteMappingCylinderHomotopy j) d.whole
  exact { h := V.h, h₀ := V.h₀, h₁ := V.h₁.trans (Category.assoc _ _ _), rel := V.rel }

/-- 元の完成 K 全族への比較は、選択済み全比較の同じ制限。 -/
def familyComparison : SSet.Homotopy
    (d.family ≫ vertexFiberι (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanProjection i x y) d.denominator ≫
      _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanCanonicalComparison i x y ≫
      _root_.SerrePositivity.InfinityCategories.Derived.Localization.groupoidCompletionMap (fixedMarkedSpans B.obj (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) x y)) f := by
  let V := functorHomotopyPrecomp d.comparison (pushout.inr (prismEndpoint 1 S) j)
  exact {
    h := V.h
    h₀ := V.h₀
    h₁ := V.h₁.trans (_root_.SerrePositivity.InfinityCategories.Derived.Localization.completedBoundaryCylinderMap_family j f H)
    rel := V.rel }

/-- 元の完成 S 境界への比較も、一つの全比較の同じ始端制限。 -/
def boundaryComparison : SSet.Homotopy
    (d.boundary ≫ vertexFiberι (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanProjection i x y) d.denominator ≫
      _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanCanonicalComparison i x y ≫
      _root_.SerrePositivity.InfinityCategories.Derived.Localization.groupoidCompletionMap (fixedMarkedSpans B.obj (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) x y)) a := by
  let V := functorHomotopyPrecomp d.comparison (finiteMappingCylinderSource j)
  exact {
    h := V.h
    h₀ := V.h₀
    h₁ := V.h₁.trans (_root_.SerrePositivity.InfinityCategories.Derived.Localization.completedBoundaryCylinderMap_boundary j f H)
    rel := V.rel }

/-- 指定された元の完成境界円柱全体への二変数比較。同じ全比較の prism 制限。 -/
def prismComparison : SSet.Homotopy
    (d.nativeHomotopy.h ≫ vertexFiberι (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanProjection i x y) d.denominator ≫
      _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanCanonicalComparison i x y ≫
      _root_.SerrePositivity.InfinityCategories.Derived.Localization.groupoidCompletionMap (fixedMarkedSpans B.obj (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) x y)) H.h := by
  let V := functorHomotopyPrecomp d.comparison (finiteMappingCylinderHomotopy j).h
  exact {
    h := V.h
    h₀ := V.h₀
    h₁ := V.h₁.trans (_root_.SerrePositivity.InfinityCategories.Derived.Localization.completedBoundaryCylinderMap_prism j f H)
    rel := V.rel }

/-- 全 prism 比較の始面は、同じ完成境界への全比較と厳密に一致する。 -/
lemma prismComparison_zero : ((SSet.ι₀ : S ⟶ S ⊗ (Δ[1] : SSet.{u})) ▷ Δ[1]) ≫
    d.prismComparison.h = d.boundaryComparison.h := by
  change (_ ▷ (Δ[1] : SSet.{u})) ≫
    ((finiteMappingCylinderHomotopy j).h ▷ (Δ[1] : SSet.{u})) ≫ d.comparison.h = _
  rw [← comp_whiskerRight_assoc, (finiteMappingCylinderHomotopy j).h₀]
  rfl

/-- 全 prism 比較の終面は、同じ K 全比較の j 制限と厳密に一致する。 -/
lemma prismComparison_one : ((SSet.ι₁ : S ⟶ S ⊗ (Δ[1] : SSet.{u})) ▷ Δ[1]) ≫
    d.prismComparison.h = (j ▷ (Δ[1] : SSet.{u})) ≫ d.familyComparison.h := by
  change (_ ▷ (Δ[1] : SSet.{u})) ≫
    ((finiteMappingCylinderHomotopy j).h ▷ (Δ[1] : SSet.{u})) ≫ d.comparison.h = _
  rw [← comp_whiskerRight_assoc, (finiteMappingCylinderHomotopy j).h₁,
    comp_whiskerRight, Category.assoc]
  rfl

/-- 回収した実分数評価と元の完成分数評価は、同じ全写像円柱上で全関手同型。 -/
def evaluationIso : FunctorIso
    (d.whole ≫ vertexFiberι (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanProjection i x y) d.denominator ≫
      _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanCanonicalComparison i x y ≫
      fixedFractionEvaluation q.hom (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) h.inverts x y)
    (_root_.SerrePositivity.InfinityCategories.Derived.Localization.completedBoundaryCylinderMap j f H ≫
      _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionMappingComparison q.hom (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) h.inverts x y) := by
  let N := d.whole ≫ vertexFiberι (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanProjection i x y) d.denominator ≫
    _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.verdierDenominatorSpanCanonicalComparison i x y
  let t := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionMappingComparison q.hom (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) h.inverts x y
  have e₀ : FunctorIso
      (N ≫ fixedFractionEvaluation q.hom (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) h.inverts x y)
      (N ≫ _root_.SerrePositivity.InfinityCategories.Derived.Localization.groupoidCompletionMap (fixedMarkedSpans B.obj (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) x y) ≫ t) := by
    exact (FunctorIso.precomp
      (_root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.fractionMappingComparisonIso q.hom (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) h.inverts x y) N).symm
  have e₁ : FunctorIso
      (N ≫ _root_.SerrePositivity.InfinityCategories.Derived.Localization.groupoidCompletionMap (fixedMarkedSpans B.obj (_root_.SerrePositivity.InfinityCategories.Stable.Verdier.Fractions.weakEquivalences i) x y) ≫ t)
      (_root_.SerrePositivity.InfinityCategories.Derived.Localization.completedBoundaryCylinderMap j f H ≫ t) := by
    simpa only [N, Category.assoc] using
      functorIsoOfSimplicialHomotopy (functorHomotopyPostcomp d.comparison t)
  simpa only [N, t, Category.assoc] using e₀ ≪≫ e₁

end VerdierCompletedSpanBoundaryRecovery
end SerrePositivity.InfinityCategories.Derived.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanBoundaryRecovery (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanBoundaryRecovery := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanBoundaryRecovery

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.exists_verdierCompletedSpanBoundaryRecovery := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.exists_verdierCompletedSpanBoundaryRecovery

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanBoundaryRecovery._sizeOf_1 (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanBoundaryRecovery._sizeOf_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanBoundaryRecovery._sizeOf_1

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanBoundaryRecovery._sizeOf_inst (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanBoundaryRecovery._sizeOf_inst := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanBoundaryRecovery._sizeOf_inst

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanBoundaryRecovery.boundary (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanBoundaryRecovery.boundary := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanBoundaryRecovery.boundary

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanBoundaryRecovery.boundaryComparison (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanBoundaryRecovery.boundaryComparison := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanBoundaryRecovery.boundaryComparison

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanBoundaryRecovery.casesOn (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanBoundaryRecovery.casesOn := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanBoundaryRecovery.casesOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanBoundaryRecovery.comparison (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanBoundaryRecovery.comparison := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanBoundaryRecovery.comparison

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanBoundaryRecovery.ctorIdx (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanBoundaryRecovery.ctorIdx := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanBoundaryRecovery.ctorIdx

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanBoundaryRecovery.denominator (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanBoundaryRecovery.denominator := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanBoundaryRecovery.denominator

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanBoundaryRecovery.evaluationIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanBoundaryRecovery.evaluationIso := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanBoundaryRecovery.evaluationIso

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanBoundaryRecovery.family (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanBoundaryRecovery.family := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanBoundaryRecovery.family

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanBoundaryRecovery.familyComparison (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanBoundaryRecovery.familyComparison := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanBoundaryRecovery.familyComparison

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanBoundaryRecovery.mk (since := "2026-11-05"), match_pattern]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanBoundaryRecovery.mk := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanBoundaryRecovery.mk

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanBoundaryRecovery.nativeHomotopy (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanBoundaryRecovery.nativeHomotopy := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanBoundaryRecovery.nativeHomotopy

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanBoundaryRecovery.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanBoundaryRecovery.noConfusion := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanBoundaryRecovery.noConfusion

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanBoundaryRecovery.noConfusionType (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanBoundaryRecovery.noConfusionType := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanBoundaryRecovery.noConfusionType

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanBoundaryRecovery.prismComparison (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanBoundaryRecovery.prismComparison := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanBoundaryRecovery.prismComparison

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanBoundaryRecovery.prismComparison_one := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanBoundaryRecovery.prismComparison_one

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanBoundaryRecovery.prismComparison_zero := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanBoundaryRecovery.prismComparison_zero

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanBoundaryRecovery.rec (since := "2026-11-05"), elab_as_elim]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanBoundaryRecovery.rec := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanBoundaryRecovery.rec

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanBoundaryRecovery.recOn (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanBoundaryRecovery.recOn := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanBoundaryRecovery.recOn

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanBoundaryRecovery.whole (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanBoundaryRecovery.whole := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanBoundaryRecovery.whole

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanBoundaryRecovery.boundaryComparison._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanBoundaryRecovery.boundaryComparison._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanBoundaryRecovery.boundaryComparison._proof_2 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanBoundaryRecovery.boundaryComparison._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanBoundaryRecovery.boundaryComparison._proof_3 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanBoundaryRecovery.boundaryComparison._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanBoundaryRecovery.evaluationIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanBoundaryRecovery.evaluationIso._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanBoundaryRecovery.evaluationIso._proof_2 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanBoundaryRecovery.evaluationIso._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanBoundaryRecovery.evaluationIso._proof_3 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanBoundaryRecovery.evaluationIso._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanBoundaryRecovery.evaluationIso._proof_4 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanBoundaryRecovery.evaluationIso._proof_4

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanBoundaryRecovery.family._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanBoundaryRecovery.family._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanBoundaryRecovery.family._proof_2 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanBoundaryRecovery.family._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanBoundaryRecovery.familyComparison._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanBoundaryRecovery.familyComparison._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanBoundaryRecovery.familyComparison._proof_2 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanBoundaryRecovery.familyComparison._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanBoundaryRecovery.familyComparison._proof_3 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanBoundaryRecovery.familyComparison._proof_3

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanBoundaryRecovery.mk._flat_ctor (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanBoundaryRecovery.mk._flat_ctor := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanBoundaryRecovery.mk._flat_ctor

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanBoundaryRecovery.mk.inj := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanBoundaryRecovery.mk.inj

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanBoundaryRecovery.mk.injEq := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanBoundaryRecovery.mk.injEq

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanBoundaryRecovery.mk.noConfusion (since := "2026-11-05")]
noncomputable deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanBoundaryRecovery.mk.noConfusion := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanBoundaryRecovery.mk.noConfusion

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanBoundaryRecovery.mk.sizeOf_spec := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanBoundaryRecovery.mk.sizeOf_spec

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanBoundaryRecovery.nativeHomotopy._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanBoundaryRecovery.nativeHomotopy._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanBoundaryRecovery.nativeHomotopy._proof_2 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanBoundaryRecovery.nativeHomotopy._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanBoundaryRecovery.nativeHomotopy._proof_3 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanBoundaryRecovery.nativeHomotopy._proof_3

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanBoundaryRecovery.nativeHomotopy._proof_4 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanBoundaryRecovery.nativeHomotopy._proof_4

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanBoundaryRecovery.prismComparison._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanBoundaryRecovery.prismComparison._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanBoundaryRecovery.prismComparison._proof_2 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanBoundaryRecovery.prismComparison._proof_2

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.LocalizingInvariants.VerdierCompletedSpanBoundaryRecovery.prismComparison._proof_3 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanBoundaryRecovery.prismComparison._proof_3
