module

public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.VerdierCompletedSpanRelativeRecovery
public import SerrePositivity.KST.LocalizingInvariants.GroupoidCompletionFiniteBoundary

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
open scoped Simplicial
open SerrePositivity.InfinityCategories SerrePositivity.KST.Fibration
namespace SerrePositivity.KST.LocalizingInvariants

variable {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}

/-- 指定完成境界円柱の全体を、同じ一つの実分母の fiber へ戻した証人。 -/
structure VerdierCompletedSpanBoundaryRecovery (h : IsVerdierSequence i q)
    (x y : B.obj _⦋0⦌) {S K : SSet.{u}} (j : S ⟶ K)
    (f : K ⟶ groupoidCompletion (fixedMarkedSpans B.obj (weakEquivalences i) x y))
    {a : S ⟶ groupoidCompletion (fixedMarkedSpans B.obj (weakEquivalences i) x y)}
    (H : SSet.Homotopy a (j ≫ f)) where
  denominator : (verdierDenominatorOver i x : SSet.{u}) _⦋0⦌
  whole : finiteMappingCylinder j ⟶
    vertexFiber (verdierDenominatorSpanProjection i x y) denominator
  comparison : SSet.Homotopy
    (whole ≫ vertexFiberι (verdierDenominatorSpanProjection i x y) denominator ≫
      verdierDenominatorSpanCanonicalComparison i x y ≫
      groupoidCompletionMap (fixedMarkedSpans B.obj (weakEquivalences i) x y))
    (completedBoundaryCylinderMap j f H)

/-- 完成側の有限境界円柱全体から、実分母と実次辺族を新仮定なしに回収する。 -/
lemma exists_verdierCompletedSpanBoundaryRecovery (h : IsVerdierSequence i q)
    (x y : B.obj _⦋0⦌) {S K : SSet.{u}} [S.Finite] [K.Finite] (j : S ⟶ K)
    (f : K ⟶ groupoidCompletion (fixedMarkedSpans B.obj (weakEquivalences i) x y))
    {a : S ⟶ groupoidCompletion (fixedMarkedSpans B.obj (weakEquivalences i) x y)}
    (H : SSet.Homotopy a (j ≫ f)) :
    Nonempty (VerdierCompletedSpanBoundaryRecovery h x y j f H) := by
  let M := finiteMappingCylinder j
  let E := verdierDenominatorSpanFamily i x y
  let b : ((⊥ : M.Subcomplex) : SSet.{u}) ⟶ E := {
    app := fun _ => TypeCat.ofHom (fun s => False.elim s.property)
    naturality := by intro n m v; ext s; exact False.elim s.property }
  have hb : b ≫ verdierDenominatorSpanCanonicalComparison i x y ≫
      groupoidCompletionMap (fixedMarkedSpans B.obj (weakEquivalences i) x y) =
      (⊥ : M.Subcomplex).ι ≫ completedBoundaryCylinderMap j f H := by
    ext n s
    exact False.elim s.property
  obtain ⟨d, g, _, G, _⟩ := verdierCompletedSpan_relative_finite_recovery h x y
    (⊥ : M.Subcomplex) b (completedBoundaryCylinderMap j f H) hb
  exact ⟨⟨d, g, G⟩⟩

namespace VerdierCompletedSpanBoundaryRecovery
variable {h : IsVerdierSequence i q} {x y : B.obj _⦋0⦌} {S K : SSet.{u}} {j : S ⟶ K}
  {f : K ⟶ groupoidCompletion (fixedMarkedSpans B.obj (weakEquivalences i) x y)}
  {a : S ⟶ groupoidCompletion (fixedMarkedSpans B.obj (weakEquivalences i) x y)}
  {H : SSet.Homotopy a (j ≫ f)} (d : VerdierCompletedSpanBoundaryRecovery h x y j f H)

/-- 全 K 次辺族。境界と同じ実分母を共有する。 -/
def family : K ⟶ vertexFiber (verdierDenominatorSpanProjection i x y) d.denominator :=
  pushout.inr (prismEndpoint 1 S) j ≫ d.whole

/-- 完成境界から回収された実 S 次辺族。 -/
def boundary : S ⟶ vertexFiber (verdierDenominatorSpanProjection i x y) d.denominator :=
  finiteMappingCylinderSource j ≫ d.whole

/-- 実分母を全時刻で固定した、同じ実境界から全族の制限への円柱。 -/
def nativeHomotopy : SSet.Homotopy d.boundary (j ≫ d.family) := by
  let V := functorHomotopyPostcomp (finiteMappingCylinderHomotopy j) d.whole
  exact { h := V.h, h₀ := V.h₀, h₁ := V.h₁.trans (Category.assoc _ _ _), rel := V.rel }

/-- 元の完成 K 全族への比較は、選択済み全比較の同じ制限。 -/
def familyComparison : SSet.Homotopy
    (d.family ≫ vertexFiberι (verdierDenominatorSpanProjection i x y) d.denominator ≫
      verdierDenominatorSpanCanonicalComparison i x y ≫
      groupoidCompletionMap (fixedMarkedSpans B.obj (weakEquivalences i) x y)) f := by
  let V := functorHomotopyPrecomp d.comparison (pushout.inr (prismEndpoint 1 S) j)
  exact {
    h := V.h
    h₀ := V.h₀
    h₁ := V.h₁.trans (completedBoundaryCylinderMap_family j f H)
    rel := V.rel }

/-- 元の完成 S 境界への比較も、一つの全比較の同じ始端制限。 -/
def boundaryComparison : SSet.Homotopy
    (d.boundary ≫ vertexFiberι (verdierDenominatorSpanProjection i x y) d.denominator ≫
      verdierDenominatorSpanCanonicalComparison i x y ≫
      groupoidCompletionMap (fixedMarkedSpans B.obj (weakEquivalences i) x y)) a := by
  let V := functorHomotopyPrecomp d.comparison (finiteMappingCylinderSource j)
  exact {
    h := V.h
    h₀ := V.h₀
    h₁ := V.h₁.trans (completedBoundaryCylinderMap_boundary j f H)
    rel := V.rel }

/-- 指定された元の完成境界円柱全体への二変数比較。同じ全比較の prism 制限。 -/
def prismComparison : SSet.Homotopy
    (d.nativeHomotopy.h ≫ vertexFiberι (verdierDenominatorSpanProjection i x y) d.denominator ≫
      verdierDenominatorSpanCanonicalComparison i x y ≫
      groupoidCompletionMap (fixedMarkedSpans B.obj (weakEquivalences i) x y)) H.h := by
  let V := functorHomotopyPrecomp d.comparison (finiteMappingCylinderHomotopy j).h
  exact {
    h := V.h
    h₀ := V.h₀
    h₁ := V.h₁.trans (completedBoundaryCylinderMap_prism j f H)
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
    (d.whole ≫ vertexFiberι (verdierDenominatorSpanProjection i x y) d.denominator ≫
      verdierDenominatorSpanCanonicalComparison i x y ≫
      fixedFractionEvaluation q.hom (weakEquivalences i) h.inverts x y)
    (completedBoundaryCylinderMap j f H ≫
      fractionMappingComparison q.hom (weakEquivalences i) h.inverts x y) := by
  let N := d.whole ≫ vertexFiberι (verdierDenominatorSpanProjection i x y) d.denominator ≫
    verdierDenominatorSpanCanonicalComparison i x y
  let t := fractionMappingComparison q.hom (weakEquivalences i) h.inverts x y
  have e₀ : FunctorIso
      (N ≫ fixedFractionEvaluation q.hom (weakEquivalences i) h.inverts x y)
      (N ≫ groupoidCompletionMap (fixedMarkedSpans B.obj (weakEquivalences i) x y) ≫ t) := by
    exact (FunctorIso.precomp
      (fractionMappingComparisonIso q.hom (weakEquivalences i) h.inverts x y) N).symm
  have e₁ : FunctorIso
      (N ≫ groupoidCompletionMap (fixedMarkedSpans B.obj (weakEquivalences i) x y) ≫ t)
      (completedBoundaryCylinderMap j f H ≫ t) := by
    simpa only [N, Category.assoc] using
      functorIsoOfSimplicialHomotopy (functorHomotopyPostcomp d.comparison t)
  simpa only [N, t, Category.assoc] using e₀ ≪≫ e₁

end VerdierCompletedSpanBoundaryRecovery
end SerrePositivity.KST.LocalizingInvariants
