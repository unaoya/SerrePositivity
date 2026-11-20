module


public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCompletedSpanRelativeRecovery
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.GroupoidCompletionFiniteBoundary

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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions
open _root_.SerrePositivity.KST.LocalizingInvariants

variable {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} {i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B} {q : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap B C}

/-- 指定完成境界円柱の全体を、同じ一つの実分母の fiber へ戻した証人。 -/
structure VerdierCompletedSpanBoundaryRecovery (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q)
    (x y : B.obj _⦋0⦌) {S K : SSet.{u}} (j : S ⟶ K)
    (f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.groupoidCompletion (fixedMarkedSpans B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) x y))
    {a : S ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.groupoidCompletion (fixedMarkedSpans B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) x y)}
    (H : SSet.Homotopy a (j ≫ f)) where
  denominator : (verdierDenominatorOver i x : SSet.{u}) _⦋0⦌
  whole : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.finiteMappingCylinder j ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierDenominatorSpanProjection i x y) denominator
  comparison : SSet.Homotopy
    (whole ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierDenominatorSpanProjection i x y) denominator ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierDenominatorSpanCanonicalComparison i x y ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.groupoidCompletionMap (fixedMarkedSpans B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) x y))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.completedBoundaryCylinderMap j f H)

/-- 完成側の有限境界円柱全体から、実分母と実次辺族を新仮定なしに回収する。 -/
lemma exists_verdierCompletedSpanBoundaryRecovery (h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q)
    (x y : B.obj _⦋0⦌) {S K : SSet.{u}} [S.Finite] [K.Finite] (j : S ⟶ K)
    (f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.groupoidCompletion (fixedMarkedSpans B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) x y))
    {a : S ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.groupoidCompletion (fixedMarkedSpans B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) x y)}
    (H : SSet.Homotopy a (j ≫ f)) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCompletedSpanBoundaryRecovery h x y j f H) := by
  let M := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.finiteMappingCylinder j
  let E := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierDenominatorSpanFamily i x y
  let b : ((⊥ : M.Subcomplex) : SSet.{u}) ⟶ E := {
    app := fun _ => TypeCat.ofHom (fun s => False.elim s.property)
    naturality := by intro n m v; ext s; exact False.elim s.property }
  have hb : b ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierDenominatorSpanCanonicalComparison i x y ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.groupoidCompletionMap (fixedMarkedSpans B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) x y) =
      (⊥ : M.Subcomplex).ι ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.completedBoundaryCylinderMap j f H := by
    ext n s
    exact False.elim s.property
  obtain ⟨d, g, _, G, _⟩ := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierCompletedSpan_relative_finite_recovery h x y
    (⊥ : M.Subcomplex) b (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.completedBoundaryCylinderMap j f H) hb
  exact ⟨⟨d, g, G⟩⟩

namespace VerdierCompletedSpanBoundaryRecovery

variable {h : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.IsVerdierSequence i q} {x y : B.obj _⦋0⦌} {S K : SSet.{u}} {j : S ⟶ K}
  {f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.groupoidCompletion (fixedMarkedSpans B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) x y)}
  {a : S ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.groupoidCompletion (fixedMarkedSpans B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) x y)}
  {H : SSet.Homotopy a (j ≫ f)} (d : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.VerdierCompletedSpanBoundaryRecovery h x y j f H)

/-- 全 K 次辺族。境界と同じ実分母を共有する。 -/
def family : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierDenominatorSpanProjection i x y) d.denominator :=
  pushout.inr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 S) j ≫ d.whole

/-- 完成境界から回収された実 S 次辺族。 -/
def boundary : S ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierDenominatorSpanProjection i x y) d.denominator :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.finiteMappingCylinderSource j ≫ d.whole

/-- 実分母を全時刻で固定した、同じ実境界から全族の制限への円柱。 -/
def nativeHomotopy : SSet.Homotopy d.boundary (j ≫ d.family) := by
  let V := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.finiteMappingCylinderHomotopy j) d.whole
  exact { h := V.h, h₀ := V.h₀, h₁ := V.h₁.trans (Category.assoc _ _ _), rel := V.rel }

/-- 元の完成 K 全族への比較は、選択済み全比較の同じ制限。 -/
def familyComparison : SSet.Homotopy
    (d.family ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierDenominatorSpanProjection i x y) d.denominator ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierDenominatorSpanCanonicalComparison i x y ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.groupoidCompletionMap (fixedMarkedSpans B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) x y)) f := by
  let V := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp d.comparison (pushout.inr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 S) j)
  exact {
    h := V.h
    h₀ := V.h₀
    h₁ := V.h₁.trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.completedBoundaryCylinderMap_family j f H)
    rel := V.rel }

/-- 元の完成 S 境界への比較も、一つの全比較の同じ始端制限。 -/
def boundaryComparison : SSet.Homotopy
    (d.boundary ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierDenominatorSpanProjection i x y) d.denominator ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierDenominatorSpanCanonicalComparison i x y ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.groupoidCompletionMap (fixedMarkedSpans B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) x y)) a := by
  let V := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp d.comparison (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.finiteMappingCylinderSource j)
  exact {
    h := V.h
    h₀ := V.h₀
    h₁ := V.h₁.trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.completedBoundaryCylinderMap_boundary j f H)
    rel := V.rel }

/-- 指定された元の完成境界円柱全体への二変数比較。同じ全比較の prism 制限。 -/
def prismComparison : SSet.Homotopy
    (d.nativeHomotopy.h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierDenominatorSpanProjection i x y) d.denominator ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierDenominatorSpanCanonicalComparison i x y ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.groupoidCompletionMap (fixedMarkedSpans B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) x y)) H.h := by
  let V := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPrecomp d.comparison (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.finiteMappingCylinderHomotopy j).h
  exact {
    h := V.h
    h₀ := V.h₀
    h₁ := V.h₁.trans (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.completedBoundaryCylinderMap_prism j f H)
    rel := V.rel }

/-- 全 prism 比較の始面は、同じ完成境界への全比較と厳密に一致する。 -/
lemma prismComparison_zero : ((SSet.ι₀ : S ⟶ S ⊗ (Δ[1] : SSet.{u})) ▷ Δ[1]) ≫
    d.prismComparison.h = d.boundaryComparison.h := by
  change (_ ▷ (Δ[1] : SSet.{u})) ≫
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.finiteMappingCylinderHomotopy j).h ▷ (Δ[1] : SSet.{u})) ≫ d.comparison.h = _
  rw [← comp_whiskerRight_assoc, (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.finiteMappingCylinderHomotopy j).h₀]
  rfl

/-- 全 prism 比較の終面は、同じ K 全比較の j 制限と厳密に一致する。 -/
lemma prismComparison_one : ((SSet.ι₁ : S ⟶ S ⊗ (Δ[1] : SSet.{u})) ▷ Δ[1]) ≫
    d.prismComparison.h = (j ▷ (Δ[1] : SSet.{u})) ≫ d.familyComparison.h := by
  change (_ ▷ (Δ[1] : SSet.{u})) ≫
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.finiteMappingCylinderHomotopy j).h ▷ (Δ[1] : SSet.{u})) ≫ d.comparison.h = _
  rw [← comp_whiskerRight_assoc, (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.finiteMappingCylinderHomotopy j).h₁,
    comp_whiskerRight, Category.assoc]
  rfl

/-- 回収した実分数評価と元の完成分数評価は、同じ全写像円柱上で全関手同型。 -/
def evaluationIso : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (d.whole ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierDenominatorSpanProjection i x y) d.denominator ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierDenominatorSpanCanonicalComparison i x y ≫
      fixedFractionEvaluation q.hom (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) h.inverts x y)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.completedBoundaryCylinderMap j f H ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionMappingComparison q.hom (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) h.inverts x y) := by
  let N := d.whole ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierDenominatorSpanProjection i x y) d.denominator ≫
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.verdierDenominatorSpanCanonicalComparison i x y
  let t := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionMappingComparison q.hom (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) h.inverts x y
  have e₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (N ≫ fixedFractionEvaluation q.hom (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) h.inverts x y)
      (N ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.groupoidCompletionMap (fixedMarkedSpans B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) x y) ≫ t) := by
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.fractionMappingComparisonIso q.hom (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) h.inverts x y) N).symm
  have e₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (N ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.groupoidCompletionMap (fixedMarkedSpans B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) x y) ≫ t)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Localization.completedBoundaryCylinderMap j f H ≫ t) := by
    simpa only [N, Category.assoc] using
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorIsoOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.functorHomotopyPostcomp d.comparison t)
  simpa only [N, t, Category.assoc] using e₀ ≪≫ e₁

end VerdierCompletedSpanBoundaryRecovery
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
