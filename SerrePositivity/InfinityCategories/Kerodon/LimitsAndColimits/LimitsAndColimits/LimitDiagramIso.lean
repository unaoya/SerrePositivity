module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.LimitConeExtension
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.EquivalenceCylinderFunctorIso
public import Mathlib.Tactic.CrossRefAttribute
/-!
概要：関手同型で結ばれた実図式の極限の存在を輸送する。
方針：可逆円柱へ延長し、両端の同値な単射に沿う実錐の制限を使う。
規約：添字には quasicategory 性を課さない。使われ方：反転された実分母図式の極限。

対応節は Kerodon 7.1（Tag 02H1）。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
/-- 同値な単射に沿う制限は、実極限の存在を保存し反映する。 -/
lemma hasLimit_iff_restrict_of_precompositionEquivalence {K L X : SSet.{u}}
    [Quasicategory X] (p : K ⟶ X) (f : L ⟶ K) [Mono f]
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IsPrecompositionEquivalence f) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit p ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit (f ≫ p) := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverRestrict_trivialKanFibration_of_precompositionEquivalence p f hf
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.restrictJoinCone c f, ?_⟩
    exact ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.qCatEquivalenceOfTrivialKanFibration
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverRestrict p f)).isTerminalVertex_iff c).mp hc
  · rintro ⟨d, hd⟩
    obtain ⟨c, hc, _, _⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.exists_limitCone_extension_of_trivialRestriction p f d hd
    exact ⟨c, hc⟩
/-- 可逆円柱の両端の実図式は、極限の存在が同値。 -/
lemma hasLimit_iff_equivalenceCylinder_endpoints {K X : SSet.{u}} [Quasicategory X]
    (H : K ⊗ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceInterval ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceCylinderEndpoint K false ≫ H) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.equivalenceCylinderEndpoint K true ≫ H) :=
  (hasLimit_iff_restrict_of_precompositionEquivalence H _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPrecompositionEquivalence_equivalenceCylinderEndpoint K false)).symm.trans
      (hasLimit_iff_restrict_of_precompositionEquivalence H _
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isPrecompositionEquivalence_equivalenceCylinderEndpoint K true))
/-- 同型な実図式は、任意 quasicategory 標的で極限の存在が同値。 -/
@[kerodon 02K2]
lemma hasLimit_iff_of_functorIso {K X : SSet.{u}} [Quasicategory X] {p q : K ⟶ X}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso p q) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit p ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasLimit q := by
  obtain ⟨H, h₀, h₁⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.exists_equivalenceCylinder_extension_of_functorIso e
  have h := hasLimit_iff_equivalenceCylinder_endpoints H
  rw [h₀, h₁] at h
  exact h
end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
