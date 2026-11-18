module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.EquivalentConeRestriction
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.FunctorVertexConeReindex
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomEvaluationNaturality

/-!
概要：同値な添字による全錐族の制限で、極限性・図式・頂点を保つ。
方針：既存の錐の読み戻し公式と join の両端の自然性を使う。
使われ方：HTT 4.1.3.1、Kerodon §7.1（Tag 02K2）の全 Γ 比較。
規約：元の形状写像による同じ全族を制限する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Project.FilteredExchange
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 同じ全錐の読み戻しは同値な形状による制限で極限性を保つ。 -/
lemma isLimitCone_functorVertexCone_reindex_iff_of_equivalence {J K X : SSet.{u}}
    [Quasicategory J] [Quasicategory K] [Quasicategory X]
    (f : J ⟶ K) (hf : IsQCatEquivalence f)
    (v : ((ihom (join (Δ[0] : SSet.{u}) K)).obj X) _⦋0⦌) :
    IsLimitCone (functorVertexCone (((pre (joinMap (𝟙 (Δ[0] : SSet.{u})) f)).app X).app _ v)) ↔
      IsLimitCone (functorVertexCone v) := by
  let c := functorVertexCone v
  let d := functorVertexCone (((pre (joinMap (𝟙 (Δ[0] : SSet.{u})) f)).app X).app _ v)
  let a := restrictJoinCone c f
  have hv : d.val = a.val := functorVertexConeMap_precomp f v
  have hp := d.property.symm.trans
    ((congrArg (fun t ↦ joinInr (Δ[0] : SSet.{u}) J ≫ t) hv).trans a.property)
  exact (isLimitCone_iff_of_diagram_eq (c := d) (d := a) hp hv).trans
    (SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isLimitCone_iff_restrict_equivalentShape f hf c).symm

/-- 全錐族の再添字は元の図式の再添字と厳密に可換。 -/
lemma coneReindex_precomp_restriction {J K X : SSet.{u}} (f : J ⟶ K) :
    (pre (joinMap (𝟙 (Δ[0] : SSet.{u})) f)).app X ≫ coneRestriction J X =
      coneRestriction K X ≫ (pre f).app X := by
  change (pre (joinMap (𝟙 (Δ[0] : SSet.{u})) f)).app X ≫
    (pre (joinInr (Δ[0] : SSet.{u}) J)).app X =
    (pre (joinInr (Δ[0] : SSet.{u}) K)).app X ≫ (pre f).app X
  rw [← NatTrans.comp_app, ← pre_map, joinInr_joinMap,
    pre_map, NatTrans.comp_app]

/-- 全錐族の再添字は元の頂点関手を厳密に保つ。 -/
lemma coneReindex_precomp_apex {J K X : SSet.{u}} (f : J ⟶ K) :
    (pre (joinMap (𝟙 (Δ[0] : SSet.{u})) f)).app X ≫
      evaluateFunctorAt (Y := X) (SSet.yonedaEquiv (joinInl (Δ[0] : SSet.{u}) J)) =
      evaluateFunctorAt (Y := X) (SSet.yonedaEquiv (joinInl (Δ[0] : SSet.{u}) K)) := by
  rw [evaluateFunctorAt_precomp]
  congr 1

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
