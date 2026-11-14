module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.FixedApexConeEdgeComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.ConeSectionsNativeComparison

/-!
概要：元の錐の全切断への全 Hom 作用は、指定された錐の辺の標準後合成と可換。
方針：元の native Hom 比較の辺の同型を、同じ全切断作用の比較で移す。
規約：全 Hom をパラメータにし、試験空間の点へ弱めない。
使われ方：G8 の切断錐から指定極限への接続。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories
open TheSliceAndJoinConstructions MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces

/-- 概要：元の全切断 Hom 作用は、同じ錐の辺の標準後合成と全族で可換。
方針：native な錐の Hom 比較の辺の同型と、元の全切断作用の比較を合成する。
規約：必要な同型を入力に足さない。使われ方：G8 の指定極限錐への比較。 -/
def coneSectionsHomAction_edgeIso {B : SSet.{u + 1}}
    {F : B ⟶ SpaceInfinity.{u}} {c d : JoinCone F}
    (e : (sliceOver F).Edge c d) (z : SpaceInfinity.{u} _⦋0⦌) :
    FunctorIso (coneSectionsHomAction c z)
      (postcompose z (SSet.Truncated.HomotopyCategory.homMk (e.map (sliceOverProjection F))) ≫
        coneSectionsHomAction d z) := by
  let v := postcompose z
    (SSet.Truncated.HomotopyCategory.homMk (e.map (sliceOverProjection F)))
  let Q := coneTransformationMap F z ≫ coherentConstantSourceMap F z
  have h₀ := (coneSectionsNativeComparisonIso c z).symm
  have h₁ := FunctorIso.postcomp (fixedApexConeHomComparison_edgeIso e z) Q
  have h₂ := FunctorIso.precomp (coneSectionsNativeComparisonIso d z) v
  simp only [Category.assoc] at h₀ h₁ h₂
  exact h₀ ≪≫ h₁ ≪≫ h₂

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
