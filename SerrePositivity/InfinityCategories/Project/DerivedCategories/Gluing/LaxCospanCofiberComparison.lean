module
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.LaxPullbackCospanMap
public import SerrePositivity.KST.LocalizingInvariants.CofiberFamilyExactComparison
public import SerrePositivity.KST.LocalizingInvariants.CofiberFamilyPrecomposition
/-!
概要：厳密 cospan 比較は、完全な基底関手の下で選択 cofiber 差と全関手同型で可換する。
方針：指定全矢印族の厳密な回収式に、cofiber の制限・完全自然性を合成する。
規約：頂点別比較ではなく全パラメータの関手同型。使われ方：元 corner cone の比較。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalClosed SSet
open _root_.SerrePositivity.KST.LocalizingInvariants
open scoped _root_.Simplicial
variable {A B C A' B' C' : SSet.{u}}
  [Quasicategory C] [Quasicategory C'] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C']
  (p : A ⟶ C) (q : B ⟶ C) (p' : A' ⟶ C') (q' : B' ⟶ C')
  (a : A ⟶ A') (b : B ⟶ B') (c : C ⟶ C') [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor c]
  (hp : p ≫ c = a ≫ p') (hq : q ≫ c = b ≫ q')

def laxCospanCofiberComparison : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullbackCospanMap p q p' q' a b c hp hq ≫
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberSquareFamily.cofiber C' (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackArrow p' q'))
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberSquareFamily.cofiber C (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackArrow p q) ≫ c) := by
  have h₁ := CofiberFamily.precompositionIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackArrow p' q')
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullbackCospanMap p q p' q' a b c hp hq)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.laxPullbackCospanMap_arrow] at h₁
  exact h₁.trans (CofiberFamily.familyExactComparison c (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackArrow p q)).symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
