module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.IdentityComparisons.IdentityLaxArrowBase
public import SerrePositivity.KST.LocalizingInvariants.CofiberFamilyExactComparison
public import SerrePositivity.KST.LocalizingInvariants.CofiberFamilyPrecomposition
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.EquivalenceStability
/-!
概要：恒等 lax 圏の矢印による基底同値は、選択 cofiber 差を全関手同型で保つ。
方針：全矢印族の厳密回収に cofiber の制限と完全自然性を合成する。
規約：対角と同じ基底比較を使用。使われ方：恒等比較入力の cone 欄。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory MonoidalClosed SSet
open _root_.SerrePositivity.KST.LocalizingInvariants
open scoped _root_.Simplicial
variable {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable X] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable Y]

def identityLaxArrowBaseCofiberComparison (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence X Y) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.identityLaxArrowBaseEquivalence e).hom ≫
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberSquareFamily.cofiber Y (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackArrow (𝟙 Y) (𝟙 Y)))
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Exact.CofiberSquareFamily.cofiber X (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackArrow (𝟙 X) (𝟙 X)) ≫ e.hom) := by
  letI : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor e.hom := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence e.isQCatEquivalence
  have h := CofiberFamily.precompositionIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackArrow (𝟙 Y) (𝟙 Y))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.identityLaxArrowBaseEquivalence e).hom
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.identityLaxArrowBaseEquivalence_arrow] at h
  exact h.trans (CofiberFamily.familyExactComparison e.hom
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.laxPullbackArrow (𝟙 X) (𝟙 X))).symm

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
