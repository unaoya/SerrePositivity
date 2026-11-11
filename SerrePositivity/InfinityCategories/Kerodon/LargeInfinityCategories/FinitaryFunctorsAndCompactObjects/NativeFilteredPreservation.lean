module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.KappaColimits
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.EquivalencePath
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.SquareFunctorTransport

/-!
概要：元の宇宙 u+1 の関手について、宇宙 u の κ-filtered 余極限の保存性を定める。
方針：F2 の κ-filtered 性と元の native 余錐の像をそのまま使う。
規約：Compact の保存性と異なり、始域と標的をさらに u+2 へ持ち上げない。
使われ方：Fun^κ(Indκ(C),D) と元の Yoneda による実際の制限写像。

対応節は Kerodon 9.2（Tag 0639）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects

/-- 宇宙 u+1 の元の関手が、宇宙 u の κ-filtered な指定 native 余極限を保存すること。 -/
def PreservesSmallKappaFilteredColimits (κ : Cardinal.{u}) {X Y : SSet.{u + 1}}
    (F : X ⟶ Y) : Prop :=
  ∀ (I : SSet.{u}) [Quasicategory I] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ I]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ X) (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D),
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c → _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone F c)

/-- 元の標的が同じ小さい κ-filtered 余極限を持つこと。 -/
def HasSmallKappaFilteredColimits (κ : Cardinal.{u}) (Y : SSet.{u + 1}) : Prop :=
  ∀ (I : SSet.{u}) [Quasicategory I] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ I]
    (D : (SSet.uliftFunctor.{u + 1, u}).obj I ⟶ Y), _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit D

/-- 全関手同型で移しても、指定 native 余錐に対する保存性は変わらない。 -/
lemma PreservesSmallKappaFilteredColimits.of_functorIso {κ : Cardinal.{u}}
    {X Y : SSet.{u + 1}} [Quasicategory Y] {F G : X ⟶ Y}
    (h : PreservesSmallKappaFilteredColimits κ F) (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso F G) :
    PreservesSmallKappaFilteredColimits κ G := by
  intro I hI hκ D c hc
  exact (h I D c hc).of_functorIso (e.precomp c.val)

/-- 構成済みの Indκ は同じ宇宙 u の小さい κ-filtered 余極限を持つ。 -/
lemma ind_hasSmallKappaFilteredColimits (κ : Cardinal.{u}) (C : SSet.{u}) [Quasicategory C] :
    HasSmallKappaFilteredColimits κ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C) := by
  intro I hI hκ D
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.ind_hasColimit κ D

/-- 元の前層への同じ全部分包含は、元の κ-filtered 余極限余錐を保存する。 -/
lemma indInclusion_preservesSmallKappaFilteredColimits (κ : Cardinal.{u})
    (C : SSet.{u}) [Quasicategory C] :
    PreservesSmallKappaFilteredColimits κ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indInclusionPresheaf κ C) := by
  intro I hI hκ D c hc
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.ind_inclusion_isColimit κ D c hc

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects
