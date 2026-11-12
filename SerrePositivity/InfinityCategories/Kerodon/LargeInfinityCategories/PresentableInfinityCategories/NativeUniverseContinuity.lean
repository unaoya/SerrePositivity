module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AccessibleFunctor
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.F2CompactUniverseColimits
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.UniverseCoconePostcomposition

/-!
概要：元の関手の κ-filtered 保存を宇宙変更後の全関手の保存性へ送る。
方針：同じ指定全余錐の後合成と持ち上げの可換性を使う。
規約：添字の宇宙は元の u のまま保持する。
使われ方：accessible 関手と元の大きい共変 Hom の全自然な比較。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：元の κ-連続関手と大きい κ-連続関手の合成は元の小さい添字の余極限を保つ。
方針：元の指定余錐を順に写し、後合成と宇宙持ち上げを可換にする。
規約：始域を再び持ち上げても新しい大きい添字の保存性を主張しない。
使われ方：小さい空間値関手を大きい Hom 族と比較する。 -/
lemma IsKappaAccessibleFunctor.comp_universe {κ : Cardinal.{u}}
    {C D : SSet.{u + 1}} {Y : SSet.{u + 2}} {F : C ⟶ D}
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ F)
    {G : (SSet.uliftFunctor.{u + 2, u + 1}).obj D ⟶ Y}
    (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.PreservesKappaFilteredColimits.{u, u + 1} κ G) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.PreservesKappaFilteredColimits.{u, u + 1} κ
      ((SSet.uliftFunctor.{u + 2, u + 1}).map F ≫ G) := by
  intro I hI hκ a c hc
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.mapJoinCocone_universe_comp]
  exact hG I (a ≫ F) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone F c) (hF I a c hc)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor export _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsKappaAccessibleFunctor (comp_universe)


/-- 概要：元の小さい空間値 κ-accessible 関手の指定宇宙変更も元の余極限を保つ。
方針：小さい空間の同じ宇宙変更の保存性と合成する。
規約：元の全関手を変えず、値の宇宙だけを上げる。
使われ方：余表現可能性の全 Hom 比較を filtered 生成で延長する。 -/
lemma IsKappaAccessibleFunctor.spaceUniverse {κ : Cardinal.{u}}
    {C : SSet.{u + 1}} {F : C ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}}
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ F) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.PreservesKappaFilteredColimits.{u, u + 1} κ
      ((SSet.uliftFunctor.{u + 2, u + 1}).map F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.spaceUniverseDiagram) :=
  hF.comp_universe (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.spaceUniverseDiagram_preservesKappaFilteredColimits κ)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor export _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsKappaAccessibleFunctor (spaceUniverse)


end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
