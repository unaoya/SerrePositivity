module

public import SerrePositivity.InfinityCategories.F2.Presentable.AccessibleFunctor
public import SerrePositivity.InfinityCategories.F2.Compact.UniverseColimits
public import SerrePositivity.InfinityCategories.Core.Compact.UniverseCoconePostcomposition

/-!
概要：元の関手の κ-filtered 保存を宇宙変更後の全関手の保存性へ送る。
方針：同じ指定全余錐の後合成と持ち上げの可換性を使う。
規約：添字の宇宙は元の u のまま保持する。
使われ方：accessible 関手と元の大きい共変 Hom の全自然な比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：元の κ-連続関手と大きい κ-連続関手の合成は元の小さい添字の余極限を保つ。
方針：元の指定余錐を順に写し、後合成と宇宙持ち上げを可換にする。
規約：始域を再び持ち上げても新しい大きい添字の保存性を主張しない。
使われ方：小さい空間値関手を大きい Hom 族と比較する。 -/
lemma IsKappaAccessibleFunctor.comp_universe {κ : Cardinal.{u}}
    {C D : SSet.{u + 1}} {Y : SSet.{u + 2}} {F : C ⟶ D}
    (hF : IsKappaAccessibleFunctor κ F)
    {G : (SSet.uliftFunctor.{u + 2, u + 1}).obj D ⟶ Y}
    (hG : Compact.PreservesKappaFilteredColimits.{u, u + 1} κ G) :
    Compact.PreservesKappaFilteredColimits.{u, u + 1} κ
      ((SSet.uliftFunctor.{u + 2, u + 1}).map F ≫ G) := by
  intro I hI hκ a c hc
  rw [Compact.mapJoinCocone_universe_comp]
  exact hG I (a ≫ F) (mapJoinCocone F c) (hF I a c hc)

/-- 概要：元の小さい空間値 κ-accessible 関手の指定宇宙変更も元の余極限を保つ。
方針：小さい空間の同じ宇宙変更の保存性と合成する。
規約：元の全関手を変えず、値の宇宙だけを上げる。
使われ方：余表現可能性の全 Hom 比較を filtered 生成で延長する。 -/
lemma IsKappaAccessibleFunctor.spaceUniverse {κ : Cardinal.{u}}
    {C : SSet.{u + 1}} {F : C ⟶ SpaceInfinity.{u}}
    (hF : IsKappaAccessibleFunctor κ F) :
    Compact.PreservesKappaFilteredColimits.{u, u + 1} κ
      ((SSet.uliftFunctor.{u + 2, u + 1}).map F ≫ Compact.spaceUniverseDiagram) :=
  hF.comp_universe (Compact.spaceUniverseDiagram_preservesKappaFilteredColimits κ)

end SerrePositivity.InfinityCategories.F2.Presentable
