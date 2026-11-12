module
public import SerrePositivity.KST.Fibration.VerdierNativeLongHomShift
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.OrderPostcomposition

/-!
概要：元の指定実合成端を、元の二つの core Kan 射の厳密合成へ照合する。
方針：既存の豊穣作用の通常の関手を読み、所有する座標回収式を使う。
規約：一般の K スペクトル関手を構成せず、元の core S• 作用の指定合成だけを比較する。
使われ方：K-6 c4 の長 Hom 入力の合成端を再構成仕様へ代入する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.SConstruction SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration

private theorem nativeComposite_coreMap_comp {A B C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}}
    (f : A ⟶ B) (g : B ⟶ C) :
    stableCoreSingleKanMap (f ≫ g) = stableCoreSingleKanMap f ≫ stableCoreSingleKanMap g := by
  let F := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor stableCoreSingleKanEnrichedFunctor
  have hm {X Y : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}} (a : X ⟶ Y) : F.map a = stableCoreSingleKanMap a := by
    apply (SimplicialCategory.homEquiv' _ _).injective
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor_vertex stableCoreSingleKanEnrichedFunctor a).trans
      (congrArg (SSet.unitHomEquiv _) (stableCoreSingleKan_hom a))
  exact (hm (f ≫ g)).symm.trans ((F.map_comp f g).trans
    (congrArg₂ (fun a b => a ≫ b) (hm f) (hm g)))

/-- 概要：元の下側合成端は実包含と実商の同じ core Kan 射の厳密合成。
方針：同じ回収完全射の合成等式を元の豊穣作用へ送る。
規約：元の実包含・実商を保持する。
使われ方：下側の長 Hom 全族の実合成端を再構成入力へ読む。 -/
theorem verdierNativeCompositePoint_lower (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    verdierNativeCompositePoint d 1 =
      ULift.up (SimplicialCategory.homEquiv' _ _
        (stableCoreSingleKanMap d.inclusion ≫ stableCoreSingleKanMap d.projection)) := by
  unfold verdierNativeCompositePoint
  rw [verdierNullCompositeOriginalMap_lower]
  exact congrArg (fun f => ULift.up (SimplicialCategory.homEquiv' _ _ f))
    (nativeComposite_coreMap_comp (show (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.left) ⟶
      (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.middle) from d.inclusion)
      (show (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.middle) ⟶ (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.right) from d.projection))

/-- 概要：元の上側合成端は指定左辺と指定上辺の同じ core Kan 射の厳密合成。
方針：元の上側完全射の回収と同じ豊穣作用の合成則を使う。
規約：指定四角形の左辺・上辺を別の射へ変更しない。
使われ方：上側再構成へ渡す指定合成端の実射との照合。 -/
theorem verdierNativeCompositePoint_upper (d : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.VerdierDiagram.{u}) :
    verdierNativeCompositePoint d 0 =
      ULift.up (SimplicialCategory.homEquiv' _ _
        (stableCoreSingleKanMap (verdierLeftExactMap d) ≫
          stableCoreSingleKanMap (verdierTopExactMap d))) := by
  unfold verdierNativeCompositePoint
  rw [verdierNullCompositeOriginalMap_upper]
  exact congrArg (fun f => ULift.up (SimplicialCategory.homEquiv' _ _ f))
    (nativeComposite_coreMap_comp (show (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.left) ⟶
      (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex d.square 0 1)) from verdierLeftExactMap d)
      (show (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex d.square 0 1)) ⟶
        (show _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat from d.right) from verdierTopExactMap d))

end SerrePositivity.KST.Fibration
