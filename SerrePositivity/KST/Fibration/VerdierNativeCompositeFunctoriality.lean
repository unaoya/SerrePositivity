module
public import SerrePositivity.KST.Fibration.VerdierNativeLongHomShift
public import SerrePositivity.InfinityCategories.F1.Coherent.OrderPostcomposition

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

private theorem nativeComposite_coreMap_comp {A B C : StableQCat.{u}}
    (f : A ⟶ B) (g : B ⟶ C) :
    stableCoreSingleKanMap (f ≫ g) = stableCoreSingleKanMap f ≫ stableCoreSingleKanMap g := by
  let F := coherentEnrichedUnderlyingFunctor stableCoreSingleKanEnrichedFunctor
  have hm {X Y : StableQCat.{u}} (a : X ⟶ Y) : F.map a = stableCoreSingleKanMap a := by
    apply (SimplicialCategory.homEquiv' _ _).injective
    exact (coherentEnrichedUnderlyingFunctor_vertex stableCoreSingleKanEnrichedFunctor a).trans
      (congrArg (SSet.unitHomEquiv _) (stableCoreSingleKan_hom a))
  exact (hm (f ≫ g)).symm.trans ((F.map_comp f g).trans
    (congrArg₂ (fun a b => a ≫ b) (hm f) (hm g)))

/-- 概要：元の下側合成端は実包含と実商の同じ core Kan 射の厳密合成。
方針：同じ回収完全射の合成等式を元の豊穣作用へ送る。
規約：元の実包含・実商を保持する。
使われ方：下側の長 Hom 全族の実合成端を再構成入力へ読む。 -/
theorem verdierNativeCompositePoint_lower (d : VerdierDiagram.{u}) :
    verdierNativeCompositePoint d 1 =
      ULift.up (SimplicialCategory.homEquiv' _ _
        (stableCoreSingleKanMap d.inclusion ≫ stableCoreSingleKanMap d.projection)) := by
  unfold verdierNativeCompositePoint
  rw [verdierNullCompositeOriginalMap_lower]
  exact congrArg (fun f => ULift.up (SimplicialCategory.homEquiv' _ _ f))
    (nativeComposite_coreMap_comp (show (show StableQCat from d.left) ⟶
      (show StableQCat from d.middle) from d.inclusion)
      (show (show StableQCat from d.middle) ⟶ (show StableQCat from d.right) from d.projection))

/-- 概要：元の上側合成端は指定左辺と指定上辺の同じ core Kan 射の厳密合成。
方針：元の上側完全射の回収と同じ豊穣作用の合成則を使う。
規約：指定四角形の左辺・上辺を別の射へ変更しない。
使われ方：上側再構成へ渡す指定合成端の実射との照合。 -/
theorem verdierNativeCompositePoint_upper (d : VerdierDiagram.{u}) :
    verdierNativeCompositePoint d 0 =
      ULift.up (SimplicialCategory.homEquiv' _ _
        (stableCoreSingleKanMap (verdierLeftExactMap d) ≫
          stableCoreSingleKanMap (verdierTopExactMap d))) := by
  unfold verdierNativeCompositePoint
  rw [verdierNullCompositeOriginalMap_upper]
  exact congrArg (fun f => ULift.up (SimplicialCategory.homEquiv' _ _ f))
    (nativeComposite_coreMap_comp (show (show StableQCat from d.left) ⟶
      (show StableQCat from stableObject (squareVertex d.square 0 1)) from verdierLeftExactMap d)
      (show (show StableQCat from stableObject (squareVertex d.square 0 1)) ⟶
        (show StableQCat from d.right) from verdierTopExactMap d))

end SerrePositivity.KST.Fibration
