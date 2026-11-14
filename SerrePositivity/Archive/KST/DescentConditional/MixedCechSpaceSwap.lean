module

public import SerrePositivity.Archive.KST.DescentConditional.MixedCechSpaces

/-!
# 混合 Čech の実際の空間図式の軸交換

## 概要
元の前層で混合 Čech の幾何的な軸交換を反変に写し、指定増強を保持する空間図式の同型にする。

## 方針
既存の幾何的な全図式の自然同型と両側の行の自然性を用い、合成の反変順序を明示する。

## 規約
二つの被覆自体も交換する。同型の存在だけでなく元の基底からの指定増強を保持する。

## 使われ方
論文 補題 3.2・3.3 の二方向の混合 Čech による細分降下。τ 位相の層論を Čech 計算で置換する。
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Prod

namespace SerrePositivity.KST.Descent

variable {C : Type u} [Category.{v} C] [HasFiniteLimits C]
  (F : Cᵒᵖ ⥤ SSet.{0}) {X W Y : C} (f : X ⟶ Y) (g : W ⟶ Y)

/-- 概要：混合 Čech の二つの軸を交換する実際の前層像の自然同型（補題 3.2・3.3）。
方針：幾何の交換同型の逆を反変に写し、行の自然性で合成の順序を比較する。
規約：元の同じ前層を全ての射で使う。使われ方：指定増強を保つ軸交換同型。 -/
def mixedCechSpaceSwapDiagramIso :
    (DoubleAugmentedCechDiagram.flatten SimplexCategory SimplexCategory
      (mixedDoubleCechSpace F f g)).right ≅
    CategoryTheory.Prod.swap _ _ ⋙
      (DoubleAugmentedCechDiagram.flatten SimplexCategory SimplexCategory
        (mixedDoubleCechSpace F g f)).right :=
  NatIso.ofComponents
    (fun nm ↦ F.mapIso (mixedCechSwapIso f g (op nm.1) (op nm.2)).symm.op)
    (fun {nm nm'} α ↦ by
      have hf := ((mixedAugmentedCech f g).map α.1.op).left.naturality α.2.op
      have hg := ((mixedAugmentedCech g f).map α.2.op).left.naturality α.1.op
      have hs := (mixedCechSwapNatIso f g).inv.naturality (α.1.op ×ₘ α.2.op)
      have hw :
          (mixedCechSwapIso f g (op nm'.1) (op nm'.2)).inv ≫
            (mixedCechInnerMap f g (op nm'.1) α.2.op ≫
              mixedCechOuterMap f g α.1.op (op nm.2)) =
          (mixedCechInnerMap g f (op nm'.2) α.1.op ≫
            mixedCechOuterMap g f α.2.op (op nm.1)) ≫
              (mixedCechSwapIso f g (op nm.1) (op nm.2)).inv :=
        (congrArg ((mixedCechSwapIso f g (op nm'.1) (op nm'.2)).inv ≫ ·) hf).trans
          (hs.symm.trans
            (congrArg (· ≫ (mixedCechSwapIso f g (op nm.1) (op nm.2)).inv) hg.symm))
      change
        (F.map (mixedCechOuterMap f g α.1.op (op nm.2)).op ≫
          F.map (mixedCechInnerMap f g (op nm'.1) α.2.op).op) ≫
            F.map (mixedCechSwapIso f g (op nm'.1) (op nm'.2)).inv.op =
        F.map (mixedCechSwapIso f g (op nm.1) (op nm.2)).inv.op ≫
          (F.map (mixedCechOuterMap g f α.2.op (op nm.1)).op ≫
            F.map (mixedCechInnerMap g f (op nm'.2) α.1.op).op)
      simp only [← F.map_comp, ← op_comp]
      exact congrArg F.map (congrArg Quiver.Hom.op hw))

/-- 概要：混合 Čech の軸交換は元の基底からの指定増強も保持（補題 3.2・3.3）。
方針：二つの増強の合成を前層で写し、交換同型の指定射影公式と Cartesian 可換式を使う。
規約：増強元は元の基底の値の恒等同型。使われ方：両方向の実降下の比較。 -/
def mixedCechSpaceSwapIso :
    DoubleAugmentedCechDiagram.flatten SimplexCategory SimplexCategory
        (mixedDoubleCechSpace F f g) ≅
      (CechReindex.augmentedRestriction (CategoryTheory.Prod.swap _ _)).obj
        (DoubleAugmentedCechDiagram.flatten SimplexCategory SimplexCategory
          (mixedDoubleCechSpace F g f)) :=
  Comma.isoMk (Iso.refl _) (mixedCechSpaceSwapDiagramIso F f g) (by
    apply NatTrans.ext
    funext nm
    have hp : (mixedCechSwapIso f g (op nm.1) (op nm.2)).inv ≫
        mixedCechSecond f g (op nm.1) (op nm.2) =
      mixedCechFirst g f (op nm.2) (op nm.1) :=
      (mixedCechSwapIso f g (op nm.1) (op nm.2)).inv_comp_eq.mpr
        (mixedCechSwapIso_second f g (op nm.1) (op nm.2)).symm
    have hw : (mixedCechSwapIso f g (op nm.1) (op nm.2)).inv ≫
        (mixedCechSecond f g (op nm.1) (op nm.2) ≫
          (Arrow.mk g).augmentedCechNerve.hom.app (op nm.1)) =
      mixedCechSecond g f (op nm.2) (op nm.1) ≫
        (Arrow.mk f).augmentedCechNerve.hom.app (op nm.2) :=
      (Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ (Arrow.mk g).augmentedCechNerve.hom.app (op nm.1)) hp).trans
          (mixedCech_isPullback g f (op nm.2) (op nm.1)).w)
    change 𝟙 _ ≫ (𝟙 _ ≫ ((𝟙 _ ≫ F.map
        ((Arrow.mk f).augmentedCechNerve.hom.app (op nm.2)).op) ≫
      (𝟙 _ ≫ F.map (mixedCechSecond g f (op nm.2) (op nm.1)).op))) =
      (𝟙 _ ≫ ((𝟙 _ ≫ F.map ((Arrow.mk g).augmentedCechNerve.hom.app (op nm.1)).op) ≫
        (𝟙 _ ≫ F.map (mixedCechSecond f g (op nm.1) (op nm.2)).op))) ≫
          F.map (mixedCechSwapIso f g (op nm.1) (op nm.2)).inv.op
    simp only [Category.id_comp]
    exact (F.map_comp
      ((Arrow.mk f).augmentedCechNerve.hom.app (op nm.2)).op
      (mixedCechSecond g f (op nm.2) (op nm.1)).op).symm.trans
      ((congrArg F.map (congrArg Quiver.Hom.op hw.symm)).trans
        ((F.map_comp
          (mixedCechSecond f g (op nm.1) (op nm.2) ≫
            (Arrow.mk g).augmentedCechNerve.hom.app (op nm.1)).op
          (mixedCechSwapIso f g (op nm.1) (op nm.2)).inv.op).trans
          (congrArg (· ≫ F.map (mixedCechSwapIso f g (op nm.1) (op nm.2)).inv.op)
            (F.map_comp ((Arrow.mk g).augmentedCechNerve.hom.app (op nm.1)).op
              (mixedCechSecond f g (op nm.1) (op nm.2)).op)))))

end SerrePositivity.KST.Descent
