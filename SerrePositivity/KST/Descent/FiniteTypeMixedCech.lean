module

public import SerrePositivity.KST.Descent.FiniteTypeBaseChangeComparison

/-!
# 指定された有限型の底変換による混合 Čech の自然比較

## 概要
実際の有限型スキームの指定底変換による混合 Čech と、圏の Čech 構成の混合図式を自然同型で結ぶ。

## 方針
全基底射に自然な Arrow の同型を Čech 図式に制限し、増強 Čech nerve 関手で写す。

## 規約
各段で pullback を別のものへ交換しない。元の前層を適用した後も同じ自然比較を使う。

## 使われ方
論文 補題 3.2・3.3 の実際の抽象 blowup 底変換と混合 Čech・Fubini の接続。
-/

@[expose] public section

universe u w t

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace SerrePositivity.KST.Descent

variable {S : Scheme.{u}} [IsNoetherian S] {X W Y : FiniteTypeSchemes S}
  (f : X ⟶ Y) (g : W ⟶ Y)

/-- 概要：指定された finiteTypePullback による混合底変換 Arrow 図式（補題 3.2）。
方針：元の Čech 図式に指定モデルの底変換関手を合成する。
規約：全ての単体射を保持。使われ方：実際の抽象 blowup と同じモデルの底変換。 -/
noncomputable def finiteTypeMixedCechBaseChange :
    SimplexCategoryᵒᵖ ⥤ Arrow (FiniteTypeSchemes S) :=
  cechOverDiagram g ⋙ finiteTypeOverBaseChangeArrow f

/-- 概要：指定モデルと圏の混合底変換 Arrow 図式の自然同型（補題 3.2）。
方針：全基底射に自然な比較を元の Čech 図式へ制限する。
規約：同じ二つの元の射を使用。使われ方：全単体射を保つ混合 Čech の比較。 -/
noncomputable def finiteTypeMixedCechBaseChangeIso :
    finiteTypeMixedCechBaseChange f g ≅ mixedCechBaseChange f g :=
  Functor.isoWhiskerLeft (cechOverDiagram g) (finiteTypeBaseChangeArrowNatIso f)

/-- 概要：実際の指定底変換を使った混合二重増強 Čech（補題 3.2）。
方針：元の Arrow 図式に増強 Čech nerve 関手を合成する。
規約：Čech の型クラスの選択を変更しない。使われ方：同じ幾何モデルに対する増強比較。 -/
noncomputable def finiteTypeMixedAugmentedCech :
    SimplexCategoryᵒᵖ ⥤ SimplicialObject.Augmented (FiniteTypeSchemes S) :=
  finiteTypeMixedCechBaseChange f g ⋙ SimplicialObject.augmentedCechNerve

/-- 概要：二つの混合増強 Čech 図式は全単体射を保つ自然同型（補題 3.2）。
方針：自然な Arrow の同型を増強 Čech nerve 関手で写す。
規約：増強先と指定射を保持する。使われ方：実際の底変換モデルを Fubini の図式へ移す。 -/
noncomputable def finiteTypeMixedAugmentedCechIso :
    finiteTypeMixedAugmentedCech f g ≅ mixedAugmentedCech f g :=
  Functor.isoWhiskerRight (finiteTypeMixedCechBaseChangeIso f g)
    SimplicialObject.augmentedCechNerve

/-- 概要：混合比較の各行は指定された増強を保つ（論文 補題 3.2）。
方針：増強 Čech の射の可換性と、同じ増強先の恒等射を使う。
規約：増強先を含めて比較する。使われ方：実際の Tot の降下比較の矢を保持する。 -/
theorem finiteTypeMixedAugmentedCechIso_augmentation (n : SimplexCategoryᵒᵖ) :
    ((finiteTypeMixedAugmentedCechIso f g).app n).hom.left ≫
        ((mixedAugmentedCech f g).obj n).hom =
      ((finiteTypeMixedAugmentedCech f g).obj n).hom := by
  have h := ((finiteTypeMixedAugmentedCechIso f g).app n).hom.w
  exact h.trans ((congrArg (_ ≫ ·) ((SimplicialObject.const (FiniteTypeSchemes S)).map_id _)).trans
    (Category.comp_id _))

/-- 概要：同じ前層の像でも指定モデルと混合 Čech の比較は図式全体の自然同型（補題 3.2）。
方針：構成した増強図式の自然同型を元の反変前層で写す。
規約：値域の Tot や π_* と極限の交換は使わない。
使われ方：有限平坦 transfer と実際の Fubini へ同じ係数つき図式を渡す。 -/
noncomputable def finiteTypeMixedCechImageIso {V : Type w} [Category.{t} V]
    (F : (FiniteTypeSchemes S)ᵒᵖ ⥤ V) :
    finiteTypeMixedAugmentedCech f g ⋙
        (SimplicialObject.Augmented.whiskering _ Vᵒᵖ).obj F.rightOp ≅
      mixedAugmentedCech f g ⋙
        (SimplicialObject.Augmented.whiskering _ Vᵒᵖ).obj F.rightOp :=
  Functor.isoWhiskerRight (finiteTypeMixedAugmentedCechIso f g)
    ((SimplicialObject.Augmented.whiskering _ Vᵒᵖ).obj F.rightOp)

end SerrePositivity.KST.Descent
