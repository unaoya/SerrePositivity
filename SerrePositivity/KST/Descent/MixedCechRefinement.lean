module

public import SerrePositivity.KST.Descent.MixedCechNaturality

/-!
# 細分射による混合 Čech の各行の実際の分裂

## 概要
一方の被覆が他方を細分するとき、細分した被覆の Čech 各段上で元の被覆の底変換は分裂する。

## 方針
零番目の射影と細分射を合成し、実際の引き戻しへの切断と extra degeneracy を作る。

## 規約
各行の切断の外側の単体射に関する自然性は主張しない。Tot の細分降下は別工程。

## 使われ方
論文 補題 3.2・3.3 の細分補題を τ 位相の層論から混合 Čech と Fubini へ置換する入力。
-/

@[expose] public section

universe u v w t

open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.KST.Descent

variable {C : Type u} [Category.{v} C] [HasFiniteLimits C]
  {X W Y : C} (f : X ⟶ Y) (g : W ⟶ Y) (a : X ⟶ W) (ha : a ≫ g = f)

/-- 概要：細分した被覆の Čech 各段から元の被覆への持ち上げ（補題 3.2）。
方針：零番目の射影と細分射を合成する。
規約：各行で選ぶ持ち上げであり、外側の全単体射への自然性は要求しない。
使われ方：元の被覆の底変換の切断。 -/
noncomputable def mixedCechRefinementLift (n : SimplexCategoryᵒᵖ) :
    (Arrow.mk f).cechNerve.obj n ⟶ W :=
  WidePullback.π (fun _ : Fin (n.unop.len + 1) ↦ f) 0 ≫ a

include ha in
/-- 概要：細分射からの各段の持ち上げは指定増強と可換（補題 3.2）。
方針：細分射の可換式と Čech の射影の構造射公式を合成する。
規約：元の基底への射の等式。
使われ方：実際の引き戻しへ切断を持ち上げる。 -/
theorem mixedCechRefinementLift_comm (n : SimplexCategoryᵒᵖ) :
    mixedCechRefinementLift f a n ≫ g = (Arrow.mk f).augmentedCechNerve.hom.app n :=
  (Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) ha).trans (WidePullback.π_arrow _ _))

/-- 概要：細分した被覆の各 Čech 段上で元の被覆の底変換は実際に分裂（補題 3.2）。
方針：持ち上げと恒等射から引き戻しへの切断を作る。
規約：有限性・平坦性・全射性はこの分裂の構成に不要。
使われ方：混合二重 Čech の片方向の各行の分裂降下。 -/
noncomputable def mixedCechRefinementStageSplitEpi (n : SimplexCategoryᵒᵖ) :
    SplitEpi ((mixedCechBaseChange g f).obj n).hom :=
  baseChangeSplitEpi g ((Arrow.mk f).augmentedCechNerve.hom.app n)
    (mixedCechRefinementLift f a n) (mixedCechRefinementLift_comm f g a ha n)

/-- 概要：細分射が与える混合二重 Čech の各行の extra degeneracy（補題 3.2）。
方針：実際の切断を増強 Čech nerve の標準構成へ入れる。
規約：全ての面射・退化射の分裂恒等式を保持する。
使われ方：実際の Tot の分裂降下へ供給するデータ。 -/
noncomputable def mixedCechRefinementStageExtraDegeneracy (n : SimplexCategoryᵒᵖ) :
    SimplicialObject.Augmented.ExtraDegeneracy ((mixedAugmentedCech g f).obj n) :=
  Arrow.AugmentedCechNerve.extraDegeneracy _ (mixedCechRefinementStageSplitEpi f g a ha n)

variable {V : Type w} [Category.{t} V]

/-- 概要：元の同じ前層による混合二重 Čech の像（補題 3.2）。
方針：反対圏への共変関手として前層を全二重図式に適用する。
規約：各次数の群だけを取り出さず、増強と全単体射を保つ。
使われ方：細分の二方向の実際の余単体図式。 -/
noncomputable def mixedCechImage (F : Cᵒᵖ ⥤ V) :
    SimplexCategoryᵒᵖ ⥤ SimplicialObject.Augmented Vᵒᵖ :=
  mixedAugmentedCech f g ⋙ (SimplicialObject.Augmented.whiskering C Vᵒᵖ).obj F.rightOp

/-- 概要：同じ前層の像の各行にも細分射からの実際の extra degeneracy がある（補題 3.2）。
方針：分裂恒等式を前層の関手性で移す。
規約：値域の Tot は構成しない。
使われ方：細分降下の Fubini に渡す片方向の各行の分裂。 -/
noncomputable def mixedCechRefinementImageExtraDegeneracy (F : Cᵒᵖ ⥤ V)
    (n : SimplexCategoryᵒᵖ) :
    SimplicialObject.Augmented.ExtraDegeneracy ((mixedCechImage g f F).obj n) :=
  (mixedCechRefinementStageExtraDegeneracy f g a ha n).map F.rightOp

/-- 概要：前層の像の各行の増強と切断は厳密な片側逆（補題 3.2）。
方針：extra degeneracy の分裂恒等式を使う。
規約：反対圏での記述なので元の余単体対象では合成順が逆。
使われ方：分裂降下の指定比較。 -/
theorem mixedCechRefinementImage_section_comp (F : Cᵒᵖ ⥤ V) (n : SimplexCategoryᵒᵖ) :
    (mixedCechRefinementImageExtraDegeneracy f g a ha F n).section_ ≫
      ((mixedCechImage g f F).obj n).hom = 𝟙 _ :=
  (mixedCechRefinementImageExtraDegeneracy f g a ha F n).section_comp_hom

/-- 概要：前層の像の各行の反対側の合成も収縮ホモトピーを持つ（補題 3.2）。
方針：実際の extra degeneracy から単体ホモトピーを得る。
規約：各次数の群の片側逆だけに弱めない。Tot のホモトピー不変性は別に必要。
使われ方：細分補題の各行の分裂降下。 -/
noncomputable def mixedCechRefinementImage_contractingHomotopy
    (F : Cᵒᵖ ⥤ V) (n : SimplexCategoryᵒᵖ) :
    SimplicialObject.Homotopy
      (((mixedCechImage g f F).obj n).hom ≫
        (mixedCechRefinementImageExtraDegeneracy f g a ha F n).section_)
      (𝟙 ((mixedCechImage g f F).obj n).left) :=
  (mixedCechRefinementImageExtraDegeneracy f g a ha F n).homotopy

end SerrePositivity.KST.Descent
