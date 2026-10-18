module

public import Mathlib.AlgebraicTopology.ExtraDegeneracy
public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits

/-!
# 補題 3.2 の分裂 Čech nerve

## 概要
任意の射を自身で底変換すると対角切断を持つ。
その実際の Čech nerve は extra degeneracy と収縮ホモトピーを持ち、任意の前層で保たれる。

## 方針
対角射を `SplitEpi` の切断として使い、Mathlib の Čech nerve の extra degeneracy を適用する。
反変前層は反対圏の共変関手として適用する。

## 規約
前層の像は反対圏の単体対象、すなわち元の値域の余単体図式として記述する。
この構成だけで Tot の実構成やホモトピー不変性を証明したとは主張しない。

## 使われ方
論文 補題 3.2 と定理 3.1 の section への還元。
原典の τ 位相による議論を分裂降下・Fubini・細分の Čech 計算に置き換えるための分裂データ。
-/

@[expose] public section

open CategoryTheory Limits

namespace SerrePositivity.KST.Descent

variable {C : Type*} [Category* C] [HasFiniteLimits C]

/-- 概要：被覆への持ち上げを持つ基底変更では、引き戻した射に切断がある（定理 3.1）。
方針：持ち上げと恒等射から引き戻しへの射を構成する。
規約：可換式は幾何学的な射の等式であり、点上の切断ではない。
使われ方：非増強 Čech 項の X 座標への射から、section を持つ被覆へ還元する。 -/
noncomputable def baseChangeSplitEpi {X Y Z : C} (f : X ⟶ Y) (g : Z ⟶ Y)
    (lift : Z ⟶ X) (comm : lift ≫ f = g) : SplitEpi (pullback.snd f g) where
  section_ := pullback.lift lift (𝟙 Z) (by simpa using comm)

/-- 概要：被覆への持ち上げがある基底変更の Čech nerve の extra degeneracy（定理 3.1）。
方針：持ち上げから得た切断を Mathlib の構成に入れる。
規約：有限全射の降下や主定理を仮定していない。
使われ方：各非増強 Čech 項上の section による軌道帰納の入力。 -/
noncomputable def baseChangeCechExtraDegeneracy {X Y Z : C} (f : X ⟶ Y) (g : Z ⟶ Y)
    (lift : Z ⟶ X) (comm : lift ≫ f = g) :
    SimplicialObject.Augmented.ExtraDegeneracy
      (Arrow.mk (pullback.snd f g)).augmentedCechNerve :=
  Arrow.AugmentedCechNerve.extraDegeneracy _ (baseChangeSplitEpi f g lift comm)

/-- 概要：自身による底変換の射は対角射を切断に持つ（論文 補題 3.2）。
方針：引き戻しの対角射と第一射影の合成を計算する。
規約：有限性・平坦性・全射性はこの分裂の構成には不要。
使われ方：有限忠実平坦射の底変換後の Čech nerve の分裂。 -/
noncomputable def selfPullbackSplitEpi {X Y : C} (f : X ⟶ Y) :
    SplitEpi (pullback.fst f f) where
  section_ := pullback.diagonal f
  id := pullback.diagonal_fst f

/-- 概要：自身で底変換した射の実際の Čech nerve の extra degeneracy（補題 3.2）。
方針：対角切断と Mathlib の Čech nerve の構成を使う。
規約：すべての Čech 次数と面射・退化射の整合条件を含む。
使われ方：任意の係数つき前層を適用する前の幾何学的な分裂データ。 -/
noncomputable def selfPullbackCechExtraDegeneracy {X Y : C} (f : X ⟶ Y) :
    SimplicialObject.Augmented.ExtraDegeneracy
      (Arrow.mk (pullback.fst f f)).augmentedCechNerve :=
  Arrow.AugmentedCechNerve.extraDegeneracy _ (selfPullbackSplitEpi f)

variable {V : Type*} [Category* V]

/-- 概要：前層を適用した底変換後の Čech 図式（論文 補題 3.2）。
方針：反変前層を反対圏への共変関手として適用する。
規約：V の Tot や V の通常の極限を定義しているのではない。
使われ方：分裂余単体図式を余分な次数切り捨てなしで保持する。 -/
noncomputable def selfPullbackCechImage (F : Cᵒᵖ ⥤ V) {X Y : C} (f : X ⟶ Y) :
    SimplicialObject.Augmented Vᵒᵖ :=
  ((SimplicialObject.Augmented.whiskering C Vᵒᵖ).obj F.rightOp).obj
    (Arrow.mk (pullback.fst f f)).augmentedCechNerve

/-- 概要：任意の前層を適用した後の Čech 図式にも extra degeneracy がある（補題 3.2）。
方針：extra degeneracy の全恒等式を前層の関手性で写す。
規約：反対圏における単体対象として余単体図式の分裂を表す。
使われ方：分裂降下を Tot のホモトピー不変性へ接続する入力。 -/
noncomputable def selfPullbackCechImageExtraDegeneracy (F : Cᵒᵖ ⥤ V)
    {X Y : C} (f : X ⟶ Y) :
    SimplicialObject.Augmented.ExtraDegeneracy (selfPullbackCechImage F f) :=
  (selfPullbackCechExtraDegeneracy f).map F.rightOp

/-- 概要：前層の Čech 図式の augmentation と切断は厳密な片側逆（論文 補題 3.2）。
方針：extra degeneracy の面射の恒等式を全次数で適用する。
規約：反対圏で記述しており、元の余単体図式では合成の向きが逆になる。
使われ方：Tot による降下比較の分裂恒等式。 -/
theorem selfPullbackCechImage_section_comp (F : Cᵒᵖ ⥤ V) {X Y : C} (f : X ⟶ Y) :
    (selfPullbackCechImageExtraDegeneracy F f).section_ ≫
      (selfPullbackCechImage F f).hom = 𝟙 _ :=
  (selfPullbackCechImageExtraDegeneracy F f).section_comp_hom

/-- 概要：反対側の合成にも収縮ホモトピーがある（論文 補題 3.2 の分裂降下）。
方針：Čech の extra degeneracy から Mathlib の単体ホモトピーを構成する。
規約：これは実際の図式のホモトピー。各次数の群の同型だけを仮定しない。
使われ方：実際の Tot のホモトピー不変性と組み合わせ、分裂降下を得る。 -/
noncomputable def selfPullbackCechImage_contractingHomotopy (F : Cᵒᵖ ⥤ V)
    {X Y : C} (f : X ⟶ Y) :
    SimplicialObject.Homotopy
      ((selfPullbackCechImage F f).hom ≫
        (selfPullbackCechImageExtraDegeneracy F f).section_)
      (𝟙 (selfPullbackCechImage F f).left) :=
  (selfPullbackCechImageExtraDegeneracy F f).homotopy

end SerrePositivity.KST.Descent
