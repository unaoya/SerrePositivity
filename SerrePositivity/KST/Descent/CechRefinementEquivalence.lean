module

public import SerrePositivity.KST.Descent.CechRefinementHomotopy

/-!
# 相互細分による Čech 比較のホモトピー逆

## 概要
同じ基底上で相互に持ち上げを持つ二つの射の Čech 比較は、両側のホモトピー逆を持つ。

## 方針
Čech 比較の恒等射・合成の保存と、平行な細分比較のホモトピーを組み合わせる。

## 規約
持ち上げの両合成が恒等射であることは要求しない。Tot による降下は別工程。

## 使われ方
論文 補題 3.2 の τ 位相の層論を Čech 計算で置換する細分の幾何入力。
-/

@[expose] public section

universe u v w t

open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.KST.Descent

variable {C : Type u} [Category.{v} C] [HasFiniteLimits C]

/-- 概要：恒等持ち上げの Čech 比較は恒等写像（論文 補題 3.2）。
方針：Arrow の恒等射と Čech nerve 関手の恒等射保存を使う。
規約：指定比較そのものの等式。
使われ方：相互細分の両側のホモトピー逆。 -/
theorem refinementCechMap_id {X Y : C} (f : X ⟶ Y) :
    refinementCechMap f f (𝟙 X) (Category.id_comp f) = 𝟙 (Arrow.mk f).cechNerve := by
  exact (SimplicialObject.cechNerve (C := C)).map_id (Arrow.mk f)

/-- 概要：細分の合成の Čech 比較は指定比較の合成（論文 補題 3.2）。
方針：Arrow の射の合成を両端で検査し、Čech 関手の合成保存を使う。
規約：同じ基底の上の三つの射を扱う。
使われ方：相互細分の合成を平行比較のホモトピーへ戻す。 -/
theorem refinementCechMap_comp {X W V Y : C} (f : X ⟶ Y) (g : W ⟶ Y) (h : V ⟶ Y)
    (a : X ⟶ W) (b : W ⟶ V) (ha : a ≫ g = f) (hb : b ≫ h = g) :
    refinementCechMap f g a ha ≫ refinementCechMap g h b hb =
      refinementCechMap f h (a ≫ b)
        ((Category.assoc _ _ _).trans ((congrArg (a ≫ ·) hb).trans ha)) := by
  let α : Arrow.mk f ⟶ Arrow.mk g :=
    Arrow.homMk a (𝟙 Y) (ha.trans (Category.comp_id f).symm)
  let β : Arrow.mk g ⟶ Arrow.mk h :=
    Arrow.homMk b (𝟙 Y) (hb.trans (Category.comp_id g).symm)
  have eqArrow : α ≫ β = (Arrow.homMk (a ≫ b) (𝟙 Y) : Arrow.mk f ⟶ Arrow.mk h) := by
    apply Arrow.hom_ext
    · rfl
    · exact Category.comp_id _
  exact ((SimplicialObject.cechNerve (C := C)).map_comp α β).symm.trans
    (congrArg (fun k ↦ Arrow.mapCechNerve k) eqArrow)

variable {X W Y : C} (f : X ⟶ Y) (g : W ⟶ Y)
  (a : X ⟶ W) (b : W ⟶ X) (ha : a ≫ g = f) (hb : b ≫ f = g)

/-- 概要：相互細分の比較の第一の合成は恒等写像にホモトピック（論文 補題 3.2）。
方針：合成持ち上げと恒等持ち上げの間の実際の Čech ホモトピーを使う。
規約：a ≫ b が恒等射であることを仮定しない。
使われ方：細分比較のホモトピー逆の一方。 -/
noncomputable def refinementCechHomotopyLeftInverse :
    SimplicialObject.Homotopy
      (refinementCechMap f g a ha ≫ refinementCechMap g f b hb)
      (𝟙 (Arrow.mk f).cechNerve) := by
  let hc := (Category.assoc a b f).trans ((congrArg (a ≫ ·) hb).trans ha)
  let H := refinementCechHomotopy f f (a ≫ b) (𝟙 X) hc (Category.id_comp f)
  exact Eq.mp
    (congrArg₂ (fun u v ↦ SimplicialObject.Homotopy u v)
      (refinementCechMap_comp f g f a b ha hb).symm (refinementCechMap_id f)) H

/-- 概要：相互細分の比較の第二の合成は恒等写像にホモトピック（論文 補題 3.2）。
方針：二つの射の役割を交換し、同じ実際のホモトピーを適用する。
規約：b ≫ a が恒等射であることを仮定しない。
使われ方：細分比較のホモトピー逆の他方。 -/
noncomputable def refinementCechHomotopyRightInverse :
    SimplicialObject.Homotopy
      (refinementCechMap g f b hb ≫ refinementCechMap f g a ha)
      (𝟙 (Arrow.mk g).cechNerve) :=
  refinementCechHomotopyLeftInverse g f b a hb ha

/-- 概要：元の前層の像でも相互細分の比較は第一のホモトピー逆を持つ（論文 補題 3.2）。
方針：実際のホモトピーを前層の反対圏への関手で写す。
規約：値域の Tot のホモトピー不変性はここでは仮定しない。
使われ方：実際の Tot に接続する細分比較の入力。 -/
noncomputable def refinementCechImageHomotopyLeftInverse
    {V : Type w} [Category.{t} V] (F : Cᵒᵖ ⥤ V) :
    SimplicialObject.Homotopy
      (((SimplicialObject.whiskering C Vᵒᵖ).obj F.rightOp).map
        (refinementCechMap f g a ha ≫ refinementCechMap g f b hb))
      (((SimplicialObject.whiskering C Vᵒᵖ).obj F.rightOp).map (𝟙 (Arrow.mk f).cechNerve)) :=
  (refinementCechHomotopyLeftInverse f g a b ha hb).whiskerRight F.rightOp

/-- 概要：元の前層の像でも相互細分の比較は第二のホモトピー逆を持つ（論文 補題 3.2）。
方針：二つの射を交換して、前層で写した第一のホモトピー逆を使う。
規約：元の同じ前層を使う。
使われ方：Tot のホモトピー不変性に供給する両側の分裂データ。 -/
noncomputable def refinementCechImageHomotopyRightInverse
    {V : Type w} [Category.{t} V] (F : Cᵒᵖ ⥤ V) :
    SimplicialObject.Homotopy
      (((SimplicialObject.whiskering C Vᵒᵖ).obj F.rightOp).map
        (refinementCechMap g f b hb ≫ refinementCechMap f g a ha))
      (((SimplicialObject.whiskering C Vᵒᵖ).obj F.rightOp).map (𝟙 (Arrow.mk g).cechNerve)) :=
  refinementCechImageHomotopyLeftInverse g f b a hb ha F

end SerrePositivity.KST.Descent
