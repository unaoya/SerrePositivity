module

public import SerrePositivity.HomotopicalAlgebra.Diagram.WeightedCones
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Functor.Currying

/-!
# 二重 Čech の重みつき錐空間の Fubini

## 概要
二つの重みの外テンソル積に対する実際の単体的錐空間を、反復した錐空間と自然同定する。

## 方針
重みとのテンソル関手の結合子を左随伴の自然同型にし、右随伴の一意性を使う。

## 規約
ここでは任意の重みの実際の右随伴を比較する。
cofibrant な重み・fibrant な図式との接続を経る前に Tot の Fubini とは呼ばない。

## 使われ方
論文 補題 3.2・3.3 の τ 位相の層論を二重 Čech の導来 Fubini へ置換する機構。
-/

@[expose] public section

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open SerrePositivity.DiagramModel

namespace SerrePositivity.KST.Descent

variable (K J : Type u) [SmallCategory K] [SmallCategory J]
  (W : K ⥤ SSet.{u}) (V : J ⥤ SSet.{u})

/-- 概要：二つの単体的重みの外テンソル積（論文 補題 3.2）。
方針：積添字の二成分にそれぞれ重みを適用する。
規約：元の重みの全ての射を保持する。使われ方：二重錐と反復錐の比較。 -/
def externalCechWeight : K × J ⥤ SSet.{u} where
  obj k := W.obj k.1 ⊗ V.obj k.2
  map f := W.map f.1 ⊗ₘ V.map f.2
  map_id k := by simp
  map_comp f g := by simp

/-- 概要：外重みは内側のテンソル関手を各外側の重みに適用した図式と同型（補題 3.2）。
方針：各対象では恒等同型、各射では tensorHom の二つの whiskering への分解を使う。
規約：元の指定重みを保持する。使われ方：反復した射影的模型からの cofibrancy の移送。 -/
def externalCechWeightIso : externalCechWeight K J W V ≅
    Functor.uncurry.obj (W ⋙ WeightedCones.tensorDiagram J V) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro k l f
    change (W.map f.1 ⊗ₘ V.map f.2) ≫ 𝟙 _ =
      𝟙 _ ≫ ((W.map f.1 ▷ V.obj k.2) ≫ (W.obj l.1 ◁ V.map f.2))
    simp [tensorHom_def])

/-- 概要：二段の重みとのテンソルを積添字へ戻す関手（論文 補題 3.2）。
方針：外側の重み、内側の重み、uncurry の順に合成する。
規約：元の実際の WeightedCones の左随伴を使う。使われ方：反復錐空間の左随伴。 -/
abbrev iteratedCechTensor : SSet.{u} ⥤ (K × J ⥤ SSet.{u}) :=
  WeightedCones.tensorDiagram K W ⋙
    (Functor.whiskeringRight K SSet.{u} (J ⥤ SSet.{u})).obj
      (WeightedCones.tensorDiagram J V) ⋙ Functor.uncurry

/-- 概要：二段の実際の重みつき錐空間（論文 補題 3.2）。
方針：積添字を curry し、内側・外側の右随伴を順に適用する。
規約：通常の極限による代用ではない。使われ方：導来 Fubini の反復側の模型。 -/
abbrev iteratedCechConeSpace : (K × J ⥤ SSet.{u}) ⥤ SSet.{u} :=
  Functor.curry ⋙
    (Functor.whiskeringRight K (J ⥤ SSet.{u}) SSet.{u}).obj
      (WeightedCones.coneSpace J V) ⋙ WeightedCones.coneSpace K W

/-- 概要：外重みとのテンソルと反復テンソルは自然同型（論文 補題 3.2）。
方針：各二重添字で単体集合のテンソル結合子の逆を使う。
規約：入力空間と二つの添字の全ての射への自然性を保つ。
使われ方：左随伴から右随伴の Fubini への移行。 -/
def externalCechTensorIso :
    WeightedCones.tensorDiagram (K × J) (externalCechWeight K J W V) ≅
      iteratedCechTensor K J W V :=
  NatIso.ofComponents (fun X ↦ NatIso.ofComponents
    (fun k ↦ (α_ X (W.obj k.1) (V.obj k.2)).symm) (by
      intro k l f
      change (𝟙 X ⊗ₘ (W.map f.1 ⊗ₘ V.map f.2)) ≫
          (α_ X (W.obj l.1) (V.obj l.2)).inv =
        (α_ X (W.obj k.1) (V.obj k.2)).inv ≫
          ((𝟙 X ⊗ₘ W.map f.1) ⊗ₘ V.map f.2)
      exact associator_inv_naturality _ _ _)) (by
    intro X Y f
    apply NatTrans.ext
    funext k
    change (f ⊗ₘ 𝟙 (W.obj k.1 ⊗ V.obj k.2)) ≫
        (α_ Y (W.obj k.1) (V.obj k.2)).inv =
      (α_ X (W.obj k.1) (V.obj k.2)).inv ≫
        ((f ⊗ₘ 𝟙 (W.obj k.1)) ⊗ₘ 𝟙 (V.obj k.2))
    simp)

/-- 概要：反復テンソルと反復錐空間は実際に随伴（論文 補題 3.2）。
方針：二つの重みつき随伴と curry/uncurry の同値の随伴を合成する。
規約：随伴の存在を追加仮定にしない。使われ方：右随伴の一意性による自然比較。 -/
def iteratedCechConeAdjunction :
    iteratedCechTensor K J W V ⊣ iteratedCechConeSpace K J W V :=
  ((WeightedCones.adjunction K W).comp ((WeightedCones.adjunction J V).whiskerRight K)).comp
    (Functor.currying (C := K) (D := J) (E := SSet.{u})).toAdjunction

/-- 概要：外重みの実際の錐空間と反復錐空間の自然同型（論文 補題 3.2・3.3）。
方針：左随伴の結合子の同型を移し、右随伴の一意性を適用する。
規約：重みの cofibrancy と図式の fibrancy を用いた導来性の比較は別工程。
使われ方：二重 Čech の導来 Fubini の模型での比較。 -/
def weightedCechFubiniIso :
    WeightedCones.coneSpace (K × J) (externalCechWeight K J W V) ≅
      iteratedCechConeSpace K J W V :=
  (WeightedCones.adjunction (K × J) (externalCechWeight K J W V)).rightAdjointUniq
    ((iteratedCechConeAdjunction K J W V).ofNatIsoLeft (externalCechTensorIso K J W V).symm)

end SerrePositivity.KST.Descent
