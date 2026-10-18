module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.Data.Fintype.Option

/-!
# 有限積を Cartesian テンソルへ分解する指定同型

## 概要
空間の有限積の弱同値の計算のため、Option 添字の積を一成分と残りの積に分解する。

## 方針
指定積射影と Cartesian テンソルの普遍性から両方向の射を構成する。

## 規約
積の選択を定義上同一視せず、射影を保つ指定同型と自然性を証明する。

## 使われ方
論文 公理 (1)、補題 3.2・3.3 の有限被覆族の各段の有限積。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace SerrePositivity.KST.Descent

variable {C : Type u} [Category.{v} C] [CartesianMonoidalCategory C]
  {ι : Type w} [Finite ι]

/-- 概要：Option 添字の積は先頭の値と残りの積の指定テンソルと同型（公理 (1)）。
方針：積射影と Cartesian テンソルの二つの射影から指定逆を構成する。
規約：Option.none を先頭とする。使われ方：有限積の帰納計算。 -/
def optionProductTensorIso (X : Option ι → C) :
    (∏ᶜ X) ≅ X none ⊗ (∏ᶜ fun i ↦ X (some i)) where
  hom := CartesianMonoidalCategory.lift (Pi.π X none)
    (Pi.lift fun i ↦ Pi.π X (some i))
  inv := Pi.lift (fun i ↦ match i with
    | none => CartesianMonoidalCategory.fst _ _
    | some j => CartesianMonoidalCategory.snd _ _ ≫ Pi.π _ j)
  hom_inv_id := by
    apply Pi.hom_ext
    intro i
    cases i <;> simp
  inv_hom_id := by
    apply CartesianMonoidalCategory.hom_ext
    · simp
    · apply Pi.hom_ext
      intro i
      simp

/-- 概要：Option 積の指定同型は各成分の射に関して自然（公理 (1)）。
方針：テンソルの両射影と残りの積の各射影で比較する。
規約：指定 Pi.map の計算。使われ方：有限積の弱同値の帰納。 -/
theorem optionProductTensorIso_naturality {X Y : Option ι → C} (f : ∀ i, X i ⟶ Y i) :
    CategoryTheory.Limits.Pi.map f ≫ (optionProductTensorIso Y).hom =
      (optionProductTensorIso X).hom ≫
        (f none ⊗ₘ CategoryTheory.Limits.Pi.map (fun i ↦ f (some i))) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [optionProductTensorIso]
  · apply Pi.hom_ext
    intro i
    simp [optionProductTensorIso]

end SerrePositivity.KST.Descent
