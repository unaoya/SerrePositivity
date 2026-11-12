module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.TwoColorCochainEquivalence
public import Mathlib.Algebra.Homology.BifunctorHomotopy

/-!
# 任意の入力複体を持つ二色の係数比較

## 概要
HA 3.2.4.7 の自由比較の係数同値を、微分を持つ任意の入力の表現の複体へ適用する。

## 方針
テンソル余不変の双関手を二つのコチェイン複体の直和全複体へ延ばし、
係数の鎖ホモトピーも同じ全複体へ移す。

## 規約
入力を零微分や有界な複体に限定しない。平坦性と群の位数の可逆性は要求しない。

## 使われ方
色付き Schur 表示の任意の cofibrant な入力複体での指定比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] (m n : ℕ)

/-- 入力と係数のテンソル余不変を取る、直和全複体の双関手。 -/
abbrev twoColorInputTotalFunctor :=
  (Rep.coinvariantsTensor A (TwoColorGroup.{u} m n)).map₂CochainComplex

/-- 入力が任意の複体であっても、指定係数射は全複体の鎖ホモトピー同値の順射。 -/
def twoColorComplexInputHomotopyEquiv
    (V : CochainComplex (Rep.{u} A (TwoColorGroup.{u} m n)) ℤ) :
    HomotopyEquiv
      (((twoColorInputTotalFunctor A m n).obj V).obj (twoColorSourceCochain A m n))
      (((twoColorInputTotalFunctor A m n).obj V).obj (twoColorTargetCochain A m n)) where
  hom := ((twoColorInputTotalFunctor A m n).obj V).map
    (twoColorCoefficientCochainHomotopyEquiv A m n).hom
  inv := ((twoColorInputTotalFunctor A m n).obj V).map
    (twoColorCoefficientCochainHomotopyEquiv A m n).inv
  homotopyHomInvId := by
    have h := mapBifunctorMapHomotopy₂ (𝟙 V)
      (twoColorCoefficientCochainHomotopyEquiv A m n).homotopyHomInvId
      (Rep.coinvariantsTensor A (TwoColorGroup.{u} m n)) (.up ℤ)
    change Homotopy
      (((twoColorInputTotalFunctor A m n).obj V).map
        ((twoColorCoefficientCochainHomotopyEquiv A m n).hom ≫
          (twoColorCoefficientCochainHomotopyEquiv A m n).inv))
      (((twoColorInputTotalFunctor A m n).obj V).map (𝟙 _)) at h
    simpa only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] using h
  homotopyInvHomId := by
    have h := mapBifunctorMapHomotopy₂ (𝟙 V)
      (twoColorCoefficientCochainHomotopyEquiv A m n).homotopyInvHomId
      (Rep.coinvariantsTensor A (TwoColorGroup.{u} m n)) (.up ℤ)
    change Homotopy
      (((twoColorInputTotalFunctor A m n).obj V).map
        ((twoColorCoefficientCochainHomotopyEquiv A m n).inv ≫
          (twoColorCoefficientCochainHomotopyEquiv A m n).hom))
      (((twoColorInputTotalFunctor A m n).obj V).map (𝟙 _)) at h
    simpa only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_id] using h

/-- 全複体の比較の順射は、元の指定係数射を入力の複体とテンソルした射である。 -/
@[simp]
lemma twoColorComplexInputHomotopyEquiv_hom
    (V : CochainComplex (Rep.{u} A (TwoColorGroup.{u} m n)) ℤ) :
    (twoColorComplexInputHomotopyEquiv A m n V).hom =
      ((twoColorInputTotalFunctor A m n).obj V).map (twoColorCoefficientCochainMap A m n) := rfl

end SerrePositivity.EInfinity.BarrattEccles
