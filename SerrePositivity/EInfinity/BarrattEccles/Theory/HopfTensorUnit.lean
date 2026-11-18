module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.HopfTensorOperations
public import Mathlib.Tactic.CategoryTheory.Monoidal.Basic

/-!
# Hopf テンソル演算の単位

## 概要
Berger–Fresse §1.1.4 の単位を保つ対角から、テンソル演算の単位則を示す。

## 方針
一次テンソル冪の分離を単位子へ戻し、各因子の代数の単位則を適用する。

## 規約
台の複体の有界性と cofibrancy を仮定しない。

## 使われ方
HA 3.2.4.7 の余積比較で使うテンソル代数の単位公理。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity
open CategoryTheory MonoidalCategory
open DifferentialGraded TensorPowers
variable {A : Type u} [CommRing A] {P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A}
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct
attribute [local implicit_reducible] TensorPowers.power SerrePositivity.SymmetricSequence
  SerrePositivity.SymmetricSequence.level

/-- BF §1.1.4 の二列分離は一次冪の指定単位子と可換。 -/
@[reassoc]
lemma tensorPowerSeparation_one (V W : Complex A) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerSeparation V W 1).hom ≫ ((oneIso V).hom ⊗ₘ (oneIso W).hom) =
      (oneIso (V ⊗ W)).hom := by
  rw [tensorPowerSeparation_succ_hom, tensorPowerSeparation_zero_hom]
  simpa only [oneIso, power, Category.assoc] using (tensor_right_unitality V W).symm

/-- BF §1.1.4 のテンソル演算は単位演算を恒等演算に送る。 -/
lemma hopfTensorAction_unit (hP : P.Hopf) (X Y : P.Algebra) :
    (P.unit ▷ power (X.carrier ⊗ Y.carrier) 1) ≫ hopfTensorAction hP X Y 1 =
      (λ_ (power (X.carrier ⊗ Y.carrier) 1)).hom ≫
        (oneIso (X.carrier ⊗ Y.carrier)).hom := by
  have hd : P.unit ≫ hP.diagonalComponent 1 =
      (λ_ (𝟙_ (Complex A))).inv ≫ (P.unit ⊗ₘ P.unit) := hP.diagonal.unit
  rw [hopfTensorAction, tensorHom_def]
  simp only [Category.assoc]
  rw [← comp_whiskerRight_assoc, hd]
  simp only [comp_whiskerRight, Category.assoc]
  rw [← whisker_exchange_assoc, tensorμ_natural_left_assoc,
    tensorHom_comp_tensorHom, X.unit_action, Y.unit_action,
    ← tensorHom_comp_tensorHom, ← whisker_exchange_assoc, ← tensor_left_unitality_assoc,
    leftUnitor_naturality_assoc, tensorPowerSeparation_one]

end SerrePositivity.EInfinity
