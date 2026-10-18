module

public import SerrePositivity.EInfinity.Operad.CompositionRightUnit
public import SerrePositivity.EInfinity.Operad.TensorFamilyUnitSeparation
public import SerrePositivity.EInfinity.Operad.TensorFamilyTensorNaturality
public import SerrePositivity.EInfinity.Operad.TensorUnitCoefficient

/-!
# 全入力へ単位係数を入れた Schur 演算

概要：Berger–Moerdijk §1 の全合成の右単位則を Schur 演算の生成射へ適用する。
方針：係数と入力の分離の自然性で単位係数を集め、単位族の縮約を入力側へ移す。
規約：全ての内側演算の arity は一とする。
使われ方：Schur 作用を生成元の包含へ制限した式を証明する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.Operad

open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
open scoped BigOperators

variable {A : Type u} [CommRing A]

attribute [local implicit_reducible] tensorFamily TensorPowers.power
  SerrePositivity.SymmetricSequence SerrePositivity.SymmetricSequence.level
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct

private lemma ι_coefficient_cast (P : Operad A) (K : Complex A) {m n : ℕ} (h : m = n) :
    (eqToHom (congrArg P.arity h) ▷ power K n) ≫ schurι A P.sequence K n =
      (P.arity m ◁ eqToHom (congrArg (power K) h.symm)) ≫ schurι A P.sequence K m := by
  subst n
  simp only [eqToHom_refl, id_whiskerRight, whiskerLeft_id, Category.id_comp]

/-- 概要：各入力に単位係数を入れた Schur 演算は入力を連結した後の生成射に一致する（Berger–Moerdijk §1）。
方針：分離の自然性と全合成の右単位則を使い、縮約した係数列を各入力の左単位子へ移す。
規約：総 arity の移送は入力側へ移して元の arity n の生成射を使う。
使われ方：自由代数の生成元に対する作用の式を導く。 -/
lemma schurOperationGenerator_units (P : Operad A) (K : Complex A) (n : ℕ) :
    (P.arity n ◁ tensorFamilyMap n (fun _ : Fin n => P.unit ▷ power K 1)) ≫
      P.schurOperationGenerator K n (fun _ => 1) =
    (P.arity n ◁ (tensorFamilyMap n (fun _ : Fin n => (λ_ (power K 1)).hom) ≫
      (tensorPowerFamilyIso K n (fun _ => 1)).hom ≫
      eqToHom (congrArg (power K) (by simp : (∑ _ : Fin n, 1) = n)))) ≫
      schurι A P.sequence K n := by
  have hs := tensorFamilyTensorIso_naturality n
    (V := fun _ => 𝟙_ (Complex A)) (W := fun _ => power K 1)
    (V' := fun _ => P.arity 1) (W' := fun _ => power K 1)
    (fun _ => P.unit) (fun _ => 𝟙 (power K 1))
  simp only [tensorHom_id, tensorFamilyMap_id] at hs
  unfold schurOperationGenerator
  rw [← whiskerLeft_comp_assoc, hs]
  simp only [whiskerLeft_comp, Category.assoc]
  rw [associator_inv_naturality_middle_assoc, whiskerRight_comp_tensorHom_assoc,
    P.composition_units]
  erw [tensorUnitCoefficient]
  rw [ι_coefficient_cast P K (by simp : n = ∑ _ : Fin n, 1)]
  simp only [← whiskerLeft_comp_assoc, Category.assoc]
  rw [reassoc_of% (tensorFamilyTensorIso_unit_left n (fun _ => power K 1))]

end SerrePositivity.EInfinity.Operad
