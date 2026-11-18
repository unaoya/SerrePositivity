module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.CompositionRightUnit
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorFamilyUnitSeparation
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorFamilyTensorNaturality
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorUnitCoefficient

/-!
模型。文献の定義との比較は後で
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

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers
open scoped _root_.BigOperators

variable {A : Type u} [CommRing A]

attribute [local implicit_reducible] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily _root_.SerrePositivity.TensorPowers.power
  SerrePositivity.SymmetricSequence SerrePositivity.SymmetricSequence.level
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct

private lemma ι_coefficient_cast (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (K : Complex A) {m n : ℕ} (h : m = n) :
    (eqToHom (congrArg P.arity h) ▷ power K n) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurι A P.sequence K n =
      (P.arity m ◁ eqToHom (congrArg (power K) h.symm)) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurι A P.sequence K m := by
  subst n
  simp only [eqToHom_refl, id_whiskerRight, whiskerLeft_id, Category.id_comp]

/-- 概要：各入力に単位係数を入れた Schur 演算は入力を連結した後の生成射に一致する（Berger–Moerdijk §1）。
方針：分離の自然性と全合成の右単位則を使い、縮約した係数列を各入力の左単位子へ移す。
規約：総 arity の移送は入力側へ移して元の arity n の生成射を使う。
使われ方：自由代数の生成元に対する作用の式を導く。 -/
lemma schurOperationGenerator_units (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (K : Complex A) (n : ℕ) :
    (P.arity n ◁ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyMap n (fun _ : Fin n => P.unit ▷ power K 1)) ≫
      P.schurOperationGenerator K n (fun _ => 1) =
    (P.arity n ◁ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyMap n (fun _ : Fin n => (λ_ (power K 1)).hom) ≫
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso K n (fun _ => 1)).hom ≫
      eqToHom (congrArg (power K) (by simp : (∑ _ : Fin n, 1) = n)))) ≫
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.schurι A P.sequence K n := by
  have hs := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyTensorIso_naturality n
    (V := fun _ => 𝟙_ (Complex A)) (W := fun _ => power K 1)
    (V' := fun _ => P.arity 1) (W' := fun _ => power K 1)
    (fun _ => P.unit) (fun _ => 𝟙 (power K 1))
  simp only [tensorHom_id, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyMap_id] at hs
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.schurOperationGenerator
  rw [← whiskerLeft_comp_assoc, hs]
  simp only [whiskerLeft_comp, Category.assoc]
  rw [associator_inv_naturality_middle_assoc, whiskerRight_comp_tensorHom_assoc,
    P.composition_units]
  erw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorUnitCoefficient]
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.ι_coefficient_cast P K (by simp : n = ∑ _ : Fin n, 1)]
  simp only [← whiskerLeft_comp_assoc, Category.assoc]
  rw [reassoc_of% (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyTensorIso_unit_left n (fun _ => power K 1))]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad
