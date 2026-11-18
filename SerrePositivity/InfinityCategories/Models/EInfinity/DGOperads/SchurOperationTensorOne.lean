module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.SchurOperationTensor
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.CompositionUnit
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorFamilyUnit

/-!
模型。文献の定義との比較は後で
# 一入力の Schur 演算のテンソル射

概要：Berger–Moerdijk §1 の一入力の全合成を、通常の部分合成のテンソルとして表す。
方針：有限テンソル族の最後の単位因子を除き、総 arity の移送を最後へまとめる。
規約：内側の演算は零入力でもよい。
使われ方：任意の代数で全合成を評価する式の一入力の場合に用いる。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers
open scoped _root_.BigOperators

variable {A : Type u} [CommRing A]

attribute [local implicit_reducible] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct

private lemma separate_one {C U W R Z : Complex A}
    (v : ((U ⊗ W) ⊗ 𝟙_ (Complex A)) ⟶
      (U ⊗ 𝟙_ (Complex A)) ⊗ (W ⊗ 𝟙_ (Complex A)))
    (f : C ⊗ U ⟶ R) (g : W ⟶ Z)
    (hv : v ≫ ((ρ_ U).hom ⊗ₘ (ρ_ W).hom) = (ρ_ (U ⊗ W)).hom) :
    (C ◁ v) ≫ (α_ C (U ⊗ 𝟙_ (Complex A)) (W ⊗ 𝟙_ (Complex A))).inv ≫
      (((C ◁ (ρ_ U).hom) ≫ f) ⊗ₘ ((ρ_ W).hom ≫ g)) =
    (C ◁ (ρ_ (U ⊗ W)).hom) ≫ (α_ C U W).inv ≫ (f ⊗ₘ g) := by
  rw [← tensorHom_comp_tensorHom]
  have h := associator_inv_naturality (𝟙 C) (ρ_ U).hom (ρ_ W).hom
  simp only [id_tensorHom] at h
  rw [← reassoc_of% h]
  rw [← whiskerLeft_comp_assoc, hv]

namespace Operad

/-- 概要：一入力の Schur 演算は部分合成と総 arity の移送で表せる（Berger–Moerdijk §1）。
方針：一次の係数合成と入力連結を簡約し、分離同型の右単位則を使う。
規約：係数と入力の arity は同じ等式で移送する。
使われ方：Schur 演算を任意の代数で評価するとき部分合成則を適用する。 -/
lemma schurOperationTensor_one (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (K : Complex A) (s : Fin 1 → ℕ) :
    P.schurOperationTensor K 1 s =
    (P.arity 1 ◁ (ρ_ (P.arity (s 0) ⊗ power K (s 0))).hom) ≫
      (α_ (P.arity 1) (P.arity (s 0)) (power K (s 0))).inv ≫
      ((P.comp 0 (s 0) 0 ≫ eqToHom (congrArg P.arity (Nat.zero_add (s 0)))) ⊗ₘ
        𝟙 (power K (s 0))) ≫
      (eqToHom (congrArg P.arity (by simp : s 0 = ∑ i, s i)) ⊗ₘ
        eqToHom (congrArg (power K) (by simp : s 0 = ∑ i, s i))) := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.schurOperationTensor
  rw [P.composition_one, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso_one]
  simp only [eqToHom_refl, tensorHom_id, id_whiskerRight,
    Category.comp_id]
  have h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.separate_one _ (P.comp 0 (s 0) 0 ≫
    eqToHom (congrArg P.arity (Nat.zero_add (s 0)))) (𝟙 (power K (s 0)))
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyTensorIso_one (fun j => P.arity (s j)) (fun j => power K (s j)))
  simp only [Category.comp_id, tensorHom_id] at h
  exact h

end Operad

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
