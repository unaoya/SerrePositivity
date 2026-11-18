module

public import SerrePositivity.EInfinity.BarrattEccles.Theory.HopfTensorOperations
public import SerrePositivity.EInfinity.BarrattEccles.Theory.TensorUnitCoherence
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.MonoidPowers

/-!
# 単位因子のテンソル冪の縮約

## 概要
BF §1.1.4 の単位代数とのテンソルで、入力の二列分離を元の入力の単位子へ戻す。

## 方針
単位対象の反復積の再帰と、二列分離と左右の単位子の整合性を使う。

## 規約
空積を含む全ての入力数で、指定されたテンソル冪の射を比較する。

## 使われ方
HA 3.2.4.7 の二つの包含に必要な、テンソル代数の左右の単位同型。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity
open CategoryTheory MonoidalCategory
open DifferentialGraded TensorPowers
variable {A : Type u} [CommRing A]
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct
attribute [local implicit_reducible] TensorPowers.power

/-- BF §1.1.4 の右単位因子の入力の縮約は元の右単位子のテンソル冪。 -/
lemma tensorPowerSeparation_rightUnit (V : Complex A) (n : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerSeparation V (𝟙_ (Complex A)) n).hom ≫
      (power V n ◁ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.powerProduct (𝟙_ (Complex A)) n) ≫ (ρ_ (power V n)).hom =
      map (ρ_ V).hom n := by
  induction n with
  | zero =>
    rw [tensorPowerSeparation_zero_hom]
    change (λ_ (𝟙_ (Complex A))).inv ≫
      ((𝟙_ (Complex A)) ◁ 𝟙 (𝟙_ (Complex A))) ≫ (ρ_ (𝟙_ (Complex A))).hom = 𝟙 _
    simp only [whiskerLeft_id, Category.id_comp, ← unitors_equal, Iso.inv_hom_id]
  | succ n ih =>
    rw [tensorPowerSeparation_succ_hom]
    simp only [Category.assoc]
    change ((V ⊗ 𝟙_ (Complex A)) ◁ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerSeparation V (𝟙_ (Complex A)) n).hom) ≫
      tensorμ V (𝟙_ (Complex A)) (power V n) (power (𝟙_ (Complex A)) n) ≫
        ((V ⊗ power V n) ◁ (((𝟙_ (Complex A)) ◁ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.powerProduct (𝟙_ (Complex A)) n) ≫
          (λ_ (𝟙_ (Complex A))).hom)) ≫ (ρ_ (V ⊗ power V n)).hom =
      (ρ_ V).hom ⊗ₘ map (ρ_ V).hom n
    have h := tensorμ_natural_right V (𝟙_ (Complex A)) (𝟙 (power V n))
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.powerProduct (𝟙_ (Complex A)) n)
    simp only [id_tensorHom, whiskerLeft_id] at h
    simp only [whiskerLeft_comp, Category.assoc]
    rw [← reassoc_of% h, tensorUnitRightAssembly, ← whiskerLeft_comp_assoc,
      whiskerLeft_comp_tensorHom, Category.assoc, ih]

/-- BF §1.1.4 の左単位因子の入力の縮約は元の左単位子のテンソル冪。 -/
lemma tensorPowerSeparation_leftUnit (V : Complex A) (n : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerSeparation (𝟙_ (Complex A)) V n).hom ≫
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.powerProduct (𝟙_ (Complex A)) n ▷ power V n) ≫ (λ_ (power V n)).hom =
      map (λ_ V).hom n := by
  induction n with
  | zero =>
    rw [tensorPowerSeparation_zero_hom]
    change (λ_ (𝟙_ (Complex A))).inv ≫
      (𝟙 (𝟙_ (Complex A)) ▷ 𝟙_ (Complex A)) ≫ (λ_ (𝟙_ (Complex A))).hom = 𝟙 _
    simp only [id_whiskerRight, Category.id_comp, Iso.inv_hom_id]
  | succ n ih =>
    rw [tensorPowerSeparation_succ_hom]
    simp only [Category.assoc]
    change ((𝟙_ (Complex A) ⊗ V) ◁ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerSeparation (𝟙_ (Complex A)) V n).hom) ≫
      tensorμ (𝟙_ (Complex A)) V (power (𝟙_ (Complex A)) n) (power V n) ≫
        ((((𝟙_ (Complex A)) ◁ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.powerProduct (𝟙_ (Complex A)) n) ≫
          (λ_ (𝟙_ (Complex A))).hom) ▷ (V ⊗ power V n)) ≫ (λ_ (V ⊗ power V n)).hom =
      (λ_ V).hom ⊗ₘ map (λ_ V).hom n
    have h := tensorμ_natural_right (𝟙_ (Complex A)) V
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.powerProduct (𝟙_ (Complex A)) n) (𝟙 (power V n))
    simp only [tensorHom_id, whiskerLeft_id] at h
    simp only [comp_whiskerRight, Category.assoc]
    rw [← reassoc_of% h, tensorUnitLeftAssembly, ← whiskerLeft_comp_assoc,
      whiskerLeft_comp_tensorHom, Category.assoc, ih]

end SerrePositivity.EInfinity
