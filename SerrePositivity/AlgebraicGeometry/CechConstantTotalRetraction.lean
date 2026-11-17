module

public import SerrePositivity.AlgebraicGeometry.CechConstantTotalRetractionDifferential
public import SerrePositivity.AlgebraicGeometry.CechComplexRetractionExact
import all SerrePositivity.HomologicalAlgebra.BicomplexProjection
import all Mathlib.Algebra.Group.Nat.Defs
import all Mathlib.CategoryTheory.Limits.HasLimits

/-!
概要：同じ補正付き射影を全複体の射にし、元のsingleの完全性へ戻す。
方針：正の縦次数の偶奇を元の0/id微分と増大で照合し、各入射からまとめる。
規約：元のsingleの増大項・同じtotal・包含を保つ。
使われ方：行が完全な定数増大列から、元の増大された二重 Čech の完全性へ渡す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits Preadditive
universe u v
local notation "up" => ComplexShape.up ℕ
variable {R : Type v} [CommRing R] (A : ModuleCat.{u} R)
variable (F : CosimplicialObject (CochainComplex (ModuleCat.{u} R) ℕ))
variable (ε : (Functor.const SimplexCategory).obj (cechConstantComplex A) ⟶ F)
variable [hK : HomologicalComplex₂.HasTotal (C := ModuleCat.{u} R) (SerrePositivity.Cech.augmentedCochain.obj (cechSingleAugmentedObject A F ε)) up]
variable [hL : HomologicalComplex₂.HasTotal (C := ModuleCat.{u} R) (SerrePositivity.Cech.augmentedCochain.obj (cechConstantAugmentedObject A F ε)) up]
include A F ε hK hL

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- 正の縦次数で、元の定数列の偶奇と増大の法則により微分を保つ。 -/
theorem cechConstantTotalRetractionComponent_comm_zero_succ (b : ℕ) :
    (HomologicalComplex₂.ιTotal (C := ModuleCat.{u} R) (SerrePositivity.Cech.augmentedCochain.obj (cechConstantAugmentedObject A F ε)) up 0 (b + 1) (b + 1) (by change 0 + (b + 1) = b + 1; omega) ≫
        cechConstantTotalRetractionComponent A F ε (b + 1)) ≫
        (HomologicalComplex₂.total (C := ModuleCat.{u} R) (SerrePositivity.Cech.augmentedCochain.obj (cechSingleAugmentedObject A F ε)) up).d (b + 1) (b + 2) =
      (HomologicalComplex₂.ιTotal (C := ModuleCat.{u} R) (SerrePositivity.Cech.augmentedCochain.obj (cechConstantAugmentedObject A F ε)) up 0 (b + 1) (b + 1)
          (by change 0 + (b + 1) = b + 1; omega) ≫
        (HomologicalComplex₂.total (C := ModuleCat.{u} R) (SerrePositivity.Cech.augmentedCochain.obj (cechConstantAugmentedObject A F ε)) up).d (b + 1) (b + 2)) ≫
        cechConstantTotalRetractionComponent A F ε (b + 2) := by
  let E : cechConstantComplex A ⟶ F.obj (SimplexCategory.mk 0) := ε.app (SimplexCategory.mk 0)
  let J := HomologicalComplex₂.ιTotal (C := ModuleCat.{u} R) (SerrePositivity.Cech.augmentedCochain.obj (cechSingleAugmentedObject A F ε)) up 1 (b + 1) (b + 2)
    (by change 1 + (b + 1) = b + 2; omega)
  have hr :
      (HomologicalComplex₂.ιTotal (C := ModuleCat.{u} R) (SerrePositivity.Cech.augmentedCochain.obj (cechConstantAugmentedObject A F ε)) up 0 (b + 1) (b + 1)
          (by change 0 + (b + 1) = b + 1; omega) ≫
        (HomologicalComplex₂.total (C := ModuleCat.{u} R) (SerrePositivity.Cech.augmentedCochain.obj (cechConstantAugmentedObject A F ε)) up).d (b + 1) (b + 2)) ≫
        cechConstantTotalRetractionComponent A F ε (b + 2) =
      E.f (b + 1) ≫ J + (cechConstantComplex A).d (b + 1) (b + 2) ≫
        (if Even (b + 2) then -(E.f (b + 1)) ≫ J else 0) := by
    rw [SerrePositivity.HomologicalAlgebra.total_d_summand (C := ModuleCat.{u} R) (SerrePositivity.Cech.augmentedCochain.obj (cechConstantAugmentedObject A F ε)) 0 (b + 1) (b + 1)]
    simp only [pow_zero, one_smul, add_comp, Category.assoc,
      cechConstantTotalRetractionComponent_ι_succ,
      cechConstantTotalRetractionComponent_ι_zero_succ]
    try rfl
  rw [cechConstantTotalRetractionComponent_ι_zero_succ, hr]
  by_cases hb : Even (b + 1)
  · have hd : Even ((b + 1) + 2) := by
      simp only [Nat.even_iff] at hb ⊢
      omega
    have hn : ¬ Even (b + 2) := by
      simp only [Nat.even_iff] at hb ⊢
      omega
    have hd' : (cechConstantComplex A).d (b + 1) (b + 2) = 0 :=
      (cechConstantComplex_d A (b + 1)).trans (ite_eq_left hd)
    erw [dite_eq_left hb, hd', zero_comp, add_zero]
    let e : ∀ q : ℕ, A ⟶ (F.obj (SimplexCategory.mk 0)).X q := fun q ↦ E.f q
    have hh : e b ≫ ((SerrePositivity.Cech.augmentedCochain.obj (cechSingleAugmentedObject A F ε)).d 1 2).f b = 0 :=
      cechConstantAugmentation_horizontal A F ε b
    have hv : e b ≫ ((SerrePositivity.Cech.augmentedCochain.obj (cechSingleAugmentedObject A F ε)).X 1).d b (b + 1) = e (b + 1) :=
      (cechConstantAugmentation_vertical A F ε b).trans (ite_eq_right hn)
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change A at x
    have hhx := congrArg (fun z ↦ z.hom x) hh
    have hvx := congrArg (fun z ↦ z.hom x) hv
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
      LinearMap.zero_apply] at hhx hvx
    have hi := congrArg (fun z ↦ z.hom (-((e b).hom x)))
      (cechBicomplex_total_d_summand_to (R := R)
        (SerrePositivity.Cech.augmentedCochain.obj (cechSingleAugmentedObject A F ε))
        1 b (b + 1) (b + 2) (by change 1 + b = b + 1; omega) (by omega))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_add,
      LinearMap.add_apply, ModuleCat.hom_zsmul, LinearMap.smul_apply,
      ModuleCat.hom_neg, LinearMap.neg_apply, pow_one, neg_one_zsmul, map_neg] at hi
    erw [hhx, hvx] at hi
    simp only [map_zero, neg_zero, zero_add, neg_neg] at hi
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_neg,
      LinearMap.neg_apply, map_neg, e, E, J, Nat.add_assoc] at hi ⊢
    convert hi using 1 <;> rfl
  · have hd : ¬ Even ((b + 1) + 2) := by
      simp only [Nat.even_iff] at hb ⊢
      omega
    have hn : Even (b + 2) := by
      simp only [Nat.even_iff] at hb ⊢
      omega
    have hd' : (cechConstantComplex A).d (b + 1) (b + 2) = 𝟙 A :=
      (cechConstantComplex_d A (b + 1)).trans (ite_eq_right hd)
    erw [dite_eq_right hb, zero_comp, hd', ite_eq_left hn, Category.id_comp]
    simp only [neg_comp, add_neg_cancel]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- 元の各直和入射の照合から、同じ全複体の全次数で微分を保つ。 -/
theorem cechConstantTotalRetractionComponent_comm (n : ℕ) :
    cechConstantTotalRetractionComponent A F ε n ≫
        (HomologicalComplex₂.total (C := ModuleCat.{u} R) (SerrePositivity.Cech.augmentedCochain.obj (cechSingleAugmentedObject A F ε)) up).d n (n + 1) =
      (HomologicalComplex₂.total (C := ModuleCat.{u} R) (SerrePositivity.Cech.augmentedCochain.obj (cechConstantAugmentedObject A F ε)) up).d n (n + 1) ≫
        cechConstantTotalRetractionComponent A F ε (n + 1) := by
  apply HomologicalComplex₂.total.hom_ext
  intro a b h
  change a + b = n at h
  cases a with
  | succ a =>
    simpa only [Category.assoc] using
      cechConstantTotalRetractionComponent_comm_succ A F ε a b n h
  | zero =>
    cases b with
    | zero =>
      have hn : n = 0 := by omega
      cases hn
      simpa only [Category.assoc] using cechConstantTotalRetractionComponent_comm_zero A F ε
    | succ b =>
      have hn : n = b + 1 := by omega
      cases hn
      simpa only [Category.assoc] using cechConstantTotalRetractionComponent_comm_zero_succ A F ε b

/-- 元の定数増大列から同じsingleの全複体への、補正付き射影。 -/
def cechConstantTotalRetraction :
    HomologicalComplex₂.total (C := ModuleCat.{u} R) (SerrePositivity.Cech.augmentedCochain.obj (cechConstantAugmentedObject A F ε)) up ⟶ HomologicalComplex₂.total (C := ModuleCat.{u} R) (SerrePositivity.Cech.augmentedCochain.obj (cechSingleAugmentedObject A F ε)) up where
  f := cechConstantTotalRetractionComponent A F ε
  comm' n m h := by
    have hm : n + 1 = m := h
    subst m
    exact cechConstantTotalRetractionComponent_comm A F ε n

/-- 元の包含と同じ補正付き射影の合成は、元のsingleのtotalの恒等。 -/
theorem cechConstantTotalRetraction_section :
    HomologicalComplex₂.total.map (cechSingleToConstantDouble A F ε) up ≫
        cechConstantTotalRetraction A F ε = 𝟙 _ := by
  apply HomologicalComplex.Hom.ext
  funext n
  exact cechConstantTotalRetractionComponent_section A F ε n

/-- 定数増大列の同じtotalの完全性から、元のsingleのtotalの完全性を戻す。 -/
theorem cechSingleTotal_acyclic_of_constant
    (h : (HomologicalComplex₂.total (C := ModuleCat.{u} R) (SerrePositivity.Cech.augmentedCochain.obj (cechConstantAugmentedObject A F ε)) up).Acyclic) :
    (HomologicalComplex₂.total (C := ModuleCat.{u} R) (SerrePositivity.Cech.augmentedCochain.obj (cechSingleAugmentedObject A F ε)) up).Acyclic :=
  cechComplex_acyclic_of_retraction
    (HomologicalComplex₂.total.map (cechSingleToConstantDouble A F ε) up)
    (cechConstantTotalRetraction A F ε) (cechConstantTotalRetraction_section A F ε) h

end SerrePositivity.AlgebraicGeometry
