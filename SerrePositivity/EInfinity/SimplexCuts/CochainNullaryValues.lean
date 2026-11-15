module

public import SerrePositivity.EInfinity.SimplexCuts.CochainNullaryAction
public import SerrePositivity.EInfinity.SimplexCuts.NullaryCoefficientValues
public import SerrePositivity.EInfinity.SimplexCuts.NormalizedGenerators
public import SerrePositivity.EInfinity.AlexanderWhitney.CochainCounitValues
public import SerrePositivity.EInfinity.BarrattEccles.Unitors
public import SerrePositivity.DifferentialGraded.Complexes.MaurerCartanCurrying

/-!
# 実際の空語作用の全整数の基底値

Berger–Fresse §2.2.6、M14 L12a、報告 §340。
同じ空語係数のaugmentationを一へ評価し、元のAW余単位へ戻す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers
open scoped Simplicial

/-- 同じ空語係数の全整数での値は元のAW余単位（BF §2.2.6）。 -/
lemma cochainAction_nullary_basis_apply (A : Type u) [CommRing A] (S : SSet.{0})
    (v : Surjection.BasisWord 0 0) (t : ℤ) (y : (chains A S).X t) :
    (cochainAction A S 0).f t
      (ιTensorObj (Surjection.complex A 0) (chains A S) 0 t t (zero_add t)
        ((Surjection.complexXIso A 0 0).inv
          (Surjection.basis A 0 0 (ULift.up v)) ⊗ₜ[A] y)) =
      (AlexanderWhitney.cochainCounit A S).f t y := by
  let e := singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))
  let a := (Surjection.complexXIso A 0 0).inv (Surjection.basis A 0 0 (ULift.up v))
  have ha : (nullaryCoefficientAugmentation A).f 0 a = e.inv (1 : A) := by
    calc
      _ = e.inv (e.hom ((nullaryCoefficientAugmentation A).f 0 a)) :=
        (e.hom_inv_id_apply _).symm
      _ = _ := congrArg (fun z => e.inv z) (nullaryCoefficientAugmentation_basis_zero A v)
  rw [cochainAction_zero_eq_nullaryAction]
  change (AlexanderWhitney.cochainCounit A S).f t
    ((λ_ (chains A S)).hom.f t
      ((nullaryCoefficientAugmentation A ▷ chains A S).f t
        (ιTensorObj (Surjection.complex A 0) (chains A S) 0 t t (zero_add t)
          (a ⊗ₜ[A] y)))) = _
  rw [SerrePositivity.DifferentialGraded.whiskerRight_apply, ha]
  change (AlexanderWhitney.cochainCounit A S).f t
    ((λ_ (chains A S)).hom.f t
      (ιTensorObj (𝟙_ (Complex A)) (chains A S) 0 t t (zero_add t)
        (e.inv (1 : A) ⊗ₜ[A] y))) = _
  rw [← BarrattEccles.cochain_leftUnitor_inv_apply A]
  have hc := ConcreteCategory.congr_hom
    (congrArg (fun f => f.f t) (λ_ (chains A S)).inv_hom_id) y
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f, ModuleCat.comp_apply,
    ModuleCat.id_apply] at hc
  rw [hc]

/-- 同じ零単体の空語作用の値は元の単位元（BF §2.2.6）。 -/
lemma cochainAction_nullary_basis_generator_zero (A : Type u) [CommRing A] (S : SSet.{0})
    (v : Surjection.BasisWord 0 0) (x : S _⦋0⦌) :
    (cochainAction A S 0).f 0
      (ιTensorObj (Surjection.complex A 0) (chains A S) 0 0 0 rfl
        ((Surjection.complexXIso A 0 0).inv
          (Surjection.basis A 0 0 (ULift.up v)) ⊗ₜ[A] gen A S 0 x)) =
      (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A) := by
  rw [cochainAction_nullary_basis_apply]
  let e := singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))
  calc
    _ = e.inv (e.hom ((AlexanderWhitney.cochainCounit A S).f 0 (gen A S 0 x))) :=
      (e.hom_inv_id_apply _).symm
    _ = _ := congrArg (fun z => e.inv z) (AlexanderWhitney.cochainCounit_generator_zero A S x)

/-- 同じ空語作用は零以外の全整数次数で零（BF §2.2.6）。 -/
lemma cochainAction_nullary_basis_eq_zero_of_ne_zero (A : Type u) [CommRing A]
    (S : SSet.{0}) (v : Surjection.BasisWord 0 0) (t : ℤ) (ht : t ≠ 0)
    (y : (chains A S).X t) :
    (cochainAction A S 0).f t
      (ιTensorObj (Surjection.complex A 0) (chains A S) 0 t t (zero_add t)
        ((Surjection.complexXIso A 0 0).inv
          (Surjection.basis A 0 0 (ULift.up v)) ⊗ₜ[A] y)) = 0 := by
  let _ : Subsingleton ((power (chains A S) 0).X t) := by
    change Subsingleton (((single (ModuleCat A) (.up ℤ) 0).obj (𝟙_ (ModuleCat A))).X t)
    exact ModuleCat.isZero_iff_subsingleton.mp
      (isZero_single_obj_X (.up ℤ) 0 (𝟙_ (ModuleCat A)) t ht)
  exact Subsingleton.elim _ _

end SerrePositivity.EInfinity.SimplexCuts
