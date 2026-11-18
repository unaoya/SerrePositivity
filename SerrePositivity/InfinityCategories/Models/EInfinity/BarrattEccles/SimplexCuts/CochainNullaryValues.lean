module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.CochainNullaryAction
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.NullaryCoefficientValues
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.NormalizedGenerators
public import SerrePositivity.HomologicalAlgebra.SimplicialChains.AlexanderWhitney.CochainCounitValues
public import SerrePositivity.EInfinity.BarrattEccles.Unitors
public import SerrePositivity.DifferentialGraded.Complexes.MaurerCartanCurrying

/-!
模型。文献の定義との比較は後で
# 実際の空語作用の全整数の基底値

Berger–Fresse §2.2.6、M14 L12a、報告 §340。
同じ空語係数のaugmentationを一へ評価し、元のAW余単位へ戻す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers
open scoped _root_.Simplicial

/-- 同じ空語係数の全整数での値は元のAW余単位（BF §2.2.6）。 -/
lemma cochainAction_nullary_basis_apply (A : Type u) [CommRing A] (S : SSet.{0})
    (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord 0 0) (t : ℤ) (y : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S).X t) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cochainAction A S 0).f t
      (ιTensorObj (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A 0) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) 0 t t (zero_add t)
        ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexXIso A 0 0).inv
          (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A 0 0 (ULift.up v)) ⊗ₜ[A] y)) =
      (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainCounit A S).f t y := by
  let e := singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))
  let a := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexXIso A 0 0).inv (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A 0 0 (ULift.up v))
  have ha : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryCoefficientAugmentation A).f 0 a = e.inv (1 : A) := by
    calc
      _ = e.inv (e.hom ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryCoefficientAugmentation A).f 0 a)) :=
        (e.hom_inv_id_apply _).symm
      _ = _ := congrArg (fun z => e.inv z) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryCoefficientAugmentation_basis_zero A v)
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cochainAction_zero_eq_nullaryAction]
  change (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainCounit A S).f t
    ((λ_ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S)).hom.f t
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.nullaryCoefficientAugmentation A ▷ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S).f t
        (ιTensorObj (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A 0) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) 0 t t (zero_add t)
          (a ⊗ₜ[A] y)))) = _
  rw [SerrePositivity.DifferentialGraded.whiskerRight_apply, ha]
  change (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainCounit A S).f t
    ((λ_ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S)).hom.f t
      (ιTensorObj (𝟙_ (Complex A)) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) 0 t t (zero_add t)
        (e.inv (1 : A) ⊗ₜ[A] y))) = _
  rw [← _root_.SerrePositivity.EInfinity.BarrattEccles.cochain_leftUnitor_inv_apply A]
  have hc := ConcreteCategory.congr_hom
    (congrArg (fun f => f.f t) (λ_ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S)).inv_hom_id) y
  simp only [HomologicalComplex.comp_f, HomologicalComplex.id_f, ModuleCat.comp_apply,
    ModuleCat.id_apply] at hc
  rw [hc]

/-- 同じ零単体の空語作用の値は元の単位元（BF §2.2.6）。 -/
lemma cochainAction_nullary_basis_generator_zero (A : Type u) [CommRing A] (S : SSet.{0})
    (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord 0 0) (x : S _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cochainAction A S 0).f 0
      (ιTensorObj (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A 0) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) 0 0 0 rfl
        ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexXIso A 0 0).inv
          (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A 0 0 (ULift.up v)) ⊗ₜ[A] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.gen A S 0 x)) =
      (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A) := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cochainAction_nullary_basis_apply]
  let e := singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))
  calc
    _ = e.inv (e.hom ((_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainCounit A S).f 0 (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.gen A S 0 x))) :=
      (e.hom_inv_id_apply _).symm
    _ = _ := congrArg (fun z => e.inv z) (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainCounit_generator_zero A S x)

/-- 同じ空語作用は零以外の全整数次数で零（BF §2.2.6）。 -/
lemma cochainAction_nullary_basis_eq_zero_of_ne_zero (A : Type u) [CommRing A]
    (S : SSet.{0}) (v : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.BasisWord 0 0) (t : ℤ) (ht : t ≠ 0)
    (y : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S).X t) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.cochainAction A S 0).f t
      (ιTensorObj (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complex A 0) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) 0 t t (zero_add t)
        ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.complexXIso A 0 0).inv
          (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.basis A 0 0 (ULift.up v)) ⊗ₜ[A] y)) = 0 := by
  let _ : Subsingleton ((power (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts.chains A S) 0).X t) := by
    change Subsingleton (((single (ModuleCat A) (.up ℤ) 0).obj (𝟙_ (ModuleCat A))).X t)
    exact ModuleCat.isZero_iff_subsingleton.mp
      (isZero_single_obj_X (.up ℤ) 0 (𝟙_ (ModuleCat A)) t ht)
  exact Subsingleton.elim _ _

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.SimplexCuts
