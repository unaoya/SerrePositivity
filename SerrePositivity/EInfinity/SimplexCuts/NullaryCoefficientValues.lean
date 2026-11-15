module

public import SerrePositivity.EInfinity.SimplexCuts.NullaryAction

/-!
# 元の空語係数augmentationの零次の値

Berger–Fresse §1.2.1・§2.2.6、M14 L12a、報告 §338。
次数延長とsingleの指定比較を保って、元の零次augmentationへ戻す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.SimplexCuts
open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers

/-- 同じ空語係数の整数複体上の零次値は元のaugmentation（BF §1.2.1）。 -/
lemma nullaryCoefficientAugmentation_zero_apply (A : Type u) [CommRing A]
    (w : Surjection.degreeModule A 0 0) :
    (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).hom
      ((nullaryCoefficientAugmentation A).f 0 ((Surjection.complexXIso A 0 0).inv w)) =
      Surjection.zeroAugmentation A 0 w := by
  change (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).hom
    ((extendSingleIso ComplexShape.embeddingDownNat (𝟙_ (ModuleCat A)) 0 0 rfl).hom.f 0
      ((extendMap (nullaryCoefficientChainAugmentation A) ComplexShape.embeddingDownNat).f 0
        ((extendXIso (Surjection.normalizedChains A 0)
          ComplexShape.embeddingDownNat rfl).inv w))) = _
  rw [extendSingleIso_hom_f,
    extendMap_f (nullaryCoefficientChainAugmentation A) ComplexShape.embeddingDownNat
      (i := 0) (i' := 0) rfl]
  simp only [ModuleCat.comp_apply, Iso.inv_hom_id_apply, ChainComplex.single₀ObjXSelf,
    Iso.refl_hom, nullaryCoefficientChainAugmentation,
    ChainComplex.toSingle₀Equiv_symm_apply_f_zero]
  exact congrArg (fun z => Surjection.zeroAugmentation A 0 z)
    ((Surjection.complexXIso A 0 0).inv_hom_id_apply w)

/-- 元の空語基底の係数の値は一（BF §1.2.1）。 -/
lemma nullaryCoefficientAugmentation_basis_zero (A : Type u) [CommRing A]
    (v : Surjection.BasisWord 0 0) :
    (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).hom
      ((nullaryCoefficientAugmentation A).f 0 ((Surjection.complexXIso A 0 0).inv
        (Surjection.basis A 0 0 (ULift.up v)))) = (1 : A) := by
  rw [nullaryCoefficientAugmentation_zero_apply, Surjection.zeroAugmentation_basis]

end SerrePositivity.EInfinity.SimplexCuts
