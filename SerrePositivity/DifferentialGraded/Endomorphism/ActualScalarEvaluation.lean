module
public import SerrePositivity.DifferentialGraded.Endomorphism.ScalarModuleDGFunctor
public import SerrePositivity.DifferentialGraded.Endomorphism.ScalarEvaluationActual

/-! # 実際に係数変更したD上の加群のHomへ向かう導来評価図式 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w w'
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory BraidedCategory

lemma dgFunctor_endomorphismEvaluationComponent (A : Type u) [CommRing A]
    {C T : Type*} [DGCategory A C] [DGCategory A T]
    (F : DGFunctor A C T) (E X Y : C) :
    (F.map E Y ⊗ₘ F.map X E) ≫
        endomorphismEvaluationComponent A T (F.obj E) (F.obj X) (F.obj Y) =
      endomorphismEvaluationComponent A C E X Y ≫ F.map X Y := by
  unfold endomorphismEvaluationComponent
  change (F.map E Y ⊗ₘ F.map X E) ≫ (β_ _ _).hom ≫ _ = (β_ _ _).hom ≫ _ ≫ _
  rw [braiding_naturality_assoc, ← F.map_comp]

variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D] [Small.{u} D] (E X Y : RightModule A D)

def actualScalarEvaluation :
    BalancedTensor.obj A' (ScalarExtension.DGBaseChange φ (EndomorphismObject E))
      (ScalarExtension.rightModule φ (EndomorphismObject E)
        (endomorphismHomRight A (RightModule A D) E Y))
      (ScalarExtension.leftModule φ (EndomorphismObject E)
        (endomorphismHomLeft A (RightModule A D) E X)) ⟶
      moduleHom A' (ScalarExtension.DGBaseChange φ D)
        (ScalarExtension.rightModule φ D X) (ScalarExtension.rightModule φ D Y) :=
  endomorphismScalarEvaluation φ (RightModule A D) E X Y ≫ scalarModuleHom φ D X Y

lemma actualScalarEvaluation_ι (b : EndomorphismObject E) :
    BalancedTensor.ι A' (ScalarExtension.DGBaseChange φ (EndomorphismObject E))
        (ScalarExtension.rightModule φ (EndomorphismObject E)
          (endomorphismHomRight A (RightModule A D) E Y))
        (ScalarExtension.leftModule φ (EndomorphismObject E)
          (endomorphismHomLeft A (RightModule A D) E X)) b ≫
      actualScalarEvaluation φ D E X Y =
    (scalarModuleHom φ D E Y ⊗ₘ scalarModuleHom φ D X E) ≫
      endomorphismEvaluationComponent A' (RightModule A' (ScalarExtension.DGBaseChange φ D))
        (ScalarExtension.rightModule φ D E) (ScalarExtension.rightModule φ D X)
        (ScalarExtension.rightModule φ D Y) := by
  rw [actualScalarEvaluation, ← Category.assoc, endomorphismScalarEvaluation_ι]
  have h := dgFunctor_endomorphismEvaluationComponent A' (scalarModuleDGFunctor φ D) E X Y
  rw [endomorphismEvaluationComponentScalar]
  exact h.symm

variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]
variable [HasDerivedCategory.{w'} (ModuleCat.{u} A')]

lemma actualDerivedScalarEvaluation_square :
    ScalarExtension.derivedBalancedComparison φ (EndomorphismObject E)
        (endomorphismHomRight A (RightModule A D) E Y)
        (endomorphismHomLeft A (RightModule A D) E X) ≫
      DerivedCategory.Q.map (actualScalarEvaluation φ D E X Y) =
    (ScalarExtension.complexDerivedExtension φ).map
        (DerivedCategory.Q.map (endomorphismEvaluation A (RightModule A D) E X Y)) ≫
      (ScalarExtension.complexDerivedExtensionAugmentation φ).app (moduleHom A D X Y) ≫
        DerivedCategory.Q.map (scalarModuleHom φ D X Y) := by
  rw [actualScalarEvaluation, CategoryTheory.Functor.map_comp, ← Category.assoc,
    endomorphismDerivedScalarEvaluation_square, Category.assoc]
  rfl

end SerrePositivity.DifferentialGraded
