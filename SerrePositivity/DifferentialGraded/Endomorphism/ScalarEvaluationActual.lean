module
public import SerrePositivity.DifferentialGraded.Endomorphism.ScalarHomFactors

/-! # 実際の係数変更先Hom因子との合成評価の可換性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w w'
namespace SerrePositivity.DifferentialGraded
open CategoryTheory MonoidalCategory
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D] (E X Y : D)

lemma endomorphismEvaluationComponentScalar :
    (ScalarExtension.tensorIso φ (homObject A D E Y) (homObject A D X E)).inv ≫
        (ScalarExtension.extension φ).map (endomorphismEvaluationComponent A D E X Y) =
      endomorphismEvaluationComponent A' (ScalarExtension.DGBaseChange φ D) E X Y := by
  unfold endomorphismEvaluationComponent
  rw [CategoryTheory.Functor.map_comp]
  change _ = (β_ ((ScalarExtension.extension φ).obj (homObject A D E Y))
    ((ScalarExtension.extension φ).obj (homObject A D X E))).hom ≫
      (ScalarExtension.tensorIso φ (homObject A D X E) (homObject A D E Y)).inv ≫
        (ScalarExtension.extension φ).map (eComp (Complex A) X E Y)
  rw [ScalarExtension.tensorIso_braiding_assoc]
  rfl

lemma endomorphismScalarHomTensorIso_evaluation :
    (endomorphismScalarHomTensorIso φ D E X Y).hom ≫
        endomorphismEvaluation A' (ScalarExtension.DGBaseChange φ D) E X Y =
      endomorphismScalarEvaluation φ D E X Y := by
  apply BalancedTensor.hom_ext A' (ScalarExtension.DGBaseChange φ (EndomorphismObject E))
  intro b
  rw [← Category.assoc, endomorphismScalarHomTensorIso_ι,
    endomorphismEvaluation_ι, endomorphismScalarEvaluation_ι,
    endomorphismEvaluationComponentScalar]

variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]
variable [HasDerivedCategory.{w'} (ModuleCat.{u} A')]

/-- 先に構成した比較射を、実際の係数変更先dg圏の合成評価へ接続する。 -/
lemma endomorphismDerivedScalarActualEvaluation_square :
    ScalarExtension.derivedBalancedComparison φ (EndomorphismObject E)
        (endomorphismHomRight A D E Y) (endomorphismHomLeft A D E X) ≫
      DerivedCategory.Q.map (endomorphismScalarHomTensorIso φ D E X Y).hom ≫
      DerivedCategory.Q.map
        (endomorphismEvaluation A' (ScalarExtension.DGBaseChange φ D) E X Y) =
    (ScalarExtension.complexDerivedExtension φ).map
        (DerivedCategory.Q.map (endomorphismEvaluation A D E X Y)) ≫
      (ScalarExtension.complexDerivedExtensionAugmentation φ).app (homObject A D X Y) := by
  rw [← CategoryTheory.Functor.map_comp, endomorphismScalarHomTensorIso_evaluation]
  exact endomorphismDerivedScalarEvaluation_square φ D E X Y

end SerrePositivity.DifferentialGraded
