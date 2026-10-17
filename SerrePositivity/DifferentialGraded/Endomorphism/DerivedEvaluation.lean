module
public import SerrePositivity.DifferentialGraded.Endomorphism.EvaluationAdjunction
public import SerrePositivity.DifferentialGraded.Derived.RightTensorResolution

/-! # U12dの導来tensorからの指定対象を通る評価

解像度のaugmentationを使って評価を定義する。同型性はここでは主張しない。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (E X Y : D)

/-- 解像度の実際のaugmentationを合成するchain-level評価。 -/
def endomorphismResolutionEvaluation
    (P : ModuleProjectiveResolution A (EndomorphismObject E)
      (ForgetEnrichment.of (Complex A) (endomorphismHomRight A D E Y))) :
    (BalancedTensor.rightTensorFunctor A _ (endomorphismHomLeft A D E X)).obj P.obj ⟶
      homObject A D X Y :=
  (BalancedTensor.rightTensorFunctor A _ (endomorphismHomLeft A D E X)).map P.π ≫
    endomorphismEvaluation A D E X Y

variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]

/-- augmentationの因子化はホモトピーまで成立するため、評価の正方形は導来圏で可換。 -/
lemma endomorphismResolutionEvaluation_comparison
    (P Q : ModuleProjectiveResolution A (EndomorphismObject E)
      (ForgetEnrichment.of (Complex A) (endomorphismHomRight A D E Y))) :
    DerivedCategory.Q.map
      ((BalancedTensor.rightTensorFunctor A _ (endomorphismHomLeft A D E X)).map
        (P.comparison Q)) ≫
        DerivedCategory.Q.map (endomorphismResolutionEvaluation A D E X Y Q) =
      DerivedCategory.Q.map (endomorphismResolutionEvaluation A D E X Y P) := by
  have h := moduleTensorDerived_map_eq_of_homotopy_map_eq A (EndomorphismObject E)
    (endomorphismHomLeft A D E X)
    (((moduleToHomotopy A (EndomorphismObject E)).map_comp (P.comparison Q) Q.π).trans
      (P.comparison_fac Q))
  dsimp only [endomorphismResolutionEvaluation]
  simpa only [CategoryTheory.Functor.map_comp, Category.assoc] using
    congrArg (fun f => f ≫ DerivedCategory.Q.map (endomorphismEvaluation A D E X Y)) h

/-- U12dの既存導来tensorを標準解像度で計算して得る評価。 -/
def endomorphismDerivedEvaluation :
    (moduleDerivedTensorRight A (EndomorphismObject E) (endomorphismHomLeft A D E X)).obj
        ((moduleToDerived A (EndomorphismObject E)).obj
          (ForgetEnrichment.of (Complex A) (endomorphismHomRight A D E Y))) ⟶
      DerivedCategory.Q.obj (homObject A D X Y) :=
  (moduleResolutionDerivedTensorComputation A (EndomorphismObject E)
      (moduleCanonicalProjectiveResolution A (EndomorphismObject E))
      (endomorphismHomLeft A D E X)
      (ForgetEnrichment.of (Complex A) (endomorphismHomRight A D E Y))).hom ≫
    DerivedCategory.Q.map (endomorphismResolutionEvaluation A D E X Y
      (moduleCanonicalProjectiveResolution A (EndomorphismObject E)
        (ForgetEnrichment.of (Complex A) (endomorphismHomRight A D E Y))))

/-- 任意の射影解像度による計算でも同じ導来評価になる。 -/
lemma endomorphismDerivedEvaluation_resolution
    (P : ModuleProjectiveResolution A (EndomorphismObject E)
      (ForgetEnrichment.of (Complex A) (endomorphismHomRight A D E Y))) :
    (moduleDerivedTensorRightResolutionComputation A (EndomorphismObject E) P
      (endomorphismHomLeft A D E X)).hom ≫
        DerivedCategory.Q.map (endomorphismResolutionEvaluation A D E X Y P) =
      endomorphismDerivedEvaluation A D E X Y := by
  simp only [moduleDerivedTensorRightResolutionComputation, Iso.trans_hom,
    Category.assoc, moduleProjectiveResolutionTensorIso_hom,
    endomorphismResolutionEvaluation_comparison, endomorphismDerivedEvaluation]

end SerrePositivity.DifferentialGraded
