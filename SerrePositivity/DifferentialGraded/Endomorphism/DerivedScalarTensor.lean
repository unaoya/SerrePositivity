module
public import SerrePositivity.DifferentialGraded.Endomorphism.DerivedTensorEvaluation
public import SerrePositivity.DifferentialGraded.Derived.ScalarExtensionTensorCoherence

/-! # 再構成導来tensorの評価と導来係数変更

係数変更側の受入済みAPIのK-flat計算条件を明示して使う。
係数変更したEnd(E)をEnd(係数変更したE)と同一視する主張は含まない。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w w'
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D] [Small.{u} D] (E : RightModule A D)
variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]
variable [HasDerivedCategory.{w'} (ModuleCat.{u} A')]

/-- 再構成tensorの評価・U12d比較を経由した導来係数変更同型。 -/
def endomorphismDerivedTensorBaseChange (d : D)
    {N : ModuleCategory A (EndomorphismObject E)}
    (P : ModuleProjectiveResolution A (EndomorphismObject E) N)
    (hPN : complexKFlat A (BalancedTensor.obj A (EndomorphismObject E)
      (ForgetEnrichment.to (Complex A) P.obj) ((endomorphismModuleAction A D E).leftAt d)))
    (hP' : moduleRelativeKFlat A' (ScalarExtension.DGBaseChange φ (EndomorphismObject E))
      (ScalarExtension.rightModule φ (EndomorphismObject E)
        (ForgetEnrichment.to (Complex A) P.obj))) :
    (ScalarExtension.complexDerivedExtension φ).obj
        ((moduleDerivedEvaluation A D d).obj ((endomorphismDerivedTensor A D E).obj
          ((moduleToDerived A (EndomorphismObject E)).obj N))) ≅
      (moduleDerivedTensorRight A' (ScalarExtension.DGBaseChange φ (EndomorphismObject E))
        (ScalarExtension.leftModule φ (EndomorphismObject E)
          ((endomorphismModuleAction A D E).leftAt d))).obj
        ((ScalarExtension.derivedExtension φ (EndomorphismObject E)).obj
          ((moduleToDerived A (EndomorphismObject E)).obj N)) :=
  (ScalarExtension.complexDerivedExtension φ).mapIso
    ((endomorphismDerivedTensorEvaluationIso A D E d).app
      ((moduleToDerived A (EndomorphismObject E)).obj N)) ≪≫
    ScalarExtension.derivedTensorBaseChange φ (EndomorphismObject E) P
      ((endomorphismModuleAction A D E).leftAt d) hPN hP'

/-- 上の計算同型は既存U12d比較と係数変更比較の正方形を与える。 -/
lemma endomorphismDerivedTensorBaseChange_square (d : D)
    {N : ModuleCategory A (EndomorphismObject E)}
    (P : ModuleProjectiveResolution A (EndomorphismObject E) N)
    (hPN : complexKFlat A (BalancedTensor.obj A (EndomorphismObject E)
      (ForgetEnrichment.to (Complex A) P.obj) ((endomorphismModuleAction A D E).leftAt d)))
    (hP' : moduleRelativeKFlat A' (ScalarExtension.DGBaseChange φ (EndomorphismObject E))
      (ScalarExtension.rightModule φ (EndomorphismObject E)
        (ForgetEnrichment.to (Complex A) P.obj))) :
    (endomorphismDerivedTensorBaseChange φ D E d P hPN hP').hom =
      (ScalarExtension.complexDerivedExtension φ).map
        ((endomorphismDerivedTensorEvaluationIso A D E d).hom.app
          ((moduleToDerived A (EndomorphismObject E)).obj N)) ≫
      (ScalarExtension.derivedTensorBaseChange φ (EndomorphismObject E) P
        ((endomorphismModuleAction A D E).leftAt d) hPN hP').hom := rfl

/-- 再構成tensor評価とU12d比較の係数変更後の全導来射自然性。 -/
lemma endomorphismDerivedTensorEvaluationScalar_naturality (d : D)
    {X Y : DerivedModuleCategory A (EndomorphismObject E)} (f : X ⟶ Y) :
    (ScalarExtension.complexDerivedExtension φ).map
        ((endomorphismDerivedTensor A D E ⋙ moduleDerivedEvaluation A D d).map f) ≫
      (ScalarExtension.complexDerivedExtension φ).map
        ((endomorphismDerivedTensorEvaluationIso A D E d).hom.app Y) =
    (ScalarExtension.complexDerivedExtension φ).map
        ((endomorphismDerivedTensorEvaluationIso A D E d).hom.app X) ≫
      (ScalarExtension.complexDerivedExtension φ).map
        ((moduleDerivedTensorRight A (EndomorphismObject E)
          ((endomorphismModuleAction A D E).leftAt d)).map f) := by
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
  exact congrArg (ScalarExtension.complexDerivedExtension φ).map
    ((endomorphismDerivedTensorEvaluationIso A D E d).hom.naturality f)

end SerrePositivity.DifferentialGraded
