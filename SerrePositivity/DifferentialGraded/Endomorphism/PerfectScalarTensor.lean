module
public import SerrePositivity.DifferentialGraded.Endomorphism.PerfectTensor
public import SerrePositivity.DifferentialGraded.Endomorphism.DerivedScalarTensor

/-! # 実際のPerf tensor制限・U12d・導来係数変更の比較

非flat係数変更の計算条件は受入済みU12f APIと同じ証拠を明示して受け取る。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w w'
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable {A A' : Type u} [CommRing A] [CommRing A'] (φ : A →+* A')
variable (D : Type v) [DGCategory A D] [Small.{u} D]
variable (S : Set D) (E : PerfectDGModuleOver A D S)
variable [HasDerivedCategory.{w} (ModuleCat.{u} A)]
variable [HasDerivedCategory.{w'} (ModuleCat.{u} A')]

/-- Perf上の実際のtensorとU12d評価比較を、導来係数変更後の自然同型として保持する。 -/
def perfectEndomorphismTensorScalarEvaluationIso (d : D) :
    perfectEndomorphismTensorToPerfect A D S E ⋙ perfectModuleInclusion A D S ⋙
        moduleDerivedEvaluation A D d ⋙ ScalarExtension.complexDerivedExtension φ ≅
      perfectModuleInclusion A (EndomorphismObject E.val) Set.univ ⋙
        moduleDerivedTensorRight A (EndomorphismObject E.val)
          ((endomorphismModuleAction A D E.val).leftAt d) ⋙
            ScalarExtension.complexDerivedExtension φ :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (perfectEndomorphismTensorInclusionIso A D S E)
      (moduleDerivedEvaluation A D d ⋙ ScalarExtension.complexDerivedExtension φ) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (perfectModuleInclusion A (EndomorphismObject E.val) Set.univ)
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (endomorphismDerivedTensorEvaluationIso A D E.val d)
          (ScalarExtension.complexDerivedExtension φ) ≪≫ Functor.associator _ _ _)

lemma perfectEndomorphismTensorScalarEvaluationIso_app (d : D)
    (N : PerfectModuleCategory A (EndomorphismObject E.val)) :
    (perfectEndomorphismTensorScalarEvaluationIso φ D S E d).hom.app N =
      (ScalarExtension.complexDerivedExtension φ).map
        ((moduleDerivedEvaluation A D d).map
          ((perfectEndomorphismTensorInclusionIso A D S E).hom.app N)) ≫
      (ScalarExtension.complexDerivedExtension φ).map
        ((endomorphismDerivedTensorEvaluationIso A D E.val d).hom.app N.obj) := by
  simp only [Functor.comp_obj, perfectEndomorphismTensorScalarEvaluationIso,
    Functor.isoWhiskerLeft_trans, Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, NatTrans.comp_app, Functor.associator_inv_app,
    Functor.whiskerRight_app, Functor.comp_map, Functor.associator_hom_app,
    Functor.whiskerLeft_app, Category.id_comp]
  erw [Category.comp_id]
  rfl

/-- Perf対象の指定加群代表上で、実際のPerf tensorを非flat導来係数変更比較へ接続する。 -/
def perfectEndomorphismTensorBaseChange (d : D)
    {N : ModuleCategory A (EndomorphismObject E.val)}
    (hN : modulePerfect A (EndomorphismObject E.val) ((moduleToDerived A _).obj N))
    (P : ModuleProjectiveResolution A (EndomorphismObject E.val) N)
    (hPN : complexKFlat A (BalancedTensor.obj A (EndomorphismObject E.val)
      (ForgetEnrichment.to (Complex A) P.obj) ((endomorphismModuleAction A D E.val).leftAt d)))
    (hP' : moduleRelativeKFlat A' (ScalarExtension.DGBaseChange φ (EndomorphismObject E.val))
      (ScalarExtension.rightModule φ (EndomorphismObject E.val)
        (ForgetEnrichment.to (Complex A) P.obj))) :
    (ScalarExtension.complexDerivedExtension φ).obj
        ((moduleDerivedEvaluation A D d).obj
          ((perfectModuleInclusion A D S).obj
            ((perfectEndomorphismTensorToPerfect A D S E).obj ⟨_, hN⟩))) ≅
      (moduleDerivedTensorRight A' (ScalarExtension.DGBaseChange φ (EndomorphismObject E.val))
        (ScalarExtension.leftModule φ (EndomorphismObject E.val)
          ((endomorphismModuleAction A D E.val).leftAt d))).obj
        ((ScalarExtension.derivedExtension φ (EndomorphismObject E.val)).obj
          ((moduleToDerived A (EndomorphismObject E.val)).obj N)) :=
  (perfectEndomorphismTensorScalarEvaluationIso φ D S E d).app ⟨_, hN⟩ ≪≫
    ScalarExtension.derivedTensorBaseChange φ (EndomorphismObject E.val) P
      ((endomorphismModuleAction A D E.val).leftAt d) hPN hP'

end SerrePositivity.DifferentialGraded
