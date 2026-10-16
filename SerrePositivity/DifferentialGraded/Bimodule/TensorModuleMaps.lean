module
public import SerrePositivity.DifferentialGraded.Bimodule.TensorComparison
public import SerrePositivity.DifferentialGraded.Bimodule.LeftEvaluation
public import SerrePositivity.DifferentialGraded.Module.LeftMapNaturality
public import SerrePositivity.DifferentialGraded.Category.TensorSmall

/-! # 積dg圏上の左加群射を全Hom自然なbimodule射へ制限する -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B] [Small.{u} C]

/-- 既存の全Hom endを持つ、Bᵒᵖ⊗C上の左dg加群の閉零圏。 -/
abbrev BimoduleTensorModuleCategory := LeftModuleCategory A (DGTensorCategory A Bᵒᵖ C)

namespace BimoduleTensorModule

abbrev underlying (M : BimoduleTensorModuleCategory A B C) : BimoduleTensorFunctor A B C :=
  ForgetEnrichment.to (Complex A) M

def rightMap {M N : BimoduleTensorModuleCategory A B C} (f : M ⟶ N) (c : C) :
    ForgetEnrichment.of (Complex A) ((underlying A B C M).rightAt c) ⟶
      ForgetEnrichment.of (Complex A) ((underlying A B C N).rightAt c) :=
  moduleMorphismMk A B
    (M := (underlying A B C M).rightAt c) (N := (underlying A B C N).rightAt c)
    (fun b => (leftModuleEvaluation A (DGTensorCategory A Bᵒᵖ C) (b, c)).map f)
    (fun x y => by
      have h := congrArg (fun z => dgTensorFirstHom A Bᵒᵖ C c x y ≫ z)
        (leftModuleMorphism_naturality A (DGTensorCategory A Bᵒᵖ C) f (x, c) (y, c))
      exact (Category.assoc _ _ _).trans (h.trans (Category.assoc _ _ _).symm))

@[simp]
lemma rightMap_component {M N : BimoduleTensorModuleCategory A B C} (f : M ⟶ N) (b : B) (c : C) :
    moduleMorphismComponent A B ((underlying A B C M).rightAt c)
      ((underlying A B C N).rightAt c) (rightMap A B C f c) b =
    (leftModuleEvaluation A (DGTensorCategory A Bᵒᵖ C) (op b, c)).map f :=
  moduleMorphismMk_eval A B _ _ b

lemma rightMap_left_naturality {M N : BimoduleTensorModuleCategory A B C} (f : M ⟶ N)
    (c c' : C) :
    (underlying A B C M).toBimodule.toFunctor.map c c' ≫
      moduleHomPostcompose A B ((underlying A B C M).rightAt c)
        ((underlying A B C M).rightAt c') ((underlying A B C N).rightAt c') (rightMap A B C f c') =
    (underlying A B C N).toBimodule.toFunctor.map c c' ≫
      moduleHomPrecompose A B ((underlying A B C M).rightAt c)
        ((underlying A B C N).rightAt c) ((underlying A B C N).rightAt c') (rightMap A B C f c) :=
      by
  apply moduleHom_ext
  intro b
  simp only [Category.assoc]
  rw [moduleHomPostcompose_π, moduleHomPrecompose_π]
  rw [rightMap_component, rightMap_component]
  have h := congrArg (fun z => dgTensorSecondHom A Bᵒᵖ C (op b) c c' ≫ z)
    (leftModuleMorphism_naturality A (DGTensorCategory A Bᵒᵖ C) f (op b, c) (op b, c'))
  have hn : ((underlying A B C M).leftAt b).map c c' ≫
      homPostcompose ((underlying A B C M).obj (op b, c))
        ((leftModuleEvaluation A (DGTensorCategory A Bᵒᵖ C) (op b, c')).map f) =
    ((underlying A B C N).leftAt b).map c c' ≫
      homPrecompose ((leftModuleEvaluation A (DGTensorCategory A Bᵒᵖ C) (op b, c)).map f)
        ((underlying A B C N).obj (op b, c')) :=
    (Category.assoc _ _ _).trans (h.trans (Category.assoc _ _ _).symm)
  have hL := congrArg (fun k : (c ⟶[Complex A] c') ⟶
      homComplex A ((underlying A B C M).obj (op b, c))
        ((underlying A B C M).obj (op b, c')) =>
    k ≫ homPostcompose ((underlying A B C M).obj (op b, c))
      ((leftModuleEvaluation A (DGTensorCategory A Bᵒᵖ C) (op b, c')).map f))
    (BimoduleTensorFunctor.toBimodule_map_π (underlying A B C M) c c' b)
  have hR := congrArg (fun k : (c ⟶[Complex A] c') ⟶
      homComplex A ((underlying A B C N).obj (op b, c))
        ((underlying A B C N).obj (op b, c')) =>
    k ≫ homPrecompose ((leftModuleEvaluation A (DGTensorCategory A Bᵒᵖ C) (op b, c)).map f)
      ((underlying A B C N).obj (op b, c')))
    (BimoduleTensorFunctor.toBimodule_map_π (underlying A B C N) c c' b)
  exact (Category.assoc _ _ _).symm.trans
    (hL.trans (hn.trans (hR.symm.trans (Category.assoc _ _ _))))

end BimoduleTensorModule
end SerrePositivity.DifferentialGraded
