module
public import SerrePositivity.DifferentialGraded.Bimodule.Evaluation
public import SerrePositivity.DifferentialGraded.Module.LeftClosedMaps

/-! # 閉零bimodule射の両対象評価と左加群としての評価 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.BimoduleCategory
open CategoryTheory MonoidalCategory
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B]

/-- 両対象を固定した値の複体への評価。 -/
def valueEvaluation (b : B) (c : C) : BimoduleCategory A B C ⥤ Complex A :=
  evaluation A B C c ⋙ moduleEvaluation A B b

lemma valueMap_left_naturality {M N : BimoduleCategory A B C} (a : M ⟶ N)
    (b : B) (c c' : C) :
    ((underlying A B C M).leftAt b).map c c' ≫
      homPostcompose ((underlying A B C M).value b c)
        ((valueEvaluation A B C b c').map a) =
    ((underlying A B C N).leftAt b).map c c' ≫
      homPrecompose ((valueEvaluation A B C b c).map a)
        ((underlying A B C N).value b c') := by
  have hp := congrArg (fun k : (c ⟶[Complex A] c') ⟶
      moduleHom A B ((underlying A B C M).rightAt c)
        ((underlying A B C N).rightAt c') =>
    k ≫ moduleHomπ A B ((underlying A B C M).rightAt c)
      ((underlying A B C N).rightAt c') b) (a.property c c')
  simp only [Category.assoc] at hp
  rw [moduleHomPostcompose_π, moduleHomPrecompose_π] at hp
  change (((underlying A B C M).toFunctor.map c c') ≫
      moduleHomπ A B ((underlying A B C M).rightAt c)
        ((underlying A B C M).rightAt c') b) ≫ _ =
    (((underlying A B C N).toFunctor.map c c') ≫
      moduleHomπ A B ((underlying A B C N).rightAt c)
        ((underlying A B C N).rightAt c') b) ≫ _
  exact (Category.assoc _ _ _).trans (hp.trans (Category.assoc _ _ _).symm)

variable [Small.{u} C]

/-- 右対象を固定した、全次数自然な左C加群への評価。 -/
def leftEvaluation (b : B) : BimoduleCategory A B C ⥤ LeftModuleCategory A C where
  obj M := ForgetEnrichment.of (Complex A) ((underlying A B C M).leftAt b)
  map a := leftModuleMorphismMk A C
    (fun c => (valueEvaluation A B C b c).map a) (valueMap_left_naturality A B C a b)
  map_id M := by
    apply leftModuleMorphism_ext A C
    intro c
    rw [leftModuleMorphismMk_eval]
    exact ((valueEvaluation A B C b c).map_id M).trans
      ((leftModuleEvaluation A C c).map_id
        (ForgetEnrichment.of (Complex A) ((underlying A B C M).leftAt b))).symm
  map_comp a d := by
    apply leftModuleMorphism_ext A C
    intro c
    rw [leftModuleMorphismMk_eval, (leftModuleEvaluation A C c).map_comp,
      leftModuleMorphismMk_eval, leftModuleMorphismMk_eval]
    exact (valueEvaluation A B C b c).map_comp a d

@[simp]
lemma leftEvaluation_map_eval {M N : BimoduleCategory A B C} (a : M ⟶ N) (b : B) (c : C) :
    (leftModuleEvaluation A C c).map ((leftEvaluation A B C b).map a) =
      (valueEvaluation A B C b c).map a :=
  leftModuleMorphismMk_eval A C
    (M := (underlying A B C M).leftAt b) (N := (underlying A B C N).leftAt b)
    (fun x => (valueEvaluation A B C b x).map a)
    (valueMap_left_naturality A B C a b) c

end SerrePositivity.DifferentialGraded.BimoduleCategory
