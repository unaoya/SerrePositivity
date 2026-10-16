module
public import SerrePositivity.DifferentialGraded.Bimodule.LeftEvaluation
public import SerrePositivity.DifferentialGraded.Module.LeftQuasiIso

/-! # 全Hom自然な閉零bimodule圏で局所化する準同型のクラス -/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.DifferentialGraded.BimoduleCategory
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B]

/-- 両対象の各値で複体のquasiIsoとなる射。両作用の全Hom自然性は元の射が保持する。 -/
def quasiIso : MorphismProperty (BimoduleCategory A B C) :=
  fun _ _ f => ∀ (b : B) (c : C), QuasiIso ((valueEvaluation A B C b c).map f)

@[simp]
lemma quasiIso_iff {M N : BimoduleCategory A B C} (f : M ⟶ N) :
    quasiIso A B C f ↔ ∀ b c, QuasiIso ((valueEvaluation A B C b c).map f) := Iff.rfl

lemma quasiIso_eq_iInf : quasiIso A B C =
    ⨅ b : B, ⨅ c : C, (HomologicalComplex.quasiIso (ModuleCat A) (.up ℤ)).inverseImage
      (valueEvaluation A B C b c) := by
  ext M N f
  simp [quasiIso, MorphismProperty.iInf_iff, MorphismProperty.inverseImage]

instance quasiIsoIsMultiplicative : (quasiIso A B C).IsMultiplicative where
  id_mem M b c := by
    rw [CategoryTheory.Functor.map_id]
    infer_instance
  comp_mem f g hf hg b c := by
    have := hf b c
    have := hg b c
    rw [CategoryTheory.Functor.map_comp]
    infer_instance

instance quasiIsoHasTwoOutOfThree : (quasiIso A B C).HasTwoOutOfThreeProperty where
  of_postcomp f g hg hfg b c := by
    have := hg b c
    have : QuasiIso ((valueEvaluation A B C b c).map f ≫
        (valueEvaluation A B C b c).map g) := by
      simpa only [← CategoryTheory.Functor.map_comp] using hfg b c
    exact quasiIso_of_comp_right _ ((valueEvaluation A B C b c).map g)
  of_precomp f g hf hfg b c := by
    have := hf b c
    have : QuasiIso ((valueEvaluation A B C b c).map f ≫
        (valueEvaluation A B C b c).map g) := by
      simpa only [← CategoryTheory.Functor.map_comp] using hfg b c
    exact quasiIso_of_comp_left ((valueEvaluation A B C b c).map f) _

instance quasiIsoStableUnderRetracts : (quasiIso A B C).IsStableUnderRetracts where
  of_retract h hg b c := by
    have := hg b c
    exact quasiIso_of_retractArrow (h.map (valueEvaluation A B C b c))

instance quasiIsoRespectsIso : (quasiIso A B C).RespectsIso := by
  rw [quasiIso_eq_iInf]
  infer_instance

lemma quasiIso_evaluation {M N : BimoduleCategory A B C} {f : M ⟶ N}
    (hf : quasiIso A B C f) (c : C) : moduleQuasiIso A B ((evaluation A B C c).map f) :=
  fun b => hf b c

variable [Small.{u} C]

lemma quasiIso_leftEvaluation {M N : BimoduleCategory A B C} {f : M ⟶ N}
    (hf : quasiIso A B C f) (b : B) :
    leftModuleQuasiIso A C ((leftEvaluation A B C b).map f) := by
  apply (leftModuleQuasiIso_iff A C _).2
  intro c
  rw [leftEvaluation_map_eval]
  exact hf b c

end SerrePositivity.DifferentialGraded.BimoduleCategory
