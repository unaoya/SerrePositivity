module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.CompositionInputDiagonalFibration

/-! 入力の指定に沿って同時評価を引き戻しても、対角評価は Kan fibration。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
variable {E I Q A : SSet.{u}} (p : E ⟶ I) (d : E ⟶ Q) (a : A ⟶ I)

def dgGluingRestrictedInputPair : pullback p a ⟶ A ⊗ Q :=
  lift (pullback.snd p a) (pullback.fst p a ≫ d)

lemma dgGluingRestrictedInputPair_isPullback :
    IsPullback (pullback.fst p a) (dgGluingRestrictedInputPair p d a)
      (lift p d) (a ⊗ₘ 𝟙 Q) := by
  have hc : pullback.fst p a ≫ lift p d =
      dgGluingRestrictedInputPair p d a ≫ (a ⊗ₘ 𝟙 Q) := by
    apply CartesianMonoidalCategory.hom_ext <;>
      simp only [dgGluingRestrictedInputPair, Category.assoc, lift_fst, lift_snd,
        tensorHom_fst, tensorHom_snd, lift_fst_assoc, Category.comp_id, pullback.condition]
  refine IsPullback.mk' hc ?_ ?_
  · intro T f g hf hg
    apply pullback.hom_ext
    · exact hf
    · have hh := congrArg (fun k => k ≫ fst A Q) hg
      simpa only [dgGluingRestrictedInputPair, Category.assoc, lift_fst] using hh
  · intro T f g h
    have hfirst : f ≫ p = (g ≫ fst A Q) ≫ a := by
      have hh := congrArg (fun k => k ≫ fst I Q) h
      simpa only [Category.assoc, lift_fst, tensorHom_fst] using hh
    have hdiag : f ≫ d = g ≫ snd A Q := by
      have hh := congrArg (fun k => k ≫ snd I Q) h
      simpa only [Category.assoc, lift_snd, tensorHom_snd, Category.comp_id] using hh
    refine ⟨pullback.lift f (g ≫ fst A Q) hfirst, pullback.lift_fst _ _ _, ?_⟩
    apply CartesianMonoidalCategory.hom_ext
    · simp only [dgGluingRestrictedInputPair, Category.assoc, lift_fst, pullback.lift_snd]
    · simpa only [dgGluingRestrictedInputPair, Category.assoc, lift_snd,
        pullback.lift_fst_assoc] using hdiag

lemma dgGluingRestrictedInputPair_fibration [Fibration (lift p d)] :
    Fibration (dgGluingRestrictedInputPair p d a) := by
  apply (SSet.modelCategoryQuillen.fibration_iff _).2
  intro B C i hi
  have : HasLiftingProperty i (lift p d) :=
    (SSet.modelCategoryQuillen.fibration_iff _).1 inferInstance i hi
  exact (dgGluingRestrictedInputPair_isPullback p d a).hasLiftingProperty i

lemma dgGluingRestrictedDiagonal_fibration [KanComplex A] [Fibration (lift p d)] :
    Fibration (pullback.fst p a ≫ d) := by
  have hpair : Fibration (dgGluingRestrictedInputPair p d a) :=
    dgGluingRestrictedInputPair_fibration p d a
  have hsnd : Fibration (snd A Q) := by
    rw [SSet.modelCategoryQuillen.fibration_iff]
    intro B C i hi
    simp only [J, MorphismProperty.iSup_iff] at hi
    obtain ⟨n, ⟨j⟩⟩ := hi
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalProductProjection_hasLiftingProperty_horn A Q n j
  have hh : dgGluingRestrictedInputPair p d a ≫ snd A Q = pullback.fst p a ≫ d :=
    CartesianMonoidalCategory.lift_snd _ _
  rw [← hh]
  infer_instance

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
