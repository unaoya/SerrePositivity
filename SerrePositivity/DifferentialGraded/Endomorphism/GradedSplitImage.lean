module
public import SerrePositivity.DifferentialGraded.Endomorphism.GradedSplitOfElements
public import SerrePositivity.DifferentialGraded.Functor.Components

/-! # 主dg加群間のdg関手は全次数分裂を保存する -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) (B : Type w)
  [DGCategory A D] [DGCategory A B] [Small.{u} D] [Small.{u} B]
variable (F : DGFunctor A (RightModule A D) (RightModule A B))

lemma dgModuleFunctor_closedElement {M N : ModuleCategory A D} (f : M ⟶ N) :
    (F.map (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A) N)).f 0
        (endomorphismClosedElement A D f) =
      endomorphismClosedElement A B (F.onClosed.map f) := by
  exact (cycleFromUnit_postcomp (ForgetEnrichment.homTo (Complex A) f)
    (F.map (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A) N))).symm

/-- 微分と可換しない分裂要素も全Hom写像で送り、全斉次作用との可換性を保持する。 -/
def dgModuleFunctorGradedSplit {M N P : ModuleCategory A D} {f : M ⟶ N} {g : N ⟶ P}
    (s : ModuleGradedSplit A D f g) :
    ModuleGradedSplit A B (F.onClosed.map f) (F.onClosed.map g) := by
  have hfa := congrArg (fun z =>
    (F.map (ForgetEnrichment.to (Complex A) M) (ForgetEnrichment.to (Complex A) M)).f 0 z)
    (gradedSplit_inclusion_retraction_element s)
  rw [F.map_forward A, F.map_unitElement A, dgModuleFunctor_closedElement] at hfa
  have hbg := congrArg (fun z =>
    (F.map (ForgetEnrichment.to (Complex A) P) (ForgetEnrichment.to (Complex A) P)).f 0 z)
    (gradedSplit_section_projection_element s)
  rw [F.map_forward A, F.map_unitElement A, dgModuleFunctor_closedElement] at hbg
  have hba := congrArg (fun z =>
    (F.map (ForgetEnrichment.to (Complex A) P) (ForgetEnrichment.to (Complex A) M)).f 0 z)
    (gradedSplit_section_retraction_element s)
  rw [F.map_forward A, map_zero] at hba
  have hdec := congrArg (fun z =>
    (F.map (ForgetEnrichment.to (Complex A) N) (ForgetEnrichment.to (Complex A) N)).f 0 z)
    (gradedSplit_decomposition_element s)
  rw [map_add, F.map_forward A, F.map_forward A, F.map_unitElement A,
    dgModuleFunctor_closedElement, dgModuleFunctor_closedElement] at hdec
  exact moduleGradedSplitOfHomElements A B (F.onClosed.map f) (F.onClosed.map g)
    ((F.map (ForgetEnrichment.to (Complex A) N) (ForgetEnrichment.to (Complex A) M)).f 0
      s.retractionElement)
    ((F.map (ForgetEnrichment.to (Complex A) P) (ForgetEnrichment.to (Complex A) N)).f 0
      s.sectionElement)
    hfa hbg hba hdec (by
      rw [← CategoryTheory.Functor.map_comp, s.inclusion_projection,
        CategoryTheory.Functor.map_zero])

end SerrePositivity.DifferentialGraded
