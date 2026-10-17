module
public import SerrePositivity.DifferentialGraded.Endomorphism.ProjectiveImage
public import SerrePositivity.DifferentialGraded.Perfect.EnhancementDerivedComparison

/-! # 射影的主K部分圏を介したU13のambient包含のshift整合性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

abbrev projectiveModuleHomotopyCategory := (moduleHomotopyProjectiveLocus A D).FullSubcategory

def projectiveModuleHomotopyToDerived :
    projectiveModuleHomotopyCategory A D ⥤ DerivedModuleCategory A D :=
  (moduleHomotopyProjectiveLocus A D).ι ⋙ moduleHomotopyToDerivedClosed A D

instance projectiveModuleHomotopyToDerivedFull :
    (projectiveModuleHomotopyToDerived A D).Full where
  map_surjective {X Y} f := by
    obtain ⟨g, hg⟩ := (moduleProjectiveLocalization_map_bijective A D X.property Y.obj).2 f
    exact ⟨ObjectProperty.homMk g, hg⟩

instance projectiveModuleHomotopyToDerivedFaithful :
    (projectiveModuleHomotopyToDerived A D).Faithful where
  map_injective {X Y} _f _g h :=
    (moduleHomotopyProjectiveLocus A D).hom_ext
      ((moduleProjectiveLocalization_map_bijective A D X.property Y.obj).1 h)

instance projectiveModuleHomotopyToDerivedCommShift :
    (projectiveModuleHomotopyToDerived A D).CommShift ℤ := by
  unfold projectiveModuleHomotopyToDerived
  infer_instance

instance projectiveModuleHomotopyToDerivedIsTriangulated :
    (projectiveModuleHomotopyToDerived A D).IsTriangulated := by
  unfold projectiveModuleHomotopyToDerived
  infer_instance

def perfectDGModuleInclusionProjectiveHomotopy (S : Set D) :
    PerfectDGHomotopyCategoryOver A D S ⥤ projectiveModuleHomotopyCategory A D :=
  (moduleHomotopyProjectiveLocus A D).lift (perfectDGModuleInclusion A D S).onHomotopy
    (fun X => (ForgetEnrichment.to (Complex A) X.as).property.1)

def perfectDGModuleInclusionProjectiveHomotopyIso (S : Set D) :
    perfectDGModuleInclusionProjectiveHomotopy A D S ⋙
        (moduleHomotopyProjectiveLocus A D).ι ≅
      (perfectDGModuleInclusion A D S).onHomotopy :=
  (moduleHomotopyProjectiveLocus A D).liftCompιIso _
    (fun X => (ForgetEnrichment.to (Complex A) X.as).property.1)

def perfectDGModuleInclusionProjectiveHomotopyDerivedIso (S : Set D) :
    perfectDGModuleInclusionProjectiveHomotopy A D S ⋙ projectiveModuleHomotopyToDerived A D ≅
      perfectDGModuleToDerived A D S :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (perfectDGModuleInclusionProjectiveHomotopyIso A D S)
      (moduleHomotopyToDerivedClosed A D)

@[instance_reducible]
def perfectDGModuleInclusionProjectiveHomotopyCommShift (S : Set D) :
    (perfectDGModuleInclusionProjectiveHomotopy A D S).CommShift ℤ :=
  Functor.CommShift.ofComp (perfectDGModuleInclusionProjectiveHomotopyDerivedIso A D S) ℤ

lemma perfectDGModuleInclusionProjectiveHomotopyIsTriangulated (S : Set D) :
    letI := perfectDGModuleInclusionProjectiveHomotopyCommShift A D S
    (perfectDGModuleInclusionProjectiveHomotopy A D S).IsTriangulated := by
  let := perfectDGModuleInclusionProjectiveHomotopyCommShift A D S
  let := Functor.CommShift.ofComp_compatibility
    (perfectDGModuleInclusionProjectiveHomotopyDerivedIso A D S) ℤ
  exact (Functor.isTriangulated_iff_comp_right
    (perfectDGModuleInclusionProjectiveHomotopyDerivedIso A D S)).2 inferInstance

@[instance_reducible]
def perfectDGModuleInclusionHomotopyCommShift (S : Set D) :
    (perfectDGModuleInclusion A D S).onHomotopy.CommShift ℤ := by
  letI := perfectDGModuleInclusionProjectiveHomotopyCommShift A D S
  exact Functor.CommShift.ofIso (perfectDGModuleInclusionProjectiveHomotopyIso A D S) ℤ

lemma perfectDGModuleInclusionHomotopyIsTriangulated (S : Set D) :
    letI := perfectDGModuleInclusionHomotopyCommShift A D S
    (perfectDGModuleInclusion A D S).onHomotopy.IsTriangulated := by
  let := perfectDGModuleInclusionProjectiveHomotopyCommShift A D S
  let := perfectDGModuleInclusionHomotopyCommShift A D S
  let := perfectDGModuleInclusionProjectiveHomotopyIsTriangulated A D S
  let := Functor.CommShift.ofIso_compatibility
    (perfectDGModuleInclusionProjectiveHomotopyIso A D S) ℤ
  have : (perfectDGModuleInclusionProjectiveHomotopy A D S ⋙
      (moduleHomotopyProjectiveLocus A D).ι).IsTriangulated := inferInstance
  exact Functor.isTriangulated_of_iso (perfectDGModuleInclusionProjectiveHomotopyIso A D S)

end SerrePositivity.DifferentialGraded
