module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGPretriangulated
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence

/-! 元の前三角 dg 圏のホモトピー零対象を、代表加群の零性から選ぶ。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]

/-- 実 dg 対象が H⁰ で零であるという対象条件。 -/
def dgGluingFactorIsZero (x : C) : Prop :=
  IsZero ((toHomotopy R C).obj (ForgetEnrichment.of (Complex R) x))

/-- 全 Hom Yoneda 同型により、元の H⁰ の零性は代表加群の K の零性と同値。 -/
lemma dgGluingFactorIsZero_iff_representable (x : C) :
    dgGluingFactorIsZero R C x ↔
      IsZero ((moduleToHomotopy R C).obj
        (ForgetEnrichment.of (Complex R) (representable R x))) := by
  let F := dgYoneda R C
  have hF (x y : C) : IsIso (F.map x y) := by
    change IsIso (dgYonedaIso R x (representable R y)).inv
    infer_instance
  let := F.onHomotopy_full_of_homIso hF
  let := F.onHomotopy_faithful_of_homIso hF
  constructor
  · exact F.onHomotopy.map_isZero
  · exact IsZero.of_full_of_faithful_of_isZero F.onHomotopy
      ((toHomotopy R C).obj (ForgetEnrichment.of (Complex R) x))

/-- 元の前三角性から、実対象型内のホモトピー零対象の存在を回収。 -/
lemma dgGluingFactorZero_exists (hC : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R C) :
    ∃ x : C, dgGluingFactorIsZero R C x := by
  let := hC
  have hz : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableHomotopyProperty R C
      ((moduleToHomotopy R C).obj (moduleZero R C)) :=
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableHomotopyProperty R C).prop_of_isZero
      ((moduleToHomotopy R C).map_isZero (moduleZero_isZero R C))
  obtain ⟨x, ⟨e⟩⟩ := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRepresentableHomotopyProperty_iff R C _).1 hz
  refine ⟨x, (dgGluingFactorIsZero_iff_representable R C x).2 ?_⟩
  exact ((moduleToHomotopy R C).map_isZero (moduleZero_isZero R C)).of_iso e.symm

def dgGluingFactorZeroObject (hC : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R C) : C :=
  Classical.choose (dgGluingFactorZero_exists R C hC)

lemma dgGluingFactorZeroObject_isZero (hC : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R C) :
    dgGluingFactorIsZero R C (dgGluingFactorZeroObject R C hC) :=
  Classical.choose_spec (dgGluingFactorZero_exists R C hC)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
