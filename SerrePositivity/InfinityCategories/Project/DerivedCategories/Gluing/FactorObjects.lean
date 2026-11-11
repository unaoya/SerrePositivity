module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.FactorSubcategories
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Nonempty

/-! 元の二圏の対象を、選んだホモトピー零成分を持つ実充満因子の対象として供給する。 -/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)

/-- 同じ元の C 対象と、選んだホモトピー零 D 成分による C 因子の実対象。 -/
def dgGluingCFactorObject (c : C) (hD : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R D) : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingCFactor R C D M :=
  ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingSeedObject R C D M c (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFactorZeroObject R D hD),
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFactorZeroObject_isZero R D hD⟩

/-- 同じ元の D 対象と、選んだホモトピー零 C 成分による D 因子の実対象。 -/
def dgGluingDFactorObject (d : D) (hC : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R C) : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingDFactor R C D M :=
  ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingSeedObject R C D M (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFactorZeroObject R C hC) d,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingFactorZeroObject_isZero R C hC⟩

lemma dgGluingCFactorObject_projection (c : C) (hD : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R D) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCFactorProjection R C D M).obj (dgGluingCFactorObject R C D M c hD) = c := rfl

omit [Small.{u} D] in
lemma dgGluingDFactorObject_projection (d : D) (hC : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R C) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDFactorProjection R C D M).obj (dgGluingDFactorObject R C D M d hC) = d := rfl

/-- 同じ C 因子の射影は実対象で全射。Hom の擬同型性は別途証明する。 -/
lemma dgGluingCFactorProjection_obj_surjective (hD : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R D) :
    Function.Surjective (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCFactorProjection R C D M).obj :=
  fun c => ⟨dgGluingCFactorObject R C D M c hD, rfl⟩

omit [Small.{u} D] in
lemma dgGluingDFactorProjection_obj_surjective (hC : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R C) :
    Function.Surjective (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDFactorProjection R C D M).obj :=
  fun d => ⟨dgGluingDFactorObject R C D M d hC, rfl⟩

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
