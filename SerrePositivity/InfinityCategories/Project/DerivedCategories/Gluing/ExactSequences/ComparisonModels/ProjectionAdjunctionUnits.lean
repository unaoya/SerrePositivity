module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ComparisonModels.CProjectionAdjunction
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.ExactSequences.ComparisonModels.DProjectionAdjunction
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-! 構成した同じ H⁰ 随伴の可逆単位・余単位と、両切断の完全忠実性。 -/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)

lemma dgGluingCProjectionAdjunction_counit (hD : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R D) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCProjectionAdjunction R C D M hD).counit =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCSectionProjectionIso R C D M hD).hom := by
  ext Y
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCProjectionHomEquiv R C D M hD _ Y).symm (𝟙 _) = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCProjectionHomEquiv_symm_apply, CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

omit [Small.{u} D] in
lemma dgGluingDProjectionAdjunction_unit (hC : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R C) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDProjectionAdjunction R C D M hC).unit =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDSectionProjectionIso R C D M hC).inv := by
  ext X
  change _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDProjectionHomEquiv R C D M hC X _ (𝟙 _) = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDProjectionHomEquiv_apply, CategoryTheory.Functor.map_id]
  erw [Category.comp_id]
  rfl

lemma dgGluingCProjectionAdjunction_counit_isIso (hD : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R D) :
    IsIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCProjectionAdjunction R C D M hD).counit := by
  rw [dgGluingCProjectionAdjunction_counit]
  infer_instance

omit [Small.{u} D] in
lemma dgGluingDProjectionAdjunction_unit_isIso (hC : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R C) :
    IsIso (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDProjectionAdjunction R C D M hC).unit := by
  rw [dgGluingDProjectionAdjunction_unit]
  infer_instance

def dgGluingCSectionHomotopyFullyFaithful (hD : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R D) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCSectionHomotopy R C D M hD).FullyFaithful := by
  letI := dgGluingCProjectionAdjunction_counit_isIso R C D M hD
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCProjectionAdjunction R C D M hD).fullyFaithfulROfIsIsoCounit

def dgGluingDSectionHomotopyFullyFaithful (hC : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R C) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDSectionHomotopy R C D M hC).FullyFaithful := by
  letI := dgGluingDProjectionAdjunction_unit_isIso R C D M hC
  exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingDProjectionAdjunction R C D M hC).fullyFaithfulLOfIsIsoUnit

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
