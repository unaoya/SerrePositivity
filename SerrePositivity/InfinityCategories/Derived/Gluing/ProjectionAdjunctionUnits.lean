module
public import SerrePositivity.InfinityCategories.Derived.Gluing.CProjectionAdjunction
public import SerrePositivity.InfinityCategories.Derived.Gluing.DProjectionAdjunction
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-! 構成した同じ H⁰ 随伴の可逆単位・余単位と、両切断の完全忠実性。 -/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)

lemma dgGluingCProjectionAdjunction_counit (hD : IsDGPretriangulated R D) :
    (dgGluingCProjectionAdjunction R C D M hD).counit =
      (dgGluingCSectionProjectionIso R C D M hD).hom := by
  ext Y
  change (dgGluingCProjectionHomEquiv R C D M hD _ Y).symm (𝟙 _) = _
  rw [dgGluingCProjectionHomEquiv_symm_apply, CategoryTheory.Functor.map_id, Category.id_comp]
  rfl

omit [Small.{u} D] in
lemma dgGluingDProjectionAdjunction_unit (hC : IsDGPretriangulated R C) :
    (dgGluingDProjectionAdjunction R C D M hC).unit =
      (dgGluingDSectionProjectionIso R C D M hC).inv := by
  ext X
  change dgGluingDProjectionHomEquiv R C D M hC X _ (𝟙 _) = _
  rw [dgGluingDProjectionHomEquiv_apply, CategoryTheory.Functor.map_id]
  erw [Category.comp_id]
  rfl

lemma dgGluingCProjectionAdjunction_counit_isIso (hD : IsDGPretriangulated R D) :
    IsIso (dgGluingCProjectionAdjunction R C D M hD).counit := by
  rw [dgGluingCProjectionAdjunction_counit]
  infer_instance

omit [Small.{u} D] in
lemma dgGluingDProjectionAdjunction_unit_isIso (hC : IsDGPretriangulated R C) :
    IsIso (dgGluingDProjectionAdjunction R C D M hC).unit := by
  rw [dgGluingDProjectionAdjunction_unit]
  infer_instance

def dgGluingCSectionHomotopyFullyFaithful (hD : IsDGPretriangulated R D) :
    (dgGluingCSectionHomotopy R C D M hD).FullyFaithful := by
  letI := dgGluingCProjectionAdjunction_counit_isIso R C D M hD
  exact (dgGluingCProjectionAdjunction R C D M hD).fullyFaithfulROfIsIsoCounit

def dgGluingDSectionHomotopyFullyFaithful (hC : IsDGPretriangulated R C) :
    (dgGluingDSectionHomotopy R C D M hC).FullyFaithful := by
  letI := dgGluingDProjectionAdjunction_unit_isIso R C D M hC
  exact (dgGluingDProjectionAdjunction R C D M hC).fullyFaithfulLOfIsIsoUnit

end SerrePositivity.InfinityCategories
