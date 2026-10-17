module
public import SerrePositivity.DifferentialGraded.Bimodule.SemifreeResolution

/-! # 準同型による増大の後合成でsemifree解像度の終域を替える -/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.DifferentialGraded.BimoduleSemifreeResolution
open CategoryTheory
variable (A : Type u) [CommRing A] (B : Type v) [DGCategory A B] [Small.{u} B]
  (C : Type w) [DGCategory A C] [Small.{u} C]

/-- sourceとfiltrationを保持し、増大を指定準同型で後合成する。 -/
def postcompose {M N : BimoduleCategory A B C} (R : BimoduleSemifreeResolution A B C M)
    (f : M ⟶ N) (hf : BimoduleCategory.quasiIso A B C f) :
    BimoduleSemifreeResolution A B C N where
  source := R.source
  filtration := R.filtration
  π := R.π ≫ f
  quasiIso := (BimoduleCategory.quasiIso A B C).comp_mem _ _ R.quasiIso hf

lemma postcompose_obj {M N : BimoduleCategory A B C} (R : BimoduleSemifreeResolution A B C M)
    (f : M ⟶ N) (hf : BimoduleCategory.quasiIso A B C f) :
    (postcompose A B C R f hf).obj = R.obj := rfl

end SerrePositivity.DifferentialGraded.BimoduleSemifreeResolution
