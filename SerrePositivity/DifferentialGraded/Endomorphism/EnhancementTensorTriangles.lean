module
public import SerrePositivity.DifferentialGraded.Endomorphism.EnhancementTensorComparison
public import SerrePositivity.DifferentialGraded.Endomorphism.EnhancementShiftTriangles

/-! # 実際のenhancement tensorと主Perf比較のshift・三角性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (S : Set D) (E : PerfectDGModuleOver A D S)
variable (hgen : endomorphismThickGeneratesPerfect A D S E)

local instance : (perfectEndomorphismTensorToPerfect A D S E).CommShift ℤ :=
  perfectEndomorphismTensorCommShift A D S E
local instance : (perfectEndomorphismTensorToPerfect A D S E).IsTriangulated :=
  perfectEndomorphismTensorIsTriangulated A D S E

@[instance_reducible]
def perfectEndomorphismTensorDGHomotopyCommShift :
    (perfectEndomorphismTensorDG A D S E).onHomotopy.CommShift ℤ :=
  Functor.CommShift.ofComp (perfectEndomorphismEnhancementTensorComparison A D S E hgen) ℤ

lemma perfectEndomorphismEnhancementTensorComparison_commShift :
    letI := perfectEndomorphismTensorDGHomotopyCommShift A D S E hgen
    NatTrans.CommShift (perfectEndomorphismEnhancementTensorComparison A D S E hgen).hom ℤ :=
  Functor.CommShift.ofComp_compatibility
    (perfectEndomorphismEnhancementTensorComparison A D S E hgen) ℤ

lemma perfectEndomorphismTensorDGHomotopyIsTriangulated :
    letI := perfectEndomorphismTensorDGHomotopyCommShift A D S E hgen
    (perfectEndomorphismTensorDG A D S E).onHomotopy.IsTriangulated := by
  let := perfectEndomorphismTensorDGHomotopyCommShift A D S E hgen
  let := perfectEndomorphismEnhancementTensorComparison_commShift A D S E hgen
  exact (Functor.isTriangulated_iff_comp_right
    (perfectEndomorphismEnhancementTensorComparison A D S E hgen)).2 inferInstance

def perfectEndomorphismEnhancementTensorTriangleSquareIso :
    letI := perfectEndomorphismTensorDGHomotopyCommShift A D S E hgen
    (perfectEndomorphismTensorDG A D S E).onHomotopy.mapTriangle ⋙
        (perfectDGModuleToPerfect A D S).mapTriangle ≅
      (perfectDGModuleToPerfect A (EndomorphismObject E.val) Set.univ).mapTriangle ⋙
        (perfectEndomorphismTensorToPerfect A D S E).mapTriangle := by
  let := perfectEndomorphismTensorDGHomotopyCommShift A D S E hgen
  let := perfectEndomorphismEnhancementTensorComparison_commShift A D S E hgen
  exact (Functor.mapTriangleCompIso _ _).symm ≪≫
    Functor.mapTriangleIso (perfectEndomorphismEnhancementTensorComparison A D S E hgen) ≪≫
      Functor.mapTriangleCompIso _ _

end SerrePositivity.DifferentialGraded
