module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.HomSpaces.HomotopyRepresentations.ConeHomotopyRepresentation
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.Comparison.TriangleThirdTransport

/-! 選んだ実 gluing 円錐代表を第三対象に持つ、K(Gluing) の実 distinguished 三角形。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Pretriangulated DifferentialGraded
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (A B : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
  (f : ForgetEnrichment.of (Complex R) A ⟶ ForgetEnrichment.of (Complex R) B)
  (hC : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R C) (hD : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.IsDGPretriangulated R D)
local notation "G" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M
local notation "K" => moduleToHomotopy R G
local notation "yf" => CategoryTheory.Functor.map (DGFunctor.onClosed (dgYoneda R G)) f

def dgGluingChosenConeModuleHomotopyIso :
    (K).obj (moduleCone R G yf) ≅ (K).obj (ForgetEnrichment.of (Complex R)
      (representable R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeObject R C D M A B f hC hD))) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeModuleHomotopyIso R C D M A B f
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingChooseConeRepresentative R C A.left B.left
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeLeftArrow R C D M A B f) hC)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingChooseConeRepresentative R D A.right B.right
      ((dgYoneda R D).onClosed.map (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingConeRightArrow R C D M A B f)) hD)

local notation "T" => moduleHomotopyConeTriangle R G yf
local notation "e" => dgGluingChosenConeModuleHomotopyIso R C D M A B f hC hD

/-- 順射は同じ Yoneda 射、第三対象は同じ選んだ実円錐対象の代表加群。 -/
def dgGluingRepresentableConeTriangle : Triangle (ModuleHomotopyCategory R G) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleThirdTransport T e

lemma dgGluingRepresentableConeTriangle_distinguished :
    dgGluingRepresentableConeTriangle R C D M A B f hC hD ∈
      distTriang (ModuleHomotopyCategory R G) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingTriangleThirdTransport_distinguished T
    (moduleHomotopyConeTriangle_distinguished R G yf) e

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
