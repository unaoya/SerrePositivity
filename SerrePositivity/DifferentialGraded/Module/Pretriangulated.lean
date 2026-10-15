module
public import SerrePositivity.DifferentialGraded.Module.ConeShiftTriangle
public import SerrePositivity.DifferentialGraded.Module.ConeRotationTriangle

/-! # 全dg自然なconeによるK(D)のpretriangulated構造

三角形のクラスは既存の標準cone三角形の同型閉包そのもの。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Pretriangulated
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleDistinguished_invRotate (T : Triangle (ModuleHomotopyCategory A D))
    (hT : T ∈ moduleDistinguishedTriangles A D) :
    T.invRotate ∈ moduleDistinguishedTriangles A D :=
  moduleDistinguished_isomorphic A D _
    (moduleDistinguished_shift A D _
      (moduleDistinguished_rotate A D _ (moduleDistinguished_rotate A D T hT)) (-1)) _
    ((invRotateIsoRotateRotateShiftFunctorNegOne _).app T)

lemma moduleDistinguished_rotate_iff (T : Triangle (ModuleHomotopyCategory A D)) :
    T ∈ moduleDistinguishedTriangles A D ↔ T.rotate ∈ moduleDistinguishedTriangles A D := by
  constructor
  · exact moduleDistinguished_rotate A D T
  · intro hT
    exact moduleDistinguished_isomorphic A D _
      (moduleDistinguished_invRotate A D T.rotate hT) _ ((triangleRotation _).unitIso.app T)

instance moduleHomotopyPretriangulated : Pretriangulated (ModuleHomotopyCategory A D) where
  distinguishedTriangles := moduleDistinguishedTriangles A D
  isomorphic_distinguished := moduleDistinguished_isomorphic A D
  contractible_distinguished := moduleDistinguished_contractible A D
  distinguished_cocone_triangle := moduleDistinguished_cocone A D
  rotate_distinguished_triangle := moduleDistinguished_rotate_iff A D
  complete_distinguished_triangle_morphism := moduleDistinguished_complete A D

lemma moduleHomotopy_distinguished_iff (T : Triangle (ModuleHomotopyCategory A D)) :
    T ∈ distTriang (ModuleHomotopyCategory A D) ↔
      T ∈ moduleDistinguishedTriangles A D := Iff.rfl

end SerrePositivity.DifferentialGraded
