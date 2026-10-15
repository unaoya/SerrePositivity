module
public import SerrePositivity.DifferentialGraded.Module.DistinguishedTriangles

/-! # coneによる三角形のクラスの受入検査 -/
@[expose] public section
universe u v
open CategoryTheory Pretriangulated SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

example (M : ModuleHomotopyCategory A D) :
    contractibleTriangle M ∈ moduleDistinguishedTriangles A D :=
  moduleDistinguished_contractible A D M

example (T : Triangle (ModuleHomotopyCategory A D))
    (hT : T ∈ moduleDistinguishedTriangles A D) : T.mor₁ ≫ T.mor₂ = 0 :=
  moduleDistinguished_comp_zero₁₂ A D T hT

#print axioms moduleHomotopyIdentityConeTriangleIso
#print axioms moduleDistinguishedTriangles
#print axioms moduleHomotopyConeTriangle_distinguished
#print axioms moduleDistinguished_isomorphic
#print axioms moduleDistinguished_cocone
#print axioms moduleDistinguished_contractible
#print axioms moduleDistinguished_complete
#print axioms moduleDistinguished_comp_zero₁₂
