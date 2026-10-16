module
public import SerrePositivity.DifferentialGraded.Derived.Triangulated

/-! # 指定導来圏における実際の加群cone三角形 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Pretriangulated
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

def moduleDerivedConeTriangle {M N : ModuleCategory A D} (f : M ⟶ N) :
    Triangle (DerivedModuleCategory A D) :=
  (moduleToDerived A D).mapTriangle.obj (moduleConeTriangle A D f)

/-- 閉零→K(D)→D(D)の比較により、同じ加群coneの像はdistinguished。 -/
lemma moduleDerivedConeTriangle_distinguished {M N : ModuleCategory A D} (f : M ⟶ N) :
    moduleDerivedConeTriangle A D f ∈ distTriang (DerivedModuleCategory A D) := by
  let e := (Functor.mapTriangleCompIso (moduleToHomotopy A D)
      (moduleHomotopyToDerivedClosed A D)).symm.app (moduleConeTriangle A D f) ≪≫
    (Functor.mapTriangleIso (moduleToHomotopyDerivedIso A D)).app (moduleConeTriangle A D f)
  exact isomorphic_distinguished _
    ((moduleHomotopyToDerivedClosed A D).map_distinguished _
      (moduleHomotopyConeTriangle_distinguished A D f)) _ e.symm

end SerrePositivity.DifferentialGraded
