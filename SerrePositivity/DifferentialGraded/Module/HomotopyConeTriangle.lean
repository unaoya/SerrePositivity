module
public import SerrePositivity.DifferentialGraded.Module.ConeHomotopyMap
public import SerrePositivity.DifferentialGraded.Module.ShiftHomotopy

/-! # K(D)の標準cone三角形とホモトピー可換squareの補完 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Pretriangulated
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

abbrev moduleHomotopyConeTriangle {M N : ModuleCategory A D} (f : M ⟶ N) :
    Triangle (ModuleHomotopyCategory A D) :=
  (moduleToHomotopy A D).mapTriangle.obj (moduleConeTriangle A D f)

/-- 全dg自然なホモトピー可換squareからK(D)の三角形の射を得る。 -/
def moduleHomotopyConeTriangleMap {M N M' N' : ModuleCategory A D}
    (f : M ⟶ N) (g : M' ⟶ N') (u : M ⟶ M') (v : N ⟶ N')
    (h : ModuleHomotopy A D (f ≫ v) (u ≫ g)) :
    moduleHomotopyConeTriangle A D f ⟶ moduleHomotopyConeTriangle A D g where
  hom₁ := (moduleToHomotopy A D).map u
  hom₂ := (moduleToHomotopy A D).map v
  hom₃ := (moduleToHomotopy A D).map (moduleConeMapOfHomotopy A D f g u v h)
  comm₁ := by
    change (moduleToHomotopy A D).map f ≫ (moduleToHomotopy A D).map v =
      (moduleToHomotopy A D).map u ≫ (moduleToHomotopy A D).map g
    rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp]
    exact (moduleToHomotopy_map_eq_iff A D _ _).2 ⟨h⟩
  comm₂ := by
    change (moduleToHomotopy A D).map (moduleConeInr A D f) ≫
      (moduleToHomotopy A D).map (moduleConeMapOfHomotopy A D f g u v h) =
        (moduleToHomotopy A D).map v ≫ (moduleToHomotopy A D).map (moduleConeInr A D g)
    rw [← CategoryTheory.Functor.map_comp, moduleConeMapOfHomotopy_inr,
      CategoryTheory.Functor.map_comp]
  comm₃ := by
    dsimp [moduleHomotopyConeTriangle, moduleConeTriangle, Functor.mapTriangle]
    let Q := moduleToHomotopy A D
    have hn := (Q.commShiftIso (1 : ℤ)).hom.naturality u
    change Q.map (u⟦(1 : ℤ)⟧') ≫ (Q.commShiftIso (1 : ℤ)).hom.app M' =
      (Q.commShiftIso (1 : ℤ)).hom.app M ≫ (Q.map u)⟦(1 : ℤ)⟧' at hn
    change (Q.map (moduleConeConnecting A D f) ≫
      (Q.commShiftIso (1 : ℤ)).hom.app M) ≫ (Q.map u)⟦(1 : ℤ)⟧' =
        Q.map (moduleConeMapOfHomotopy A D f g u v h) ≫
          Q.map (moduleConeConnecting A D g) ≫ (Q.commShiftIso (1 : ℤ)).hom.app M'
    rw [Category.assoc, ← hn, ← Category.assoc, ← CategoryTheory.Functor.map_comp,
      moduleConeMapOfHomotopy_connecting, CategoryTheory.Functor.map_comp, Category.assoc]

/-- K(D)で可換なsquareは標準cone三角形の射へ補完できる。 -/
lemma moduleHomotopyConeTriangle_complete {M N M' N' : ModuleCategory A D}
    (f : M ⟶ N) (g : M' ⟶ N')
    (a : (moduleToHomotopy A D).obj M ⟶ (moduleToHomotopy A D).obj M')
    (b : (moduleToHomotopy A D).obj N ⟶ (moduleToHomotopy A D).obj N')
    (comm : (moduleToHomotopy A D).map f ≫ b = a ≫ (moduleToHomotopy A D).map g) :
    ∃ t : moduleHomotopyConeTriangle A D f ⟶ moduleHomotopyConeTriangle A D g,
      t.hom₁ = a ∧ t.hom₂ = b := by
  obtain ⟨a, rfl⟩ := (moduleToHomotopy A D).map_surjective a
  obtain ⟨b, rfl⟩ := (moduleToHomotopy A D).map_surjective b
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp] at comm
  obtain ⟨h⟩ := (moduleToHomotopy_map_eq_iff A D _ _).1 comm
  exact ⟨moduleHomotopyConeTriangleMap A D f g a b h, rfl, rfl⟩

end SerrePositivity.DifferentialGraded
