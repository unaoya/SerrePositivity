module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.KanActualHomotopy
public import SerrePositivity.HomotopicalAlgebra.Simplicial.SimplexParameterHom

/-! # A comparison triangle retains two selected whole interval families

Both given comparisons have the same final map. The missing edge is a
comparison of their initial maps, and the two original edges are fixed.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

namespace SerrePositivity.SimplicialModel.KanComparisonTriangle
variable {T K : SSet.{v}} {f g z : T ⟶ K}
  (F : SSet.Homotopy f z) (G : SSet.Homotopy g z)

structure Data where
  triangle : SSet.stdSimplex.obj (SimplexCategory.mk 2) ⟶ (ihom T).obj K
  face_zero : SSet.stdSimplex.δ (0 : Fin 3) ≫ triangle = curry G.h
  face_one : SSet.stdSimplex.δ (1 : Fin 3) ≫ triangle = curry F.h

variable (hK : SSet.modelCategoryQuillen.J.rlp (terminal.from K))

def build : Data F G := by
  have hc : SSet.stdSimplex.δ (0 : Fin 2) ≫ curry G.h =
      SSet.stdSimplex.δ (0 : Fin 2) ≫ curry F.h :=
    (LargeParameterSquare.edge_one G).trans (LargeParameterSquare.edge_one F).symm
  let ht := KanTwoHornLift.exists_triangle (terminal.from ((ihom T).obj K))
    (SimplexParameterHom.native_kan T K hK) (curry G.h) (curry F.h)
    (terminal.from _) hc (terminal.hom_ext _ _) (terminal.hom_ext _ _)
  exact ⟨ht.choose, ht.choose_spec.1, ht.choose_spec.2.1⟩

variable (d : Data F G)

abbrev family : T ⊗ SSet.stdSimplex.obj (SimplexCategory.mk 2) ⟶ K := uncurry d.triangle

lemma family_zero : T ◁ SSet.stdSimplex.δ (0 : Fin 3) ≫ family F G d = G.h := by
  rw [family, ← uncurry_natural_left, d.face_zero, uncurry_curry]

lemma family_one : T ◁ SSet.stdSimplex.δ (1 : Fin 3) ≫ family F G d = F.h := by
  rw [family, ← uncurry_natural_left, d.face_one, uncurry_curry]

private lemma vertex_zero :
    SSet.stdSimplex.δ.{v} (1 : Fin 2) ≫ SSet.stdSimplex.δ (2 : Fin 3) =
      SSet.stdSimplex.δ (1 : Fin 2) ≫ SSet.stdSimplex.δ (1 : Fin 3) := by
  change SSet.stdSimplex.map _ ≫ SSet.stdSimplex.map _ =
    SSet.stdSimplex.map _ ≫ SSet.stdSimplex.map _
  rw [← SSet.stdSimplex.map_comp, ← SSet.stdSimplex.map_comp]
  exact congrArg SSet.stdSimplex.map (by decide)

private lemma vertex_one :
    SSet.stdSimplex.δ.{v} (0 : Fin 2) ≫ SSet.stdSimplex.δ (2 : Fin 3) =
      SSet.stdSimplex.δ (1 : Fin 2) ≫ SSet.stdSimplex.δ (0 : Fin 3) := by
  change SSet.stdSimplex.map _ ≫ SSet.stdSimplex.map _ =
    SSet.stdSimplex.map _ ≫ SSet.stdSimplex.map _
  rw [← SSet.stdSimplex.map_comp, ← SSet.stdSimplex.map_comp]
  exact congrArg SSet.stdSimplex.map (by decide)

def comparison : SSet.Homotopy f g :=
  CurriedHomotopy.ofEdge (SSet.stdSimplex.δ (2 : Fin 3) ≫ d.triangle)
    (by rw [← Category.assoc, vertex_zero, Category.assoc, d.face_one]
        exact LargeParameterSquare.edge_zero F)
    (by rw [← Category.assoc, vertex_one, Category.assoc, d.face_zero]
        exact LargeParameterSquare.edge_zero G)

lemma family_two : T ◁ SSet.stdSimplex.δ (2 : Fin 3) ≫ family F G d =
    (comparison F G d).h := by
  change _ = uncurry (SSet.stdSimplex.δ (2 : Fin 3) ≫ d.triangle)
  rw [uncurry_natural_left]

end SerrePositivity.SimplicialModel.KanComparisonTriangle
