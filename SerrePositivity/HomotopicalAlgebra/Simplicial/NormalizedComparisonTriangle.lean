module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.NormalizedTriangleHorn
public import SerrePositivity.HomotopicalAlgebra.Simplicial.NaturalHornFilling
public import SerrePositivity.HomotopicalAlgebra.Simplicial.ComparisonTriangleTransport

/-! # A comparison triangle strictly natural in the original source parameter

One filling operation is chosen in the original small target K. It
preserves both triangle degeneracies. In particular two identical
comparison edges give the actual degenerate cone triangle. Earlier
independently selected triangles remain relatively comparable.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

namespace SerrePositivity.SimplicialModel.NormalizedComparisonTriangle
open KanComparisonTriangle
variable {T K : SSet.{v}} {f g z : T ⟶ K}
  (F : SSet.Homotopy f z) (G : SSet.Homotopy g z)
  (hK : SSet.modelCategoryQuillen.J.rlp (terminal.from K))

abbrev triangle : SSet.stdSimplex.obj (SimplexCategory.mk 2) ⟶ (ihom T).obj K :=
  NaturalHornFilling.fill K 2 (NormalizedTriangleHorn.section_ K 2 hK) (hornMap F G)

lemma horn_restriction : (SSet.horn 2 2).ι ≫ triangle F G hK = hornMap F G :=
  NaturalHornFilling.fill_restriction K 2 (NormalizedTriangleHorn.section_ K 2 hK) (hornMap F G)
    (NormalizedTriangleHorn.section_restriction K 2 hK)

def build : Data F G where
  triangle := triangle F G hK
  face_zero := by
    rw [← SSet.horn.ι_ι (2 : Fin 3) 0 (by decide), Category.assoc,
      horn_restriction, hornMap_zero]
  face_one := by
    rw [← SSet.horn.ι_ι (2 : Fin 3) 1 (by decide), Category.assoc,
      horn_restriction, hornMap_one]

lemma triangle_reindex {U : SSet.{v}} (j : U ⟶ T) :
    triangle (HomotopyClasses.preHomotopy j F) (HomotopyClasses.preHomotopy j G) hK =
      triangle F G hK ≫ (pre j).app K := by
  have hb := ComparisonTriangleTransport.hornMap_post F G
    (HomotopyClasses.preHomotopy j F) (HomotopyClasses.preHomotopy j G) ((pre j).app K)
    (curry_pre_app j F.h) (curry_pre_app j G.h)
  change NaturalHornFilling.fill K 2 (NormalizedTriangleHorn.section_ K 2 hK) _ = _
  rw [← hb]
  exact NaturalHornFilling.fill_reindex K 2 (NormalizedTriangleHorn.section_ K 2 hK)
    (hornMap F G) j

lemma family_reindex {U : SSet.{v}} (j : U ⟶ T) :
    KanComparisonTriangle.family (HomotopyClasses.preHomotopy j F)
      (HomotopyClasses.preHomotopy j G)
      (build (HomotopyClasses.preHomotopy j F) (HomotopyClasses.preHomotopy j G) hK) =
    j ▷ SSet.stdSimplex.obj (SimplexCategory.mk 2) ≫
      KanComparisonTriangle.family F G (build F G hK) := by
  change uncurry (triangle _ _ hK) = _
  rw [triangle_reindex]
  exact uncurry_pre_app K (triangle F G hK) j

lemma diagonal_triangle : triangle F F hK = (ComparisonTriangleDegeneracy.diagonal F).triangle := by
  have hb := (Data.horn_restriction F F (ComparisonTriangleDegeneracy.diagonal F)).symm
  change NaturalHornFilling.fill K 2 (NormalizedTriangleHorn.section_ K 2 hK) _ = _
  rw [hb]
  exact NaturalHornFilling.fill_degenerate K 2 (NormalizedTriangleHorn.section_ K 2 hK) 0
    (curry F.h) (NormalizedTriangleHorn.section_degeneracy K 2 hK 0)

lemma diagonal_comparison : (comparison F F (build F F hK)).h =
    CategoryTheory.CartesianMonoidalCategory.fst T
      (SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫ f := by
  have ht : (build F F hK).triangle = (ComparisonTriangleDegeneracy.diagonal F).triangle :=
    diagonal_triangle F hK
  change uncurry (SSet.stdSimplex.δ (2 : Fin 3) ≫ (build F F hK).triangle) = _
  rw [ht]
  exact ComparisonTriangleDegeneracy.diagonal_comparison F

def compare (a : Data F G) : RelativeChoiceSpace.FixedBoundaryHomotopy (SSet.horn 2 2).ι
    (hornMap F G) a.triangle (build F G hK).triangle :=
  ComparisonTriangleChoices.fixedBoundaryComparison F G hK a (build F G hK)

end SerrePositivity.SimplicialModel.NormalizedComparisonTriangle
