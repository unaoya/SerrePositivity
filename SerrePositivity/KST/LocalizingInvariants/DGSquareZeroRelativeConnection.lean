module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeWitness
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathConnectionNaturality

/-!
概要：相対 class 経路の connection と二つの対角が同じ全二重底射影を持つ。
方針：実 connection の自然性と定数経路での等式を使う。
規約：底の四隅だけで代用しない。使われ方：動く class 正方形の affine 補正。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZero.RelativeWitness
open DGAlgebra
variable {R : Type u} [CommRing R] {B W : Mon (Complex R)} {N : Bimod B B}
  {q : W ⟶ B} {a b : W ⟶ algebra B N} (v : RelativeWitness q N a b)

lemma connection_projection : (v.hom ≫ DGAlgebra.Path.connection R (algebra B N)) ≫
    DGAlgebra.Path.map R (DGAlgebra.Path.map R (projection B N)) =
      (q ≫ DGAlgebra.Path.diagonal R B) ≫ DGAlgebra.Path.diagonal R
        (DGAlgebra.Path.algebra R B) := by
  rw [Category.assoc, ← DGAlgebra.Path.connection_naturality, ← Category.assoc, v.projection_eq,
    Category.assoc, DGAlgebra.Path.diagonal_connection, ← Category.assoc]

lemma outerDiagonal_projection :
    (v.hom ≫ DGAlgebra.Path.diagonal R (DGAlgebra.Path.algebra R (algebra B N))) ≫
    DGAlgebra.Path.map R (DGAlgebra.Path.map R (projection B N)) =
      (q ≫ DGAlgebra.Path.diagonal R B) ≫ DGAlgebra.Path.diagonal R
        (DGAlgebra.Path.algebra R B) := by
  rw [Category.assoc, DGAlgebra.Path.diagonal_naturality, ← Category.assoc, v.projection_eq]

lemma innerDiagonal_projection :
    (v.hom ≫ DGAlgebra.Path.map R (DGAlgebra.Path.diagonal R (algebra B N))) ≫
    DGAlgebra.Path.map R (DGAlgebra.Path.map R (projection B N)) =
      (q ≫ DGAlgebra.Path.diagonal R B) ≫ DGAlgebra.Path.diagonal R
        (DGAlgebra.Path.algebra R B) := by
  rw [Category.assoc, ← DGAlgebra.Path.map_comp, DGAlgebra.Path.diagonal_naturality,
    DGAlgebra.Path.map_comp,
    ← Category.assoc, v.projection_eq, Category.assoc, DGAlgebra.Path.diagonal_naturality]
  simp only [Category.assoc]

end SerrePositivity.KST.LocalizingInvariants.SquareZero.RelativeWitness
