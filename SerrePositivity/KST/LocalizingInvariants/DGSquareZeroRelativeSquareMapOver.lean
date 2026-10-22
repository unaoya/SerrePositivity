module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeWitnessMapOver
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeWitnessSquare

/-!
概要：相対二重経路を、基底射を持つ実平方零代数射で写す。
方針：全二重経路を後合成し、内外の両端と底の射影を自然性で移す。
規約：各辺の全経路を保持。使われ方：合成自然性比較の零底係数への移送。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZero.RelativeWitnessSquare
variable {R : Type u} [CommRing R] {B C W : Mon (Complex R)}
  {M : Bimod B B} {N : Bimod C C} {q : W ⟶ B}
  (f : B ⟶ C) (k : algebra B M ⟶ algebra C N)
  (hk : k ≫ projection C N = projection B M ≫ f)
  {a b : W ⟶ algebra B M} {v w : RelativeWitness q M a b}
  (h : RelativeWitnessSquare v w)

def mapOver : RelativeWitnessSquare (v.mapOver f k hk) (w.mapOver f k hk) where
  hom := h.hom ≫ DGAlgebra.Path.map R (DGAlgebra.Path.map R k)
  source_eq := by
    rw [Category.assoc, DGAlgebra.Path.map_source, ← Category.assoc, h.source_eq]
    rfl
  target_eq := by
    rw [Category.assoc, DGAlgebra.Path.map_target, ← Category.assoc, h.target_eq]
    rfl
  source_trace := by
    rw [Category.assoc, ← DGAlgebra.Path.map_comp, DGAlgebra.Path.map_source,
      DGAlgebra.Path.map_comp, ← Category.assoc, h.source_trace, Category.assoc,
      DGAlgebra.Path.diagonal_naturality]
    exact (Category.assoc _ _ _).symm
  target_trace := by
    rw [Category.assoc, ← DGAlgebra.Path.map_comp, DGAlgebra.Path.map_target,
      DGAlgebra.Path.map_comp, ← Category.assoc, h.target_trace, Category.assoc,
      DGAlgebra.Path.diagonal_naturality]
    exact (Category.assoc _ _ _).symm
  projection_eq := by
    rw [Category.assoc, ← DGAlgebra.Path.map_comp, ← DGAlgebra.Path.map_comp, hk,
      DGAlgebra.Path.map_comp, DGAlgebra.Path.map_comp, ← Category.assoc, h.projection_eq]
    simp only [Category.assoc, reassoc_of% (DGAlgebra.Path.diagonal_naturality R f),
      DGAlgebra.Path.diagonal_naturality]

end SerrePositivity.KST.LocalizingInvariants.SquareZero.RelativeWitnessSquare
