module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeWitnessRectangleBoundary

/-!
概要：固定端点の class 二重経路の両経路に、同じ元の相対経路を前置する。
方針：元の前置経路の外対角と定数二重経路を、実 affine 演算で加減する。
規約：全経路の乗法性・全底射影を保持。使われ方：三経路貼合せの輪郭比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Preadditive
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZero.RelativeWitnessSquare
variable {R : Type u} [CommRing R] {B W : Mon (Complex R)} {N : Bimod B B}
  {q : W ⟶ B} {x a b : W ⟶ algebra B N}
  {v w : RelativeWitness q N a b} (u : RelativeWitness q N x a) (h : RelativeWitnessSquare v w)

/-- 前置後の二重経路の実代数射。 -/
def prependHom : W ⟶ DGAlgebra.Path.algebra R (DGAlgebra.Path.algebra R (algebra B N)) :=
  affineDoublePathHom R N
    (u.hom ≫ DGAlgebra.Path.diagonal R (DGAlgebra.Path.algebra R (algebra B N)))
    ((RelativeWitness.refl a u.target_projection).hom ≫
      DGAlgebra.Path.diagonal R (DGAlgebra.Path.algebra R (algebra B N))) h.hom
    (u.outerDiagonal_projection.trans
      (RelativeWitness.refl a u.target_projection).outerDiagonal_projection.symm)
    (u.outerDiagonal_projection.trans h.projection_eq.symm)

lemma prependHom_post_linear {D : Mon (Complex R)}
    (k : DGAlgebra.Path.algebra R (DGAlgebra.Path.algebra R (algebra B N)) ⟶ D) :
    (prependHom u h ≫ k).hom =
    ((u.hom ≫ DGAlgebra.Path.diagonal R (DGAlgebra.Path.algebra R (algebra B N))) ≫ k).hom -
    (((a ≫ DGAlgebra.Path.diagonal R (algebra B N)) ≫
      DGAlgebra.Path.diagonal R (DGAlgebra.Path.algebra R (algebra B N))) ≫ k).hom +
    (h.hom ≫ k).hom := by
  rw [Mon.comp_hom']
  change (affineDoublePathHom R N _ _ _ _ _).hom ≫ k.hom = _
  rw [affineDoublePathHom_linear]
  simp only [sub_comp, add_comp, Mon.comp_hom']
  rfl

/-- 同じ前置経路を保つ固定端点二重経路。 -/
def prepend : RelativeWitnessSquare (u.comp v) (u.comp w) where
  hom := prependHom u h
  source_eq := by
    apply Mon.Hom.ext
    rw [prependHom_post_linear]
    simp only [Category.assoc, DGAlgebra.Path.diagonal_source, Category.comp_id, h.source_eq]
    exact (RelativeWitness.comp_hom_linear u v).symm
  target_eq := by
    apply Mon.Hom.ext
    rw [prependHom_post_linear]
    simp only [Category.assoc, DGAlgebra.Path.diagonal_target, Category.comp_id, h.target_eq]
    exact (RelativeWitness.comp_hom_linear u w).symm
  source_trace := by
    apply Mon.Hom.ext
    rw [prependHom_post_linear]
    simp only [Category.assoc, DGAlgebra.Path.diagonal_naturality,
      reassoc_of% u.source_eq, reassoc_of% (DGAlgebra.Path.diagonal_source R (algebra B N)),
      h.source_trace]
    abel
  target_trace := by
    apply Mon.Hom.ext
    rw [prependHom_post_linear]
    simp only [Category.assoc, DGAlgebra.Path.diagonal_naturality,
      reassoc_of% u.target_eq, reassoc_of% (DGAlgebra.Path.diagonal_target R (algebra B N)),
      h.target_trace]
    abel
  projection_eq := (affineDoublePathHom_projection R N _ _ _ _ _).trans u.outerDiagonal_projection

end SerrePositivity.KST.LocalizingInvariants.SquareZero.RelativeWitnessSquare
