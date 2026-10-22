module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeWitnessRectangleBoundary

/-!
概要：固定端点の class 二重経路の両経路に同じ元の相対経路を後置する。
方針：元の二重経路・中点の定数二重経路・後置経路を実 affine 演算で加減する。
規約：全経路の乗法性と底射影を保持。使われ方：元の W を保つ右 class 比較。
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
  {q : W ⟶ B} {a b c : W ⟶ algebra B N}
  {v w : RelativeWitness q N a b} (h : RelativeWitnessSquare v w) (u : RelativeWitness q N b c)

def appendHom : W ⟶ DGAlgebra.Path.algebra R (DGAlgebra.Path.algebra R (algebra B N)) :=
  affineDoublePathHom R N h.hom
    ((RelativeWitness.refl b u.source_projection).hom ≫
      DGAlgebra.Path.diagonal R (DGAlgebra.Path.algebra R (algebra B N)))
    (u.hom ≫ DGAlgebra.Path.diagonal R (DGAlgebra.Path.algebra R (algebra B N)))
    (h.projection_eq.trans
      (RelativeWitness.refl b u.source_projection).outerDiagonal_projection.symm)
    (h.projection_eq.trans u.outerDiagonal_projection.symm)

lemma appendHom_post_linear {D : Mon (Complex R)}
    (k : DGAlgebra.Path.algebra R (DGAlgebra.Path.algebra R (algebra B N)) ⟶ D) :
    (appendHom h u ≫ k).hom = (h.hom ≫ k).hom -
      (((b ≫ DGAlgebra.Path.diagonal R (algebra B N)) ≫
        DGAlgebra.Path.diagonal R (DGAlgebra.Path.algebra R (algebra B N))) ≫ k).hom +
      ((u.hom ≫ DGAlgebra.Path.diagonal R (DGAlgebra.Path.algebra R (algebra B N))) ≫ k).hom := by
  rw [Mon.comp_hom']
  change (affineDoublePathHom R N _ _ _ _ _).hom ≫ k.hom = _
  rw [affineDoublePathHom_linear]
  simp only [sub_comp, add_comp, Mon.comp_hom']
  rfl

def append : RelativeWitnessSquare (v.comp u) (w.comp u) where
  hom := appendHom h u
  source_eq := by
    apply Mon.Hom.ext
    rw [appendHom_post_linear]
    simp only [Category.assoc, DGAlgebra.Path.diagonal_source, Category.comp_id, h.source_eq]
    exact (RelativeWitness.comp_hom_linear v u).symm
  target_eq := by
    apply Mon.Hom.ext
    rw [appendHom_post_linear]
    simp only [Category.assoc, DGAlgebra.Path.diagonal_target, Category.comp_id, h.target_eq]
    exact (RelativeWitness.comp_hom_linear w u).symm
  source_trace := by
    apply Mon.Hom.ext
    rw [appendHom_post_linear]
    simp only [Category.assoc, DGAlgebra.Path.diagonal_naturality,
      reassoc_of% u.source_eq, reassoc_of% (DGAlgebra.Path.diagonal_source R (algebra B N)),
      h.source_trace]
    abel
  target_trace := by
    apply Mon.Hom.ext
    rw [appendHom_post_linear]
    simp only [Category.assoc, DGAlgebra.Path.diagonal_naturality,
      reassoc_of% u.target_eq, reassoc_of% (DGAlgebra.Path.diagonal_target R (algebra B N)),
      h.target_trace]
    abel
  projection_eq := (affineDoublePathHom_projection R N _ _ _ _ _).trans h.projection_eq

end SerrePositivity.KST.LocalizingInvariants.SquareZero.RelativeWitnessSquare
