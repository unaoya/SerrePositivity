module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroAffineDoublePath
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeWitnessSquare
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeConnection

/-!
概要：固定端点の class 二重経路を反転・縦合成し、同じ全底射影を保持する。
方針：実 affine 二重経路と外対角を使う。
規約：存在だけの関係に切り詰めない。使われ方：cell・affine・二因子分解比較の貼合せ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Preadditive
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZero
variable {R : Type u} [CommRing R] {B W : Mon (Complex R)} (N : Bimod B B)
  (a b c : W ⟶ DGAlgebra.Path.algebra R (DGAlgebra.Path.algebra R (algebra B N)))
  (hab : a ≫ DGAlgebra.Path.map R (DGAlgebra.Path.map R (projection B N)) =
    b ≫ DGAlgebra.Path.map R (DGAlgebra.Path.map R (projection B N)))
  (hac : a ≫ DGAlgebra.Path.map R (DGAlgebra.Path.map R (projection B N)) =
    c ≫ DGAlgebra.Path.map R (DGAlgebra.Path.map R (projection B N)))

lemma affineDoublePathHom_post_linear {D : Mon (Complex R)}
    (k : DGAlgebra.Path.algebra R (DGAlgebra.Path.algebra R (algebra B N)) ⟶ D) :
    (affineDoublePathHom R N a b c hab hac ≫ k).hom =
      (a ≫ k).hom - (b ≫ k).hom + (c ≫ k).hom := by
  rw [Mon.comp_hom', affineDoublePathHom_linear, add_comp, sub_comp]
  rfl

namespace RelativeWitnessSquare
variable {N} {q : W ⟶ B} {x y : W ⟶ algebra B N} {u v w : RelativeWitness q N x y}

def symm (s : RelativeWitnessSquare u v) : RelativeWitnessSquare v u where
  hom := affineDoublePathHom R N
    (u.hom ≫ DGAlgebra.Path.diagonal R (DGAlgebra.Path.algebra R (algebra B N))) s.hom
    (v.hom ≫ DGAlgebra.Path.diagonal R (DGAlgebra.Path.algebra R (algebra B N)))
    (u.outerDiagonal_projection.trans s.projection_eq.symm)
    (u.outerDiagonal_projection.trans v.outerDiagonal_projection.symm)
  source_eq := by
    apply Mon.Hom.ext
    rw [affineDoublePathHom_post_linear]
    simp only [Category.assoc, DGAlgebra.Path.diagonal_source, Category.comp_id,
      s.source_eq, sub_self, zero_add]
  target_eq := by
    apply Mon.Hom.ext
    rw [affineDoublePathHom_post_linear]
    simp only [Category.assoc, DGAlgebra.Path.diagonal_target, Category.comp_id,
      s.target_eq, sub_add_cancel]
  source_trace := by
    apply Mon.Hom.ext
    rw [affineDoublePathHom_post_linear]
    simp only [Category.assoc, DGAlgebra.Path.diagonal_naturality,
      reassoc_of% u.source_eq, reassoc_of% v.source_eq, s.source_trace, sub_self, zero_add]
  target_trace := by
    apply Mon.Hom.ext
    rw [affineDoublePathHom_post_linear]
    simp only [Category.assoc, DGAlgebra.Path.diagonal_naturality,
      reassoc_of% u.target_eq, reassoc_of% v.target_eq, s.target_trace, sub_self, zero_add]
  projection_eq := (affineDoublePathHom_projection R N _ _ _ _ _).trans u.outerDiagonal_projection

def trans (s : RelativeWitnessSquare u v) (t : RelativeWitnessSquare v w) :
    RelativeWitnessSquare u w where
  hom := affineDoublePathHom R N s.hom
    (v.hom ≫ DGAlgebra.Path.diagonal R (DGAlgebra.Path.algebra R (algebra B N))) t.hom
    (s.projection_eq.trans v.outerDiagonal_projection.symm)
    (s.projection_eq.trans t.projection_eq.symm)
  source_eq := by
    apply Mon.Hom.ext
    rw [affineDoublePathHom_post_linear]
    simp only [Category.assoc, DGAlgebra.Path.diagonal_source, Category.comp_id,
      s.source_eq, t.source_eq, sub_add_cancel]
  target_eq := by
    apply Mon.Hom.ext
    rw [affineDoublePathHom_post_linear]
    simp only [Category.assoc, DGAlgebra.Path.diagonal_target, Category.comp_id,
      s.target_eq, t.target_eq, sub_self, zero_add]
  source_trace := by
    apply Mon.Hom.ext
    rw [affineDoublePathHom_post_linear]
    simp only [Category.assoc, DGAlgebra.Path.diagonal_naturality,
      reassoc_of% v.source_eq, s.source_trace, t.source_trace, sub_self, zero_add]
  target_trace := by
    apply Mon.Hom.ext
    rw [affineDoublePathHom_post_linear]
    simp only [Category.assoc, DGAlgebra.Path.diagonal_naturality,
      reassoc_of% v.target_eq, s.target_trace, t.target_trace, sub_self, zero_add]
  projection_eq := (affineDoublePathHom_projection R N _ _ _ _ _).trans s.projection_eq

end RelativeWitnessSquare
end SerrePositivity.KST.LocalizingInvariants.SquareZero
