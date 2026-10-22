module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroAffinePathLinear

/-!
概要：底の定数経路を保つ平方零標的への経路を束ね、同じ源上の逆と合成を構成する。
方針：三経路の affine 演算で、元の端点と元の底を保持する。
規約：一般代数標的の経路演算へは拡張しない。使われ方：class 経路の実補正。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Preadditive
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZero
variable {R : Type u} [CommRing R] {B W : Mon (Complex R)} (q : W ⟶ B) (N : Bimod B B)

structure RelativeWitness (f g : W ⟶ algebra B N) extends DGAlgebra.Path.Witness R f g where
  projection_eq : hom ≫ DGAlgebra.Path.map R (projection B N) = q ≫ DGAlgebra.Path.diagonal R B

namespace RelativeWitness
variable {q N} {f g h k : W ⟶ algebra B N}

lemma source_projection (v : RelativeWitness q N f g) : f ≫ projection B N = q := by
  rw [← v.source_eq, Category.assoc, ← DGAlgebra.Path.map_source, ← Category.assoc,
    v.projection_eq, Category.assoc, DGAlgebra.Path.diagonal_source, Category.comp_id]

lemma target_projection (v : RelativeWitness q N f g) : g ≫ projection B N = q := by
  rw [← v.target_eq, Category.assoc, ← DGAlgebra.Path.map_target, ← Category.assoc,
    v.projection_eq, Category.assoc, DGAlgebra.Path.diagonal_target, Category.comp_id]

def refl (f : W ⟶ algebra B N) (hf : f ≫ projection B N = q) : RelativeWitness q N f f where
  toWitness := DGAlgebra.Path.Witness.refl f
  projection_eq := by
    change (f ≫ DGAlgebra.Path.diagonal R (algebra B N)) ≫ _ = _
    rw [Category.assoc, DGAlgebra.Path.diagonal_naturality, ← Category.assoc, hf]

def comp (v : RelativeWitness q N f g) (w : RelativeWitness q N g h) : RelativeWitness q N f h where
  hom := affinePathHom R N v.hom (refl g v.target_projection).hom w.hom
    (v.projection_eq.trans (refl g v.target_projection).projection_eq.symm)
    (v.projection_eq.trans w.projection_eq.symm)
  source_eq := by
    apply Mon.Hom.ext
    rw [affinePathHom_source_linear, v.source_eq, (refl g v.target_projection).source_eq,
      w.source_eq, sub_add_cancel]
  target_eq := by
    apply Mon.Hom.ext
    rw [affinePathHom_target_linear, v.target_eq, (refl g v.target_projection).target_eq,
      w.target_eq, sub_self, zero_add]
  projection_eq := (affinePathHom_projection R N _ _ _ _ _).trans v.projection_eq

def reverse (v : RelativeWitness q N f g) : RelativeWitness q N g f where
  hom := affinePathHom R N (refl f v.source_projection).hom v.hom (refl g v.target_projection).hom
    ((refl f v.source_projection).projection_eq.trans v.projection_eq.symm)
    ((refl f v.source_projection).projection_eq.trans
      (refl g v.target_projection).projection_eq.symm)
  source_eq := by
    apply Mon.Hom.ext
    rw [affinePathHom_source_linear, (refl f v.source_projection).source_eq, v.source_eq,
      (refl g v.target_projection).source_eq, sub_self, zero_add]
  target_eq := by
    apply Mon.Hom.ext
    rw [affinePathHom_target_linear, (refl f v.source_projection).target_eq, v.target_eq,
      (refl g v.target_projection).target_eq, sub_add_cancel]
  projection_eq := (affinePathHom_projection R N _ _ _ _ _).trans
    (refl f v.source_projection).projection_eq

lemma comp_hom_linear (v : RelativeWitness q N f g) (w : RelativeWitness q N g h) :
    (v.comp w).hom.hom =
      v.hom.hom - (g ≫ DGAlgebra.Path.diagonal R (algebra B N)).hom + w.hom.hom :=
  affinePathHom_linear R N _ _ _ _ _

lemma reverse_hom_linear (v : RelativeWitness q N f g) : (v.reverse).hom.hom =
    (f ≫ DGAlgebra.Path.diagonal R (algebra B N)).hom - v.hom.hom +
      (g ≫ DGAlgebra.Path.diagonal R (algebra B N)).hom := affinePathHom_linear R N _ _ _ _ _

lemma comp_reverse_hom (v : RelativeWitness q N f g) :
    (v.comp v.reverse).hom = f ≫ DGAlgebra.Path.diagonal R (algebra B N) := by
  apply Mon.Hom.ext
  rw [comp_hom_linear, reverse_hom_linear]
  abel

lemma reverse_comp_hom (v : RelativeWitness q N f g) :
    (v.reverse.comp v).hom = g ≫ DGAlgebra.Path.diagonal R (algebra B N) := by
  apply Mon.Hom.ext
  rw [comp_hom_linear, reverse_hom_linear]
  abel

lemma comp_assoc_hom (v : RelativeWitness q N f g) (w : RelativeWitness q N g h)
    (z : RelativeWitness q N h k) : ((v.comp w).comp z).hom = (v.comp (w.comp z)).hom := by
  apply Mon.Hom.ext
  rw [comp_hom_linear, comp_hom_linear, comp_hom_linear, comp_hom_linear]
  abel

end RelativeWitness
end SerrePositivity.KST.LocalizingInvariants.SquareZero
