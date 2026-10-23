module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeSourceSlide

/-!
概要：動く始点の二重経路が、元の経路・逆経路合成・始点経路・定数終点を持つと示す。
方針：全線形式と connection の四辺の式を使う。
規約：全四辺を厳密に保持。使われ方：実模型経路の普遍 lift の境界。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Preadditive
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZero.RelativeWitness
variable {R : Type u} [CommRing R] {A W : Mon (Complex R)} {N : Bimod A A}
  {q : W ⟶ A} {a b c : W ⟶ algebra A N}
  (v : RelativeWitness q N a b) (p : RelativeWitness q N a c)

lemma sourceSlideHom_source : sourceSlideHom v p ≫
    DGAlgebra.Path.source R (DGAlgebra.Path.algebra R (algebra A N)) = p.hom := by
  apply Mon.Hom.ext
  rw [sourceSlideHom_post_linear]
  simp only [Category.assoc, DGAlgebra.Path.map_source, DGAlgebra.Path.connection_source,
    DGAlgebra.Path.diagonal_source, Category.comp_id, reassoc_of% v.source_eq,
    sub_self, zero_add]

lemma sourceSlideHom_target : sourceSlideHom v p ≫
    DGAlgebra.Path.target R (DGAlgebra.Path.algebra R (algebra A N)) =
      (v.reverse.comp p).hom := by
  apply Mon.Hom.ext
  rw [sourceSlideHom_post_linear, comp_hom_linear, reverse_hom_linear]
  simp only [Category.assoc, DGAlgebra.Path.map_target, DGAlgebra.Path.connection_target,
    DGAlgebra.Path.diagonal_target, Category.comp_id, reassoc_of% v.target_eq]
  abel

lemma sourceSlideHom_source_trace : sourceSlideHom v p ≫
    DGAlgebra.Path.map R (DGAlgebra.Path.source R (algebra A N)) = v.hom := by
  apply Mon.Hom.ext
  rw [sourceSlideHom_post_linear]
  simp only [Category.assoc, ← DGAlgebra.Path.map_comp, DGAlgebra.Path.diagonal_source,
    DGAlgebra.Path.map_id, Category.comp_id, DGAlgebra.Path.connection_innerSource,
    DGAlgebra.Path.diagonal_naturality, reassoc_of% v.source_eq, reassoc_of% p.source_eq]
  abel

lemma sourceSlideHom_target_trace : sourceSlideHom v p ≫
    DGAlgebra.Path.map R (DGAlgebra.Path.target R (algebra A N)) =
      c ≫ DGAlgebra.Path.diagonal R (algebra A N) := by
  apply Mon.Hom.ext
  rw [sourceSlideHom_post_linear]
  simp only [Category.assoc, ← DGAlgebra.Path.map_comp, DGAlgebra.Path.diagonal_target,
    DGAlgebra.Path.map_id, Category.comp_id, DGAlgebra.Path.connection_innerTarget,
    DGAlgebra.Path.diagonal_naturality, reassoc_of% p.target_eq, sub_self, zero_add]

def sourceSlideRectangle : RelativeWitnessRectangle p (v.reverse.comp p) v
    (refl c p.target_projection) where
  hom := sourceSlideHom v p
  source_eq := sourceSlideHom_source v p
  target_eq := sourceSlideHom_target v p
  source_trace := sourceSlideHom_source_trace v p
  target_trace := sourceSlideHom_target_trace v p
  projection_eq := sourceSlideHom_projection v p

end SerrePositivity.KST.LocalizingInvariants.SquareZero.RelativeWitness
