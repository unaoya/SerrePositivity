module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeWitnessRectangle

/-!
概要：底を固定して動く始点と、元の終点を固定した経路の実二重経路を構成する。
方針：始点経路の内対角から connection を引き、元の経路の外対角を加える。
規約：全て実乗法的 affine 射。使われ方：元の source 自然性を模型経路へ移す。
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

def sourceSlideHom : W ⟶ DGAlgebra.Path.algebra R (DGAlgebra.Path.algebra R (algebra A N)) :=
  affineDoublePathHom R N
    (v.hom ≫ DGAlgebra.Path.map R (DGAlgebra.Path.diagonal R (algebra A N)))
    (v.hom ≫ DGAlgebra.Path.connection R (algebra A N))
    (p.hom ≫ DGAlgebra.Path.diagonal R (DGAlgebra.Path.algebra R (algebra A N)))
    (v.innerDiagonal_projection.trans v.connection_projection.symm)
    (v.innerDiagonal_projection.trans p.outerDiagonal_projection.symm)

lemma sourceSlideHom_projection : sourceSlideHom v p ≫
    DGAlgebra.Path.map R (DGAlgebra.Path.map R (projection A N)) =
      (q ≫ DGAlgebra.Path.diagonal R A) ≫
        DGAlgebra.Path.diagonal R (DGAlgebra.Path.algebra R A) :=
  (affineDoublePathHom_projection R N _ _ _ _ _).trans v.innerDiagonal_projection

lemma sourceSlideHom_post_linear {D : Mon (Complex R)}
    (m : DGAlgebra.Path.algebra R (DGAlgebra.Path.algebra R (algebra A N)) ⟶ D) :
    (sourceSlideHom v p ≫ m).hom =
      ((v.hom ≫ DGAlgebra.Path.map R (DGAlgebra.Path.diagonal R (algebra A N))) ≫ m).hom -
      ((v.hom ≫ DGAlgebra.Path.connection R (algebra A N)) ≫ m).hom +
      ((p.hom ≫ DGAlgebra.Path.diagonal R (DGAlgebra.Path.algebra R (algebra A N))) ≫ m).hom := by
  rw [Mon.comp_hom']
  change (affineDoublePathHom R N _ _ _ _ _).hom ≫ m.hom = _
  rw [affineDoublePathHom_linear, add_comp, sub_comp]
  rfl

end SerrePositivity.KST.LocalizingInvariants.SquareZero.RelativeWitness
