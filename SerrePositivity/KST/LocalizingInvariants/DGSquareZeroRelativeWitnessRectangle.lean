module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeConnection
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroAffineDoublePath
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeWitnessSquare

/-!
概要：四辺が動く相対 class 正方形の、輪郭比較への affine 補正を構成する。
方針：右辺の connection と外対角、左辺の内対角と connection を二段で合成する。
規約：全二重底射影を保持する。使われ方：固定端点の実 class 二重経路。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZero
variable {R : Type u} [CommRing R] {B W : Mon (Complex R)} {N : Bimod B B}
  {q : W ⟶ B} {a₀ a₁ b₀ b₁ : W ⟶ algebra B N}

/-- 全四辺と全底射影を指定した実相対正方形。左右の辺も動いてよい。 -/
structure RelativeWitnessRectangle (v : RelativeWitness q N a₀ b₀)
    (w : RelativeWitness q N a₁ b₁) (l : RelativeWitness q N a₀ a₁)
    (r : RelativeWitness q N b₀ b₁) extends DGAlgebra.Path.Witness R v.hom w.hom where
  source_trace : hom ≫ DGAlgebra.Path.map R (DGAlgebra.Path.source R (algebra B N)) = l.hom
  target_trace : hom ≫ DGAlgebra.Path.map R (DGAlgebra.Path.target R (algebra B N)) = r.hom
  projection_eq : hom ≫ DGAlgebra.Path.map R (DGAlgebra.Path.map R (projection B N)) =
    (q ≫ DGAlgebra.Path.diagonal R B) ≫
      DGAlgebra.Path.diagonal R (DGAlgebra.Path.algebra R B)

namespace RelativeWitnessRectangle
variable {v : RelativeWitness q N a₀ b₀} {w : RelativeWitness q N a₁ b₁}
  {l : RelativeWitness q N a₀ a₁} {r : RelativeWitness q N b₀ b₁}
  (s : RelativeWitnessRectangle v w l r)

/-- H - connection(r) + outerDiagonal(r)。 -/
def rightCorrected : W ⟶ DGAlgebra.Path.algebra R (DGAlgebra.Path.algebra R (algebra B N)) :=
  affineDoublePathHom R N s.hom
    (r.hom ≫ DGAlgebra.Path.connection R (algebra B N))
    (r.hom ≫ DGAlgebra.Path.diagonal R (DGAlgebra.Path.algebra R (algebra B N)))
    (s.projection_eq.trans r.connection_projection.symm)
    (s.projection_eq.trans r.outerDiagonal_projection.symm)

lemma rightCorrected_projection : s.rightCorrected ≫
    DGAlgebra.Path.map R (DGAlgebra.Path.map R (projection B N)) =
      (q ≫ DGAlgebra.Path.diagonal R B) ≫
        DGAlgebra.Path.diagonal R (DGAlgebra.Path.algebra R B) :=
  (affineDoublePathHom_projection R N _ _ _ _ _).trans s.projection_eq

/-- 右補正から innerDiagonal(l) を引き connection(l) を加える。 -/
def contourHom : W ⟶ DGAlgebra.Path.algebra R (DGAlgebra.Path.algebra R (algebra B N)) :=
  affineDoublePathHom R N s.rightCorrected
    (l.hom ≫ DGAlgebra.Path.map R (DGAlgebra.Path.diagonal R (algebra B N)))
    (l.hom ≫ DGAlgebra.Path.connection R (algebra B N))
    (s.rightCorrected_projection.trans l.innerDiagonal_projection.symm)
    (s.rightCorrected_projection.trans l.connection_projection.symm)

lemma contourHom_projection : s.contourHom ≫
    DGAlgebra.Path.map R (DGAlgebra.Path.map R (projection B N)) =
      (q ≫ DGAlgebra.Path.diagonal R B) ≫
        DGAlgebra.Path.diagonal R (DGAlgebra.Path.algebra R B) :=
  (affineDoublePathHom_projection R N _ _ _ _ _).trans s.rightCorrected_projection

lemma contourHom_linear : s.contourHom.hom =
    s.hom.hom - (r.hom ≫ DGAlgebra.Path.connection R (algebra B N)).hom +
      (r.hom ≫ DGAlgebra.Path.diagonal R (DGAlgebra.Path.algebra R (algebra B N))).hom -
      (l.hom ≫ DGAlgebra.Path.map R (DGAlgebra.Path.diagonal R (algebra B N))).hom +
      (l.hom ≫ DGAlgebra.Path.connection R (algebra B N)).hom := by
  dsimp only [contourHom]
  rw [affineDoublePathHom_linear]
  dsimp only [rightCorrected]
  rw [affineDoublePathHom_linear]

end RelativeWitnessRectangle
end SerrePositivity.KST.LocalizingInvariants.SquareZero
