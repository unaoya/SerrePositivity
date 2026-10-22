module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeTransport
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeWitnessSquare
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroAffineDoublePath

/-!
概要：class 経路間の相対二重経路を、輸送公式の実二重経路へ移す。
方針：定数二重経路から元の比較二重経路を引き、模型の定数経路を加える。
規約：全ての affine 演算は乗法的な射として構成する。使われ方：輸送射の実経路。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Preadditive
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZeroExtension
variable {R : Type u} [CommRing R] {A W : Mon (Complex R)} (N : Bimod A A)
  {q : W ⟶ A} {a b : W ⟶ SquareZero.algebra A N}
  {v w : SquareZero.RelativeWitness q N a b} (h : SquareZero.RelativeWitnessSquare v w)

def transportConstantPath (s : relativeModel N a ⟶
    DGAlgebra.Path.algebra R (SquareZero.algebra A N)) :
    relativeModel N a ⟶ DGAlgebra.Path.algebra R
      (DGAlgebra.Path.algebra R (SquareZero.algebra A N)) :=
  s ≫ DGAlgebra.Path.diagonal R (DGAlgebra.Path.algebra R (SquareZero.algebra A N))

lemma transportSquare_first_base :
    transportConstantPath N (relativeLeft N a ≫ b ≫
      DGAlgebra.Path.diagonal R (SquareZero.algebra A N)) ≫
      DGAlgebra.Path.map R (DGAlgebra.Path.map R (SquareZero.projection A N)) =
    (relativeLeft N a ≫ h.hom) ≫
      DGAlgebra.Path.map R (DGAlgebra.Path.map R (SquareZero.projection A N)) := by
  simp only [transportConstantPath, Category.assoc, DGAlgebra.Path.diagonal_naturality,
    h.projection_eq]
  rw [← Category.assoc (DGAlgebra.Path.diagonal R (SquareZero.algebra A N)),
    DGAlgebra.Path.diagonal_naturality]
  simp only [Category.assoc]
  rw [← Category.assoc b, v.target_projection]

include v in
lemma transportSquare_last_base :
    transportConstantPath N (relativeLeft N a ≫ b ≫
      DGAlgebra.Path.diagonal R (SquareZero.algebra A N)) ≫
      DGAlgebra.Path.map R (DGAlgebra.Path.map R (SquareZero.projection A N)) =
    transportConstantPath N (relativePath N a) ≫
      DGAlgebra.Path.map R (DGAlgebra.Path.map R (SquareZero.projection A N)) := by
  simp only [transportConstantPath, Category.assoc, DGAlgebra.Path.diagonal_naturality]
  rw [← Category.assoc (relativePath N a), relativePath_base]
  rw [← Category.assoc (DGAlgebra.Path.diagonal R (SquareZero.algebra A N)),
    DGAlgebra.Path.diagonal_naturality]
  simp only [Category.assoc]
  rw [← Category.assoc b, v.target_projection, ← Category.assoc a, v.source_projection]

def transportSquarePath : relativeModel N a ⟶ DGAlgebra.Path.algebra R
    (DGAlgebra.Path.algebra R (SquareZero.algebra A N)) :=
  SquareZero.affineDoublePathHom R N
    (transportConstantPath N (relativeLeft N a ≫ b ≫
      DGAlgebra.Path.diagonal R (SquareZero.algebra A N)))
    (relativeLeft N a ≫ h.hom) (transportConstantPath N (relativePath N a))
    (transportSquare_first_base N h)
    (transportSquare_last_base N (v := v))

lemma transportSquarePath_linear : (transportSquarePath N h).hom =
    (transportConstantPath N (relativeLeft N a ≫ b ≫
      DGAlgebra.Path.diagonal R (SquareZero.algebra A N))).hom -
      (relativeLeft N a ≫ h.hom).hom + (transportConstantPath N (relativePath N a)).hom :=
  SquareZero.affineDoublePathHom_linear R N _ _ _ _ _

end SerrePositivity.KST.LocalizingInvariants.SquareZeroExtension
