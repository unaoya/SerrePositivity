module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeSquarePrepend
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeSquareCongr

/-!
概要：指定二重経路 G⋅D ≃ H から、同じ底上の D ≃ G⁻¹⋅H を構成する。
方針：G の反転を前置し、元の affine 反転と合成の厳密相殺を使う。
規約：全二重経路と両端の定数 trace を保持。使われ方：fixed Γ の右三角形。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Preadditive
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZero
variable {R : Type u} [CommRing R] {B W : Mon (Complex R)} {N : Bimod B B}
  {q : W ⟶ B} {a b c : W ⟶ algebra B N}

lemma RelativeWitness.reverse_prepend_cancel_hom (g : RelativeWitness q N a b)
    (v : RelativeWitness q N b c) : (g.reverse.comp (g.comp v)).hom = v.hom := by
  apply Mon.Hom.ext
  rw [RelativeWitness.comp_hom_linear, RelativeWitness.comp_hom_linear,
    RelativeWitness.reverse_hom_linear]
  abel

def RelativeWitnessSquare.solveLeft (g : RelativeWitness q N a b)
    (v : RelativeWitness q N b c) (w : RelativeWitness q N a c)
    (h : RelativeWitnessSquare (g.comp v) w) :
    RelativeWitnessSquare v (g.reverse.comp w) :=
  (h.prepend g.reverse).replacePaths (g.reverse_prepend_cancel_hom v) rfl

end SerrePositivity.KST.LocalizingInvariants.SquareZero
