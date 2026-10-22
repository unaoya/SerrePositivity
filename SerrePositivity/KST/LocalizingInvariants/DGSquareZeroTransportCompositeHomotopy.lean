module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeTransportHomotopy
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeWitnessRectangleTransport

/-!
概要：二つの affine 合成経路の実二重比較を、四つの実模型射の合成の経路へ移す。
方針：合成経路の輸送比較と、輸送の厳密な合成式を使う。
規約：元の四経路と全模型射を保持。使われ方：Γ の自然性正方形の実模型比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZeroExtension
variable {R : Type u} [CommRing R] {B W : Mon (Complex R)}
  (N : Bimod B B) {q : W ⟶ B} {a b c d : W ⟶ SquareZero.algebra B N}
  (v : SquareZero.RelativeWitness q N a b) (w : SquareZero.RelativeWitness q N b c)
  (v' : SquareZero.RelativeWitness q N a d) (w' : SquareZero.RelativeWitness q N d c)
  (h : SquareZero.RelativeWitnessSquare (v.comp w) (v'.comp w'))

def transportCompositeHomotopy : DGAlgebra.Path.Witness R
    (transport N v ≫ transport N w) (transport N v' ≫ transport N w') := by
  let z := transportHomotopy (R := R) N (q := q) (a := a) (b := c)
      (v := v.comp w) (w := v'.comp w') h
  refine ⟨z.hom, ?_, ?_⟩
  · exact z.source_eq.trans (transport_comp N v w).symm
  · exact z.target_eq.trans (transport_comp N v' w').symm

end SerrePositivity.KST.LocalizingInvariants.SquareZeroExtension
