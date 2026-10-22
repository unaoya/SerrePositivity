module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeWitnessSquare

/-!
概要：相対二重経路が比較する元の二経路を、そのまま取り出す。
方針：依存する境界経路を明示した射として返す。
規約：新しい充填・端点を選ばない。使われ方：既存の貼合せ比較の同じ源への移送。
-/

@[expose] public section
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZero.RelativeWitnessSquare
variable {R : Type u} [CommRing R] {B W : Mon (Complex R)} {N : Bimod B B}
  {q : W ⟶ B} {a b : W ⟶ algebra B N} {v w : RelativeWitness q N a b}

def leftPath (_h : RelativeWitnessSquare v w) : RelativeWitness q N a b := v

def rightPath (_h : RelativeWitnessSquare v w) : RelativeWitness q N a b := w

end SerrePositivity.KST.LocalizingInvariants.SquareZero.RelativeWitnessSquare
