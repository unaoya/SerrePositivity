module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeWitnessSquare
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeWitnessPrecomp

/-!
概要：元の class 二重経路を、指定源への前合成と等しい底射への移送で保持する。
方針：全二重経路を同じ射で前合成し、内側の定数辺と全底射影を照合する。
規約：新しい充填を選び直さない。使われ方：Γ と自然性比較の同じ細分への移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZero.RelativeWitnessSquare
variable {R : Type u} [CommRing R] {B W T : Mon (Complex R)} {N : Bimod B B}
  {q q' : W ⟶ B} {a b : W ⟶ algebra B N} {v w : RelativeWitness q N a b}
  (h : RelativeWitnessSquare v w)

def precomp (e : T ⟶ W) : RelativeWitnessSquare (v.precomp e) (w.precomp e) where
  hom := e ≫ h.hom
  source_eq := by rw [Category.assoc, h.source_eq]; rfl
  target_eq := by rw [Category.assoc, h.target_eq]; rfl
  source_trace := by rw [Category.assoc, h.source_trace, ← Category.assoc]
  target_trace := by rw [Category.assoc, h.target_trace, ← Category.assoc]
  projection_eq := by
    rw [Category.assoc, h.projection_eq]
    simp only [Category.assoc]

def rebase (e : q = q') : RelativeWitnessSquare (v.rebase e) (w.rebase e) where
  hom := h.hom
  source_eq := h.source_eq
  target_eq := h.target_eq
  source_trace := h.source_trace
  target_trace := h.target_trace
  projection_eq := h.projection_eq.trans (congrArg (fun k =>
    (k ≫ DGAlgebra.Path.diagonal R B) ≫
      DGAlgebra.Path.diagonal R (DGAlgebra.Path.algebra R B)) e)

end SerrePositivity.KST.LocalizingInvariants.SquareZero.RelativeWitnessSquare
