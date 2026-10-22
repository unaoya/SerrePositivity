module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeWitnessSquare

/-!
概要：同じ両端の二つの class 経路を、全経路の等式に沿って置換する。
方針：元の二重経路そのものを保持し、外側の両端の式だけを移送する。
規約：内側両辺と底射影を変えない。使われ方：三経路貼合せの厳密相殺。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZero
namespace RelativeWitness
variable {R : Type u} [CommRing R] {B W : Mon (Complex R)} {N : Bimod B B}
  {q : W ⟶ B} {a b c : W ⟶ algebra B N}
  {v v' : RelativeWitness q N a b} {w w' : RelativeWitness q N b c}

lemma comp_congr_hom (hv : v.hom = v'.hom) (hw : w.hom = w'.hom) :
    (v.comp w).hom = (v'.comp w').hom := by
  apply Mon.Hom.ext
  rw [comp_hom_linear, comp_hom_linear, hv, hw]

end RelativeWitness
namespace RelativeWitnessSquare
variable {R : Type u} [CommRing R] {B W : Mon (Complex R)} {N : Bimod B B}
  {q : W ⟶ B} {a b : W ⟶ algebra B N} {v w v' w' : RelativeWitness q N a b}

def replacePaths (h : RelativeWitnessSquare v w) (hv : v.hom = v'.hom)
    (hw : w.hom = w'.hom) : RelativeWitnessSquare v' w' where
  hom := h.hom
  source_eq := h.source_eq.trans hv
  target_eq := h.target_eq.trans hw
  source_trace := h.source_trace
  target_trace := h.target_trace
  projection_eq := h.projection_eq

end RelativeWitnessSquare
end SerrePositivity.KST.LocalizingInvariants.SquareZero
