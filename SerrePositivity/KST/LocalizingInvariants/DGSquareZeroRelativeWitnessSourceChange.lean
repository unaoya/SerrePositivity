module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeWitness

/-!
概要：元の相対 class 経路の始点表示だけを、全射と底を保って移す。
方針：与えられた始点等式を元の評価式へ後合成する。
規約：元の class 経路の全射を変えない。使われ方：fixed 模型射の元の証人の表示。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZero.RelativeWitness
variable {R : Type u} [CommRing R] {A W : Mon (Complex R)} {N : Bimod A A}
  {q : W ⟶ A} {a a' b : W ⟶ algebra A N}

def changeSource (v : RelativeWitness q N a b) (h : a = a') : RelativeWitness q N a' b where
  hom := v.hom
  source_eq := v.source_eq.trans h
  target_eq := v.target_eq
  projection_eq := v.projection_eq

lemma changeSource_hom (v : RelativeWitness q N a b) (h : a = a') :
    (v.changeSource h).hom = v.hom := rfl

end SerrePositivity.KST.LocalizingInvariants.SquareZero.RelativeWitness
