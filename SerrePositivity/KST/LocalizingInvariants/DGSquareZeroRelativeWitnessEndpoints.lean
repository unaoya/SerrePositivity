module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeWitness
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathMap

/-!
概要：実相対 class 経路の端点を取り出し、全経路の前後合成式から端点式を導く。
方針：元の経路の両評価と Path.map の自然性を使う。
規約：元の全経路の等式を入力する。使われ方：輸送後の class の元の標的への復元。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZero.RelativeWitness
variable {R : Type u} [CommRing R] {A B W V : Mon (Complex R)} {M : Bimod A A}
  {N : Bimod B B} {q : W ⟶ A} {r : V ⟶ B}
  {a b : W ⟶ algebra A M} {c d : V ⟶ algebra B N}

def targetMap (_v : RelativeWitness q M a b) : W ⟶ algebra A M := b

lemma targetMap_eq (v : RelativeWitness q M a b) : v.targetMap = b := rfl

lemma targetMap_whisker (v : RelativeWitness q M a b) (w : RelativeWitness r N c d)
    (e : W ⟶ V) (k : algebra B N ⟶ algebra A M)
    (h : v.hom = e ≫ w.hom ≫ DGAlgebra.Path.map R k) : v.targetMap = e ≫ w.targetMap ≫ k := by
  change b = e ≫ d ≫ k
  rw [← v.target_eq, h, Category.assoc, Category.assoc, DGAlgebra.Path.map_target,
    ← Category.assoc w.hom, w.target_eq]

lemma targetMap_projection (v : RelativeWitness q M a b) :
    v.targetMap ≫ projection A M = q := v.target_projection

end SerrePositivity.KST.LocalizingInvariants.SquareZero.RelativeWitness
