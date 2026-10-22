module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeWitness

/-!
概要：相対平方零経路の源の変更と、等しい底射への移送を構成する。
方針：元の経路の前合成と、底への定数射影の式をそのまま使う。
規約：元の経路の射を保持。使われ方：class 模型の源上へ経路を移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZero.RelativeWitness
variable {R : Type u} [CommRing R] {B W T : Mon (Complex R)} {N : Bimod B B}
  {q q' : W ⟶ B} {f g : W ⟶ algebra B N}

def precomp (v : RelativeWitness q N f g) (a : T ⟶ W) :
    RelativeWitness (a ≫ q) N (a ≫ f) (a ≫ g) where
  toWitness := v.toWitness.precomp a
  projection_eq := by
    change (a ≫ v.hom) ≫ _ = (a ≫ q) ≫ _
    rw [Category.assoc, v.projection_eq, Category.assoc]

def rebase (v : RelativeWitness q N f g) (h : q = q') : RelativeWitness q' N f g where
  toWitness := v.toWitness
  projection_eq := v.projection_eq.trans (congrArg (fun t => t ≫ DGAlgebra.Path.diagonal R B) h)

lemma precomp_hom (v : RelativeWitness q N f g) (a : T ⟶ W) :
    (v.precomp a).hom = a ≫ v.hom := rfl

lemma rebase_hom (v : RelativeWitness q N f g) (h : q = q') : (v.rebase h).hom = v.hom := rfl

end SerrePositivity.KST.LocalizingInvariants.SquareZero.RelativeWitness
