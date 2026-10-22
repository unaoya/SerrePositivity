module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroAffineMap
public import SerrePositivity.KST.LocalizingInvariants.MonoidPullbackUniversal

/-!
概要：平方零代数の同じ底の三重 fiber product 上に、実代数射 s − t + u を構成する。
方針：三つの射影の底が一致する式を affineMapOver に渡す。
規約：underlying 射は三射影の線形結合。使われ方：経路関手を介した相対経路の補正。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits Preadditive
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZero
variable {R : Type u} [CommRing R] (B : Mon (Complex R)) (N : Bimod B B)

def affinePair : Mon (Complex R) := MonoidPullback.obj (projection B N) (projection B N)

def affinePairBase : affinePair B N ⟶ B :=
  MonoidPullback.fst (projection B N) (projection B N) ≫ projection B N

def affineTriple : Mon (Complex R) := MonoidPullback.obj (affinePairBase B N) (projection B N)

def affineFirst : affineTriple B N ⟶ algebra B N :=
  MonoidPullback.fst (affinePairBase B N) (projection B N) ≫
    MonoidPullback.fst (projection B N) (projection B N)

def affineMiddle : affineTriple B N ⟶ algebra B N :=
  MonoidPullback.fst (affinePairBase B N) (projection B N) ≫
    MonoidPullback.snd (projection B N) (projection B N)

def affineLast : affineTriple B N ⟶ algebra B N :=
  MonoidPullback.snd (affinePairBase B N) (projection B N)

def affineBase : affineTriple B N ⟶ B := affineLast B N ≫ projection B N

lemma affineFirst_projection : affineFirst B N ≫ projection B N = affineBase B N := by
  rw [affineFirst, Category.assoc]
  exact MonoidPullback.condition _ _

lemma affineMiddle_projection : affineMiddle B N ≫ projection B N = affineBase B N := by
  rw [affineMiddle, Category.assoc, ← MonoidPullback.condition, ← Category.assoc]
  exact affineFirst_projection B N

def affineOperation : affineTriple B N ⟶ algebra B N :=
  affineMapOver (affineBase B N) N (affineFirst B N) (affineMiddle B N) (affineLast B N)
    (affineFirst_projection B N) (affineMiddle_projection B N) rfl

lemma affineOperation_linear : (affineOperation B N).hom =
    (affineFirst B N).hom - (affineMiddle B N).hom + (affineLast B N).hom :=
  affineMapOver_linear _ _ _ _ _ _ _ _

lemma affineOperation_projection : affineOperation B N ≫ projection B N = affineBase B N :=
  affineMapOver_projection _ _ _ _ _ _ _ _

lemma affineOperation_comp_linear {W : Mon (Complex R)} (p : W ⟶ affineTriple B N) :
    (p ≫ affineOperation B N).hom =
      (p ≫ affineFirst B N).hom - (p ≫ affineMiddle B N).hom + (p ≫ affineLast B N).hom := by
  simp only [Mon.comp_hom', affineOperation_linear, comp_add, comp_sub]

end SerrePositivity.KST.LocalizingInvariants.SquareZero
