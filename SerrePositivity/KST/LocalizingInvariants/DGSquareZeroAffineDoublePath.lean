module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroAffinePath
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathPullbackDoubleLift
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathMapAffine

/-!
概要：同じ底への二重経路を持つ三つの class 二重経路を affine 合成する。
方針：二重経路の実 pullback 持ち上げと、元の乗法的 affine 演算を使う。
規約：全二重経路の線形公式を保つ。使われ方：class 輸送射の二次比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Preadditive
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZero
open DGAlgebra
variable (R : Type u) [CommRing R] {B W : Mon (Complex R)} (N : Bimod B B)
  (a b c : W ⟶ DGAlgebra.Path.algebra R (DGAlgebra.Path.algebra R (algebra B N)))
  (hab : a ≫ DGAlgebra.Path.map R (DGAlgebra.Path.map R (projection B N)) =
    b ≫ DGAlgebra.Path.map R (DGAlgebra.Path.map R (projection B N)))
  (hac : a ≫ DGAlgebra.Path.map R (DGAlgebra.Path.map R (projection B N)) =
    c ≫ DGAlgebra.Path.map R (DGAlgebra.Path.map R (projection B N)))

def affinePairDoublePath : W ⟶
    DGAlgebra.Path.algebra R (DGAlgebra.Path.algebra R (affinePair B N)) :=
  PathPullback.doubleLift R (projection B N) (projection B N) a b hab

include hac in
lemma affineTripleDoublePath_condition : affinePairDoublePath R N a b hab ≫
    DGAlgebra.Path.map R (DGAlgebra.Path.map R (affinePairBase B N)) =
      c ≫ DGAlgebra.Path.map R (DGAlgebra.Path.map R (projection B N)) := by
  rw [affinePairBase, DGAlgebra.Path.map_comp, DGAlgebra.Path.map_comp, ← Category.assoc]
  change (PathPullback.doubleLift R _ _ _ _ _ ≫
    DGAlgebra.Path.map R (DGAlgebra.Path.map R (MonoidPullback.fst _ _))) ≫ _ = _
  rw [PathPullback.doubleLift_fst]
  exact hac

def affineTripleDoublePath : W ⟶
    DGAlgebra.Path.algebra R (DGAlgebra.Path.algebra R (affineTriple B N)) :=
  PathPullback.doubleLift R (affinePairBase B N) (projection B N)
    (affinePairDoublePath R N a b hab) c (affineTripleDoublePath_condition R N a b c hab hac)

lemma affineTripleDoublePath_first : affineTripleDoublePath R N a b c hab hac ≫
    DGAlgebra.Path.map R (DGAlgebra.Path.map R (affineFirst B N)) = a := by
  rw [affineFirst, DGAlgebra.Path.map_comp, DGAlgebra.Path.map_comp, ← Category.assoc]
  change (PathPullback.doubleLift R _ _ _ _ _ ≫
    DGAlgebra.Path.map R (DGAlgebra.Path.map R (MonoidPullback.fst _ _))) ≫ _ = _
  rw [PathPullback.doubleLift_fst]
  exact PathPullback.doubleLift_fst R _ _ _ _ _

lemma affineTripleDoublePath_middle : affineTripleDoublePath R N a b c hab hac ≫
    DGAlgebra.Path.map R (DGAlgebra.Path.map R (affineMiddle B N)) = b := by
  rw [affineMiddle, DGAlgebra.Path.map_comp, DGAlgebra.Path.map_comp, ← Category.assoc]
  change (PathPullback.doubleLift R _ _ _ _ _ ≫
    DGAlgebra.Path.map R (DGAlgebra.Path.map R (MonoidPullback.fst _ _))) ≫ _ = _
  rw [PathPullback.doubleLift_fst]
  exact PathPullback.doubleLift_snd R _ _ _ _ _

lemma affineTripleDoublePath_last : affineTripleDoublePath R N a b c hab hac ≫
    DGAlgebra.Path.map R (DGAlgebra.Path.map R (affineLast B N)) = c :=
  PathPullback.doubleLift_snd R _ _ _ _ _

def affineDoublePathHom : W ⟶
    DGAlgebra.Path.algebra R (DGAlgebra.Path.algebra R (algebra B N)) :=
  affineTripleDoublePath R N a b c hab hac ≫
    DGAlgebra.Path.map R (DGAlgebra.Path.map R (affineOperation B N))

lemma affineDoublePathHom_projection : affineDoublePathHom R N a b c hab hac ≫
    DGAlgebra.Path.map R (DGAlgebra.Path.map R (projection B N)) =
      a ≫ DGAlgebra.Path.map R (DGAlgebra.Path.map R (projection B N)) := by
  rw [affineDoublePathHom, Category.assoc, ← DGAlgebra.Path.map_comp,
    ← DGAlgebra.Path.map_comp, affineOperation_projection, affineBase,
    DGAlgebra.Path.map_comp, DGAlgebra.Path.map_comp, ← Category.assoc,
    affineTripleDoublePath_last]
  exact hac.symm

lemma affineDoublePathHom_linear : (affineDoublePathHom R N a b c hab hac).hom =
    a.hom - b.hom + c.hom := by
  have h₁ := DGAlgebra.Path.map_affine R (affineFirst B N) (affineMiddle B N)
    (affineLast B N) (affineOperation B N) (affineOperation_linear B N)
  have h₂ := DGAlgebra.Path.map_affine R _ _ _ _ h₁
  have h := congrArg (fun t => (affineTripleDoublePath R N a b c hab hac).hom ≫ t) h₂
  simpa only [comp_add, comp_sub, ← Mon.comp_hom', affineTripleDoublePath_first,
    affineTripleDoublePath_middle, affineTripleDoublePath_last, affineDoublePathHom] using h

end SerrePositivity.KST.LocalizingInvariants.SquareZero
