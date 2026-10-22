module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroAffineOperation
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathPullback

/-!
概要：底への全経路が一致する三つの乗法的経路から、実 affine 経路を構成する。
方針：三重 fiber product の経路へ持ち上げ、実 affine 演算で後合成する。
規約：同じ底への経路の等式を保持する。使われ方：class 経路の実補正。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits Preadditive
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZero
open DGAlgebra
variable (R : Type u) [CommRing R] {B W : Mon (Complex R)} (N : Bimod B B)
  (a b c : W ⟶ DGAlgebra.Path.algebra R (algebra B N))
  (hab : a ≫ DGAlgebra.Path.map R (projection B N) = b ≫ DGAlgebra.Path.map R (projection B N))
  (hac : a ≫ DGAlgebra.Path.map R (projection B N) = c ≫ DGAlgebra.Path.map R (projection B N))

def affinePairPath : W ⟶ DGAlgebra.Path.algebra R (affinePair B N) :=
  PathPullback.lift R (projection B N) (projection B N) a b hab

include hac in
lemma affineTriplePath_condition :
    affinePairPath R N a b hab ≫ DGAlgebra.Path.map R (affinePairBase B N) =
    c ≫ DGAlgebra.Path.map R (projection B N) := by
  rw [affinePairBase, DGAlgebra.Path.map_comp, ← Category.assoc]
  change (PathPullback.lift R _ _ a b hab ≫ DGAlgebra.Path.map R (MonoidPullback.fst _ _)) ≫ _ = _
  rw [PathPullback.lift_fst]
  exact hac

def affineTriplePath : W ⟶ DGAlgebra.Path.algebra R (affineTriple B N) :=
  PathPullback.lift R (affinePairBase B N) (projection B N) (affinePairPath R N a b hab) c
    (affineTriplePath_condition R N a b c hab hac)

lemma affineTriplePath_first : affineTriplePath R N a b c hab hac ≫
    DGAlgebra.Path.map R (affineFirst B N) = a := by
  rw [affineFirst, DGAlgebra.Path.map_comp, ← Category.assoc]
  change (PathPullback.lift R _ _ _ _ _ ≫ DGAlgebra.Path.map R (MonoidPullback.fst _ _)) ≫ _ = _
  rw [PathPullback.lift_fst]
  exact PathPullback.lift_fst R _ _ _ _ _

lemma affineTriplePath_middle : affineTriplePath R N a b c hab hac ≫
    DGAlgebra.Path.map R (affineMiddle B N) = b := by
  rw [affineMiddle, DGAlgebra.Path.map_comp, ← Category.assoc]
  change (PathPullback.lift R _ _ _ _ _ ≫ DGAlgebra.Path.map R (MonoidPullback.fst _ _)) ≫ _ = _
  rw [PathPullback.lift_fst]
  exact PathPullback.lift_snd R _ _ _ _ _

lemma affineTriplePath_last : affineTriplePath R N a b c hab hac ≫
    DGAlgebra.Path.map R (affineLast B N) = c := PathPullback.lift_snd R _ _ _ _ _

def affinePathHom : W ⟶ DGAlgebra.Path.algebra R (algebra B N) :=
  affineTriplePath R N a b c hab hac ≫ DGAlgebra.Path.map R (affineOperation B N)

lemma affinePathHom_projection : affinePathHom R N a b c hab hac ≫
    DGAlgebra.Path.map R (projection B N) = a ≫ DGAlgebra.Path.map R (projection B N) := by
  rw [affinePathHom, Category.assoc, ← DGAlgebra.Path.map_comp, affineOperation_projection,
    affineBase, DGAlgebra.Path.map_comp, ← Category.assoc, affineTriplePath_last]
  exact hac.symm

lemma affinePathHom_endpoint_linear
    (e : DGAlgebra.Path.algebra R (affineTriple B N) ⟶ affineTriple B N)
    (v : DGAlgebra.Path.algebra R (algebra B N) ⟶ algebra B N)
    (hop : DGAlgebra.Path.map R (affineOperation B N) ≫ v = e ≫ affineOperation B N)
    (hfirst : e ≫ affineFirst B N = DGAlgebra.Path.map R (affineFirst B N) ≫ v)
    (hmiddle : e ≫ affineMiddle B N = DGAlgebra.Path.map R (affineMiddle B N) ≫ v)
    (hlast : e ≫ affineLast B N = DGAlgebra.Path.map R (affineLast B N) ≫ v) :
    (affinePathHom R N a b c hab hac ≫ v).hom =
      (a ≫ v).hom - (b ≫ v).hom + (c ≫ v).hom := by
  have hm : affinePathHom R N a b c hab hac ≫ v =
      (affineTriplePath R N a b c hab hac ≫ e) ≫ affineOperation B N := by
    rw [affinePathHom, Category.assoc, hop, ← Category.assoc]
  rw [hm, affineOperation_comp_linear]
  have h₁ : (affineTriplePath R N a b c hab hac ≫ e) ≫ affineFirst B N = a ≫ v := by
    rw [Category.assoc, hfirst, ← Category.assoc, affineTriplePath_first]
  have h₂ : (affineTriplePath R N a b c hab hac ≫ e) ≫ affineMiddle B N = b ≫ v := by
    rw [Category.assoc, hmiddle, ← Category.assoc, affineTriplePath_middle]
  have h₃ : (affineTriplePath R N a b c hab hac ≫ e) ≫ affineLast B N = c ≫ v := by
    rw [Category.assoc, hlast, ← Category.assoc, affineTriplePath_last]
  rw [h₁, h₂, h₃]

lemma affinePathHom_source_linear :
    (affinePathHom R N a b c hab hac ≫ DGAlgebra.Path.source R (algebra B N)).hom =
      (a ≫ DGAlgebra.Path.source R (algebra B N)).hom -
      (b ≫ DGAlgebra.Path.source R (algebra B N)).hom +
        (c ≫ DGAlgebra.Path.source R (algebra B N)).hom :=
  affinePathHom_endpoint_linear R N a b c hab hac _ _ (DGAlgebra.Path.map_source R _)
    (DGAlgebra.Path.map_source R _).symm (DGAlgebra.Path.map_source R _).symm
    (DGAlgebra.Path.map_source R _).symm

lemma affinePathHom_target_linear :
    (affinePathHom R N a b c hab hac ≫ DGAlgebra.Path.target R (algebra B N)).hom =
      (a ≫ DGAlgebra.Path.target R (algebra B N)).hom -
      (b ≫ DGAlgebra.Path.target R (algebra B N)).hom +
        (c ≫ DGAlgebra.Path.target R (algebra B N)).hom :=
  affinePathHom_endpoint_linear R N a b c hab hac _ _ (DGAlgebra.Path.map_target R _)
    (DGAlgebra.Path.map_target R _).symm (DGAlgebra.Path.map_target R _).symm
    (DGAlgebra.Path.map_target R _).symm

end SerrePositivity.KST.LocalizingInvariants.SquareZero
