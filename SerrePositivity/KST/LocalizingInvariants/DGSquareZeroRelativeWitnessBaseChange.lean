module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroBaseChangeWitness
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeWitnessSquare

/-!
概要：元の相対 class 経路を、任意の指定した共通底への相対証人に持ち上げる。
方針：元の底変更経路の両端と定数射影を、そのまま相対証人へ束ねる。
規約：元の class 経路への射影を厳密に保つ。使われ方：class 二重経路の底変更。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.SquareZero
variable {R : Type u} [CommRing R] {A B W : Mon (Complex R)} (q : A ⟶ B) (N : Bimod B B)
  (a : W ⟶ A) {u v : W ⟶ algebra B N} (w : RelativeWitness (a ≫ q) N u v)

def baseChangeRelativeWitness : RelativeWitness a (bimoduleRestrict q N)
    (baseChangeLift q N a u w.source_projection)
    (baseChangeLift q N a v w.target_projection) where
  toWitness := baseChangeWitness q N a u v w.source_projection w.target_projection
    w.toWitness w.projection_eq
  projection_eq := baseChangeWitness_relative q N a u v w.source_projection
    w.target_projection w.toWitness w.projection_eq

lemma baseChangeRelativeWitness_map : (baseChangeRelativeWitness q N a w).hom ≫
    DGAlgebra.Path.map R (baseChangeMap q N) = w.hom :=
  baseChangeWitness_map q N a u v w.source_projection w.target_projection
    w.toWitness w.projection_eq

end SerrePositivity.KST.LocalizingInvariants.SquareZero
