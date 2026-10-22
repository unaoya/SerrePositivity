module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroBaseChangePath

/-!
概要：元の底に相対的な平方零代数の実経路を、指定した共通底へ厳密に持ち上げる。
方針：底の定数経路と元の経路を、実経路 pullback の lift へ渡す。
規約：底射影の経路は元の定数経路に一致。使われ方：Postnikov の像 class の比較。
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
  (a : W ⟶ A) (u v : W ⟶ algebra B N) (hu : u ≫ projection B N = a ≫ q)
  (hv : v ≫ projection B N = a ≫ q) (w : DGAlgebra.Path.Witness R u v)
  (hw : w.hom ≫ DGAlgebra.Path.map R (projection B N) =
    (a ≫ q) ≫ DGAlgebra.Path.diagonal R B)

include hw in
lemma baseChangeWitness_condition : (a ≫ DGAlgebra.Path.diagonal R A) ≫
    DGAlgebra.Path.map R q = w.hom ≫ DGAlgebra.Path.map R (projection B N) := by
  rw [hw, Category.assoc, DGAlgebra.Path.diagonal_naturality, ← Category.assoc]

def baseChangeWitness : DGAlgebra.Path.Witness R (baseChangeLift q N a u hu)
    (baseChangeLift q N a v hv) where
  hom := baseChangePathLift q N (a ≫ DGAlgebra.Path.diagonal R A) w.hom
    (baseChangeWitness_condition q N a u v w hw)
  source_eq := by
    apply baseChange_hom_ext q N
    · rw [Category.assoc, ← DGAlgebra.Path.map_source, ← Category.assoc,
        baseChangePathLift_projection, Category.assoc, DGAlgebra.Path.diagonal_source,
        Category.comp_id, baseChangeLift_projection]
    · rw [Category.assoc, ← DGAlgebra.Path.map_source, ← Category.assoc,
        baseChangePathLift_map, w.source_eq, baseChangeLift_map]
  target_eq := by
    apply baseChange_hom_ext q N
    · rw [Category.assoc, ← DGAlgebra.Path.map_target, ← Category.assoc,
        baseChangePathLift_projection, Category.assoc, DGAlgebra.Path.diagonal_target,
        Category.comp_id, baseChangeLift_projection]
    · rw [Category.assoc, ← DGAlgebra.Path.map_target, ← Category.assoc,
        baseChangePathLift_map, w.target_eq, baseChangeLift_map]

lemma baseChangeWitness_relative : (baseChangeWitness q N a u v hu hv w hw).hom ≫
    DGAlgebra.Path.map R (projection A (bimoduleRestrict q N)) =
      a ≫ DGAlgebra.Path.diagonal R A := baseChangePathLift_projection _ _ _ _ _

lemma baseChangeWitness_map : (baseChangeWitness q N a u v hu hv w hw).hom ≫
    DGAlgebra.Path.map R (baseChangeMap q N) = w.hom := baseChangePathLift_map _ _ _ _ _

end SerrePositivity.KST.LocalizingInvariants.SquareZero
