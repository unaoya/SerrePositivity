module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroBaseChangeDoublePath
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroRelativeWitnessBaseChange

/-!
概要：底を固定する class 二重経路を、指定した共通底へ持ち上げる。
方針：底の定数二重経路と元の class 二重経路を、底変更の二重経路 lift に渡す。
規約：元の二重経路と共通底を全体で保持。使われ方：Γ の相対 class coherence。
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
  (a : W ⟶ A) {u v : W ⟶ algebra B N} {s t : RelativeWitness (a ≫ q) N u v}
  (h : RelativeWitnessSquare s t)

lemma baseChangeSquare_condition :
    ((a ≫ DGAlgebra.Path.diagonal R A) ≫
      DGAlgebra.Path.diagonal R (DGAlgebra.Path.algebra R A)) ≫
      DGAlgebra.Path.map R (DGAlgebra.Path.map R q) =
    h.hom ≫ DGAlgebra.Path.map R (DGAlgebra.Path.map R (projection B N)) := by
  rw [h.projection_eq, Category.assoc, DGAlgebra.Path.diagonal_naturality]
  rw [Category.assoc a, ← Category.assoc (DGAlgebra.Path.diagonal R A),
    DGAlgebra.Path.diagonal_naturality]
  simp only [Category.assoc]

def baseChangeSquareHom : W ⟶ DGAlgebra.Path.algebra R
    (DGAlgebra.Path.algebra R (algebra A (bimoduleRestrict q N))) :=
  baseChangeDoublePathLift q N
    ((a ≫ DGAlgebra.Path.diagonal R A) ≫
      DGAlgebra.Path.diagonal R (DGAlgebra.Path.algebra R A)) h.hom
    (baseChangeSquare_condition q N a h)

lemma baseChangeSquareHom_projection : baseChangeSquareHom q N a h ≫
    DGAlgebra.Path.map R (DGAlgebra.Path.map R (projection A (bimoduleRestrict q N))) =
    (a ≫ DGAlgebra.Path.diagonal R A) ≫
      DGAlgebra.Path.diagonal R (DGAlgebra.Path.algebra R A) :=
  baseChangeDoublePathLift_projection q N _ _ _

lemma baseChangeSquareHom_map : baseChangeSquareHom q N a h ≫
    DGAlgebra.Path.map R (DGAlgebra.Path.map R (baseChangeMap q N)) = h.hom :=
  baseChangeDoublePathLift_map q N _ _ _

lemma baseChangeSquareHom_source : baseChangeSquareHom q N a h ≫
    DGAlgebra.Path.source R (DGAlgebra.Path.algebra R (algebra A (bimoduleRestrict q N))) =
      (baseChangeRelativeWitness q N a s).hom := by
  apply baseChangePath_hom_ext q N
  · rw [Category.assoc, ← DGAlgebra.Path.map_source, ← Category.assoc,
      baseChangeSquareHom_projection, Category.assoc, DGAlgebra.Path.diagonal_source,
      Category.comp_id]
    exact (baseChangeRelativeWitness q N a s).projection_eq.symm
  · rw [Category.assoc, ← DGAlgebra.Path.map_source, ← Category.assoc,
      baseChangeSquareHom_map, h.source_eq, baseChangeRelativeWitness_map]

lemma baseChangeSquareHom_target : baseChangeSquareHom q N a h ≫
    DGAlgebra.Path.target R (DGAlgebra.Path.algebra R (algebra A (bimoduleRestrict q N))) =
      (baseChangeRelativeWitness q N a t).hom := by
  apply baseChangePath_hom_ext q N
  · rw [Category.assoc, ← DGAlgebra.Path.map_target, ← Category.assoc,
      baseChangeSquareHom_projection, Category.assoc, DGAlgebra.Path.diagonal_target,
      Category.comp_id]
    exact (baseChangeRelativeWitness q N a t).projection_eq.symm
  · rw [Category.assoc, ← DGAlgebra.Path.map_target, ← Category.assoc,
      baseChangeSquareHom_map, h.target_eq, baseChangeRelativeWitness_map]

end SerrePositivity.KST.LocalizingInvariants.SquareZero
