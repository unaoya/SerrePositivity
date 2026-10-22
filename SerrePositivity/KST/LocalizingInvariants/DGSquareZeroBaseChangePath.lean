module

public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroBaseChangePullback
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathPullback

/-!
概要：一致する底経路と平方零代数の経路を、底変更した平方零代数へ移す。
方針：経路関手の実 pullback 錐と、元の底変更同型の逆を合成する。
規約：元の二脚の経路を厳密に保持。使われ方：Postnikov 相対経路の共通底。
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

lemma baseChangeIso_inv_projection : (baseChangeIso q N).inv ≫
    projection A (bimoduleRestrict q N) = MonoidPullback.fst q (projection B N) := by
  rw [← baseChangeIso_projection, Iso.inv_hom_id_assoc]

lemma baseChangeIso_inv_map : (baseChangeIso q N).inv ≫ baseChangeMap q N =
    MonoidPullback.snd q (projection B N) := by
  rw [← baseChangeIso_map, Iso.inv_hom_id_assoc]

variable (a : W ⟶ DGAlgebra.Path.algebra R A) (b : W ⟶ DGAlgebra.Path.algebra R (algebra B N))
  (h : a ≫ DGAlgebra.Path.map R q = b ≫ DGAlgebra.Path.map R (projection B N))

def baseChangePathLift : W ⟶ DGAlgebra.Path.algebra R (algebra A (bimoduleRestrict q N)) :=
  DGAlgebra.PathPullback.lift R q (projection B N) a b h ≫
    DGAlgebra.Path.map R (baseChangeIso q N).inv

lemma baseChangePathLift_projection : baseChangePathLift q N a b h ≫
    DGAlgebra.Path.map R (projection A (bimoduleRestrict q N)) = a := by
  rw [baseChangePathLift, Category.assoc, ← DGAlgebra.Path.map_comp,
    baseChangeIso_inv_projection, DGAlgebra.PathPullback.lift_fst]

lemma baseChangePathLift_map : baseChangePathLift q N a b h ≫
    DGAlgebra.Path.map R (baseChangeMap q N) = b := by
  rw [baseChangePathLift, Category.assoc, ← DGAlgebra.Path.map_comp,
    baseChangeIso_inv_map, DGAlgebra.PathPullback.lift_snd]

lemma baseChangePathLift_source : baseChangePathLift q N a b h ≫
    DGAlgebra.Path.source R (algebra A (bimoduleRestrict q N)) =
      baseChangeLift q N (a ≫ DGAlgebra.Path.source R A)
        (b ≫ DGAlgebra.Path.source R (algebra B N))
        (DGAlgebra.PathPullback.source_condition R _ _ _ _ h).symm := by
  apply baseChange_hom_ext q N
  · rw [Category.assoc, ← DGAlgebra.Path.map_source, ← Category.assoc,
      baseChangePathLift_projection, baseChangeLift_projection]
  · rw [Category.assoc, ← DGAlgebra.Path.map_source, ← Category.assoc,
      baseChangePathLift_map, baseChangeLift_map]

lemma baseChangePathLift_target : baseChangePathLift q N a b h ≫
    DGAlgebra.Path.target R (algebra A (bimoduleRestrict q N)) =
      baseChangeLift q N (a ≫ DGAlgebra.Path.target R A)
        (b ≫ DGAlgebra.Path.target R (algebra B N))
        (DGAlgebra.PathPullback.target_condition R _ _ _ _ h).symm := by
  apply baseChange_hom_ext q N
  · rw [Category.assoc, ← DGAlgebra.Path.map_target, ← Category.assoc,
      baseChangePathLift_projection, baseChangeLift_projection]
  · rw [Category.assoc, ← DGAlgebra.Path.map_target, ← Category.assoc,
      baseChangePathLift_map, baseChangeLift_map]

end SerrePositivity.KST.LocalizingInvariants.SquareZero
