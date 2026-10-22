module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraRelativeCellPathLift

/-!
概要：底の定数経路を保つ実経路を、元の相対経路代数へ厳密に持ち上げる。
方針：経路と底射の定数経路を実 pullback に渡す。
規約：源の変更なしに元の両端と全経路を保持。使われ方：相対二経路の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.RelativePath
variable (R : Type u) [CommRing R] {W C B : Mon (Complex R)} (p : C ⟶ B)
  {f g : W ⟶ C} (v : Path.Witness R f g)
  (hv : v.hom ≫ Path.map R p = (f ≫ p) ≫ Path.diagonal R B)

def witnessLift : W ⟶ algebra R p :=
  MonoidPullback.lift (Path.map R p) (Path.diagonal R B) v.hom (f ≫ p) hv

lemma witnessLift_inclusion : witnessLift R p v hv ≫ inclusion R p = v.hom :=
  MonoidPullback.lift_fst _ _ _ _ _

lemma witnessLift_projection : witnessLift R p v hv ≫ projection R p = f ≫ p :=
  MonoidPullback.lift_snd _ _ _ _ _

lemma witnessLift_source : witnessLift R p v hv ≫ source R p = f := by
  rw [source, ← Category.assoc, witnessLift_inclusion, v.source_eq]

lemma witnessLift_target : witnessLift R p v hv ≫ target R p = g := by
  rw [target, ← Category.assoc, witnessLift_inclusion, v.target_eq]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.RelativePath
