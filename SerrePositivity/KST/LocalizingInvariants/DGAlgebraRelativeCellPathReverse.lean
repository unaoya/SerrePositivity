module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraRelativeCellPathOperations

/-!
概要：元の底を固定した乗法的経路を、cell augmentation の後で向き反転する。
方針：相対経路の source の全射準同型性で、元の経路を定数経路へ結ぶ。
規約：底への全経路を保持し、元の源上の厳密反転を仮定しない。使われ方：相対経路の貼合せ。
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
  (hs : ∀ n : ℤ, Function.Surjective (p.hom.f n))
  {f g : W ⟶ C} (v : Path.Witness R f g)
  (hv : v.hom ≫ Path.map R p = (f ≫ p) ≫ Path.diagonal R B)

lemma source_surjective (n : ℤ) : Function.Surjective ((source R p).hom.f n) := by
  have := RelativeComposedPath.sourceEvaluation_epi R p
  exact (ModuleCat.epi_iff_surjective _).1 inferInstance

include v hv in
lemma witness_base_eq : f ≫ p = g ≫ p := by
  have he := congrArg (fun t => t ≫ p) (witnessLift_target R p v hv)
  rw [Category.assoc, target_projection, witnessLift_projection] at he
  exact he

lemma cellReverseLift_condition : witnessLift R p v hv ≫ source R p =
    (f ≫ diagonal R p) ≫ source R p := by
  rw [witnessLift_source, Category.assoc, diagonal_source, Category.comp_id]

def cellReverseLift : Path.Witness R (cellAugmentation R W ≫ witnessLift R p v hv)
    (cellAugmentation R W ≫ (f ≫ diagonal R p)) :=
  cellPathWitness R (source R p) (source_surjective R p)
    (source_quasiIso_of_surjective R p hs) (witnessLift R p v hv) (f ≫ diagonal R p)
    (cellReverseLift_condition R p v hv)

def cellReverse : Path.Witness R (cellAugmentation R W ≫ g) (cellAugmentation R W ≫ f) where
  hom := (cellReverseLift R p hs v hv).hom ≫ Path.map R (target R p)
  source_eq := by
    rw [Category.assoc, Path.map_source, ← Category.assoc,
      (cellReverseLift R p hs v hv).source_eq, Category.assoc, witnessLift_target]
  target_eq := by
    rw [Category.assoc, Path.map_target, ← Category.assoc,
      (cellReverseLift R p hs v hv).target_eq, Category.assoc, Category.assoc,
      diagonal_target, Category.comp_id]

lemma cellReverse_relative : (cellReverse R p hs v hv).hom ≫ Path.map R p =
    ((cellAugmentation R W ≫ g) ≫ p) ≫ Path.diagonal R B := by
  change ((cellReverseLift R p hs v hv).hom ≫ Path.map R (target R p)) ≫ _ = _
  rw [Category.assoc, ← Path.map_comp, target_projection, ← source_projection,
    Path.map_comp, ← Category.assoc, cellReverseLift, cellPathWitness_relative]
  rw [witnessLift_source, Category.assoc, Path.diagonal_naturality]
  simpa only [Category.assoc] using congrArg (fun t =>
    (cellAugmentation R W ≫ t) ≫ Path.diagonal R B) (witness_base_eq R p v hv)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.RelativePath
