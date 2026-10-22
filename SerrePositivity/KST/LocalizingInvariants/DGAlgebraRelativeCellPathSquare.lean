module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraRelativePathWitnessLift

/-!
概要：全射準同型の上の二つの並行な相対経路を、端点を固定する二重経路で比較する。
方針：相対二端点射の全射準同型性に cell 経路持ち上げをもう一度適用する。
規約：明示的な cell augmentation を一度前合成する。使われ方：class 自然性の経路整合。
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
  (hs : ∀ n : ℤ, Function.Surjective (p.hom.f n)) (hq : QuasiIso p.hom)
  {f g : W ⟶ C} (v w : Path.Witness R f g)
  (hv : v.hom ≫ Path.map R p = (f ≫ p) ≫ Path.diagonal R B)
  (hw : w.hom ≫ Path.map R p = (f ≫ p) ≫ Path.diagonal R B)

lemma parallelWitnessLift_endpoints : witnessLift R p v hv ≫ endpointsMap R p =
    witnessLift R p w hw ≫ endpointsMap R p := by
  apply MonoidPullback.hom_ext p p
  · change (witnessLift R p v hv ≫ endpointsMap R p) ≫ endpointsSource R p =
      (witnessLift R p w hw ≫ endpointsMap R p) ≫ endpointsSource R p
    rw [Category.assoc, endpointsMap_source, witnessLift_source,
      Category.assoc, endpointsMap_source, witnessLift_source]
  · change (witnessLift R p v hv ≫ endpointsMap R p) ≫ endpointsTarget R p =
      (witnessLift R p w hw ≫ endpointsMap R p) ≫ endpointsTarget R p
    rw [Category.assoc, endpointsMap_target, witnessLift_target,
      Category.assoc, endpointsMap_target, witnessLift_target]

def cellSquareRelative : Path.Witness R
    (cellAugmentation R W ≫ witnessLift R p v hv)
    (cellAugmentation R W ≫ witnessLift R p w hw) :=
  cellPathWitness R (endpointsMap R p) (endpointsMap_surjective R p)
    (endpointsMap_quasiIso R p hs hq) (witnessLift R p v hv) (witnessLift R p w hw)
    (parallelWitnessLift_endpoints R p v w hv hw)

lemma cellSquareRelative_endpoints : (cellSquareRelative R p hs hq v w hv hw).hom ≫
    Path.map R (endpointsMap R p) =
      (cellAugmentation R W ≫ witnessLift R p v hv ≫ endpointsMap R p) ≫
        Path.diagonal R (endpoints R p) := cellPathWitness_relative _ _ _ _ _ _ _

def cellSquareWitness : Path.Witness R (cellAugmentation R W ≫ v.hom)
    (cellAugmentation R W ≫ w.hom) where
  hom := (cellSquareRelative R p hs hq v w hv hw).hom ≫ Path.map R (inclusion R p)
  source_eq := by
    rw [Category.assoc, Path.map_source, ← Category.assoc,
      (cellSquareRelative R p hs hq v w hv hw).source_eq, Category.assoc, witnessLift_inclusion]
  target_eq := by
    rw [Category.assoc, Path.map_target, ← Category.assoc,
      (cellSquareRelative R p hs hq v w hv hw).target_eq, Category.assoc, witnessLift_inclusion]

lemma cellSquareRelative_factor {D : Mon (Complex R)} (t : algebra R p ⟶ D)
    (r : endpoints R p ⟶ D) (ht : t = endpointsMap R p ≫ r) :
    (cellSquareRelative R p hs hq v w hv hw).hom ≫ Path.map R t =
      (cellAugmentation R W ≫ witnessLift R p v hv ≫ t) ≫ Path.diagonal R D := by
  rw [ht, Path.map_comp, ← Category.assoc, cellSquareRelative_endpoints]
  simp only [Category.assoc, Path.diagonal_naturality]

lemma cellSquareWitness_source_trace : (cellSquareWitness R p hs hq v w hv hw).hom ≫
    Path.map R (Path.source R C) = (cellAugmentation R W ≫ f) ≫ Path.diagonal R C := by
  change ((cellSquareRelative R p hs hq v w hv hw).hom ≫ Path.map R (inclusion R p)) ≫ _ = _
  rw [Category.assoc, ← Path.map_comp]
  change (cellSquareRelative R p hs hq v w hv hw).hom ≫ Path.map R (source R p) = _
  rw [cellSquareRelative_factor R p hs hq v w hv hw (source R p) (endpointsSource R p)
    (endpointsMap_source R p).symm]
  simp only [Category.assoc, witnessLift_source]

lemma cellSquareWitness_target_trace : (cellSquareWitness R p hs hq v w hv hw).hom ≫
    Path.map R (Path.target R C) = (cellAugmentation R W ≫ g) ≫ Path.diagonal R C := by
  change ((cellSquareRelative R p hs hq v w hv hw).hom ≫ Path.map R (inclusion R p)) ≫ _ = _
  rw [Category.assoc, ← Path.map_comp]
  change (cellSquareRelative R p hs hq v w hv hw).hom ≫ Path.map R (target R p) = _
  rw [cellSquareRelative_factor R p hs hq v w hv hw (target R p) (endpointsTarget R p)
    (endpointsMap_target R p).symm]
  simp only [Category.assoc, witnessLift_target]


/-- 二重経路も元の底の定数二重経路を厳密に保つ。 -/
lemma cellSquareWitness_base_trace : (cellSquareWitness R p hs hq v w hv hw).hom ≫
    Path.map R (Path.map R p) =
      ((cellAugmentation R W ≫ f ≫ p) ≫ Path.diagonal R B) ≫
        Path.diagonal R (Path.algebra R B) := by
  change ((cellSquareRelative R p hs hq v w hv hw).hom ≫
    Path.map R (inclusion R p)) ≫ _ = _
  rw [Category.assoc, ← Path.map_comp, condition]
  have ht : projection R p ≫ Path.diagonal R B =
      endpointsMap R p ≫ (endpointsSource R p ≫ p ≫ Path.diagonal R B) := by
    simp only [← Category.assoc, endpointsMap_source, source_projection]
  rw [cellSquareRelative_factor R p hs hq v w hv hw _ _ ht]
  rw [← Category.assoc (witnessLift R p v hv), witnessLift_projection]
  simp only [Category.assoc]


end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.RelativePath
