module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathBoundaryComparison
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCellResolutionMapLift

/-!
概要：指定した底の実経路と両端を、一回の cell augmentation 後に厳密に持ち上げる。
方針：両端と全底経路を homotopy pullback に束ね、境界比較の全射準同型性で持ち上げる。
規約：底の経路を選び直さない。使われ方：元の右経路を保つ class 比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
variable (R : Type u) [CommRing R] {W C B : Mon (Complex R)} (p : C ⟶ B)
  (hs : ∀ n : ℤ, Function.Surjective (p.hom.f n)) (hq : QuasiIso p.hom)
  {f g : W ⟶ C} (w : Path.Witness R (f ≫ p) (g ≫ p))

def fixedBasePathCone : W ⟶ HomotopyPullbackModel.algebra R p p :=
  HomotopyPullbackModel.lift R p p f g w

def cellFixedBasePathLift : cellResolution R W ⟶ Path.algebra R C :=
  cellResolutionMapLift R (fixedBasePathCone R p w) (Path.boundaryMap R p)
    (Path.boundaryMap_surjective R p hs) (Path.boundaryMap_quasiIso R p hq)

lemma cellFixedBasePathLift_boundary : cellFixedBasePathLift R p hs hq w ≫
    Path.boundaryMap R p = cellAugmentation R W ≫ fixedBasePathCone R p w :=
  cellResolutionMapLift_projection R _ _ _ _

lemma cellFixedBasePathLift_source : cellFixedBasePathLift R p hs hq w ≫ Path.source R C =
    cellAugmentation R W ≫ f := by
  rw [← Path.boundaryMap_source R p, ← Category.assoc, cellFixedBasePathLift_boundary,
    Category.assoc]
  exact congrArg (fun t => cellAugmentation R W ≫ t)
    (HomotopyPullbackModel.lift_left R p p f g w)

lemma cellFixedBasePathLift_target : cellFixedBasePathLift R p hs hq w ≫ Path.target R C =
    cellAugmentation R W ≫ g := by
  rw [← Path.boundaryMap_target R p, ← Category.assoc, cellFixedBasePathLift_boundary,
    Category.assoc]
  exact congrArg (fun t => cellAugmentation R W ≫ t)
    (HomotopyPullbackModel.lift_right R p p f g w)

lemma cellFixedBasePathLift_map : cellFixedBasePathLift R p hs hq w ≫ Path.map R p =
    cellAugmentation R W ≫ w.hom := by
  rw [← Path.boundaryMap_path R p, ← Category.assoc, cellFixedBasePathLift_boundary,
    Category.assoc]
  exact congrArg (fun t => cellAugmentation R W ≫ t)
    (HomotopyPullbackModel.lift_path R p p f g w)

def Path.Witness.cellLiftFixedBase : Path.Witness R (cellAugmentation R W ≫ f)
    (cellAugmentation R W ≫ g) where
  hom := cellFixedBasePathLift R p hs hq w
  source_eq := cellFixedBasePathLift_source R p hs hq w
  target_eq := cellFixedBasePathLift_target R p hs hq w

lemma Path.Witness.cellLiftFixedBase_map : (w.cellLiftFixedBase R p hs hq).hom ≫ Path.map R p =
    cellAugmentation R W ≫ w.hom := cellFixedBasePathLift_map R p hs hq w

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
