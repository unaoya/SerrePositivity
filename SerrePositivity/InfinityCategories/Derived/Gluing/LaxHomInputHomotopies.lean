module
public import SerrePositivity.InfinityCategories.Derived.Gluing.LaxHomCompositionInputLifts
public import SerrePositivity.InfinityCategories.Derived.Gluing.HomDerivedCompositionInputLifts
public import SerrePositivity.InfinityCategories.F1B.TrivialFibrationHomotopy

/-! 元の二三角形と係数模型の二三角形を、同じ元 Hom 入力の上で結ぶ。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory DifferentialGraded SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] (M : Bimodule R C D)

lemma dgGluingLaxHomFirstInputHomotopy_exists (X Y : DGGluingObject R C D M) :
    ∃ H : SSet.Homotopy (dgGluingLaxHomFirstCompositionInputLift R C D M X Y)
        (dgGluingHomDerivedFirstCompositionInputLift R C D M X Y),
      H.h ≫ dgGluingDerivedFirstCompositionInputProjection R C D M X Y =
        fst _ (Δ[1] : SSet.{max (u + 1) v w}) ≫
          (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
            (complexPinchedMap.{u, max u v w} (dgGluingRightHomMap R C D M X Y)) := by
  have := dgGluingDerivedFirstCompositionInputProjection_trivialKanFibration R C D M X Y
  obtain ⟨H, hh⟩ := exists_homotopy_over_trivialKanFibration
    (dgGluingDerivedFirstCompositionInputProjection R C D M X Y)
    (dgGluingLaxHomFirstCompositionInputLift R C D M X Y)
    (dgGluingHomDerivedFirstCompositionInputLift R C D M X Y) (by
      rw [dgGluingLaxHomFirstCompositionInputLift_input R C D M X Y,
        dgGluingHomDerivedFirstCompositionInputLift_input R C D M X Y])
  refine ⟨H, ?_⟩
  simpa only [Category.assoc, dgGluingHomDerivedFirstCompositionInputLift_input R C D M X Y]
    using hh

lemma dgGluingLaxHomLastInputHomotopy_exists (X Y : DGGluingObject R C D M) :
    ∃ H : SSet.Homotopy (dgGluingLaxHomLastCompositionInputLift R C D M X Y)
        (dgGluingHomDerivedLastCompositionInputLift R C D M X Y),
      H.h ≫ dgGluingDerivedLastCompositionInputProjection R C D M X Y =
        fst _ (Δ[1] : SSet.{max (u + 1) v w}) ≫
          (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
            (complexPinchedMap.{u, max u v w} (dgGluingLeftHomMap R C D M X Y)) := by
  have := dgGluingDerivedLastCompositionInputProjection_trivialKanFibration R C D M X Y
  obtain ⟨H, hh⟩ := exists_homotopy_over_trivialKanFibration
    (dgGluingDerivedLastCompositionInputProjection R C D M X Y)
    (dgGluingLaxHomLastCompositionInputLift R C D M X Y)
    (dgGluingHomDerivedLastCompositionInputLift R C D M X Y) (by
      rw [dgGluingLaxHomLastCompositionInputLift_input R C D M X Y,
        dgGluingHomDerivedLastCompositionInputLift_input R C D M X Y])
  refine ⟨H, ?_⟩
  simpa only [Category.assoc, dgGluingHomDerivedLastCompositionInputLift_input R C D M X Y]
    using hh

def dgGluingLaxHomFirstInputHomotopy (X Y : DGGluingObject R C D M) :=
  Classical.choose (dgGluingLaxHomFirstInputHomotopy_exists R C D M X Y)

def dgGluingLaxHomLastInputHomotopy (X Y : DGGluingObject R C D M) :=
  Classical.choose (dgGluingLaxHomLastInputHomotopy_exists R C D M X Y)

lemma dgGluingLaxHomFirstInputHomotopy_over (X Y : DGGluingObject R C D M) :
    (dgGluingLaxHomFirstInputHomotopy R C D M X Y).h ≫
        dgGluingDerivedFirstCompositionInputProjection R C D M X Y =
      fst _ (Δ[1] : SSet.{max (u + 1) v w}) ≫
        (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
          (complexPinchedMap.{u, max u v w} (dgGluingRightHomMap R C D M X Y)) :=
  Classical.choose_spec (dgGluingLaxHomFirstInputHomotopy_exists R C D M X Y)

lemma dgGluingLaxHomLastInputHomotopy_over (X Y : DGGluingObject R C D M) :
    (dgGluingLaxHomLastInputHomotopy R C D M X Y).h ≫
        dgGluingDerivedLastCompositionInputProjection R C D M X Y =
      fst _ (Δ[1] : SSet.{max (u + 1) v w}) ≫
        (SSet.uliftFunctor.{max (u + 1) v w, max u v w}).map
          (complexPinchedMap.{u, max u v w} (dgGluingLeftHomMap R C D M X Y)) :=
  Classical.choose_spec (dgGluingLaxHomLastInputHomotopy_exists R C D M X Y)

end SerrePositivity.InfinityCategories
