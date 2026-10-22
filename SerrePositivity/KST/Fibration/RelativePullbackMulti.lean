module
public import SerrePositivity.KST.Fibration.RelativePullbackIteration
public import SerrePositivity.KST.SConstruction.RelativeMultiRealizationAdditivity

/-! # 共同反映を持つ元の相対引き戻し比較の全正有限反復 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open SerrePositivity.KST.SConstruction
open SerrePositivity.SimplicialModel
namespace SerrePositivity.KST.Fibration

/-- 反復座標の同型は、元の射影と保持した quotient の射対を厳密に保つ。 -/
lemma RelativePullback.iteratedCoordinate_pair {X : StableModel.{u}}
    {A B : ClosedStablePredicate X} (D : RelativePullback X A B) (r : ℕ) :
    D.iteratedPair r ≫ ((iteratedSRealizationCoordinateIso r D.base).hom ⊗ₘ
      (iteratedSRealizationCoordinateIso r (closedStableModel B)).hom) =
        (iteratedSRealizationCoordinateIso r D.total).hom ≫
          D.pair (multiRealizationFunctor (r + 1)) := by
  rw [D.iteratedPair_eq]
  unfold RelativePullback.pair
  rw [lift_map, comp_lift, iteratedSRealizationCoordinateIso_naturality,
    iteratedSRealizationCoordinateIso_naturality]

/-- 全相対引き戻し比較の前段から、次の全多重対角の元の射対の同値性を得る。 -/
lemma RelativePullback.multiPair_step_localized_isIso (r : ℕ)
    (hr : ∀ (Y : StableModel.{u}) (P Q : ClosedStablePredicate Y) (E : RelativePullback Y P Q),
      IsIso (AnodyneHomotopy.anodyneQ.map (E.pair (multiRealizationFunctor r))))
    {X : StableModel.{u}} {A B : ClosedStablePredicate X} (D : RelativePullback X A B) :
    IsIso (AnodyneHomotopy.anodyneQ.map (D.pair (multiRealizationFunctor (r + 1)))) := by
  let Q := AnodyneHomotopy.anodyneQ
  have := D.iteratedPair_localized_isIso r hr
  have he := congrArg Q.map (D.iteratedCoordinate_pair r)
  rw [Q.map_comp, Q.map_comp] at he
  have hi : IsIso (Q.map (iteratedSRealizationCoordinateIso r D.total).hom ≫
      Q.map (D.pair (multiRealizationFunctor (r + 1)))) := he ▸ inferInstance
  exact (isIso_comp_left_iff _ _).mp hi

/-- 元の実引き戻しと共同反映から、全正有限反復の同じ射影・quotient 比較は局所化同型。 -/
theorem RelativePullback.multiPair_localized_isIso (r : ℕ) {X : StableModel.{u}}
    {A B : ClosedStablePredicate X} (D : RelativePullback X A B) :
    IsIso (AnodyneHomotopy.anodyneQ.map (D.pair (multiRealizationFunctor (r + 1)))) := by
  induction r generalizing X with
  | zero => exact D.singlePair_localized_isIso
  | succ r ih =>
    exact D.multiPair_step_localized_isIso (r + 1) (fun _ _ _ => ih)

end SerrePositivity.KST.Fibration
