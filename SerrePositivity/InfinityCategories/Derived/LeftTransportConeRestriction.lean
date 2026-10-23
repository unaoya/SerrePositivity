module
public import SerrePositivity.InfinityCategories.HomotopyLimits.RelativeRestrictionComparison
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorBaseChangeNaturality
public import SerrePositivity.InfinityCategories.F1.Transport.LeftTransportRepresentation
/-!
概要：同じ全錐の切断制限を、底変換およびその分類図式の pointed-space 射影へ移す。
方針：元の底変換同型の制限自然性と、実表現の底上の比較を使う。
規約：実切断制限を保持する。使われ方：導来 Hom 関手による極限錐の検出。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits SSet HomotopyLimits
open scoped Simplicial
/-- 同じ全錐と実底変換の切断制限の比較。 -/
local instance coneRestrictionPullback_leftFibration {E B D : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) : LeftFibration (pullback.snd p k) :=
  ⟨leftFibrations.pullback_snd p k (LeftFibration.mem (p := p))⟩
/-- 同じ全錐と実底変換の切断制限の比較。 -/
lemma leftFibrationConeRestriction_baseChange_iff
    {K E B D : SSet.{u}} [Quasicategory B] [Quasicategory D]
    (p : E ⟶ B) [LeftFibration p] (k : D ⟶ B) {d : K ⟶ D} (c : JoinCone d) :
    IsQCatEquivalence (leftFibrationConeRestriction (pullback.snd p k) c) ↔
      IsQCatEquivalence (leftFibrationConeRestriction p (mapJoinCone k c)) := by
  let g := Over.homMk (U := Over.mk d) (V := Over.mk c.val)
    (joinInr (Δ[0] : SSet.{u}) K) c.property
  have hA : IsQCatEquivalence (relativeFunctorBaseChangeForward p k d) :=
    (qCatEquivalenceOfIso (relativeFunctorBaseChangeIso p k d)).isQCatEquivalence
  have hB : IsQCatEquivalence (relativeFunctorBaseChangeForward p k c.val) :=
    (qCatEquivalenceOfIso (relativeFunctorBaseChangeIso p k c.val)).isQCatEquivalence
  have hn := relativeFunctorBaseChangeForward_overPre p k g
  have hg : (Over.map k).map g = Over.homMk (U := Over.mk (d ≫ k))
      (V := Over.mk (mapJoinCone k c).val) (joinInr (Δ[0] : SSet.{u}) K)
      (mapJoinCone k c).property := by
    apply Over.OverMorphism.ext
    rfl
  rw [hg] at hn
  rw [leftFibrationConeRestriction_eq_overPre, leftFibrationConeRestriction_eq_overPre]
  constructor
  · intro h
    apply hB.cancel_left
    erw [← hn]
    exact h.comp hA
  · intro h
    apply hA.cancel_right
    erw [hn]
    exact hB.comp h
/-- 同じ全錐と実底変換の切断制限の比較。 -/
lemma LeftTransportRepresentation.coneRestriction_iff
    {K E B : SSet.{u + 1}} [Quasicategory B] (p : E ⟶ B) [LeftFibration p]
    (R : LeftTransportRepresentation p) {d : K ⟶ B} (c : JoinCone d) :
    IsQCatEquivalence (leftFibrationConeRestriction p c) ↔
      IsQCatEquivalence (leftFibrationConeRestriction pointedSpaceProjection
        (mapJoinCone R.diagram c)) := by
  have h := leftFibrationConeRestriction_isQCatEquivalence_iff_of_comparison
    p (leftUnstraighteningProjection R.diagram) R.comparison R.over_base
      R.isPrecompositionEquivalence c
  exact h.trans (leftFibrationConeRestriction_baseChange_iff pointedSpaceProjection R.diagram c)
end SerrePositivity.InfinityCategories
