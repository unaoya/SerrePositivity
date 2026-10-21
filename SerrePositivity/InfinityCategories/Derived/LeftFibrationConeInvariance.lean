module
public import SerrePositivity.InfinityCategories.Derived.LeftFibrationFiberInvariance
public import SerrePositivity.InfinityCategories.HomotopyLimits.LeftFibrationConeRestriction
public import SerrePositivity.InfinityCategories.Core.EquivalenceLimits
/-!
概要：同じ全錐から底への切断制限の同値性を、錐全体の全関手同型に沿って移す。
方針：終域の等式輸送を消し、元の相対前合成の同値判定へ戻す。
規約：底図式と錐の値を保持する。使われ方：導来 Hom 試験の全錐比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet HomotopyLimits
open scoped Simplicial
/-- 同じ全錐の切断制限の同値性の不変性。 -/
lemma leftFibrationConeRestriction_isQCatEquivalence_iff_pre
    {K E B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [LeftFibration p]
    {d : K ⟶ B} (c : JoinCone d) :
    IsQCatEquivalence (leftFibrationConeRestriction p c) ↔
      IsQCatEquivalence (relativeFunctorPre p c.val (joinInr (Δ[0] : SSet.{u}) K)) := by
  have h := (qCatEquivalenceOfIso
    (eqToIso (congrArg (relativeFunctorSpace p) c.property))).isQCatEquivalence
  constructor
  · intro hc
    exact h.cancel_right hc
  · intro hc
    exact hc.comp h
/-- 同じ全錐の切断制限の同値性の不変性。 -/
lemma leftFibrationConeRestriction_isQCatEquivalence_iff_of_functorIso
    {K E B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [LeftFibration p]
    {d d' : K ⟶ B} (c : JoinCone d) (c' : JoinCone d') (e : FunctorIso c.val c'.val) :
    IsQCatEquivalence (leftFibrationConeRestriction p c) ↔
      IsQCatEquivalence (leftFibrationConeRestriction p c') := by
  rw [leftFibrationConeRestriction_isQCatEquivalence_iff_pre,
    leftFibrationConeRestriction_isQCatEquivalence_iff_pre]
  exact relativeFunctorPre_isQCatEquivalence_iff_of_functorIso p _ e
/-- 同じ全錐の切断制限の同値性の不変性。 -/
lemma leftFibrationConeRestriction_mapJoinCone_iff_of_functorIso
    {K X E B : SSet.{u}} [Quasicategory B] (p : E ⟶ B) [LeftFibration p]
    {F G : X ⟶ B} (e : FunctorIso F G) {d : K ⟶ X} (c : JoinCone d) :
    IsQCatEquivalence (leftFibrationConeRestriction p (mapJoinCone F c)) ↔
      IsQCatEquivalence (leftFibrationConeRestriction p (mapJoinCone G c)) :=
  leftFibrationConeRestriction_isQCatEquivalence_iff_of_functorIso p _ _ (e.precomp c.val)
end SerrePositivity.InfinityCategories
