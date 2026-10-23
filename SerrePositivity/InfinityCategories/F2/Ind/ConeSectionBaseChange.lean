module

public import SerrePositivity.InfinityCategories.HomotopyLimits.RelativeRestrictionComparison
public import SerrePositivity.InfinityCategories.F1.FunctorCategories.RelativeFunctorBaseChangeNaturality

/-!
概要：同じ全錐の切断制限の同値性を、厳密な底変換から元の全空間へ戻す。
方針：元の底変換の切断同型と全制限自然性の可換正方形を二対三則で使う。
規約：全錐の実際の像と脚を保持。使われ方：Ind の comma から全係数極限判定への帰還。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
open HomotopyLimits

local instance coneSectionBaseChange_leftFibration {E B A : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (k : A ⟶ B) : LeftFibration (pullback.snd p k) :=
  ⟨leftFibrations.pullback_snd p k (LeftFibration.mem (p := p))⟩

/-- 厳密な底変換上の切断制限は、元の全空間上の同じ像の全錐の切断制限と同値に同値。 -/
lemma leftFibrationConeRestriction_baseChange_iff {K E B A : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (k : A ⟶ B) {D : K ⟶ A} (c : JoinCone D) :
    IsQCatEquivalence (leftFibrationConeRestriction (pullback.snd p k) c) ↔
      IsQCatEquivalence (leftFibrationConeRestriction p (mapJoinCone k c)) := by
  let g := Over.homMk (U := Over.mk D) (V := Over.mk c.val)
    (joinInr (Δ[0] : SSet.{u}) K) c.property
  have ha : IsQCatEquivalence (relativeFunctorBaseChangeForward p k D) :=
    (qCatEquivalenceOfIso (relativeFunctorBaseChangeIso p k D)).isQCatEquivalence
  have hb : IsQCatEquivalence (relativeFunctorBaseChangeForward p k c.val) :=
    (qCatEquivalenceOfIso (relativeFunctorBaseChangeIso p k c.val)).isQCatEquivalence
  have hn := relativeFunctorBaseChangeForward_overPre p k g
  change relativeFunctorOverPre (pullback.snd p k) g ≫
    relativeFunctorBaseChangeForward p k D = relativeFunctorBaseChangeForward p k c.val ≫
      relativeFunctorOverPre p ((Over.map k).map g) at hn
  rw [leftFibrationConeRestriction_eq_overPre, leftFibrationConeRestriction_eq_overPre]
  change IsQCatEquivalence (relativeFunctorOverPre (pullback.snd p k) g) ↔
    IsQCatEquivalence (relativeFunctorOverPre p ((Over.map k).map g))
  constructor
  · intro h
    have hh := h.comp ha
    rw [hn] at hh
    exact hb.cancel_left hh
  · intro h
    have hh := hb.comp h
    rw [← hn] at hh
    exact ha.cancel_right hh

end SerrePositivity.InfinityCategories.F2.Ind
