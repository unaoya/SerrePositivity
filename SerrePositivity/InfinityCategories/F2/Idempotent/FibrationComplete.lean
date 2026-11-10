module

public import SerrePositivity.InfinityCategories.Core.Idempotent.Coherent
public import SerrePositivity.InfinityCategories.F2.Idempotent.IdemConeRestriction
public import SerrePositivity.InfinityCategories.HomotopyLimits.Idempotent.IdemCoconeRestriction
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：左右 fibration の標的が冪等完備なら、その全体も冪等完備。
方針：元の Idem 包含の左右 anodyne 性で、底の強い分裂全体を厳密に持ち上げる。
規約：持ち上げは元の全図式を回収し、極限の存在を入力に置かない。
使われ方：HTT 5.1.4.3 の slice と coslice の冪等完備性。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 右 fibration の底が冪等完備なら、元の全体も厳密な強い分裂を持つ。 -/
@[kerodon 0606]
lemma isIdempotentComplete_of_rightFibration {X Y : SSet.{u}} (p : X ⟶ Y)
    [RightFibration p] (hY : IsIdempotentComplete Y) : IsIdempotentComplete X := by
  intro d
  obtain ⟨s⟩ := hY (d ≫ p)
  have : HasLiftingProperty idemInclusion p :=
    idemInclusion_rightAnodyne p (RightFibration.mem (p := p))
  have sq : CommSq d idemInclusion p s.val := ⟨s.property.symm⟩
  exact ⟨⟨sq.lift, sq.fac_left⟩⟩

/-- 左 fibration の底が冪等完備なら、元の全体も厳密な強い分裂を持つ。 -/
@[kerodon 0606]
lemma isIdempotentComplete_of_leftFibration {X Y : SSet.{u}} (p : X ⟶ Y)
    [LeftFibration p] (hY : IsIdempotentComplete Y) : IsIdempotentComplete X := by
  intro d
  obtain ⟨s⟩ := hY (d ≫ p)
  have : HasLiftingProperty idemInclusion p :=
    idemInclusion_leftAnodyne p (LeftFibration.mem (p := p))
  have sq : CommSq d idemInclusion p s.val := ⟨s.property.symm⟩
  exact ⟨⟨sq.lift, sq.fac_left⟩⟩

end SerrePositivity.InfinityCategories.F2.Idempotent
