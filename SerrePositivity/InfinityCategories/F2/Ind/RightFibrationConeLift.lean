module

public import SerrePositivity.InfinityCategories.F2.Ind.RightFibrationPrismCorner

/-!
概要：right fibration で、元のパラメーター付き余錐の終端側面を保って持ち上げる。
方針：余錐点の right anodyne 性を任意のパラメーターとの積へ移す。
規約：元の全底図式と終端側面を保持し、両形状の有限性を課さない。
使われ方：下方の元の全余錐を同じ終点 slice へ持ち上げる。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
/-- 概要：元の全余錐を、指定終端側面を保って right fibration へ持ち上げる。
方針：余錐点とパラメーターの積の持ち上げ。規約：元の全射。使われ方：下方補間。 -/
lemma exists_rightFibration_cone_lift {A K E B : SSet.{u}}
    (p : E ⟶ B) [RightFibration p] (b : join A (Δ[0] : SSet.{u}) ⊗ K ⟶ B)
    (t : (Δ[0] : SSet.{u}) ⊗ K ⟶ E)
    (ht : t ≫ p = (joinInr A (Δ[0] : SSet.{u}) ▷ K) ≫ b) :
    ∃ W : join A (Δ[0] : SSet.{u}) ⊗ K ⟶ E,
      W ≫ p = b ∧ (joinInr A (Δ[0] : SSet.{u}) ▷ K) ≫ W = t := by
  have ha : rightAnodyneExtensions (joinInr A (Δ[0] : SSet.{u}) ▷ K) :=
    cofinalRightAnodyne_pushoutObjObj_left _ (conePoint_rightAnodyne A) (initial.to K)
      (.ofIsInitialRight (curriedTensor _) _ (initial.to K) initialIsInitial)
  have : HasLiftingProperty (joinInr A (Δ[0] : SSet.{u}) ▷ K) p :=
    ha p (RightFibration.mem (p := p))
  let sq : CommSq t (joinInr A (Δ[0] : SSet.{u}) ▷ K) p b := ⟨ht⟩
  exact ⟨sq.lift, sq.fac_right, sq.fac_left⟩

end SerrePositivity.InfinityCategories.F2.Ind
