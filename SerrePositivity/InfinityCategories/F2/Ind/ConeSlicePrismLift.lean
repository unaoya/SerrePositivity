module

public import SerrePositivity.InfinityCategories.F2.Ind.ConeTerminalSliceSection
public import SerrePositivity.InfinityCategories.F2.Ind.RightFibrationConeLift
public import SerrePositivity.InfinityCategories.F2.Ind.RightFibrationTensorCorner

/-!
概要：一般の下方形状の全余錐と円柱を、同じ指定終点の slice へ持ち上げる。
方針：元の D の標準切断を終端側面とし、right fibration の相対持ち上げを使う。
規約：全底図式・下方全境界・元の D 側面を厳密に保持する。
使われ方：有限半順序形状の点追加における二段補間の実 slice データ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {L X : SSet.{u}} [Quasicategory X] (d : join L (Δ[0] : SSet.{u}) ⟶ X)

/-- 概要：下方の全余錐を、元の D の同じ終端側面を保って持ち上げる。
方針：余錐点の right anodyne 性。規約：元の全射。使われ方：下方全族の slice 表示。 -/
lemma exists_coneSlice_cone_lift {A : SSet.{u}} (b : join A (Δ[0] : SSet.{u}) ⊗ L ⟶ X)
    (ht : (joinInr A (Δ[0] : SSet.{u}) ▷ L) ≫ b =
      snd (Δ[0] : SSet.{u}) L ≫ joinInl L Δ[0] ≫ d) :
    ∃ W : join A (Δ[0] : SSet.{u}) ⊗ L ⟶ sliceOver (joinInr L Δ[0] ≫ d),
      W ≫ sliceOverProjection (joinInr L Δ[0] ≫ d) = b ∧
      (joinInr A (Δ[0] : SSet.{u}) ▷ L) ≫ W =
        snd (Δ[0] : SSet.{u}) L ≫ joinInl L Δ[0] ≫ coneTerminalSliceSection d := by
  apply exists_rightFibration_cone_lift (sliceOverProjection (joinInr L Δ[0] ≫ d)) b
    (snd (Δ[0] : SSet.{u}) L ≫ joinInl L Δ[0] ≫ coneTerminalSliceSection d)
  rw [Category.assoc, Category.assoc, coneTerminalSliceSection_projection]
  exact ht.symm

/-- 概要：元の全円柱を、指定下方境界と元の D 側面を同時に保って持ち上げる。
方針：一般の二境界付き right fibration 持ち上げ。規約：全射の等号。使われ方：全補間。 -/
lemma exists_coneSlice_prism_lift {A : SSet.{u}}
    (b : join A (Δ[0] : SSet.{u}) ⊗ join L Δ[0] ⟶ X)
    (a : join A (Δ[0] : SSet.{u}) ⊗ L ⟶ sliceOver (joinInr L Δ[0] ≫ d))
    (h : (joinInr A (Δ[0] : SSet.{u}) ▷ L) ≫ a =
      snd (Δ[0] : SSet.{u}) L ≫ joinInl L Δ[0] ≫ coneTerminalSliceSection d)
    (ha : a ≫ sliceOverProjection (joinInr L Δ[0] ≫ d) =
      (join A (Δ[0] : SSet.{u}) ◁ joinInl L Δ[0]) ≫ b)
    (ht : (joinInr A (Δ[0] : SSet.{u}) ▷ join L Δ[0]) ≫ b =
      snd (Δ[0] : SSet.{u}) (join L Δ[0]) ≫ d) :
    ∃ W : join A (Δ[0] : SSet.{u}) ⊗ join L Δ[0] ⟶ sliceOver (joinInr L Δ[0] ≫ d),
      W ≫ sliceOverProjection (joinInr L Δ[0] ≫ d) = b ∧
      (join A (Δ[0] : SSet.{u}) ◁ joinInl L Δ[0]) ≫ W = a ∧
      (joinInr A (Δ[0] : SSet.{u}) ▷ join L Δ[0]) ≫ W =
        snd (Δ[0] : SSet.{u}) (join L Δ[0]) ≫ coneTerminalSliceSection d := by
  apply exists_rightFibration_tensor_corner_lift (sliceOverProjection (joinInr L Δ[0] ≫ d))
    (joinInr A (Δ[0] : SSet.{u})) (conePoint_rightAnodyne A) (joinInl L Δ[0]) b a
    (snd (Δ[0] : SSet.{u}) (join L Δ[0]) ≫ coneTerminalSliceSection d)
  · rw [← Category.assoc, whiskerLeft_snd, Category.assoc]
    exact h
  · exact ha
  · rw [Category.assoc, coneTerminalSliceSection_projection]
    exact ht.symm

end SerrePositivity.InfinityCategories.F2.Ind
