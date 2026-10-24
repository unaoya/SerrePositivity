module

public import SerrePositivity.InfinityCategories.F2.Ind.ConeSlicePrismLift

/-!
概要：下方の元の全余錐と旧族の元の全円柱を、互換な二つの slice 持ち上げへ移す。
方針：下方余錐を先に持ち上げ、その同じ制限を全円柱の指定下方境界にする。
規約：元の両底図式と同じ D 側面を全射の等号で保持する。
使われ方：有限半順序形状の点追加で実 scalar comma の両境界を構成する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
/-- 概要：元の下方全余錐と旧族の全円柱は、全境界を保って二段で持ち上がる。
方針：同じ下方持ち上げを全円柱へ使用。規約：元の全射。使われ方：点追加の補間。 -/
lemma exists_coneSlice_twoStage_lift {A L X : SSet.{u}} [Quasicategory X]
    (d : join L (Δ[0] : SSet.{u}) ⟶ X)
    (b : join A (Δ[0] : SSet.{u}) ⊗ join L Δ[0] ⟶ X)
    (g : join (join A (Δ[0] : SSet.{u})) Δ[0] ⊗ L ⟶ X)
    (hOld : (joinMap (joinInl A (Δ[0] : SSet.{u})) (𝟙 Δ[0]) ▷ L) ≫ g =
      (join A (Δ[0] : SSet.{u}) ◁ joinInl L Δ[0]) ≫ b)
    (hG : (joinInr (join A (Δ[0] : SSet.{u})) Δ[0] ▷ L) ≫ g =
      snd (Δ[0] : SSet.{u}) L ≫ joinInl L Δ[0] ≫ d)
    (hB : (joinInr A (Δ[0] : SSet.{u}) ▷ join L Δ[0]) ≫ b =
      snd (Δ[0] : SSet.{u}) (join L Δ[0]) ≫ d) :
    ∃ U : join (join A (Δ[0] : SSet.{u})) Δ[0] ⊗ L ⟶ sliceOver (joinInr L Δ[0] ≫ d),
    ∃ W : join A (Δ[0] : SSet.{u}) ⊗ join L Δ[0] ⟶ sliceOver (joinInr L Δ[0] ≫ d),
      U ≫ sliceOverProjection (joinInr L Δ[0] ≫ d) = g ∧
      (joinInr (join A (Δ[0] : SSet.{u})) Δ[0] ▷ L) ≫ U =
        snd (Δ[0] : SSet.{u}) L ≫ joinInl L Δ[0] ≫ coneTerminalSliceSection d ∧
      W ≫ sliceOverProjection (joinInr L Δ[0] ≫ d) = b ∧
      (join A (Δ[0] : SSet.{u}) ◁ joinInl L Δ[0]) ≫ W =
        (joinMap (joinInl A (Δ[0] : SSet.{u})) (𝟙 Δ[0]) ▷ L) ≫ U ∧
      (joinInr A (Δ[0] : SSet.{u}) ▷ join L Δ[0]) ≫ W =
        snd (Δ[0] : SSet.{u}) (join L Δ[0]) ≫ coneTerminalSliceSection d := by
  obtain ⟨U, hU, hUt⟩ := exists_coneSlice_cone_lift d g hG
  let i := joinMap (joinInl A (Δ[0] : SSet.{u})) (𝟙 Δ[0])
  let a := (i ▷ L) ≫ U
  have ha : a ≫ sliceOverProjection (joinInr L Δ[0] ≫ d) =
      (join A (Δ[0] : SSet.{u}) ◁ joinInl L Δ[0]) ≫ b := by
    rw [Category.assoc, hU]
    exact hOld
  have hat : (joinInr A (Δ[0] : SSet.{u}) ▷ L) ≫ a =
      snd (Δ[0] : SSet.{u}) L ≫ joinInl L Δ[0] ≫ coneTerminalSliceSection d := by
    change (joinInr A (Δ[0] : SSet.{u}) ▷ L) ≫ (i ▷ L) ≫ U = _
    rw [← Category.assoc, ← comp_whiskerRight, joinInr_joinMap, Category.id_comp]
    exact hUt
  obtain ⟨W, hW, hWa, hWt⟩ := exists_coneSlice_prism_lift d b a hat ha hB
  exact ⟨U, W, hU, hUt, hW, hWa, hWt⟩
end SerrePositivity.InfinityCategories.F2.Ind
