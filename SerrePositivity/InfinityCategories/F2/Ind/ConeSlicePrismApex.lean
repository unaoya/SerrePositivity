module

public import SerrePositivity.InfinityCategories.F2.Ind.ConeTerminalSliceIdentity

/-!
概要：指定 D 側面を持つ全 slice 円柱の同じ二重頂点は終対象。
方針：元の側面の等号を二つの余錐点で制限し、同じ標準切断の終点へ戻す。
規約：元の全円柱の頂点を取り替えない。
使われ方：旧族全体を固定した三境界の相対再構成に終対象性を渡す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
/-- 概要：同じ指定 D 側面を持つ元の全円柱の二重頂点は終対象。
方針：元の全側面で制限。規約：元の頂点。使われ方：三境界の相対再構成。 -/
lemma coneSlicePrism_apex_isTerminal {A L X : SSet.{u}} [Quasicategory X]
    (d : join L (Δ[0] : SSet.{u}) ⟶ X)
    (W : join A (Δ[0] : SSet.{u}) ⊗ join L Δ[0] ⟶ sliceOver (joinInr L Δ[0] ≫ d))
    (h : (joinInr A (Δ[0] : SSet.{u}) ▷ join L Δ[0]) ≫ W =
      snd (Δ[0] : SSet.{u}) (join L Δ[0]) ≫ coneTerminalSliceSection d) :
    IsTerminalVertex (SSet.yonedaEquiv
      (lift (joinInr A (Δ[0] : SSet.{u})) (joinInr L Δ[0]) ≫ W)) := by
  have hi : lift (joinInr A (Δ[0] : SSet.{u})) (joinInr L Δ[0]) =
      lift (𝟙 (Δ[0] : SSet.{u})) (joinInr L Δ[0]) ≫
        (joinInr A (Δ[0] : SSet.{u}) ▷ join L Δ[0]) := by
    rw [lift_whiskerRight, Category.id_comp]
  rw [hi, Category.assoc, h, ← Category.assoc, lift_snd]
  exact coneTerminalSliceSection_tip_isTerminal d
end SerrePositivity.InfinityCategories.F2.Ind
