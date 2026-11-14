module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.CoherentConeSectionSpace

/-!
概要：同じjoin錐のcoslice切断の全単体は、元の全射の同じセルへの制限。
方針：curryの既存定義と指定頂点の等式消去を使う。
規約：IS-W2 D01の既存構成の評価則。頂点だけに制限しない。
使われ方：Kerodon 7.4.1、元のnative Tot錐の全セルとの照合。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open scoped Simplicial

/-- 同じ正規化coslice切断の各単体は、元の全join射の同じセル制限。 -/
theorem coherentConeCosliceSection_cell {K X : SSet.{u}} {p : K ⟶ X}
    (c : JoinCone p) (z : X _⦋0⦌) (h : c.vertex = z) {n : ℕ} (σ : K _⦋n⦌) :
    (((coherentConeCosliceSection c ≫ eqToHom (congrArg
      (fun w => sliceUnder (SSet.yonedaEquiv.symm w)) h)).app
        (Opposite.op ⦋n⦌) σ)).val =
      joinMap (𝟙 Δ[0]) (SSet.yonedaEquiv.symm σ) ≫ c.val := by
  cases h
  simp only [eqToHom_refl, Category.comp_id]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces
