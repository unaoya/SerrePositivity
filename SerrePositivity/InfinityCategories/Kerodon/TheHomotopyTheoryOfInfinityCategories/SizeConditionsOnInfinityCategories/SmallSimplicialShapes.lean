module

public import Mathlib.AlgebraicTopology.SimplicialSet.Finite
public import Mathlib.SetTheory.Cardinal.Regular
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：非退化単体の個数による κ-small な単体集合。
方針：非退化単体の型の濃度を用い、ℵ₀-small と有限性を比較する。
規約：κ と単体集合は同じ宇宙。正則性は必要な定理で別途明示する。
使われ方：filtered 図式の形状と Indκ の添字の大きさ。

対応節は Kerodon 4.9（Tag 03PP）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories

/-- 概要：非退化単体の集合の濃度が κ 未満であること。
方針：退化単体を重複計数せず、mathlib の非退化単体の型を使う。
規約：有限形状を ℵ₀-small として含む。
使われ方：κ-filtered 性で試験する全ての小さい図式。 -/
@[kerodon 03S2]
def IsKappaSmall (κ : Cardinal.{u}) (K : SSet.{u}) : Prop :=
  Cardinal.mk K.N < κ

/-- 概要：小ささの上限を増やすと κ-small 性は保たれる。
方針：濃度の不等式の推移性を使う。
規約：κ、μ の正則性は不要。使われ方：filtered 性の濃度に関する単調性。 -/
lemma IsKappaSmall.mono {κ μ : Cardinal.{u}} {K : SSet.{u}}
    (h : IsKappaSmall κ K) (hκμ : κ ≤ μ) : IsKappaSmall μ K :=
  lt_of_lt_of_le h hκμ

/-- 概要：ℵ₀-small な単体集合は有限単体集合とちょうど一致する。
方針：濃度が ℵ₀ 未満であることと型の有限性の同値を使う。
規約：各次数が有限であるだけの条件とは区別する。
使われ方：κ-filtered の ℵ₀ 特殊化を通常の filtered 性へ戻す。 -/
lemma isKappaSmall_aleph0_iff (K : SSet.{u}) :
    IsKappaSmall Cardinal.aleph0 K ↔ K.Finite := by
  rw [IsKappaSmall, Cardinal.mk_lt_aleph0_iff]
  exact ⟨fun h ↦ ⟨h⟩, fun h ↦ h.finite⟩

/-- 概要：有限形状は任意の無限濃度に関して小さい。
方針：ℵ₀-small 性から小ささの上限を増やす。
規約：無限性を ℵ₀ ≤ κ と明示する。使われ方：κ-filtered から filtered への制限。 -/
lemma isKappaSmall_of_finite {κ : Cardinal.{u}} (hκ : Cardinal.aleph0 ≤ κ)
    (K : SSet.{u}) [K.Finite] : IsKappaSmall κ K :=
  IsKappaSmall.mono ((isKappaSmall_aleph0_iff K).2 inferInstance) hκ

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories
