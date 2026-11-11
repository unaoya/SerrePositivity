module

public import Mathlib.AlgebraicTopology.SimplicialSet.FiniteColimits
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Cocone
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.SmallSimplicialShapes
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：filtered ∞ 圏と κ-filtered ∞ 圏の余錐による定義。
方針：有限または κ-small な全ての単体集合からの図式に実際の余錐を要求する。
規約：添字を通常の圏の nerve に制限しない。正則性は後続の定理で明示する。
使われ方：一般の coherent な filtered 図式、compact 対象と Indκ。

対応節は Kerodon 9.1（Tag 05WY）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories

/-- 概要：有限な全ての図式が余錐を持つ ∞ 圏。
方針：有限単体集合からの図式に join による余錐の非空性を課す。
規約：余錐に余極限性は要求しない。使われ方：通常の filtered ∞ 圏。 -/
@[kerodon 02PB]
class IsFilteredInfinity (C : SSet.{u}) [Quasicategory C] : Prop where
  cocone_nonempty {K : SSet.{u}} [K.Finite] (f : K ⟶ C) : Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone f)

/-- 概要：κ-small な全ての図式が余錐を持つ ∞ 圏。
方針：非退化単体の濃度を制限し、元の図式を延長する余錐を要求する。
規約：κ は同じ宇宙。正則な κ に対する理論の前提として用いる。
使われ方：Indκ と κ-compact 対象。 -/
@[kerodon 05X0]
class IsKappaFiltered (κ : Cardinal.{u}) (C : SSet.{u}) [Quasicategory C] : Prop where
  cocone_nonempty {K : SSet.{u}} (hK : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall κ K) (f : K ⟶ C) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone f)

/-- 概要：μ-filtered な ∞ 圏は κ ≤ μ のとき κ-filtered。
方針：試験形状の小ささの単調性を使う。
規約：図式も余錐も変更しない。使われ方：無限濃度間の filtered 性の比較。 -/
lemma isKappaFiltered_of_le {κ μ : Cardinal.{u}} {C : SSet.{u}} [Quasicategory C]
    (hκμ : κ ≤ μ) [IsKappaFiltered μ C] : IsKappaFiltered κ C where
  cocone_nonempty hK f := IsKappaFiltered.cocone_nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall.mono hK hκμ) f

/-- 概要：ℵ₀-filtered 性は filtered 性と同値。
方針：試験形状について ℵ₀-small 性と有限性の同値を適用する。
規約：一般の有限単体集合を全て試験する。使われ方：Ind と Indω の整合。 -/
@[kerodon 05X0]
lemma isKappaFiltered_aleph0_iff (C : SSet.{u}) [Quasicategory C] :
    IsKappaFiltered Cardinal.aleph0 C ↔ IsFilteredInfinity C := by
  constructor
  · intro h
    exact ⟨fun f ↦ h.cocone_nonempty ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.isKappaSmall_aleph0_iff _).2 inferInstance) f⟩
  · intro h
    refine ⟨fun hK f ↦ ?_⟩
    have := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.isKappaSmall_aleph0_iff _).1 hK
    exact h.cocone_nonempty f

/-- 概要：無限濃度について κ-filtered な ∞ 圏は filtered。
方針：有限な試験形状を κ-small とみなす。
規約：濃度の無限性を明示する。使われ方：κ 版から通常版への忘却。 -/
lemma isFilteredInfinity_of_isKappaFiltered {κ : Cardinal.{u}}
    (hκ : Cardinal.aleph0 ≤ κ) (C : SSet.{u}) [Quasicategory C] [IsKappaFiltered κ C] :
    IsFilteredInfinity C where
  cocone_nonempty f := IsKappaFiltered.cocone_nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.isKappaSmall_of_finite hκ _) f

/-- 概要：filtered ∞ 圏には頂点が存在する。
方針：有限な空形状からの図式の余錐の頂点を取る。
規約：非空性を別の定義フィールドに追加しない。
使われ方：filtered 添字の非空性の回収。 -/
lemma nonempty_vertices_of_isFilteredInfinity (C : SSet.{u}) [Quasicategory C]
    [IsFilteredInfinity C] : Nonempty (C _⦋0⦌) := by
  obtain ⟨c⟩ := IsFilteredInfinity.cocone_nonempty (initial.to C)
  exact ⟨c.vertex⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories
