module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.SmallShapeSimplices

/-!
概要：非可算正則 μ での形状の小ささは単体集合の積で保たれる。
方針：積の各単体を元の二つの単体へ埋め込み、全単体の小ささを使う。
規約：積の非退化単体は両成分で非退化とは限らないため、全単体で比較する。
使われ方：μ-small な形状と標準単体の積に対する因子化。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 全次数の単体の小ささは、単体集合の同じ積で保たれる。 -/
lemma hasCardinalLT_tensor_simplices {μ : Cardinal.{u}} (hμ : Cardinal.aleph0 ≤ μ)
    {K L : SSet.{u}} (hK : HasCardinalLT K.S μ) (hL : HasCardinalLT L.S μ) :
    HasCardinalLT (K ⊗ L).S μ := by
  have hp := hasCardinalLT_prod hμ hK hL
  apply hp.of_injective (fun s ↦ (S.mk s.simplex.1, S.mk s.simplex.2))
  intro s t h
  have hfst := congrArg Prod.fst h
  have hsnd := congrArg Prod.snd h
  cases s with
  | @mk n xy =>
    cases t with
    | @mk m zw =>
      rcases xy with ⟨x, y⟩
      rcases zw with ⟨z, w⟩
      cases hfst
      cases hsnd
      rfl

/-- 非可算正則 μ に対して、元の二つの μ-small な形状の積も μ-small。 -/
lemma isKappaSmall_tensor {μ : Cardinal.{u}} [Fact μ.IsRegular]
    (hμ : Cardinal.aleph0 < μ) {K L : SSet.{u}} (hK : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall μ K)
    (hL : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall μ L) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall μ (K ⊗ L) := by
  have hs := hasCardinalLT_tensor_simplices hμ.le
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.hasCardinalLT_allSimplices_of_isKappaSmall hμ hK)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.hasCardinalLT_allSimplices_of_isKappaSmall hμ hL)
  have hn : HasCardinalLT (K ⊗ L).N μ :=
    hs.of_injective N.toS (fun _ _ h ↦ (N.ext_iff _ _).mpr h)
  exact (hasCardinalLT_iff_cardinal_mk_lt _ _).mp hn

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
