module

public import SerrePositivity.InfinityCategories.F2.Ind.SmallPushout
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FilteredCosliceCofinality
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.KappaFilteredCoslices

/-!
概要：小さい全前置図式の下の表示添字は、元の filtered 添字へ共終に射影する。
方針：小さい二図式の和の coslice と、元の頂点 comma を実引き戻しで比較する。
規約：前置図式に有限性・終対象を要求しない。
使われ方：極限前置段全体を固定した同じ表示の filtered 余極限。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback

/-- 概要：二つの μ-small 形状の元の直和も μ-small。
方針：始対象からの単射の pushout と同型で比較する。
規約：非退化単体の個数の小ささを保持する。
使われ方：全前置図式と一点を同時に含む comma の形状。 -/
lemma isKappaSmall_coprod {μ : Cardinal.{u}} (hμ : μ.IsRegular)
    {K L : SSet.{u}} (hK : IsKappaSmall μ K) (hL : IsKappaSmall μ L) :
    IsKappaSmall μ (K ⨿ L) := by
  have h := Ind.isKappaSmall_pushout_of_mono hμ (initial.to K) (initial.to L) hK hL
  exact (Ind.isKappaSmall_iff_of_iso (IsPushout.of_hasBinaryCoproduct' K L).isoPushout).mpr h

/-- 概要：μ-small な全前置図式の coslice 射影は元の μ-filtered 圏へ right cofinal。
方針：各頂点 comma を前置図式と一点の和の coslice と同型にする。
規約：前置図式が終頂点を持つとは仮定しない。
使われ方：表示添字の全前置段を固定する相対因子化の共終性。 -/
lemma smallPrefix_cosliceProjection_isRightCofinal
    {μ : Cardinal.{u}} (hμ : μ.IsRegular)
    {K I : SSet.{u}} [Quasicategory I] [IsKappaFiltered μ I]
    (hK : IsKappaSmall μ K) (a : K ⟶ I) :
    IsRightCofinal (sliceUnderProjection a) := by
  apply isRightCofinal_of_weaklyContractible_coslices
  intro b
  have hshape := isKappaSmall_coprod hμ hK (isKappaSmall_of_finite hμ.aleph0_le Δ[0])
  have h := isWeaklyContractible_sliceUnder_of_kappaFiltered hμ hshape
    (coprod.desc a (SSet.yonedaEquiv.symm b))
  have he := (isPrecompositionEquivalence_of_iso
    (cosliceCoproduct_isPullback a (SSet.yonedaEquiv.symm b)).isoPullback).isWeakHomotopyEquivalence
  exact he.weaklyContractible_iff.mp h

end SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback
