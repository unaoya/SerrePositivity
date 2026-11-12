module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.OrdinalInterleaving
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.PartialColimits

/-!
概要：長さ κ₀ の全交互図式の余極限と、その μ-compact 性を同じ余錐で得る。
方針：交互添字の κ₀-filtered 性と μ-small 性を小 poset の compact 閉性へ渡す。
規約：全小余極限の存在や保存は仮定しない。
使われ方：相対交互構成の最終段の両成分とその像の compact 性。

対応節は Kerodon 9.4（Tag 06GT）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility

/-- 概要：長さ κ の両成分を交互に並べた元の添字は μ-small。
方針：段数 κ と二点の積を正則 μ で評価する。
規約：元の添字型を保持する。
使われ方：全交互図式の compact 余極限の小ささ。 -/
lemma alternatingIndex_hasCardinalLT {κ μ : Cardinal.{u}} [Fact μ.IsRegular]
    (hκμ : κ < μ) : HasCardinalLT (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingIndex κ) μ := by
  change HasCardinalLT (κ.ord.ToType × Fin 2) μ
  exact hasCardinalLT_prod (Cardinal.IsRegular.aleph0_le Fact.out)
    (by simpa [hasCardinalLT_iff_cardinal_mk_lt] using hκμ)
    (hasCardinalLT_of_finite _ _ (Cardinal.IsRegular.aleph0_le Fact.out))

/-- 概要：元の全交互 nerve の全非退化単体は同じ μ より小さい。
方針：小さい thin 圏の nerve の濃度変更判定を使う。
規約：各次数だけでなく元の IsKappaSmall を結論する。
使われ方：全前置図式と最終図式の compact 因子化。 -/
lemma alternatingNerve_isKappaSmall {κ μ : Cardinal.{u}}
    [Fact κ.IsRegular] [Fact μ.IsRegular] (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsCardinalChangeBound κ μ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall μ (nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingIndex κ)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isKappaSmall_nerve_of_cardinalChangeBound h _ (alternatingIndex_hasCardinalLT h.1)

/-- 概要：長さ κ の交互図式には元の μ-compact な余極限があり、その像も μ-compact。
方針：κ-filtered 余極限を取り、その同じ余錐と保存像に compact 閉性を適用する。
規約：κ-filtered 保存だけを入力に取り、μ-filtered と取り違えない。
使われ方：一般 accessible 引き戻しの相対交互構成の最終 compact 対象。 -/
lemma exists_alternatingColimit_compact_image
    {κ μ : Cardinal.{u}} [Fact κ.IsRegular] [Fact μ.IsRegular]
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsCardinalChangeBound κ μ)
    {C B : SSet.{u + 1}} [Quasicategory C] [Quasicategory B]
    (hC : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.HasSmallKappaFilteredColimits κ C)
    (p : C ⟶ B) (hpc : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ p)
    (F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingIndex κ)) ⟶ C)
    (hF : ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (F.app _ (ULift.up i)))
    (hFp : ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (p.app _ (F.app _ (ULift.up i)))) :
    ∃ c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone F, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ c.vertex ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (p.app _ c.vertex) := by
  have : IsCardinalFiltered (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingIndex κ) κ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.alternatingIndex_isCardinalFiltered κ
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ (nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingIndex κ)) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isKappaFiltered_nerve_of_cardinalFiltered _
  obtain ⟨c, hc⟩ := hC (nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingIndex κ)) F
  have hsmall := alternatingIndex_hasCardinalLT h.1
  refine ⟨c, hc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.isMuCompact_smallPosetColimit_universe.{u, u + 1}
    h (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingIndex κ) hsmall c hc ?_, ?_⟩
  · rintro ⟨i⟩
    exact hF i
  · apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.isMuCompact_smallPosetColimit_universe.{u, u + 1}
      h (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AlternatingIndex κ) hsmall (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone p c) (hpc _ F c hc)
    rintro ⟨i⟩
    exact hFp i

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility
