module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.Stability
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.CompactGeneratorImage

/-!
概要：安定 Ind の compact 生成と元の完全 Yoneda を一つの公開界面にまとめる。
方針：保存済みの安定性・生成同値・同じ頂点の filtered 表示をそのまま組み合わせる。
規約：交換入力と C の有限全存在を明示し、同値の順射を元の compact Yoneda に固定。
使われ方：I-2 c・e の結論、および K-B の K-7 d4 向け入力。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

/-- 安定性・完全包含・実生成同値と、任意の元の頂点の compact 生成表示。 -/
structure StableCompactGeneration (κ : Cardinal.{u}) (C : SSet.{u}) [Quasicategory C] where
  /-- 元の Ind 自身の安定性。 -/
  stable : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C)
  /-- 元の全 Yoneda の充満忠実性。 -/
  fullyFaithful : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ C)
  /-- 同じ Yoneda の完全性。 -/
  exactYoneda : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ C)
  /-- 同じ Yoneda 像の κ-compact 性。 -/
  yonedaCompact : ∀ x : C _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} κ
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ C).app (Opposite.op ⦋0⦌) (ULift.up x))
  /-- 元の C と compact 部分との実同値。 -/
  equivalence : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence ((SSet.uliftFunctor.{u + 1, u}).obj C)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactObjects.{u, u + 1} κ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C))
  /-- 選択した同値の順射を元の compact Yoneda に固定する。 -/
  equivalence_hom : equivalence.hom = _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.compactIndYoneda κ C
  /-- 任意の元の頂点そのものを頂点とする、小さい filtered 生成表示。 -/
  generated : ∀ x : (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C) _⦋0⦌,
    ∃ (I : SSet.{u}) (hI : Quasicategory I),
      letI := hI
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ I ∧ ∃ a : I ⟶ C,
        ∃ c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone ((SSet.uliftFunctor.{u + 1, u}).map a ≫ equivalence.hom ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactInclusion.{u, u + 1} κ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C)),
          c.vertex = x ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c

/-- 明示交換入力のもとで、安定な冪等完備 C の安定 compact 生成界面を構成。 -/
def ind_stableCompactGeneration (κ : Cardinal.{u}) [Fact κ.IsRegular]
    (hκ : Cardinal.aleph0 ≤ κ) (hex : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndFiniteLimitExchangeInput.{u})
    (C : SSet.{u}) [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C]
    [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits C] [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteColimits C]
    (hC : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete C) : StableCompactGeneration κ C where
  stable := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.ind_isStable κ hκ hex C
  fullyFaithful := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda_isFullyFaithful κ C
  exactYoneda := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda_isExactFunctor κ hκ hex C
  yonedaCompact := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.indYoneda_isKappaCompact κ
  equivalence := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.compactGenerationEquivalence κ hC
  equivalence_hom := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.compactGenerationEquivalence_hom κ hC
  generated := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indVertex_has_compactGeneratorPresentation κ hC

/-- 公開界面の選んだ逆射は、元の全 compact 包含を回収する。 -/
def StableCompactGeneration.inverse_inclusion {κ : Cardinal.{u}} [Fact κ.IsRegular]
    {C : SSet.{u}} [Quasicategory C] (g : StableCompactGeneration κ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (g.equivalence.inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ C)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactInclusion.{u, u + 1} κ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.compactGenerationChoice_inclusion κ g.equivalence g.equivalence_hom

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
