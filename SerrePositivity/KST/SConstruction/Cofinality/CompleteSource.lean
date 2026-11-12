module
public import SerrePositivity.KST.SConstruction.KSpectrumInvariance
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.CompleteImageRetracts
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.Completion
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.EquivalenceStability

/-!
概要：始域も冪等完備な場合に、指定完備化射の実 K 比較を全整数次数で証明する。
方針：充満忠実な像の retract 閉性から同じ射の本質全射性を得て、既存の同値不変性を使う。
規約：一般の共終性とは区別する。始域の完備性はこの補助結果だけの明示入力。
使われ方：共終性の完備始域の場合の検算と、元の K 射を保持する比較。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open Spectra

/-- 概要：始域も完備なら、指定完備化射の各対象は同じ射の像と同型。
方針：完備始域の充満忠実な像の retract 閉性を使う。
規約：元の射と元の終域を保つ。
使われ方：同じ完全射の実際の同値性の認証。 -/
lemma completion_isEssentiallySurjective_of_complete_source {X Y : StableModel.{u}}
    (f : X ⟶ Y) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val)
    (hX : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete X.carrier) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsEssentiallySurjective f.val := by
  intro y
  obtain ⟨x, ⟨r⟩⟩ := hf.2.2 y
  obtain ⟨x', ⟨e⟩⟩ := hX.retract_iso_in_image f.val hf.2.1 x y r
  exact ⟨x', ⟨e.symm⟩⟩

/-- 概要：始域も完備なら、指定完備化射自体が quasicategory の同値。
方針：元の充満忠実性と同じ射の本質全射性を合わせる。
規約：一般の完備化射の本質全射性は主張しない。
使われ方：完全な逆射を構成する入口。 -/
lemma completion_isQCatEquivalence_of_complete_source {X Y : StableModel.{u}}
    (f : X ⟶ Y) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val)
    (hX : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete X.carrier) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence f.val :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.isQCatEquivalence_of_isFullyFaithful_of_isEssentiallySurjective f.val hf.2.1
    (completion_isEssentiallySurjective_of_complete_source f hf hX)

/-- 概要：完備始域の場合、元の完全射を順方向に保つ完全な逆データ。
方針：同じ射の quasicategory 同値の逆の完全性を使う。
規約：順方向の K 射を別の同値射へ取り替えない。
使われ方：既存の S• 同値不変性への代入。 -/
def completionStableEquivalenceOfCompleteSource {X Y : StableModel.{u}}
    (f : X ⟶ Y) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val)
    (hX : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete X.carrier) : StableModelEquivalence X Y := by
  let e := (completion_isQCatEquivalence_of_complete_source f hf hX).choose
  let : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor e.inv :=
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isExactFunctor_of_isQCatEquivalence e.symm.isQCatEquivalence
  exact ⟨f, ⟨e.inv, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesZero,
    fun t ht => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsExactFunctor.preservesCofiber t ht⟩,
    e.homInvIso, e.invHomIso⟩

/-- 概要：完備始域の実比較は元の K 射で全整数次数の同型を誘導する。
方針：完全な逆データを既存の BF K 同値不変性へ渡す。
規約：始域完備性を一般共終性の入力にはしない。
使われ方：共終性の特殊場合の独立した検算。 -/
theorem kSpectrumMap_piIsomorphism_of_complete_source {X Y : StableModel.{u}}
    (f : X ⟶ Y) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val)
    (hX : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentComplete X.carrier) :
    OmegaSpectrum.PiIsomorphism (kSpectrumMap f) :=
  kSpectrumMap_piIsomorphism_of_equivalence
    (completionStableEquivalenceOfCompleteSource f hf hX)

end SerrePositivity.KST.SConstruction.Cofinality
