module
public import SerrePositivity.KST.SConstruction.Cofinality.CofinalityFromInputs
public import SerrePositivity.KST.LocalizingInvariants.CoreFlag.KanPullbackAll

/-!
概要：到着した Sp-8 (3) の実証明を元の K 共終性の一般射影入力へ代入する。
方針：既存 CoreFlag.All と分離された供給集約を消費葉で import する。
規約：入力定義からこの消費葉や KanPullbackAll を import しない。
使われ方：唯一の未供給の相対全旗自然性から元の実 kSpectrumMap を結論する。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory Spectra
open SerrePositivity.InfinityCategories

/-- 概要：Sp-8 (3) の一般 Kan 引き戻しの実証明。
方針：独立した供給集約の証明を元の明示入力へ直接渡す。
規約：一般 API を複製せず、公理や instance にしない。
使われ方：元の射影と元の K 射の供給仮定の消去。 -/
theorem kanPullbackCofinalityInput : KanPullbackCofinalityInput.{u} :=
  LocalizingInvariants.CoreFlag.kanPullbackCofinalityInput

/-- 概要：相対全旗自然性の一入力から指定完備化射の元の K 共終性条件を得る。
方針：Sp-8 (3) の実証明を二入力の元の定理へ代入する。
規約：Sp-8 (1)(2)(3) は仮定に残さず、元の指定 kSpectrumMap を結論する。
使われ方：K-B2-S1 の残る供給を代入して一般主結論を閉じる。 -/
theorem kSpectrumMap_cofinality_of_relativeFiber_input
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val)
    (h : Fibration.Relative.ClosedStableFlagPostPullback
      (completionImageClosedPredicate 0 Fin.elim0 f hf)) :
    (∀ j : ℤ, 0 < j → Function.Bijective (OmegaSpectrum.homotopyMap (kSpectrumMap f) j)) ∧
      Function.Injective (OmegaSpectrum.homotopyMap (kSpectrumMap f) 0) :=
  kSpectrumMap_cofinality_of_inputs kanPullbackCofinalityInput f hf h

end SerrePositivity.KST.SConstruction.Cofinality
