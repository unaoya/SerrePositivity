module

public meta import SerrePositivity.Util.Citation
public import SerrePositivity.KST.SConstruction.Cofinality.KanPullbackSupply
public import SerrePositivity.KST.Fibration.Relative.ClosedStableFiberUnconditional

/-!
概要：指定冪等完備化射に対する Thomason の共終性を無条件で公開する。
方針：S1 の全旗自然性の実証明を既存の相対 Kan・K 境界比較へ代入する。
規約：元の kSpectrumMap を保持し、Verdier 列・商比較・K-6 を使用しない。
使われ方：K-B3 の K-7 e が正次数全単射と零次単射を消費する。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction.Cofinality
open CategoryTheory Spectra
open SerrePositivity.InfinityCategories

/-- 概要：指定冪等完備化射の K 射は正次数で全単射、零次で単射。
方針：無条件 S1 と同じ全旗自然性証明で最後の明示入力を放電する。
規約：入力は X・Y・f とその冪等完備化証拠のみ。
使われ方：`(kSpectrumMap_cofinality f hf).1 j hj` と `.2`。 -/
theorem kSpectrumMap_cofinality
    {X Y : StableModel.{u}} (f : X ⟶ Y)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.RetractsAndIdempotents.IsIdempotentCompletion f.val) :
    (∀ j : ℤ, 0 < j → Function.Bijective (OmegaSpectrum.homotopyMap (kSpectrumMap f) j)) ∧
      Function.Injective (OmegaSpectrum.homotopyMap (kSpectrumMap f) 0) :=
  kSpectrumMap_cofinality_of_relativeFiber_input f hf
    (Fibration.closedStableFlagPostPullback _)

end SerrePositivity.KST.SConstruction.Cofinality

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite AGH "Thm A.3.2" (partial := component) "仮定：冪等完備化を与える安定模型の完全関手（Karoubi 同値の特殊形）。結論：π₀K の単射（A.3.2 の単射の成分。部分群との全単射は別）。"] _root_.SerrePositivity.KST.SConstruction.Cofinality.kSpectrumMap_cofinality
