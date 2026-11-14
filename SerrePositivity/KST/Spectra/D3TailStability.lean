module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.KST.Spectra.D3TailLoopEquivalence
public import SerrePositivity.KST.Spectra.SpectrumFiniteLimits
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LoopEquivalenceStability

/-!
概要：B の全関手比較を明示入力とする元の Sp の安定性。
方針：実零対象・有限極限・指定 nativeLoop 切断と d3c を D の判定へ代入する。
規約：B の存在や無条件の安定性を主張せず、安定性インスタンスは登録しない。
使われ方：Sp-2b d3d、実 B 到着後の K-B3 d3 向け接続。
-/

@[expose] public section
universe u
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum
open AdjointLoopRelativeBF

/-- 概要：B を明示引数に持つ元の Sp の安定性。
方針：既存の零対象・有限極限・指定切断と d3c を一般判定へ代入する。
規約：B の存在・無条件版・グローバル instance は主張しない。
使われ方：B 到着後の K-B3 d3 向け接続。 -/
theorem sp_isStable (hB : NativeLoopComparison.{u}) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable Sp.{u} := by
  exact _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.isStable_of_loopEquivalence nativeLoopTargetEquivalence.inv
    nativeLoopTargetEquivalence_inv_target
    (nativeLoop_isQCatEquivalence_of_tailComparison hB)

end SerrePositivity.KST.Spectra.OmegaSpectrum

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "1.1.1.11" (partial := stronger-hyp) "仮定：スペクトルの BF 模型に対する NativeLoopComparison（Lean が強い：HA の例では比較を仮定しない）。結論：Sp の準圏が安定。安定性の特例であり、HA の模型との比較と普遍性はこの型にない（Lean が弱い）。"] _root_.SerrePositivity.KST.Spectra.OmegaSpectrum.sp_isStable
attribute [cite HA "1.4.2.17" (partial := stronger-hyp) "仮定：点付き Kan 空間の Ω スペクトル模型に NativeLoopComparison を与える（Lean が強い：一般の有限極限を持つ C でなく空間に限り、比較を仮定）。結論：この模型の Sp が安定（Lean が弱い：一般の Sp(C) と切除関手模型の比較はこの型に含まれない）。"] _root_.SerrePositivity.KST.Spectra.OmegaSpectrum.sp_isStable
attribute [cite HA "1.4.3.6" (partial := component) "仮定：点付き Kan 空間による Sp の模型に NativeLoopComparison を与える（Lean が強い：比較データを要求）。結論：Sp の安定性（Lean が弱い：accessible t 構造、左右の完備性と Ab に同値な心は型にない）。"] _root_.SerrePositivity.KST.Spectra.OmegaSpectrum.sp_isStable
