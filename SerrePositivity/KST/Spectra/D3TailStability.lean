module

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
