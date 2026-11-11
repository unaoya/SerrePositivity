module

public import SerrePositivity.KST.Spectra.CoherentCospanLimits
public import SerrePositivity.KST.Spectra.SpectrumZeroObject
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.FiniteLimitGeneration

/-!
概要：元の BF スペクトルの coherent nerve に全有限極限を与える。
方針：実零対象の終対象性と任意 coherent cospan の極限を既存の有限形状生成へ渡す。
規約：有限形状は Sp と同じ宇宙で量化し、通常図式への制限を仮定しない。
使われ方：実 nativeLoop 同値から Sp の安定性を結論する入力。
-/

@[expose] public section
universe u
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Spectra.OmegaSpectrum

/-- 概要：元の Sp は任意の有限単体集合形状の極限を持つ。
方針：終対象と標準 cospan 極限による有限極限生成を適用する。
規約：追加のモデル構造や有限余極限の入力は不要。
使われ方：D の loop 同値による一般安定性判定。 -/
instance sp_hasFiniteLimits : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits Sp.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.hasFiniteLimits_of_terminal_pullbacks pointZeroVertex.vertex pointZeroVertex.isTerminal
    CoherentPullback.hasLimit

end SerrePositivity.KST.Spectra.OmegaSpectrum
