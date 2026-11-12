module
public import SerrePositivity.KST.NonConnective.DGNonconnectiveKConnectiveComparison
public import SerrePositivity.KST.NonConnective.DGNonconnectiveKFibrationTail
public import SerrePositivity.KST.NonConnective.DGNonconnectiveKZero
public import SerrePositivity.KST.NonConnective.DGSuspensionIndComparison
public import SerrePositivity.KST.NonConnective.DGKappaConeCompactComparison
public import SerrePositivity.KST.NonConnective.DGKInputCompactNativeChoiceCoherence
public import SerrePositivity.KST.NonConnective.DGKappaResolvedIndChoiceComparison
public import SerrePositivity.KST.NonConnective.DGKappaSuspensionKChoicePiCoherence
public import SerrePositivity.KST.NonConnective.DGSuspensionUnconditionalIterationMorita
public import SerrePositivity.KST.NonConnective.SequentialFilteredExchangeInjection
public import SerrePositivity.KST.NonConnective.SequentialFilteredCandidatePi

/-!
第 I 段の固定入力成果の公開入口。固定 R・κ・A に対して、実懸垂列、
dgNonconnectiveK、実 Sp 余錐と余極限性、整数 π 余極限、非負次数連結比較、
末尾表示、ν-零入力の零保存を公開する。

対象別 Ind／compact・選択・商・共終性比較、指定 Morita 射の各実反復射の
保存、指定 filtered BF 図式の交換も上記公開葉を参照する。
Morita 保存には元の射が Morita 射であるという仮定、BF 交換には指定図式の
仮定がある。全入力作用や未供給の比較を追加仮定として要求するものではない。

全入力関手、全入力で自然な構造辺、最終 K^{nc} の Morita／Verdier／filtered 保存、
κ を変える同値、局所化登録は本入口の完成成果に含めない。
-/
@[expose] public noncomputable section
universe u v w
open CategoryTheory SSet
open SerrePositivity.InfinityCategories SerrePositivity.KST.SConstruction

open SerrePositivity.KST.Spectra
namespace SerrePositivity.KST.NonConnective
local instance fixedInputSpectrumCategory :
    SimplicialCategory OmegaSpectrum.{w} := OmegaSpectrum.simplicialCategory

/-- 固定入力の実 BF 図式を全単体で Sp に表示する。入力 A に関する関手性は含まない。 -/
def dgNonconnectiveKFixedInputDiagram (R : Type u) [CommRing R]
    (κ : Cardinal.{u}) [Fact κ.IsRegular] (hκ : Cardinal.aleph0 < κ)
    (A : PerfDGInput.{u, max (u + 1) v} R) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram (dgNonconnectiveKDiagram R κ hκ A)

end SerrePositivity.KST.NonConnective
