module

public import SerrePositivity.KST.Spectra.FilteredHomotopyGroups
public import SerrePositivity.KST.Spectra.FilteredLoopColimit
public import SerrePositivity.KST.Spectra.FilteredSpectrumHomotopy
public import SerrePositivity.KST.Spectra.RationalTelescopeNaturality
public import SerrePositivity.KST.Spectra.FilteredSpectrumMap
public import SerrePositivity.KST.Spectra.AcyclicFiber
public import SerrePositivity.KST.Spectra.AcyclicKanLifting
public import SerrePositivity.KST.Spectra.AcyclicFibrationLifting
public import SerrePositivity.KST.Spectra.UnbasedHomotopyIsomorphism
public import SerrePositivity.KST.Spectra.PostMappingIsomorphism
public import SerrePositivity.KST.Spectra.SpectrumTail
public import SerrePositivity.KST.Spectra.CirclePower
public import SerrePositivity.KST.Spectra.RelStructHomotopy
public import SerrePositivity.KST.Spectra.CircleMappingComponents
public import SerrePositivity.KST.Spectra.InternalHomExchangeNaturality
public import SerrePositivity.KST.Spectra.LoopPositivePower
public import SerrePositivity.KST.Spectra.RationalSpectrumModelMap
public import SerrePositivity.KST.Spectra.CotensorIntegerPower
public import SerrePositivity.KST.Spectra.SpectrumHomotopyRectification
public import SerrePositivity.KST.Spectra.TriangleDiskCellIso
public import SerrePositivity.KST.Spectra.RelativeTriangleContraction
public import SerrePositivity.KST.Spectra.SquareTriangleOuterFaces
public import SerrePositivity.KST.Spectra.SquareReducedDesc
public import SerrePositivity.KST.Spectra.SquareSmashExt
public import SerrePositivity.KST.Spectra.BoundaryTensorExt
public import SerrePositivity.KST.Spectra.TrianglePairDesc
public import SerrePositivity.KST.Spectra.CircleSmashTriangles

/-!
概要：スペクトルの telescope 有理化に使う余極限とホモトピー群の比較。
方針：有限な代表・関係を後続段へ移し、Kan 性と群の余極限を実証する。
規約：有理化の対象と全次数のテンソル比較を含む。元の対象からの標準射と自然性は継続する。
使われ方：Goerss–Jardine I §7、BF 1978 §2、HA §1.4.2。L9d の集約入口。
-/
