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

/-!
概要：スペクトルの telescope 有理化に使う余極限とホモトピー群の比較。
方針：有限な代表・関係を後続段へ移し、Kan 性と群の余極限を実証する。
規約：有理化対象と ℚ テンソルの比較は L9d の後続部分で加える。
使われ方：Goerss–Jardine I §7、BF 1978 §2、HA §1.4.2。L9d の集約入口。
-/
