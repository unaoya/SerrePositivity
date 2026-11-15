module

public import SerrePositivity.BhattScholze.Andre.OrdinaryRoots.Adjoin
public import SerrePositivity.BhattScholze.Andre.Variants.Auxiliary
public import SerrePositivity.BhattScholze.Andre.Perfection.PerfectPrismMonic
public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.Varpi
public import SerrePositivity.BhattScholze.Andre.Variants.RootedExtension
public import SerrePositivity.BhattScholze.Andre.OrdinaryRoots.Family
public import SerrePositivity.BhattScholze.Andre.Envelope.MonicSource
public import SerrePositivity.BhattScholze.Andre.Envelope.MonicCandidate
public import SerrePositivity.BhattScholze.Andre.Variants.ArbitraryFamily
public import SerrePositivity.BhattScholze.Semiperfectoid.Quasiregular.RootFamilies.PowerRootPolynomial
public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.PowerRootInput
public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.DividedPowerPrime
public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.PrincipalDP

public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.VarpiPD
public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.Initiality
public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.CompletionPD
public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.Unconditional.Localization
public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.DeltaDivisionResidue
public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.DeltaDivisionWitt
public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.CompletionPrism
public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.PerfectionFaithful
public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.FrobeniusPullback
public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.InputUniversal
public import SerrePositivity.BhattScholze.Prism.Bounded.Completeness
public import SerrePositivity.BhattScholze.Prism.Perfectoid.PerfectPrismHomLift
public import SerrePositivity.BhattScholze.Prism.Bounded.Tilt
public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.Unconditional.FrobeniusPD
public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.Unconditional.Residue



public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.Unconditional.RawRegular

public import SerrePositivity.BhattScholze.Andre.PowerRootEnvelope.VarpiComparison

/-!
# BS 著者版 Remark 7.15 の包の計算 の集約

## 概要

BS 著者版 Theorem 7.14（著者版 p.61）、BS 著者版 Remark 7.15（p.62）の正次数モニック族の根付き p 完全忠実平坦 perfectoid 拡大の証明を集約する。

## 方針

通常のモニック商の自由性と独立変数の関係式の正則性から準備し、
任意の関係族の δ 除算から perfectoid 根候補を構成する。
原典の BS 著者版 Proposition 7.11 を使う経路とは異なる実 PD 計算と具体的係数比較による構成を使う。

## 規約

`exists_monicRootedPerfectoidExtension` は承認済みの正次数仮定を明示する。
添字型全体の有限性や基底の p 正則性・ねじれなしは仮定しない。
無限 p 冪根変数の単項式・小数指数基底とモニック冪商の自由性も公開する。原典の具体的 pd 包との比較の補完は別工程である。

## 使われ方

ルートの公開入口から本レーンの検証済み結果を読み込む。
-/
