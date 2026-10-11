module

public import SerrePositivity.CategoryTheory.VerdierTStructure
public import SerrePositivity.CategoryTheory.BoundedTStructureGeneration
public import SerrePositivity.Asymptotic.LengthDerivedQuotient
public import SerrePositivity.Asymptotic.SmallLengthDerivedQuotient
public import SerrePositivity.Asymptotic.OrdinaryHeartResolution
public import SerrePositivity.CategoryTheory.TriangulatedK0
public import SerrePositivity.Asymptotic.FreeSequenceGenerator
public import SerrePositivity.Asymptotic.RankQuotientBaseChange
public import SerrePositivity.Asymptotic.SequenceDerived
public import SerrePositivity.Asymptotic.SequenceResolution
public import SerrePositivity.Asymptotic.SequenceSupport
public import SerrePositivity.Asymptotic.SupportedRankQuotient
public import SerrePositivity.Asymptotic.SupportedKaroubi
public import SerrePositivity.Asymptotic.SequenceKoszulBounds
public import SerrePositivity.Asymptotic.LengthFamilies
public import SerrePositivity.Asymptotic.EulerLimit
public import SerrePositivity.Asymptotic.RankEulerAdditivity
public import SerrePositivity.PerfectComplex.ResolutionFamilies
public import SerrePositivity.Asymptotic.PaperRankGenerators
public import SerrePositivity.Asymptotic.PaperBaseChangeEvaluation
public import SerrePositivity.Asymptotic.PaperVanishing
public import SerrePositivity.Asymptotic.PaperMinimalLowerBound
public import SerrePositivity.Paper.Section4.PaperK0Comparison
public import SerrePositivity.Paper.Section4.SymmetricComparison
public import SerrePositivity.Paper.Section4.FlatRealization
public import SerrePositivity.Paper.Section4.Theorem4_7

/-!
# §4 の構成済みの基盤

自由列の加法圏、共通有界ホモトピー圏、冪等完備化前のランク商とその係数変更、
導来圏の積への完全忠実性、長さの漸近評価・正規化超極限をまとめて読み込む。
有限長加群列の持ち上げとその一様な台、支持部分圏の商の完全忠実性、
商の支持対象の直和因子表示と冪等完備化後の圏同値も含む。
長さの Serre 商、支持つきランク商からのホモロジー評価、その冪等完備化への延長、
対象上の有限な Euler 和と実際の複体列での超極限公式も構成済み。
冪等完備化前の支持つきランク商では Euler 評価の三角加法性と `K₀` への降下も含む。
係数変更と各段のテンソル積の自然同型、一様な台の保存、支持つき商の係数変更も含む。
一般の三角圏の `K₀` と、有界 t 構造に関する既存の結果も含める。
長さで制限した加群列の有界導来圏については、全ホモロジーが通常の `o(s)`、
または超極限で長さ零になる対象による商の有界 t 構造と冪等完備性を構成した。
heart からの有限 Postnikov 生成と、充満な三角関手の本質像に対する帰着も含める。
通常の長さの heart の各対象、およびその `o(s)` 部分圏の対象について、
支持つき自由分解と小さいランクの分解への具体的な接続も含める。
有限 Postnikov 構成により、共通有界で各次数のホモロジーが長さの一様条件を
満たす族全体を支持つき自由列で表せる。小さいランク条件と、全ホモロジーの
通常の `o(s)` 条件の同値も証明した。
A 側では支持つき自由列とそのランク商の有界 t 構造を構成し、後者の冪等完備性を得た。
この冪等完備性を、論文の支持圏上の一般の Koszul Euler 基底公式に適用する。

Karoubi 包絡の標準的な三角構造は八面体公理まで構成済み。
完備化と Verdier 商の順序を交換する線形三角同値を構成し、
次数零の小さい自由列が生成する厚い部分圏との一致も証明した。
これにより論文の D_S、N_S、P_S と計算用の圏を比較できる。
論文の支持圏上で通常・係数変更後のホモロジー評価、非負で有限台の実数値、
Euler 和の K₀ への降下、および公式 (4.2) の係数等式を得た。
公式 (4.2) は元の列の一様支持を仮定せず、商でスカラーの冪が零になる条件を使う。
その証明は共通の反復錐の長さ公式を使う。実際の Koszul の振幅から、
対象としての消滅、第零次の同型、全射による Euler 下界も得られる。
係数変更後の論文側のホモロジー関手への消滅の移送も含める。
極小性から実際の Koszul 第零ホモロジーの全射を作り、
零次項のランクの正規化超極限による Euler 下界を論文側の係数変更後にも証明した。
二段階の係数変更と直接の係数変更の自然同型を、支持つき商、完備化、論文の圏で構成した。
任意の Koszul Euler 数による全対象の基底公式を構成した。
通常・正規化の比較は、この係数の一致を確認して共通の対称比較へ渡す。
異なる二つの長さ付き代数について、Koszul Euler 数の一致と不変類の降下だけから
共役和が一致する対称な比較も含む。

2026-10-10 の方針変更により、補題4.6と定理3.1の K₀ に関する帰結を
`supportedRankK0_descent` という一つの名前付き未証明入力として切り出した。
係数変更によるひねりと K₀ 上の群作用、(4.1) からの有限性を証明し、
その入力に相対的な定理4.7を、対称比較の系として対象と K₀ 類の両方について証明した。
定理4.7で使う正則パラメータの正則性は証明済み。
§2の具体的な環の構成は必要とせず、§2からの適用は§5側の作業である。

保留する範囲と他節への接続は次のとおり。

- 任意の Serre heart からの一般的な降下、および別に構成した有界導来商との同定は
  未証明。ただし現在の A 側の商の構成には不要で、ホモロジー関手の核を直接使った。
- 補題4.6の dg 表示と一般係数版定理3.1からの降下の導出は未実装。
  現在はその K₀ 帰結を引用しており、補題4.6を証明済みとはしない。
- §2の具体的な長さ代数へ§4の定理を適用する接続、有限近似と正値性は§5側。
  §4単体の完了条件には含めない。

このモジュールはリポジトリのルートから import される。
個別のビルドでも、ここまでの構成をまとめて検証できる。
-/
