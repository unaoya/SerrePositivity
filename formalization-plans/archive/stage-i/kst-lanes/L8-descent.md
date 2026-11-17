# K-L8（論文 §3 の降下）

> **休止（2026-10-19）**：基盤に集中する決定により第 II 段で再開。引き継ぎ節を正本として保持。Main/Auxiliary の分離は維持。

## 引き継ぎ（2026-10-19）

### 現在地

- 正本 KST 経路 §13 決定15（§100 提案1–7承認）に従い、主経路と条件付き補助を分離済み。
- `Descent.Main` は旧56モジュールを import せず、`Descent.Auxiliary` が旧 import を保持する。
- 旧56ファイルは変更していない。ルート集約は Main のみを public import する。
- 実 `PointedTotalization` と Reedy 置換後の Tot への指定増強比較・基点保存・自然性を証明済み。
- 実 `PointedHomotopyLimit`・任意の `PointedWeightedEnd` の指定比較・自然性・忘却後の一致を証明済み。
- Tot/BK の段ごとの π_* 同型と増強元の同型による、指定降下の保存・反映を証明済み。
- 既存の軌道・閉和・次元／成分帰納は、自然な blowup 列等の明示的入力に対する結果として保持。
- 最小公理(1)–(8)全体、一般の定理3.1、K0・Eへの実現は未完。空間側の π_* を整数次数と同一視しない。
- 最新コミット：`ed6d33c2`（分離・実Tot）、`b4eac59f`（実end・段ごとの保存反映）。
- 最終対象ビルド：4646 jobs 成功。主経路監査1485宣言、全補助込み255モジュール・2652宣言。
- 許容公理は標準三公理のみ。主経路の56モジュール排除と公開型の三種の仮定の grep は成功。
- 検証ログ：`/tmp/l8-main-weighted-{target,main-audit,full-audit}.log`。

### 残り（依存順・原典番号・時間見積もり）

- 実Tot/endの指定比較を保つFubini・引き戻し交換（§2.2の代替経路、論文補題3.2・3.3）：16–40時間。
- extra degeneracyから増強→実Totのπ_*同型（補題3.2）：16–40時間。前項と併せて実構成上で証明する。
- 随伴添字変更・細分の各段の比較と降下反映（補題3.2）：16–32時間。N/αの既存結果を読む。
- 元のSp上の自然なtransfer、各整数次数の局所rank、有限平坦Čech降下（補題3.2）：24–48時間。
- 実fiber・自然LESから既存NaturalBlowupSequencesへ接続し、最小公理全体を束ねる（補題3.3、定理3.1）：24–48時間。
- 幾何の帰納と上記を結合して全整数次数の主定理を完成、最終構造体・主定理を#check監査（定理3.1、(3.8)）：16–32時間。
- K0・T2の明示的界面で支持の同定を接続（(3.6)、TT局所化）：8–24時間＋L4/K0界面の待ち。
- E=fib(K_ℚ→K[1/p]_ℚ)の実現、既存入力側の二定理への接続（§4の使用）：16–40時間＋L4/L10の待ち。
- 見積もりはLean実装の概算で、外部APIの不足・他レーンの完成待ちを含まない。

### 主要宣言（名前のみ）

- `SerrePositivity.KST.Descent.GradedPresheaf`
- `SerrePositivity.KST.Descent.GradedPresheaf.PiDescent`
- `SerrePositivity.KST.Descent.NaturalBlowupSequences.sectioned_piDescent`
- `SerrePositivity.KST.Descent.Main.AugmentedTotDiagram`
- `SerrePositivity.KST.Descent.Main.rawTotComparison`
- `SerrePositivity.KST.Descent.Main.totComparison`
- `SerrePositivity.KST.Descent.Main.HasTotDescent`
- `SerrePositivity.KST.Descent.Main.totComparison_naturality`
- `SerrePositivity.KST.Descent.Main.hasTotDescent_iff_of_stagewise_piIsomorphism`
- `SerrePositivity.KST.Descent.Main.AugmentedLimitDiagram`
- `SerrePositivity.KST.Descent.Main.homotopyLimitComparison`
- `SerrePositivity.KST.Descent.Main.HasHomotopyLimitDescent`
- `SerrePositivity.KST.Descent.Main.hasHomotopyLimitDescent_iff_of_stagewise_piIsomorphism`
- `SerrePositivity.KST.Descent.Main.weightedEndComparison`
- `SerrePositivity.KST.Descent.Main.weightedEndComparison_underlying`
- `SerrePositivity.KST.Descent.Main.weightedEndComparison_bousfieldKan`

### 依存と提供

- 読取専用：L9のCosimplicialTotalization、ReplacedTotalization、PointedHomotopyLimit、PointedWeightedEnd、KanCompositeCancellation。
- 読取専用：NのHomotopyLimits（WeightedFunctor等）、αの二宇宙版Core.InitialCofinality。次工程で再利用する。
- L4/K0/T2/L10から実fiber・局所化・K/E実現を受ける。所有外のInputs・Section4・KTheory等は編集しない。
- 提供：主経路の実指定比較、段ごとの保存・反映、既存の有限型幾何・軌道／次元帰納と(3.6)の条件付き界面。

### 未コミット

- L8所有のLean・監査はすべてコミット済み。本節追加だけを別コミットで保存する。
- ワークスペースの他レーンの未コミット差分は触らず残す。

### 既知の問題

- 旧56モジュールはModelCategory等を明示的に仮定する条件付き補助。instanceは供給しておらず主経路に接続しない。
- 最小公理全体・主定理全体は未宣言なので、その最終的な型の#check監査はまだ未達。現存する公開型だけ記録済み。
- CosimplicialKanMapEquivalenceは置換の各段のπ_*同型。Totの不変性はTotalizationHomotopyInvariance/ReplacedTotalization。
- ContractibleTotalSequenceはfiber列の次数移動で、extra degeneracy降下の定理ではない。
- 実Totと一般BK/endの比較、Spの全整数次数、自然LESへの接続は今後必要。通常の極限・群の同型だけで代用しない。
- 最終L8対象ビルドは成功。過去の全体ビルドは所有外F1/F1BのrelativeFunctorVertex名衝突で失敗（現在の修正状況は未再確認）。
- `theorem_3_1_K0`・`supportedRankK0_descent`の既存入力側は未解消。新規sorry・公理は導入していない。

### 次の一手

- 新チャットでMainAugmentedWeightedEndの実指定比較を起点に、実Tot/endと引き戻しのFubiniをDescent内で証明する。
- 最初にN/L9の実APIを確認し、56モジュールを主経路へ戻さず、対象ビルドと両監査で保存する。

## 2. 所有と編集範囲

所有する Lean ディレクトリは `SerrePositivity/KST/Descent/`。
namespace は `SerrePositivity.KST.Descent`。
集約入口は `SerrePositivity/KST/Descent.lean`。
ルートへの変更は `public import SerrePositivity.KST.Descent` の一行。
本計画の所有ファイルはこの Markdown。
監査入口は `scripts/audit_kst_descent.lean`。
共有作業ツリーの既存変更を保持する。
他レーンの新規ファイルをコミットに含めない。
共有ルートの他レーンの import を取り込まない。
`Inputs/Descent.lean` は読むだけ。
`Paper/Section4/SupportedDescent.lean` は読むだけ。
`KTheory/` は読むだけ。
`CommutativeAlgebra/` は読むだけ。
`PerfectComplex/` は型と比較定理を読むだけ。
D_qc・局所化は K-L4 の所有。
Sp・π_n・Tot・hG の実構成は K-L9 の所有。
K0 の正確な型の固定は K-L1・K-L11 の合流点 S1。
本レーンで Sp の代用品を実装しない。
K に依存する界面は明示的な構造体の引数にする。
その界面の存在を勝手に仮定する定理を作らない。

## 3. 完成時の主張

係数は H を引数として保持する。
基底は A 上有限型スキームの圏。
次数は n ∈ ℤ。
第 1 段の主張は全次数の π_* 同型。
目的の写像は幾何学的な引き戻しから誘導される。
目標は K_n^J(H)_ℚ ≅ (K_n^J(H ⊗_A T)_ℚ)^G。
同型が存在するだけでなく、指定した引き戻し写像が同型になることを示す。
G 作用との両立を結論の型の中で保持する。
n = 0 の全射性だけに弱めない。
負次数を切り捨てない。
H = A のとき既存 `theorem_3_1_K0` への比較を可能にする。
H = B_A のとき F5 を経て `supportedRankK0_descent` に接続する。
既存の二つの保留定理の証明置換は所有者との合流作業。
本レーンでは他者所有の保留定理を直接変更しない。
Sp の同値 (3.1) は γ3 後の精密化。
第 1 段の全次数主張と精密化を混同しない。

## 4. 原典の対応表

| 対象 | 原典 | 本レーンの責務 |
| --- | --- | --- |
| 台つき有理降下 | 主論文 §3 定理 3.1、(3.1) | 全次数 π_* 版 |
| π_0 の全射性 | 主論文 (3.2) | 主定理の帰結 |
| E の定義 | 主論文 (3.3) | 接続する値域の指定 |
| truncating 経路 | 主論文 (3.4) | 第 1 段では KST 経路へ置換 |
| L の定義 | 主論文 (3.5) | 係数と台を含む前層 |
| K の台との同定 | 主論文 (3.6) | K0・T2 への界面 |
| 有限忠実平坦降下 | 主論文 補題 3.2 | transfer と Čech 分裂 |
| 有限全射降下 | 主論文 補題 3.3 | 平坦化・閉集合帰納 |
| 軌道比較 | 主論文 (3.7) | 自然な引き戻し比較 |
| Shapiro | 主論文 (3.8) | 有理不変部分の計算 |
| 係数圏との比較 | 主論文 §4 補題 4.6 | K-L10 の入力 |
| 漸近ノルム比較 | 主論文 §4 定理 4.7 | 利用箇所の確認 |
| perfect 局所化 | TT 命題 5.2.2–5.2.4、定理 7.4 | K-L4 の T2 |
| Zariski 降下 | TT 定理 8.1 | K-L4 の T3 |
| 抽象 blowup | KST 定理 A、係数版 | 他レーンから E の降下へ |
| 平坦化 | 主論文 補題 3.3、Stacks 0815 | Fitting 版の幾何入力 |

## 5. 既存の整数版の型

`theorem_3_1_K0` は Noether 局所環 A と有限 A 代数 T に対する命題。
パラメータ列 z は有限個。
z の生成するイデアルの根基は A の極大イデアル。
剰余標数は素数 p。
有限群 G は T に A 線形に作用する。
素スペクトル上の射は全射。
幾何ファイバー上で G が推移的。
T 側の G 不変類 y に対して正の整数倍が A から来る。
有理同型からこの整数版へは分母とねじれを消去する。
`K0Supported` の universe は環の universe より一つ大きい。
既存の群作用は `g • [P] = [twist g⁻¹ P]`。
幾何学的な前層の反変性との向きを確認する。
比較同型は群作用と引き戻しの両方に自然でなければならない。
単なる群の抽象同型だけでは既存の定理を置換できない。
`supportedRankK0_descent` は支持つきランク商の三角 K₀ に対する同じ整数形。
この命題は補題 4.6 と一般係数の降下の両方を現在含む。
その全体を L8 のみで完成したとは主張しない。

## 6. 工程と完成条件

| 工程 | ファイル | 完成条件 | 現在 |
| --- | --- | --- | --- |
| L8a | `Axioms.lean` と補助モジュール | 最小公理 (1)–(8) と全次数の主張 | 実現界面、transfer と不変部分の基礎を実装 |
| L8b | `Theorem31.lean` | 補題 3.2・3.3 と軌道帰納の証明 | 代数的な軌道帰納段階を証明、幾何・降下・Čech は未接続 |
| L8c | `SchemeFacts.lean`、`ClosedDimension.lean` | 必要な幾何補題の証明・再利用 | 基本補題実装、有限型の次元上界との接続は未完 |
| L8d | 台の比較用モジュール | K0・T2 から (3.6) | 未着手 |
| L8e | E 接続用モジュール | 実際の E が公理を満たす | 外部成果待ち |

各工程で対象ビルドを行う。
各保存単位で監査入口を実行する。
許容する公理は `propext`、`Classical.choice`、`Quot.sound`。
内部補助宣言も監査の対象にする。
新しい引用公理を許容リストに追加しない。
工程の区切りで全体ビルドを行う。
他レーンに起因する import 閉包の破損は回避しない。
自分の型付けの誤りは自分で修正する。
ビルドの未実施と失敗を区別して報告する。
検証済みの自分のファイルだけを `git commit --only` で保存する。
各検証コマンドでは `set -o pipefail` を使う。
amend、rebase、reset は使わない。

## 7. L8a：値域と反変性

初期の公開データは係数 H と整数次数を持つ有理加群値の前層。
有理化済みであることを ℚ 加群構造で表す。
引き戻しは ℚ 線形。
恒等射の引き戻しは恒等写像。
合成の引き戻しは反変順序。
基底圏は A 上有限型スキームの充満部分圏。
スキームの構造射の有限型性を条件として記録する。
射には基底との可換条件がある。
H は A 上の係数の添字として明示する。
係数の ring/dg 構造は K0 接続時の界面で精密化する。
前層データだけで最小公理を実装したと扱わない。
各次数の群と導来降下の構造を区別する。
Tot は次数ごとの通常の極限ではない。
ホモトピー引き戻しは次数ごとの群の引き戻しではない。
L9 の Tot・fiber を使う界面の設計が必要。
L9 が所有する具体的 Sp の定義を本レーンで重複させない。
導来降下の法則を結論そのものに置き換えない。

## 8. 最小公理 (1)：Zariski Čech 降下

対象は係数つき前層 L。
有限アフィン開被覆に対する比較を記録する。
Čech nerve の重なりを含む全余単体図式を使う。
Tot への比較の全次数 π_* 同型を主張する。
単なる等化子の完全性だけでは置き換えない。
被覆の引き戻しに対する自然性を保持する。
補題 3.2 のベクトル束の自明化を貼り合わせるために使う。
係数の自然性は後の K0 接続で必要。
Zariski 局所性だけを有限全射の降下と取り違えない。
T3 の成果を最終的な E の検証に使う。

## 9. 最小公理 (2)：抽象 blowup の実降下

入力は固有射と閉中心からなる正方形。
中心の補集合で固有射が同型になる。
L による像はホモトピー引き戻し。
pro のままの主張ではない。
KST 定理 A から実降下への移行は E 側で行う。
閉和の正方形はこの公理の特殊例。
軌道正方形もこの公理の適用先。
有限群作用との両立を保持する。
π_* で扱う場合は長完全列と境界写像の自然性を保持する。
各次数の通常の pullback 条件に強めてはならない。

## 10. 最小公理 (3)：冪零 thickening 不変性

冪零閉埋め込みによる引き戻しが全次数で同型。
Noether スキームの reduction を扱える形にする。
Y の被約化で使う。
V = (X ×_S Y)_red の比較で使う。
中心上のファイバー積の被約化でも使う。
一般の閉埋め込みへの不変性を仮定しない。
冪零イデアルと単なる radical support を区別する。
E の不変性の実証明は K 固有の外部レーン入力。

## 11. 最小公理 (4)：有限平坦 transfer

有限平坦射 f に対する restriction of scalars を用いる。
引き戻しと逆方向の transfer を持つ。
transfer は基底上のスキームの前層の自然変換。
有限平坦底変換と両立する。
射影公式を持つ。
合成 trf ∘ f* は f_* O_X による作用。
ベクトル束が自由 rank a になる開集合上で a 倍になる。
大域的に rank 倍と仮定してはならない。
有限忠実平坦ならその局所 rank は正。
ℚ 上で a を割って前層の retract を作る。
split descent の retract であることを全 Čech 図式で示す。
各次数の単射性だけでは補題 3.2 の証明にならない。
ベクトル束の自明化と基底変更の両立を使う。

## 12. 最小公理 (5)：有理固定点

有限群 G の有理不変部分は完全関手。
平均作用素は |G| の逆数を使う。
自明作用の不変部分は元の有理加群。
推移的有限 G 集合 I 上の積を計算する。
I = G/G_s の場合は Shapiro の形になる。
安定化部分群は各コピーで自明に作用する。
係数が基底から引かれていることを使う。
不変な積の元は対角的な定数族。
この代数計算は (3.8) の π_* 側の構成要素。
通常の不変部分と hG を同じ記号で定義しない。
π_n(hG) と不変部分の比較は L9 の実構成に接続する。
非有界な場合に収束するスペクトル系列を勝手に仮定しない。

## 13. 最小公理 (6)：Fitting 版平坦化

有限全射 X → Y の整な基底を扱う。
Y を支配する X の被約既約成分 X₀ を選ぶ。
稠密開集合上で有限平坦になる。
その補集合内の中心を blowup する。
strict transform X₀′ は Y′ 上平坦かつ有限表示。
strict transform は X₀ ×_Y Y′ の閉部分。
従って Y′ 上有限。
generic point を含む像が閉なので全射。
この有限忠実平坦射が元の X への被覆を細分する。
中心 Z の次元に関する帰納と組み合わせる。
平坦化の結論に有限全射降下そのものを含めない。
本レーンの幾何命題として扱うか K-L7 と整合する界面を使う。

## 14. 最小公理 (7)：スキーム補題

分離射の切断は閉埋め込み。
分離な対象への二つの射の等化子は閉。
被約な始域上で稠密部分から一致を延長する。
整スキームの真閉部分で次元が真に下がる。
次元帰納では有限次元の仮定を明示する。
有限型性だけから無条件に有限次元と結論しない。
基底 A の有限 Krull 次元を使用する。
点全射な閉埋め込みは終域が被約なら同型。
始域のみ被約ではこの結論は成り立たない。
有限射は固有。
有限個の閉部分の和と交わりを扱う。
有限 G の軌道による section の閉像を扱う。
Mathlib の既存証明をまず使用する。
同じ補題の再証明より適切な仮定の wrapper を優先する。

## 15. 最小公理 (8)：(3.6) の同定

L(Y) は (3.5) の二重 fiber。
E は K_ℚ → K[1/p]_ℚ の fiber。
p ∈ J を保持する。
p を反転すると台が空になる。
fiber の交換から支持つき K_ℚ と比較する。
T2 は perfect 圏の局所化を供給する。
K0 はその dg 商列を長完全列に送る。
台の判定は中心局所化の telescope と compact 性から得る。
局所化で消えることと恒等射が z の冪で消えることを比較する。
有限個の生成元に共通の冪を取る。
Y = S と Y = X の二箇所だけを主定理への接続に使う。
比較は引き戻しと G 作用に自然。
K0・T2 の構造体引数を公開する。
最終同型を仮説に入れた定理を証明済みと呼ばない。

## 16. L8b：Čech による証明の順序

最初に分裂余単体対象の降下を証明する。
次に比較写像の retract が同型になることを証明する。
Tot と基底変更の可換性を保持する。
Tot とホモトピー引き戻しの Fubini を使う。
二重 Čech nerve の順序交換を証明する。
細分により降下が引き継がれる補題を証明する。
これらを使って補題 3.2 を証明する。
閉和と平坦化から補題 3.3 を証明する。
原典の τ 位相の層論をこの Čech 計算で置き換える。
Nisnevich 位相を導入しない。
hyperdescent を追加仮定にしない。
cdh 層化や Milnor 切除を使わない。
有限全射の Čech 項上で section を得る。
section を持つ幾何的推移的射へ還元する。
整 → 被約 → 一般の順に帰納を構成する。
section の G 軌道の相異なる元を I とする。
二つの異なる section の一致場所の和を Z とする。
Z が真閉であることを generic point の一致延長から示す。
W = ⨿_I Y → V が Z の外で同型であることを示す。
軌道正方形に抽象 blowup 降下を適用する。
有理固定点と (3.8) を適用する。
Z 上の帰納仮定で残りの辺を同型とする。
被約化を戻し、Čech 計算で元の基底に戻る。
(3.6) により全次数の支持つき K の主張にする。

## 記録の所在

実施記録・現在地の詳細・型一覧は [archive/L8-descent-log.md](../../L8-descent-log.md) に移した（2026-10-19）。現在地は冒頭の引き継ぎ節が正本で、工程ごとの記録はコミットメッセージに置く。
