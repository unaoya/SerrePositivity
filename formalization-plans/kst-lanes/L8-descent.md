# K-L8（論文 §3 の降下）

## 1. 目的と現在地

作成日：2026-10-18。
レーン名：K-L8（論文 §3 の降下）。
正本は [KST 経路](../k-theory-kst-route.md)。
基盤の正本は [foundations](../foundations.md)。
特に KST 経路 §2.2、§3、§5 E、§13 の決定 4・5 を優先する。
本計画は L8 の設計、工程、現在地、宣言の対応を管理する。
実施の経緯はコミットメッセージに記録する。
状態：L8a の次数付き前層、指定比較、図式上の transfer による比較の retract、
有理不変部分の完全性とホモロジー保存、底変換後の Čech nerve の分裂を実装。
公理 (3) の幾何学的な型と不変性の法則の型、抽象 blowup の幾何データ、
指定制限写像と境界を持つ長完全列の比較、有限次元の真閉部分の次元低下を実装。
有限個の一致場所の和の真閉性・次元低下と、G 同変な長完全列の不変部分を実装。
一致場所を台とする被約閉中心を有限型の圏内で構成し、次元低下を実際の中心へ移した。
被約閉中心の引き戻しの実際の Cartesian 正方形を構成した。
アフィン Noether の reduction の核の冪零性と、公理 (3) による比較を証明した。
一般の reduction の普遍性・関手性と、その包含の自然性を証明した。
有限型の圏内にも reduction 関手を構成し、Noether 基底上で公理 (3) から
全次数の降下比較とその reduction の比較の同値を証明した。
有限個の切断の非交和からの有限・固有な軌道射と、コピーの G 置換作用を構成した。
被約化への軌道射の有限性・同変性と、明示した像の被覆条件からの全射性を証明した。
一致中心の外の制限切断の像の互いに素と、被約な終域の有限閉被覆の非交和同型を証明した。
有限非交和と開制限の標準同型で軌道射そのものの開制限の同型性へ接続した。
有限型の圏内の軌道射と、基底の一致中心を引き戻した中心による実際の抽象 blowup を構成した。
この軌道正方形の四頂点の G 作用と四辺の同変性も有限型の圏内で構成した。
前層の指定制限と差の同変性を証明し、境界の同変性を入力する長完全列への接続を実装した。
境界が幾何正方形の射に関して自然な列の接続データを型にし、そこから境界の同変性を導いた。
軌道正方形から基底の恒等中心正方形への同変立方体を構成し、
中項・例外部分の固定比較から実際の指定 PiDescent を得る軌道判定を証明した。
実際の軌道のコピーの包含・fold と、有限型の圏内の非交和の普遍性を証明した。
コピーの積を保つ前層について (3.8) の指定対角比較を幾何的な fold へ接続し、
中心上の降下から実際の中項の固定比較を導いた。
例外部分を Z のコピーの非交和として有限型の圏内で構成し、既存の作用が添字を置換することを証明した。
自然な blowup 列とコピーの有限積保存のもとで、中心上の降下だけから
実際の軌道段階の全次数 PiDescent を得る定理を証明した。
Noether な終域への全射閉埋め込みの冪零性と、Noether な対象への底変換後の冪零性を証明した。
公理 (3) から、冪零な基底変更の前後の全次数降下の同値を証明した。
基底を固定した始域だけの被約化の比較も証明し、被約化した中心上の降下を
実際の非被約な中心の軌道段階へ移した。
一つの切断の移動から、重複を除いた有限・非空・推移的な添字と相異なる族を構成した。
この族の一致中心での次元低下と、基礎点のファイバーの推移性からの像の被覆を証明した。
既存の環論的な幾何的推移性から通常の点のファイバーの推移性を導き、
切断を持つ有限型アフィン対象の実際の移動切断の被覆へ接続した。
任意の A 代数 B への係数拡大で、既存の幾何的推移性が保存されることを証明した。
基底変更後のアフィン対象の被覆、および基底を固定した始域の被約化での点の推移性を証明した。
被約な基底では元の切断を始域の被約化へ持ち上げ、実際の移動切断の被覆へ接続した。
任意の閉中心への実際の引き戻しに切断・点の推移性・被約化後の被覆を移し、
構成済みの orbitCenterAction と実際の中心の射影へ直接接続した。
二つの閉部分の被覆を実際の抽象 blowup 正方形とし、自然な列のデータから
閉和の境界を含む全次数列を得る構成も実装した。
閉被覆を始域へ引き戻した二つの閉部分と交わりから、元の閉被覆への実際の比較立方体を構成した。
四頂点の群作用と立方体の同変性を証明し、自然な列の有理不変部分を比較した。
二つの閉部分と実際の交わりの指定 PiDescent から元の射の全次数 PiDescent を導く閉和の貼り合わせを証明した。
既約成分を同じ基底上の整な有限型閉部分スキームとして構成し、Noether の場合の有限閉被覆を証明した。
一成分と残りの被約閉和に分け、実際の交わりの次元低下を証明した。
残りを他の元の整成分からの実際の閉埋め込みで覆い、その被覆の成分数が一つ減ることを証明した。
閉和の交わりの指定比較へ元の切断と点の推移性を移し、両側の被約化後の移動切断による被覆を証明した。
被約化が切断・点の推移性・次元を保つことと、同型射・空の基底の全次数降下も証明した。
厳密に低い次元に限った帰納仮定から、整な基底の軌道段階を閉じた。
中心の切断・推移性・被覆・次元低下を実際に供給し、Noether 性と公理 (3) で始域の被約性も外した。
零より低い次元に対する帰納仮定は、空の基底の降下から証明した。
残り自身の既約成分数の厳密な減少を証明し、内側の成分数の強い帰納を完了した。
外側の次元上界の帰納も実行し、切断を持つ射の全次数 PiDescent を低次元の仮定なしで証明した。
環の分裂から固定した S 上の切断を構成し、分裂する底変換と自己底変換の
テンソル積モデルに同じ L の全次数降下を適用した。
テンソル積の指定二射影の実際の Cartesian 性と、右射影の同変性を証明した。
この二射影・作用・切断を同じ S 上の有限型の圏内にも構成し、
その Cartesian 性と指定第一射影の全次数降下を証明した。
Noether 基底上の有限型の圏に有限極限を構成し、実際の Čech nerve・各段での
底変換の関手・二重 Čech 図式と元の前層による像を構成した。
各非増強段の底変換に実際の切断と extra degeneracy を構成した。
Cartesian モデルと指定引き戻しの標準同型の同変性を証明し、アフィン底変換の
指定 pullbackAction に関する全次数降下を実際の第一射影へ移した。
Čech 各段のファイバーの作用の外側の単体射との同変性と、
元の前層の全次数の指定不変比較の自然性を証明した。
有限型の圏の包含の有限極限保存とスキームへの忘却の有限連結極限保存を証明した。
実際のアフィン Čech 各段と底変換の始域のアフィン性・S 上の分離性を証明した。
局所 Noether 基底では、各段の有限次元上界も実際の構造射から供給した。
元の環論的な幾何的推移性から任意のアフィン基底変更の点の推移性を導き、
元の有限型の圏内の指定作用と、実際の Čech 各段へ移した。
切断・推移性・分離性・次元上界を全て供給し、実際の各段の全次数降下を証明した。
増強 Čech nerve の右随伴性から実際の底変換比較を証明した。
恒等射の Čech の定数図式との自然同型、および実際の二重 Čech 全体の
軸交換の自然同型を構成した。値域の Tot の Fubini は引き続き未完である。
同じ基底上の平行な Čech 細分比較の間の実際の単体ホモトピーを構成した。
相互細分の指定比較は両側のホモトピー逆を持ち、元の前層の像にもホモトピーを移した。
元の前層の実際の底変換から自然な pullback を構成し、自然な transfer と局所 rank 公式から
基底の値を含む指定 Čech 増強比較の retract を構成した（§44）。
底変換された係数図式を実際の底変換被覆の Čech 図式と自然同型で結び、
増強先を含む矢の圏の同型から、実際の底変換被覆を使う transfer 還元を得た（§45）。
元の値域の線形性なしでも、実際の図式関手の像に対する観測後の rank 公式から
全次数ごとに transfer を正規化する経路を構成した（§46）。
有限全射の実際の strict transform の有限性・全射性を証明し、局所 Noether 基底で
実際の構造射が平坦なら有限忠実平坦な細分を取り出した（§47）。
この図式を同じ有限型の圏へ持ち上げ、底変換した元の被覆への Čech 細分比較と、
実際の blowup の抽象 blowup 正方形を構成した（§48）。
基底の生成点の持ち上げから全射な被約既約成分を選び、その成分の平坦化後の
有限忠実平坦被覆を元の有限全射の底変換へ細分する射を構成した（§49）。
Noether 整域上の有限加群の非零元による自由化を証明し、実際の全チャートで純変換を
平坦にする中心の存在に必要だった境界外の平坦性を供給した（§50）。
加群純変換を実際の商代数と同定し、その Spec を基本開のスキーム論的像に
閉包含と構造射を保つ同型で結び、全チャートのその像の有限平坦性を証明した（§51）。
像と開底変換の両立から global strict transform の開チャートを周辺チャートの像で表示し、
その構造射を保つ同型と Zariski 局所性で平坦性を貼り合わせた（§52）。
非零因子の境界基本開の逆像の実際の blowup 上の稠密性を証明し、中心補集合と
同一視せず、平坦化で使う同じ D(r) の全射性と有限忠実平坦な細分へ接続した（§53）。
テンソル積の Spec と実際の周辺チャートを同定し、二つの基底への構造射と
同じ境界元の基本開を保つことを証明した（§54）。
`Theorem31.lean` では (3.8) と中心上の帰納仮定による代数的な軌道貼り合わせを証明。
正本 D7 に従う導来値域への実現の型を §19 に明示する。
検証状態：`lake build SerrePositivity.KST.Descent` が成功。
監査状態：`scripts/audit_kst_descent.lean` は 130 モジュール・1564 宣言を検査し成功。
許容公理は標準三公理のみ。主定理や八つの公理の完成を意味しない。
切断を持つ射の帰納の区切りとして、全体ビルド `lake build` も成功（9418 ジョブ）。
終了コードは `set -eo pipefail` で確認。ログは `/tmp/l8-sectioned-full-build.log`。
§38 の Čech 図式の区切りでの全体ビルドは、所有範囲外の
`KST/ProExcision/LinearizedTensor.lean` の 110 行・104 行・140 行のエラーで失敗。
ログは `/tmp/l8-finite-type-cech-full-build.log`、終了コード 1 を確認した。
L8 の対象ビルドと監査は成功しており、import 閉包の破損ではない。
今回の §40 の幾何条件の区切りの全体ビルドは成功（9756 ジョブ）。
`set -eo pipefail` で終了コード 0 を確認し、ログは `/tmp/l8-cech-geometry-full-build.log`。
§41 の全体ビルドはルート集約で失敗。`InfinityCategories/F1/CocartesianPath` の import が
`InfinityCategories/Core/CocartesianPathVertices` と `cocartesianPathVertex._proof_1` を重複登録する。
所有範囲外の衝突で、L8 の対象ビルドと監査は成功したままである。
§45 の transfer 幾何接続の区切りでは全体ビルドが成功（10024 ジョブ）。
`set -eo pipefail` で終了コード 0 を確認。ログは `/tmp/l8-cech-transfer-geometry-full-build.log`。
§48 の strict transform の有限平坦細分の幾何接続でも全体ビルドが成功（10100 ジョブ）。
`set -eo pipefail` で終了コード 0 を確認。ログは `/tmp/l8-strict-transform-refinement-full-build.log`。
終了コード 1 を確認し、ログは `/tmp/l8-affine-cech-descent-full-build.log`。
§42 の全体ビルドも同じ所有範囲外の宣言重複でルート集約に失敗（終了コード 1）。
ログは `/tmp/l8-double-cech-comparison-full-build.log`。L8 の対象ビルド・監査は成功。
L8a 全体の完成とは区別する。
L8b の切断を持つ射について「整 → 被約 → 一般」の帰納を完了した。
自然な列・有限積保存・冪零不変性を明示的に入力する条件付きの段階である。
実際の軌道正方形は構成済み。前層の実降下・Čech 還元とは未接続。
L8c の基本幾何補題を実装。有限型スキームの有限次元上界との接続は残る。
L8d の (3.6) は K0・T2 への明示的な引数として設計する。
L8e の E への接続は外部レーンの成果を使う。
未完成の命題を `sorry` や新しい公理で埋めない。
標準三公理だけの監査通過を、数学的な工程の完成と取り違えない。

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

## 17. 主要宣言の表

この表は検証済みの宣言と予定を区別する。

| 宣言・モジュール | 役割 | 検証状態 |
| --- | --- | --- |
| `FiniteTypeSchemes` | 基底上有限型の圏 | 実装済み |
| `GradedPresheaf` | H、n ∈ ℤ、有理加群、反変性 | 実装済み |
| `GradedPresheaf.pullback_comp` | 反変合成 | 対象ビルド済み |
| `GradedPresheaf.invariantComparison` | 幾何学的な引き戻しの値域制限 | 対象ビルド済み |
| `GradedPresheaf.PiDescent` | 全次数の指定比較が同型という命題の型 | 定義のみ、主定理未証明 |
| `normalizedTransfer_comp` | 正 rank の局所公式から左逆 | 対象ビルド済み |
| `pullback_injective_of_transfer` | 同公式から各次数の単射性 | 対象ビルド済み |
| `normalizedTransfer_naturality` | rank による正規化は自然性を保つ | 対象ビルド済み |
| `permutationInvariants_constant` | 推移的作用の不変族は定数 | 対象ビルド済み |
| `permutationInvariantsEquiv` | (3.8) の代数的な線形同型 | 対象ビルド済み |
| `permutationInvariantsEquiv_apply_eq` | 評価点に依存しない | 対象ビルド済み |
| `piIsomorphisms` | 指定した観測関手による全整数次数の比較 | 対象ビルド済み |
| `piIsomorphisms_of_retract` | 比較射の retract による全次数同型の移行 | 対象ビルド済み |
| `PresheafRealization` | V 値前層と次数付き前層の自然な比較 | 型を実装、実際の E の実現は未構成 |
| `rankTransferRetract` | 導来図式を保持する有理線形圏の retract | 対象ビルド済み |
| `naturalTransferRetract` | 自然変換としての transfer の retract | 対象ビルド済み |
| `naturalComparisonRetract` | 自然な比較そのものの矢の圏の retract | 対象ビルド済み |
| `piComparison_of_transfer` | rank 公式と分裂側の比較から全次数比較 | 対象ビルド済み |
| `trivialInvariantsEquiv` | 自明表現の通常の不変部分の同型 | 対象ビルド済み |
| `averageMap_naturality` | 平均作用素の同変写像に対する自然性 | 対象ビルド済み |
| `invariantMap_surjective` | 有理不変部分は有限群の全射を保つ | 対象ビルド済み |
| `invariantMap_exact` | 有理不変部分は任意の隣接二射の完全性を保つ | 対象ビルド済み |
| `GradedPresheaf.pullbackRepresentation` | 逆元による引き戻しの左表現 | 対象ビルド済み |
| `GradedPresheaf.invariantMap_equivariantPullback` | 表現論的な制限と指定比較の一致 | 対象ビルド済み |
| `rationalInvariants_preservesHomology` | 有理不変部分関手のホモロジー保存 | 対象ビルド済み |
| `invariantsHomologyIso` | 任意の短複体のホモロジーと不変部分の比較 | 対象ビルド済み |
| `baseChangeSplitEpi` | 被覆への持ち上げがある基底変更の切断 | 対象ビルド済み |
| `baseChangeCechExtraDegeneracy` | 非増強 Čech 項上の section への還元用分裂 | 対象ビルド済み |
| `selfPullbackCechExtraDegeneracy` | 自身による底変換後の Čech nerve の分裂 | 対象ビルド済み |
| `selfPullbackCechImageExtraDegeneracy` | 任意の前層を適用した余単体図式の分裂 | 対象ビルド済み |
| `selfPullbackCechImage_contractingHomotopy` | 前層の Čech 図式の収縮ホモトピー | 対象ビルド済み |
| `IsNilpotentThickening` | 核イデアル層が冪零な閉埋め込み | 型を実装 |
| `Nilinvariant` | 係数つき前層に要求する公理 (3) | 法則の型を実装、E の検証は未完 |
| `nilpotentThickening_surjective` | 冪零 thickening の点全射性 | 対象ビルド済み |
| `nilpotentThickening_isIso_of_reduced` | 終域が被約な場合の同型性 | 対象ビルド済み |
| `proper_of_finite` | 有限射の固有性 | 対象ビルド済み |
| `isIso_of_surjective_closedImmersion` | 被約な終域への点全射閉埋め込みの同型性 | 対象ビルド済み |
| `closedImmersion_of_section` | 分離射の切断の閉埋め込み性 | 対象ビルド済み |
| `closedImmersion_equalizer` | 分離な対象への二射の等化子の閉埋め込み性 | 対象ビルド済み |
| `equalizer_range_ne_univ_of_ne` | 被約な始域からの異なる二射の一致場所は真閉 | 対象ビルド済み |
| `topologicalKrullDim_properClosed_lt_bound` | 有限次元上界からの真閉部分の次元低下 | 対象ビルド済み |
| `integral_properClosed_dimension_lt` | 有限次元の整スキームの真閉部分の次元低下 | 対象ビルド済み |
| `AbstractBlowupSquare` | 有限型・Cartesian・固有・閉中心・補開集合上の同型 | 幾何データの型を実装 |
| `GradedMayerVietoris.Hom.bijective_mapA` | 全次数の境界の自然性を使う五項補題 | 対象ビルド済み |
| `GradedPresheaf.squareDifference_comp_squareRestriction` | 指定制限と符号付きの差の零合成 | 対象ビルド済み |
| `SquareMayerVietoris` | 前層の指定制限を持つ長完全列 | 列のデータの型を実装、実降下からの供給は未完 |
| `SquareMayerVietoris.bijective_base_of_three_vertices` | 三頂点の全次数比較から元の指定比較の同型 | 対象ビルド済み |
| `finite_iUnion_proper_closed` | 既約空間上の有限個の真閉部分の和の真閉性 | 対象ビルド済み |
| `coincidenceLocus` | 相異なる添字の射の等化子の像の和 | 定義済み |
| `coincidenceLocus_ne_univ` | 既約被約な基底上の一致場所の和の真閉性 | 対象ビルド済み |
| `eq_index_of_common_restriction_outside` | 補集合で異なる二射の共通の制限を排除 | 対象ビルド済み |
| `coincidenceLocus_dimension_lt_bound` | 一致場所の和における有限次元低下 | 対象ビルド済み |
| `GradedMayerVietoris.Action.fixedSequence` | G 同変な長完全列の有理不変部分も全次数完全 | 対象ビルド済み |
| `GradedMayerVietoris.EquivariantHom.fixedHom` | 境界に自然な比較の不変部分への制限 | 対象ビルド済み |
| `GradedMayerVietoris.EquivariantHom.bijective_fixed_mapA` | 固定部分の B、C の比較から A の比較の全単射性 | 対象ビルド済み |
| `permutationRepresentation` | コピーの逆元による添字置換の左表現 | 定義済み |
| `permutationDiagonal_bijective` | (3.8) の指定対角比較の全単射性 | 対象ビルド済み |
| `permutationDiagonal_naturality` | 指定対角比較と同じ係数写像のコピーへの適用の可換性 | 対象ビルド済み |
| `invariantsProdEquiv` | 積の通常の不変部分と不変部分の積の具体的な線形同型 | 対象ビルド済み |
| `invariantMap_product_bijective` | 成分の不変部分の比較から積の不変部分の比較の同型性 | 対象ビルド済み |
| `splitMayerVietoris` | 比較元の恒等的な正方形の分裂長完全列 | 対象ビルド済み |
| `splitMayerVietorisComparison` | 境界の自然性も差の全射性から導く列の比較 | 対象ビルド済み |
| `orbitStep_pi_bijective` | (3.8) と中心上の帰納仮定による全次数の軌道貼り合わせ | 対象ビルド済み、主定理全体は未完 |
| `Theorem31.lean` | 最小公理から主定理へ | 代数的貼り合わせと実際の軌道段階を公開、全体の証明は未完 |
| `reducedClosedSubscheme` | 任意の閉集合の消滅イデアル層による被約閉構造 | 対象ビルド済み |
| `reducedClosedHomeo` | 被約閉部分スキームとその台の位相同型 | 対象ビルド済み |
| `reducedClosedAsFiniteType` | 基底上有限型の圏内の被約閉中心 | 対象ビルド済み |
| `coincidenceCenter` | section の一致場所の和の被約閉構造 | 対象ビルド済み |
| `coincidenceCenter_dimension_lt_bound` | 実際の一致中心のスキームの次元低下 | 対象ビルド済み |
| `closedCenterSquare_cartesian` | 中心の引き戻しの実際の Cartesian 性 | 対象ビルド済み |
| `abstractBlowupOfReducedCenter` | 中心の外で同型な固有射から抽象 blowup 正方形 | 対象ビルド済み、軌道射自体は未構成 |
| `affine_nilradical_isNilpotent` | アフィン Noether の nilradical イデアル層の冪零性 | 対象ビルド済み |
| `Nilinvariant.affineReduction_pullback_bijective` | 公理 (3) から実際のアフィン被約化の全次数比較 | 対象ビルド済み |
| `schemeReductionLift`、`schemeReductionLift_unique` | 被約な始域からの一意な因子分解 | 対象ビルド済み |
| `schemeReductionFunctor`、`schemeReductionInclusionNat` | 一般の reduction の関手と包含の自然変換 | 対象ビルド済み |
| `schemeReductionAction_comp_inclusion` | 被約化上への群作用の移行と包含の同変性 | 対象ビルド済み |
| `idealSheaf_isNilpotent_of_finite_affine_cover` | 有限被覆上の冪零指数の統一 | 対象ビルド済み |
| `noetherian_nilradical_isNilpotent` | 非アフィンを含む Noether スキームの nilradical の冪零性 | 対象ビルド済み |
| `finiteTypeScheme_isNoetherian` | Noether 基底上の有限型対象の Noether 性 | 対象ビルド済み |
| `finiteTypeReductionFunctor` | 前層 L の定義域内の reduction と包含の自然性 | 対象ビルド済み |
| `GradedPresheaf.invariantPullback_bijective` | 全単射な同変引き戻しの不変部分への制限 | 対象ビルド済み |
| `GradedPresheaf.piDescent_iff_of_bijective_square` | 同変正方形による指定降下比較の移行 | 対象ビルド済み |
| `Nilinvariant.piDescent_iff_reduction` | Noether 基底上の「一般 → 被約」の全次数還元 | 対象ビルド済み、公理 (3) を仮定 |
| `isNilpotentThickening_of_surjective_of_noetherian` | Noether な終域への点全射閉埋め込みの核の冪零性 | 対象ビルド済み |
| `nilpotentThickening_pullback_fst` | Noether な対象への底変換後の冪零性 | 対象ビルド済み |
| `Nilinvariant.piDescent_iff_thickening_baseChange` | 冪零な基底変更の前後の全次数比較 | 対象ビルド済み、公理 (3) を仮定 |
| `Nilinvariant.piDescent_iff_reducedSource` | 基底を固定した始域だけの被約化 | 対象ビルド済み、公理 (3) を仮定 |
| `NaturalBlowupSequences.orbit_piDescent_of_reduced_center` | 被約化した中心上の降下から実際の軌道段階へ | 対象ビルド済み、次元帰納そのものは未完 |
| `TranslatedSectionIndex` | 一つの切断の移動から重複を除いた添字 | 対象ビルド済み、有限・非空・推移的な作用 |
| `translatedSection_identity`、`translatedSection_injective` | 相異なる実際の切断族 | 対象ビルド済み |
| `translatedSection_covering` | 基礎点のファイバーの推移性からの像の被覆 | 対象ビルド済み、アフィンの幾何的推移性との接続も実装 |
| `translatedSection_center_dimension_lt_bound` | 移動切断の一致中心での次元低下 | 対象ビルド済み、有限次元上界を明示 |
| `exists_common_geometric_points` | 同じ基底点上の二点を共通の代数閉体から表示 | 対象ビルド済み |
| `geometricTransitivity_on_fibers` | 既存の環論的な幾何的推移性から通常の点の推移性 | 対象ビルド済み |
| `specAction`、`specAction_over_base` | 逆元を介した Spec の左作用と基底の保存 | 対象ビルド済み |
| `affineAlgebraObject`、`affineAlgebraAction` | 有限型の圏内の実際のアフィン対象と群作用 | 対象ビルド済み |
| `affine_translatedSection_covering` | 幾何的推移性から重複を除いた実際の移動切断の被覆 | 対象ビルド済み、切断の存在は入力 |
| `tensorBaseChangeMulSemiringAction`、`tensorBaseChange_smulCommClass` | B ⊗_A T 上の B 線形な群作用 | 対象ビルド済み |
| `tensorBaseChangeFiberEquiv_equivariant` | 幾何ファイバーの標準同型と作用の両立 | 対象ビルド済み |
| `geometricTransitivity_baseChange` | 任意の係数拡大による既存の幾何的推移性の保存 | 対象ビルド済み、平坦性・有限型性は不要 |
| `reducedSourceAction_transitive_on_fibers` | 始域だけの被約化による点のファイバーの推移性の保存 | 対象ビルド済み、Noether 性は不要 |
| `finiteTypeReductionLift`、`finiteTypeReductionLift_comp_inclusion` | 被約な始域から有限型の圏内の被約化への指定持ち上げ | 対象ビルド済み |
| `affine_baseChange_liftedSection_covering` | 基底変更と始域の被約化後の、元の切断からの移動切断の被覆 | 対象ビルド済み、基底は被約 |
| `closedBaseChangeAction_transitive_on_fibers` | 任意の閉中心への実際の引き戻しでの点の推移性 | 対象ビルド済み |
| `closedBaseChangeSection`、`closedBaseChangeSection_identity` | 元の切断から実際の閉中心上の切断を構成 | 対象ビルド済み |
| `closedBaseChange_reducedSection_covering` | 被約な閉中心上の始域の被約化後の被覆 | 対象ビルド済み |
| `orbitCenterAction_transitive_on_fibers`、`orbitCenterSection` | 構成済みの軌道中心への推移性と切断の直接接続 | 対象ビルド済み |
| `orbitCenter_reducedSection_covering` | 実際の軌道中心の始域の被約化後の移動切断の被覆 | 対象ビルド済み |
| `closedCoverAbstractBlowup` | 被約な終域の二つの閉部分による被覆を抽象 blowup とする | 対象ビルド済み、交わりは実際の引き戻し |
| `NaturalBlowupSequences.closedCoverSequence` | 閉和の全次数の境界と完全性を供給 | 対象ビルド済み、自然な blowup 列のデータを入力 |
| `closedCoverPullback_covering`、`closedCoverPullbackBlowup` | 始域へ引き戻した実際の閉被覆と抽象 blowup | 対象ビルド済み |
| `closedCoverPullbackCube` | 引き戻した交わりから元の交わりへの射と比較立方体 | 対象ビルド済み |
| `closedCoverPullbackSquareAction`、`closedCoverPullbackCube_equivariant` | 閉和の四頂点の作用と比較の同変性 | 対象ビルド済み |
| `NaturalBlowupSequences.closedCoverFixedComparison` | 閉和の境界を含む有理固定部分の列の比較 | 対象ビルド済み |
| `NaturalBlowupSequences.closedCover_piDescent` | 二つの閉部分と交わりの指定降下から元の射の全次数降下 | 対象ビルド済み、自然な列と三つの局所降下を入力 |
| `integralComponent`、`integralComponent_isIntegral` | 各既約成分の整な有限型閉構造 | 対象ビルド済み |
| `irreducibleComponentIndex_finite`、`integralComponent_covering` | Noether の場合の有限な整成分の閉被覆 | 対象ビルド済み |
| `componentSplitBlowup` | 一成分と残りの被約閉和の実際の正方形 | 対象ビルド済み |
| `componentSplit_intersection_dimension_lt_bound` | 非被約なままの実際の交わりの次元低下 | 対象ビルド済み、自然数上界を明示 |
| `componentRemainder_cover_card_lt` | 残りを覆う元の成分数の減少 | 対象ビルド済み |
| `reducedClosedMapOfLE` | 閉集合の包含から被約閉構造間の実際の射 | 対象ビルド済み |
| `componentToRemainder_covering` | 他の元の整成分から残りへの実際の有限閉被覆 | 対象ビルド済み |
| `fiberTransitivity_of_injective_square` | 同変で始域側が点上単射な正方形による推移性の移行 | 対象ビルド済み |
| `finiteTypeReductionMap_section`、`finiteTypeReductionAction_transitive_on_fibers` | 始域・基底の同時の被約化後の切断と点の推移性 | 対象ビルド済み |
| `finiteTypeReduction_dimension` | 有限型の圏内の被約化の次元保存 | 対象ビルド済み |
| `closedCoverIntersectionSection_identity` | 元の切断から交わりの指定比較の実際の切断を構成 | 対象ビルド済み |
| `closedCoverIntersection_transitive_on_fibers` | 実際の交わりの指定比較の点の推移性 | 対象ビルド済み |
| `closedCoverIntersection_reduced_covering` | 両側の被約化後の交わり上の移動切断の被覆 | 対象ビルド済み、幾何条件を元の射から導出 |
| `GradedPresheaf.piDescent_of_isIso`、`GradedPresheaf.piDescent_of_empty_target` | 同型と空の基底の全次数降下 | 対象ビルド済み、前層の降下公理は不要 |
| `SectionedDescentBelow` | 厳密に低い基底次元の切断を持つ射に対する帰納仮定の型 | 定義済み、前層の公理には含めない |
| `sectionedDescentBelow_zero` | 零より低い次元の帰納仮定を空の基底から供給 | 対象ビルド済み |
| `NaturalBlowupSequences.integral_reducedSource_piDescent_of_below` | 整な基底と被約な始域の段階を低次元から閉じる | 対象ビルド済み、中心上の降下は低次元から導出 |
| `NaturalBlowupSequences.integral_piDescent_of_below` | 整な基底と一般の始域の全次数降下の帰納段階 | 対象ビルド済み、Noether 性と公理 (3) を明示 |
| `irreducibleComponents_card_le_of_closed_cover` | 有限既約閉被覆による実際の既約成分数の上界 | 対象ビルド済み |
| `componentRemainder_componentCount_lt` | 残り自身の既約成分数の厳密な減少 | 対象ビルド済み |
| `SectionedDescentFewerComponents` | 成分数が厳密に少ない被約基底への帰納仮定の型 | 定義済み、最小公理には含めない |
| `NaturalBlowupSequences.reducedBase_piDescent_of_below` | 成分数の強い帰納を実行した被約基底の段階 | 対象ビルド済み、成分数の仮定は残らない |
| `NaturalBlowupSequences.piDescent_of_below` | 被約化を戻した一般の基底の一段 | 対象ビルド済み、低次元の仮定だけを入力 |
| `NaturalBlowupSequences.sectionedDescentBelow` | 外側の次元帰納による全ての低次元の仮定の構成 | 対象ビルド済み |
| `NaturalBlowupSequences.sectioned_piDescent` | 切断を持つ射の全次数降下 | 対象ビルド済み、局所降下・次元・成分数の帰納仮定は残らない |
| `affineSplitSection`、`affineSplitSection_identity` | 環の分裂から固定した S 上の切断 | 対象ビルド済み |
| `NaturalBlowupSequences.affine_split_piDescent` | 分裂するアフィン射の全次数降下 | 対象ビルド済み、元の L を使用 |
| `tensorBaseChangeRetraction` | 指定された T → B から底変換の分裂 | 対象ビルド済み、B 代数射 |
| `NaturalBlowupSequences.affine_baseChange_piDescent` | 分裂するテンソル積底変換の全次数降下 | 対象ビルド済み |
| `NaturalBlowupSequences.affine_selfBaseChange_piDescent` | 自己底変換の全次数降下 | 対象ビルド済み |
| `tensorSpecSquare_isPullback` | 指定二射影の実際の Cartesian 性 | 対象ビルド済み |
| `tensorSpecSquare_right_equivariant` | 右射影の元の作用との同変性 | 対象ビルド済み |
| `affineTensorSquare_isPullback` | 同じ S 上の有限型の圏内の Cartesian 性 | 対象ビルド済み |
| `affineTensorSection`、`affineTensorSection_identity` | 指定環射から有限型の圏内の切断と分裂恒等式 | 対象ビルド済み |
| `affineTensorAction_over_base`、`affineTensorSnd_equivariant` | 有限型の圏内の二射影の同変性 | 対象ビルド済み |
| `NaturalBlowupSequences.affineTensorFst_piDescent` | 指定された実際の底変換の第一射影の全次数降下 | 対象ビルド済み、元の L を使用 |
| `finiteTypeMorphism_locallyOfFiniteType` | 有限型対象間の射の局所有限型性 | 対象ビルド済み、Noether 性は不要 |
| `finiteTypePullback_isPullback` | Noether 基底上の実際の引き戻しを有限型の圏内へ構成 | 対象ビルド済み |
| `finiteTypeSchemes_hasFiniteLimits` | Noether 基底上の有限型の圏の有限極限 | 対象ビルド済み、幾何的な通常の極限 |
| `finiteTypeAugmentedCech` | 元の前層の定義域内の増強 Čech nerve | 対象ビルド済み |
| `finiteTypeCechBaseChange` | Čech 各段での底変換を束ねた Arrow の関手 | 対象ビルド済み、全単体射に対して定義 |
| `finiteTypeDoubleCech`、`finiteTypeDoubleCechImage` | 実際の二重 Čech 図式と元の前層の像 | 対象ビルド済み |
| `finiteTypeCechStageSplitEpi` | 各非増強段での底変換の実際の切断 | 対象ビルド済み、切断の外側自然性は主張しない |
| `finiteTypeCechStageExtraDegeneracy`、`finiteTypeCechStageImageExtraDegeneracy` | 各行の全次数の分裂と同じ前層の像での分裂 | 対象ビルド済み、Tot の実降下は未完 |
| `isPullback_isoPullback_equivariant` | Cartesian モデルと指定引き戻しの標準同型の同変性 | 対象ビルド済み、任意の圏で証明 |
| `pullbackAction_map_trivialBase` | 基底変更の射と元の始域の作用の可換性 | 対象ビルド済み |
| `affineTensorPullbackIso_equivariant` | テンソル積モデルと実際のアフィン引き戻しの作用の比較 | 対象ビルド済み |
| `NaturalBlowupSequences.affine_pullback_piDescent` | 指定引き戻しの第一射影の全次数降下 | 対象ビルド済み、元の L と指定作用を保持 |
| `finiteTypeCechStageAction_over_base` | 実際の Čech 各段のファイバーへの群作用 | 対象ビルド済み |
| `finiteTypeCechStageAction_naturality` | 外側の全単体射による底変換の射の同変性 | 対象ビルド済み |
| `GradedPresheaf.finiteTypeCechStageComparison_naturality` | 全係数・全整数次数の指定不変比較の外側自然性 | 対象ビルド済み |
| `finiteTypeOverInclusion_preservesFiniteLimits` | 有限型の圏から Over への包含の有限極限保存 | 対象ビルド済み、Noether 基底 |
| `finiteTypeSchemesForget_preservesFiniteConnectedLimits` | スキームへの忘却の有限連結極限保存 | 対象ビルド済み、終対象保存とは区別 |
| `finiteTypeLimit_isAffine` | アフィン有限型対象の有限連結極限のアフィン性 | 対象ビルド済み |
| `finiteTypeCechStage_isAffine`、`finiteTypeCechStageSource_isAffine` | 実際の Čech 段と底変換の始域のアフィン性 | 対象ビルド済み |
| `finiteTypeCechStageSource_isSeparated` | 各段の底変換の始域の S 上の分離性 | 対象ビルド済み、S の分離性は不要 |
| `finiteType_spec_dimension_bound` | Noether 基底環の上界から有限型代数の有限次元上界を供給 | 対象ビルド済み、多項式環の商を使用 |
| `localNoether_spec_dimension_bound` | 局所 Noether 基底の極大イデアルの生成元数による上界 | 対象ビルド済み |
| `affineMorphism_dimension_bound` | 実際の有限型アフィン射の始域の次元上界 | 対象ビルド済み、座標環の代数構造と有限型性を導出 |
| `localNoether_finiteTypeCechStage_dimension_bound` | 局所 Noether 基底の実際の Čech 各段の有限次元上界 | 対象ビルド済み、段ごとの上界を仮定しない |
| `schemeFiberTransitivity_of_iso` | 同変な始域・基底の同型による点の推移性の移行 | 対象ビルド済み |
| `schemeFiberTransitivity_of_injective_square` | underlying scheme の同変な単射正方形による推移性の移行 | 対象ビルド済み |
| `affineSchemeBaseChange_transitive` | 任意のアフィン基底変更の指定作用の点の推移性 | 対象ビルド済み、元の幾何的推移性から導出 |
| `affineFiniteTypeBaseChange_transitive` | 有限型の圏の指定引き戻しの点の推移性 | 対象ビルド済み、忘却による Cartesian 比較を使用 |
| `affineCechStage_transitive` | 実際のアフィン Čech 各段での底変換の推移性 | 対象ビルド済み、段ごとの推移性を仮定しない |
| `NaturalBlowupSequences.affineCechStage_piDescent` | 実際の Čech 各非増強段での全次数降下 | 対象ビルド済み、局所 Noether 基底、段ごとの幾何条件と降下の仮定は残らない |
| `arrow_isPullback_of_components` | Arrow の両端での Cartesian 性の検査 | 対象ビルド済み |
| `augmentedCechNerve_preservesPullbacks` | 増強 Čech nerve の引き戻し保存 | 対象ビルド済み、既存の右随伴性を使用 |
| `baseChangeAugmentedCech_isPullback` | 底変換した射の増強 Čech 図式の Cartesian 性 | 対象ビルド済み |
| `identityCechIso` | 恒等射の Čech nerve と定数図式の自然同型 | 対象ビルド済み、指定増強が hom |
| `baseChangeCechIso` | Čech の実際の底変換比較の全単体次数の同型 | 対象ビルド済み、図式全体の標準同型 |
| `doubleCech_isPullback` | 実際の二重 Čech 各対象のファイバー積表示 | 対象ビルド済み、二射影を指定 |
| `doubleCechSwapIso_involutive` | 二重 Čech の軸交換の二回の合成が恒等 | 対象ビルド済み |
| `doubleCechSwapIso_inner_naturality`、`doubleCechSwapIso_outer_naturality` | 全ての単体射と軸交換の整合性 | 対象ビルド済み |
| `doubleCechSwapNatIso` | 実際の二重 Čech 全体の軸交換の自然同型 | 対象ビルド済み、Tot の交換とは区別 |
| `cechMixIndex` と七つの添字恒等式 | 細分ホモトピーの重複座標と比較タグ | 対象ビルド済み、有限順序集合の算術 |
| `refinementCechHomotopy` | 同じ基底上の平行な細分 Čech 比較の単体ホモトピー | 対象ビルド済み、全ての面射・退化射を検査 |
| `refinementCechMap_id`、`refinementCechMap_comp` | 指定細分比較の恒等射・合成の保存 | 対象ビルド済み |
| `refinementCechHomotopyLeftInverse`、`refinementCechHomotopyRightInverse` | 相互細分の両側のホモトピー逆 | 対象ビルド済み、持ち上げの合成が恒等である仮定は不要 |
| `refinementCechImageHomotopyLeftInverse`、`refinementCechImageHomotopyRightInverse` | 元の前層の像における両側のホモトピー | 対象ビルド済み、Tot の実降下とは区別 |
| `baseChangePresheafPullback`、`baseChangePresheafPullback_at_base` | 元の前層の実際の底変換の自然な pullback と基底での比較 | 対象ビルド済み、実際の二射影を使用 |
| `BaseChangeTransfer.retract` | 自然な transfer と局所 rank 公式からの前層 retract | 対象ビルド済み、transfer の存在は明示入力 |
| `presheafAugmentationComparison`、`BaseChangeTransfer.augmentationRetract` | 基底の値を含む指定増強の自然性と retract | 対象ビルド済み、全ての図式射を保持 |
| `BaseChangeTransfer.cechAugmentationRetract` | 実際の Čech 増強比較の矢の圏の retract | 対象ビルド済み、Tot はまだ接続しない |
| `BaseChangeTransfer.piCechComparison_of_transfer` | 図式関手での像の全次数比較の移行 | 対象ビルド済み、実際の観測関手は明示入力 |
| `cechBaseChangeGeometryIso` | 実際の底変換被覆の Čech と Over 底変換図式の自然同型 | 対象ビルド済み、二射影と全単体射を保持 |
| `cechBaseChangeStageIso_augmentation`、`cechBaseChangeAugmentationIso` | 幾何的増強の可換性と前層の増強比較の矢の圏の同型 | 対象ビルド済み、増強先も含む |
| `BaseChangeTransfer.cechBaseChangedCoverRetract` | 実際の底変換被覆の Čech 比較への retract | 対象ビルド済み、transfer と局所 rank 公式は明示入力 |
| `BaseChangeTransfer.piCechComparison_of_baseChangedCover` | 実際の底変換被覆の全次数比較から元への還元 | 対象ビルド済み、Tot の実構成と分裂降下は別工程 |
| `invertibleCompositeRetract`、`naturalComparisonRetractOfIsoComposite` | 往復の合成の同型性による比較射の retract | 対象ビルド済み、圏の線形性は不要 |
| `piComparison_of_observedComposite`、`piComparison_of_observedRank` | 観測後の同型・rank 公式による全次数比較の移行 | 対象ビルド済み、元の圏に線形性を課さない |
| `BaseChangeTransfer.piCechComparison_of_observedRank` | 実際の底変換被覆からの観測後の transfer 還元 | 対象ビルド済み、rank 公式は実際の図式関手の像で要求 |
| `surjective_of_proper_dense_restrict` | 固有射の稠密開集合上の全射性から全射性 | 対象ビルド済み、開部分での同型性は不要 |
| `strictTransformπ_isFinite`、`strictTransformπ_restrict_surjective` | 実際の strict transform の有限性と開部分上の全射性 | 対象ビルド済み、既存の実際の閉包含を使用 |
| `strictTransformπ_centerComplement_surjective` | 有限全射の中心外からの strict transform の全射性 | 対象ビルド済み、実際の blowup の中心外の稠密性を使用 |
| `strictTransformπ_locallyOfFinitePresentation` | 局所 Noether 基底上の有限射の strict transform の有限表示性 | 対象ビルド済み、基底の局所 Noether 性を明示 |
| `exists_finiteFlat_refinement_of_flat_strictTransform` | 平坦化した実際の strict transform から有限忠実平坦な細分を取り出す | 対象ビルド済み、平坦化中心の存在は別工程 |
| `finiteTypeBlowup`、`finiteTypeBlowupProjection` | 元の有限型の圏内の実際の blowup と構造射 | 対象ビルド済み、Noether 基底上 |
| `finiteTypeStrictTransform`、`finiteTypeStrictTransformProjection`、`finiteTypeStrictTransformToOriginal` | 元の有限型の圏内の実際の strict transform と二つの指定射 | 対象ビルド済み、有限射を要求 |
| `finiteTypeStrictTransformToPullback`、`finiteTypeStrictTransformCechRefinement` | 実際の底変換被覆への細分射と Čech 比較 | 対象ビルド済み、全単体射と指定増強を保持 |
| `finiteTypeStrictTransform_flatCover` | 平坦化後の指定射の有限性・平坦性・全射性・局所有限表示性 | 対象ビルド済み、平坦性は実際の構造射の入力 |
| `finiteTypeBlowupSquare` | 実際の blowup の抽象 blowup 正方形 | 対象ビルド済み、被約閉中心と実際の引き戻しを使用 |
| `surjective_of_proper_genericPoint_mem_range` | 生成点を像に含む固有射の全射性 | 対象ビルド済み、既約性と閉像性を使用 |
| `integralComponentMap`、`integralComponentMap_isFinite` | 被約既約成分から元の基底への指定射と有限性 | 対象ビルド済み、同じ有限型の圏内 |
| `exists_surjective_integralComponent` | 既約基底への固有全射から全射な整成分を選ぶ | 対象ビルド済み、Noether 性も成分の有限個性も不要 |
| `exists_finite_surjective_integralComponent` | 整基底への有限全射から平坦化すべき整な有限全射成分を選ぶ | 対象ビルド済み、始域の被約性は不要 |
| `exists_finiteFlat_cover_refining_blowup` | 支配する整成分の平坦化後の被覆から元の射の底変換への細分 | 対象ビルド済み、指定中心での実際の平坦性は入力 |
| `exists_nonzero_away_free_of_finite` | Noether 整域上の有限加群の非零元による自由化 | 対象ビルド済み、元の平坦性は不要 |
| `exists_nonzero_away_flat_of_finite` | 同じ有限加群の境界外の平坦性 | 対象ビルド済み、生成点付近の自由化から導出 |
| `exists_nonzero_finite_module_flattening_center` | Noether 整域上有限な加群の実際の全チャート純変換の平坦化中心 | 対象ビルド済み、スキームの strict transform との同定は別工程 |
| `boundaryTorsionIdeal`、`algebraPureTransform` | 境界ねじれを除く実際のイデアルと商代数 | 対象ビルド済み、有限性は定義に不要 |
| `algebraPureTransformModuleEquiv`、`boundaryTorsionIdeal_eq_ker` | 加群純変換との線形同型と環の局所化の核との一致 | 対象ビルド済み、代表元を保つ |
| `algebraPureTransformToLocalization_injective` | 商代数から一元局所化への単射 | 対象ビルド済み、全射性は主張しない |
| `algebraPureTransformSpecπ_flat`、`algebraPureTransformSpecπ_isFinite` | 商の実際の Spec の平坦性・有限性 | 対象ビルド済み、元の加群の性質から移送 |
| `algebraPureTransformImageIso`、`algebraPureTransformBasicOpenImageIso` | 商の Spec と局所化・基本開の実際のスキーム論的像との同型 | 対象ビルド済み、閉包含を保持 |
| `algebraPureTransformBasicOpenImageIso_hom_structure` | 基本開の像との同型の基礎環上の可換性 | 対象ビルド済み、構造射を保持 |
| `algebraBoundaryOpen_image_flat`、`algebraBoundaryOpen_image_isFinite` | 基本開の実際のスキーム論的像の構造射の平坦性・有限性 | 対象ビルド済み、構造層を保持 |
| `exists_nonzero_finiteFlat_image_charts` | 実際の全 blowup チャート上のアフィン像を有限平坦にする中心 | 対象ビルド済み、global strict transform とのチャート比較・貼り合わせは別工程 |
| `ker_of_openBaseChange`、`ker_pullback_open` | 準コンパクトな射の核と開底変換の両立 | 対象ビルド済み、イデアル層としての等式 |
| `imageOpenBaseChangeIsoOfIsPullback`、`imageOpenBaseChangeIso` | 実際の像と開底変換の標準同型 | 対象ビルド済み、具体的な Cartesian モデルにも適用可 |
| `strictTransformOpen_quasiCompact` | 局所 Noether 基底上の有限型射の strict transform の定義開包含の準コンパクト性 | 対象ビルド済み、像の底変換の入力を供給 |
| `strictTransformOpenChartIso`、`strictTransformOpenChartIso_hom_snd` | 周辺チャートの像と global strict transform の実際のチャートの同型 | 対象ビルド済み、チャート基底への構造射を保持 |
| `strictTransform_chart_flat_of_image_flat` | 周辺チャートの像の平坦性から strict transform のチャートの平坦性 | 対象ビルド済み、実際のスキームの射に適用 |
| `strictTransform_flat_of_openChart_images` | 周辺チャートの全ての像の平坦性から global strict transform の平坦性 | 対象ビルド済み、実際の開被覆を使う |
| `basicOpen_dense_of_nonZeroDivisor` | 非零因子の基本開の稠密性 | 対象ビルド済み、Noether 性・被約性は不要 |
| `affineBlowup_boundary_dense` | アフィン blowup 上の境界基本開の逆像の稠密性 | 対象ビルド済み、中心補集合との一致は不要 |
| `blowup_boundary_dense_of_isAffine` | アフィン基底の実際の global blowup 上の境界逆像の稠密性 | 対象ビルド済み、全体のアフィンモデルから移送 |
| `strictTransformπ_boundary_surjective` | 平坦化と同じ境界基本開からの有限全射の strict transform の全射性 | 対象ビルド済み、生成点・中心の補集合の置換はしない |
| `exists_finiteFlat_cover_refining_boundary` | 同じ境界での整成分の平坦化から元の有限射を細分する有限忠実平坦被覆 | 対象ビルド済み、実際の平坦性は引き続き供給すべき入力 |
| `strictTransformTensorChart_isPullback`、`strictTransformTensorChart_ambient_isPullback` | テンソル積モデルと実際の周辺チャートの共通の Cartesian 表示 | 対象ビルド済み、チャートの係数射との可換性を明示 |
| `strictTransformTensorChartIso` | テンソル積の Spec と実際の周辺チャートの標準同型 | 対象ビルド済み、引き戻しの普遍性を使用 |
| `strictTransformTensorChartIso_hom_snd`、`strictTransformTensorChartIso_hom_base` | チャート基底と元の基礎環への構造射の保存 | 対象ビルド済み、同じ指定射を使用 |
| `strictTransformTensorChartIso_preimage_boundary` | 同じ境界基本開の二つのチャートでの一致 | 対象ビルド済み、型の一致だけではなく開集合として証明 |
| `finiteCoproductDesc_isFinite` | 共通の終域への有限個の有限射を非交和にまとめる | 対象ビルド済み |
| `sectionOrbitMap_isFinite`、`sectionOrbitMap_isProper` | 分離射の有限個の切断からの軌道射の有限性・固有性 | 対象ビルド済み |
| `reducedSectionOrbitMap_isFinite` | 被約化への切断の軌道射の有限性 | 対象ビルド済み |
| `sectionOrbitAction` | コピーの添字の左作用による非交和の自己同型 | 対象ビルド済み |
| `reducedSectionOrbitMap_equivariant` | 被約化への軌道射の G 同変性 | 対象ビルド済み |
| `reducedSectionOrbitMap_surjective` | 明示した像の被覆から軌道射の全射性 | 対象ビルド済み、幾何的推移性との接続は未完 |
| `openImmersion_of_closedImmersion_of_open_range` | 被約な終域への開像を持つ閉埋め込みの開埋め込み性 | 対象ビルド済み |
| `finiteClosedCoproduct_isIso` | 被約な終域の互いに素な有限閉被覆の非交和は同型 | 対象ビルド済み |
| `eq_index_of_equal_section_points_outside` | 共通像を持つ点を引き戻しへ持ち上げた一致場所の判定 | 対象ビルド済み |
| `disjoint_restricted_section_ranges_outside` | 中心の逆像を避ける開集合上の切断の像の互いに素 | 対象ビルド済み |
| `restrictedSectionCoproduct_isIso` | 制限切断の非交和から被約な補開集合への同型 | 対象ビルド済み |
| `coproductRestrictionIso` | 有限非交和と開制限の標準同型 | 対象ビルド済み、指定制限との可換式を保持 |
| `sectionOrbitMap_restrict_isIso` | 軌道射自体の一致中心の外での同型 | 対象ビルド済み |
| `abstractBlowupOfClosedImmersion` | 非被約な閉中心も許す実際の引き戻し正方形 | 対象ビルド済み |
| `orbitSource`、`orbitMorphism` | 有限型の圏内の軌道射と有限性 | 対象ビルド済み |
| `orbitAbstractBlowup` | 中心 V ×_B Z を保持する実際の抽象 blowup | 対象ビルド済み、像の被覆を明示的に仮定 |
| `orbitAction`、`orbitMorphism_equivariant` | 有限型の圏内のコピーの作用と軌道射の同変性 | 対象ビルド済み |
| `pullbackAction` | 基底の作用も許す実際の引き戻し上の G 作用 | 対象ビルド済み、両射影の同変性も証明 |
| `finiteTypeActionOfSchemeAction` | 構造射を保つスキームの作用の有限型の圏への持ち上げ | 対象ビルド済み |
| `closedPullbackAction` | 閉中心の引き戻しの有限型の圏内の作用 | 対象ビルド済み、非被約な中心を許す |
| `SquareAction` | 四頂点の作用と四辺の同変性 | 幾何データの型を実装 |
| `orbitAbstractBlowupAction` | 実際の軌道正方形の四頂点・四辺の同変性 | 対象ビルド済み |
| `SquareAction.restriction_equivariant`、`difference_equivariant` | 前層の指定制限と差の同変性 | 対象ビルド済み |
| `SquareMayerVietoris.withSquareAction` | 幾何正方形と境界の同変性から全次数の列の作用 | 対象ビルド済み、境界の同変性は明示的な入力 |
| `SquareMayerVietoris.pullbackComparison` | 異なる幾何正方形の射による長完全列の比較 | 対象ビルド済み、境界の自然性を入力 |
| `NaturalBlowupSequences` | 実降下から供給する自然な全次数の列の接続データ | 型を実装、実降下からの存在の構成は未完 |
| `NaturalBlowupSequences.boundary_equivariant` | 境界の自然性から同変性を導出 | 対象ビルド済み |
| `NaturalBlowupSequences.fixedComparison_bijective_base` | 同変立方体の固定部分の列の全次数五項補題 | 対象ビルド済み |
| `identityCenterSquare`、`identityCenterBlowup` | 基底と中心の恒等変形の比較元 | 対象ビルド済み、境界の零性も証明 |
| `orbitComparisonCube`、`orbitComparisonCube_equivariant` | 実際の軌道正方形から基底の分裂正方形への同変立方体 | 対象ビルド済み |
| `NaturalBlowupSequences.orbitFixedComparison` | 指定幾何射からの不変部分の全次数比較 | 対象ビルド済み |
| `NaturalBlowupSequences.orbit_piDescent_of_fixed_components` | 中項・例外部分の固定比較から実際の PiDescent | 対象ビルド済み、(3.8)・帰納からの仮定の供給は未完 |
| `GradedPresheaf.copyEvaluation`、`copyEvaluationIntertwining` | 各コピーの包含の引き戻しと置換表現への同変性 | 対象ビルド済み |
| `GradedPresheaf.copyEvaluation_fixed_fold` | 実際の fold の比較と指定対角写像の一致 | 対象ビルド済み |
| `GradedPresheaf.copyEvaluation_bijective_of_preservesProduct` | 非交和の普遍性と積保存から指定評価の全単射性 | 対象ビルド済み、有限積保存は実降下からの供給が残る |
| `orbitComponent`、`orbitComponent_action`、`orbitFold` | 有限型の圏内のコピーの包含と fold、置換との両立 | 対象ビルド済み |
| `orbitSourceIsCoproduct` | 有限型の圏内の軌道の非交和の実際の普遍性 | 対象ビルド済み |
| `orbitFold_piDescent_of_preservesProduct` | コピーの有限積保存から (3.8) の幾何的な全次数比較 | 対象ビルド済み |
| `GradedPresheaf.fixedPullbackIntertwining_bijective` | 指定降下比較を幾何的自明作用からの固定比較へ移す | 対象ビルド済み |
| `NaturalBlowupSequences.orbitProductComparison_bijective` | (3.8) と中心上の降下から実際の中項の固定比較 | 対象ビルド済み |
| `NaturalBlowupSequences.orbit_piDescent_of_center_and_exceptional` | 中心上の降下と例外部分の比較から軌道段階を閉じる | 対象ビルド済み、後続の定理で例外部分の入力も導出 |
| `finiteTypeCofanIsColimitOfSchemeIsColimit` | スキームの非交和の普遍性を有限型の圏へ反映 | 対象ビルド済み |
| `closedImmersionSquare_isPullback` | 閉中心の具体的な引き戻しの有限型の圏内の普遍性 | 対象ビルド済み、持ち上げと二射影の公式も実装 |
| `orbitExceptional_isPullback` | 二段の例外部分の合成引き戻し W ×_B Z の普遍性 | 対象ビルド済み、スキームの圏でも証明 |
| `orbitExceptionalIsCoproduct` | 実際の例外部分が指定された Z のコピーの非交和 | 対象ビルド済み、有限型の圏内の普遍性 |
| `orbitExceptionalComponent_action` | 既存の引き戻し作用が指定包含を添字で置換 | 対象ビルド済み |
| `orbitExceptional_piDescent_of_preservesProduct` | 例外部分の (3.8) による全次数降下 | 対象ビルド済み、Z のコピーの有限積保存を入力 |
| `NaturalBlowupSequences.orbitExceptionalComparison_bijective` | 実際の比較立方体の例外部分の固定比較の同型 | 対象ビルド済み |
| `NaturalBlowupSequences.orbit_piDescent_of_center` | 自然な列・二つのコピーの積保存・中心上の降下から実際の軌道段階 | 対象ビルド済み、主定理の次元帰納は未完 |
| `SchemeFacts` | 幾何入力の証明 | 基本補題を実装、有限型での次元上界との接続は未完 |
| support comparison（予定） | K0・T2 から (3.6) | 未実装 |
| E realization（予定） | 外部レーンの実装への接続 | 未実装 |

## 18. 設計の確認点

次数付き可換群値の前層だけから Tot を復元しない。
各次数の通常の極限で Tot を置換しない。
導来降下を記述するための値域の追加構造を区別する。
π_* の公開界面とスペクトルの具体的な構成を分離する。
界面を確定する場合は L9 の所有と整合させる。
既に完成したとの体裁で未実装の法則を bundle に隠さない。
正本 D7 がすでに認める導来値域の型の具体化は §19 に従って進める。
必要な数学的設計変更があれば具体的な差分を提示して停止する。
独立に証明できる代数的基礎は先に検証可能にする。
import 閉包破損で停止した場合は失敗した import とログを記録する。
工程完了時は現在地と主要宣言表を更新する。
その報告後は承認を待たず次の工程に進む。

## 19. 導来値域への実現と全次数の公開界面

正本 D7 は Sp と Sp 内の極限を γ から受けることをすでに指定している。
従って導来値域を外部の引数にすることは、その既存の方針の型への具体化である。
次数付き可換群値の前層だけでは、公理 (1) の Tot と公理 (2) の
ホモトピー引き戻しを定義できないため、このデータを区別する。
全次数の群を保持することと、導来図式を保持することは別の条件。
最小公理そのものの数学的内容は変更しない。
公開主張を全次数 π_* 同型に保ちながら、実現のデータを外部から受ける。

### 19.1 誤った置換が生む具体的な問題

有理 Eilenberg–Mac Lane スペクトルを Hℚ とする。
ホモトピー引き戻し `0 ×ʰ_{Hℚ} 0` は `ΩHℚ`。
従ってその π₋₁ は ℚ で非零。
一方、各次数の通常の引き戻し `0 ×_{π_n(Hℚ)} 0` はすべて零。
このため、blowup 降下を各次数の群の通常の pullback としては書けない。
必要なのは境界写像を含む長完全列とその自然性。
Tot でも、単に次数ごとの通常の極限を取る定義は使えない。
補題 3.2 の transfer の左逆も、導来図式上の自然な retract である必要がある。
π_* の上でだけ分裂を作り、Tot にそのまま移してはならない。

### 19.2 実装した実現の界面

L9 が所有する導来値域 V とその図式・homotopy limit の構造を引数として受ける。
本レーンでは V の具体的なモデルを新設しない。
H ごとに V 値の反変前層 `value H` を保持する。
各 n の有理加群値の観測関手を引数にする。
L8 ではこれを π_n として新たに定義せず、L9 の実構成を後で代入する。
その合成と現在の `GradedPresheaf H n` との自然な比較同型を保持する。
記号的には `observation n ∘ value H ≅ L H n`。
Lean では `PresheafRealization.comparison` の自然同型として保持する。
π_n はこの界面に接続し、L8 で別の π_n を定義しない。
Zariski Čech 比較は V の実際の Tot に対して書く（未実装）。
抽象 blowup 比較は V の実際のホモトピー引き戻しに対して書く（未実装）。
transfer は導来図式を保持する圏の自然な射として持つ。
`rankTransferRetract` は任意の有理線形圏の射でこの分裂を証明する。
通常の関手圏の場合は `naturalTransferRetract` に特殊化する。
実際の導来図式の圏に二つの関手と比較自然変換があれば、
`naturalComparisonRetract` と `piComparison_of_transfer` が降下の retract を与える。
局所自明化後の rank 倍の恒等式もその図式上で書く。
Fubini・分裂降下・細分の法則は、対応する実際の homotopy limit に対して証明する。
全次数 π_* 同型という公開主張は現在の `PiDescent` のまま保つ。
K0・T2 の (3.6) 同定は別の明示的な引数として保持する。
E の実現でこの追加データを実際に供給する責任を残す。
界面の存在や導来降下の結論を新しい公理で埋めない。
固定点の π_* 比較も通常の不変部分の定義と分離する。

### 19.3 残る型と証明

L8a は次数付き前層とその導来値域への実現に対して八つの性質を記述する。
`PresheafRealization` は前層の実現データだけであり、八つの性質はまだ含まない。
L8b の数学的な証明経路は変わらない。
L8c の幾何補題の主張も変わらない。
L8d の K0・T2 依存を明示する方針も変わらない。
L8e の E の実現はこの持ち上げまで含めて検証する。
L9 の実装を編集したり、所有を移したりしない。
π_* の関手だけでは足りない導来図式の界面を、L9 との接続点として明示する。
現在の基礎モジュールはこの変更後もそのまま使用できる。

### 19.4 次の実装順序

L9 の Tot・hG の実構成は未着手で、現在の型は π_* の基礎が中心。
その実装を変更せず、L8 内で実際の比較図式とその法則の型を具体化する。
最小公理 (1)–(8) の定義を完成させる。
それから補題 3.2・3.3 と定理 3.1 の証明に進む。
独立な代数的基礎の実装を主定理の完成として数えない。

## 20. 最小公理と証明の未完部分

| 項目 | 証明・実装済みの範囲 | 残る責務 |
| --- | --- | --- |
| (1) Zariski Čech | 底変換後の実際の nerve の分裂・収縮 | Tot と比較、被覆での降下法則 |
| (2) 抽象 blowup | 幾何正方形、境界を持つ長完全列と三頂点比較、同変列の不変部分の完全性、自然な列から境界の同変性と固定比較 | 実際の降下からの列と境界の自然性の供給 |
| (3) 冪零不変性 | 冪零閉埋め込みの条件、点全射性、不変性の法則の型、Noether スキームの reduction の冪零性、全次数降下比較の被約化への還元 | 一般の thickening の底変換、E の不変性の検証 |
| (4) transfer | rank 公式から図式の retract、比較の全次数同型への移行 | 有限平坦な幾何射の transfer、底変換、射影公式、自明化による貼り合わせ |
| (5) 有理固定点 | 通常の不変部分の完全性・ホモロジー保存、指定対角比較、W と例外部分の実際の同変なコピー分解と指定前層比較、中心上の降下との積の固定比較 | L9 の実際の hG と π_* の比較、実降下からのコピーの有限積保存、導来 Shapiro への接続 |
| (6) 平坦化 | 原典と必要な型の調査 | Fitting 版の平坦化と細分の型・証明 |
| (7) スキーム補題 | 有限⇒固有、全射閉埋め込み⇒同型、切断・等化子、一致中心と次元低下、被約化、軌道正方形、係数拡大と閉中心への幾何入力の移行、閉和の同変比較、整成分の有限閉被覆と実際の交わりの次元低下 | 有限型スキームの有限次元上界、次元と有限被覆の個数による帰納を閉じる接続 |
| (8) (3.6) | 実現の自然同型を保持する型 | K0・T2 に対する台の比較と二重 fiber の同定 |
| L8b | 比較の retract、分裂 Čech、同変な全次数比較、(3.8) と中心の帰納仮定による軌道貼り合わせ、一般から被約への還元 | Fubini、細分、補題 3.2・3.3、実際の軌道正方形との接続、整→被約の帰納 |
| L8e | 接続先を分離した設計 | E の実構成による (1)–(6) の検証と界面への接続 |

これらは現在の未完部分であり、証明義務を削減した完成条件ではない。
有理不変部分のホモロジー保存を、スペクトルの hG の完成と取り違えない。
Čech nerve の extra degeneracy を、実際の Tot の全構成の完成と取り違えない。
対象ビルドと公理監査の成功だけでは、八つの公理や定理 3.1 の完成を認定しない。

## 21. 被約閉中心と reduction の適用範囲

任意の閉集合の消滅イデアル層から、実際の被約閉部分スキームを構成する。
その包含の像を元の閉集合と同定し、位相同型で次元を移す。
有限型対象内の構造射と包含も構成する。
これにより、一致場所の和の真閉性・次元低下が実際の中心 Z への帰納に使える。
元の有限個の等化子が非被約である場合、そのすべてが Z へ因子分解するとは主張しない。
必要な中心の台と、スキームとしての因子分解を区別する。

有限型対象の射と被約閉中心について、実際の引き戻しを有限型の圏内で構成する。
固有性と補集合上の同型を証明できれば `AbstractBlowupSquare` に包める。
この構成では例外部分が被約であることは仮定しない。
定理 3.1 の軌道射は有限個の切断の標準の非交和から構成した。
各切断の閉埋め込み性と二項非交和の有限性から、有限な添字の帰納で有限性を証明した。
コピーを置換する作用を構成し、section の族の同変性から軌道射の同変性を証明した。
被約な始域の場合は、終域の reduction への持ち上げ後にも有限性と同変性が成り立つ。
section の像が全体を覆うことを入力すれば全射性も得る。
有限型の圏内の軌道射と中心の引き戻しによる抽象 blowup は構成した。
幾何的推移性からの被覆条件は、切断を持つ有限型アフィン対象に対して §28 で接続した。
任意の係数拡大と、アフィン基底を固定した始域の被約化後の被覆は §29 で接続した。
実際の閉中心への幾何的入力は §30 で直接構成した。
中心上の降下の帰納仮定そのものの証明は残る。

補集合上の同型のため、被約な終域の互いに素な有限閉被覆の非交和同型を証明した。
各閉像は残りの有限閉像の和の補集合でもあるため開。
閉埋め込みをその開像へ持ち上げ、被約な終域への全射閉埋め込みの同型性を使う。
有限閉被覆の非交和からの開埋め込みは全射なので同型となる。
さらに、二つの切断の像が同じ点を含むと、その二つの原像点を実際のスキームの
引き戻しへ持ち上げ、切断の恒等式で二射影を等しくし、一致場所へ写す。
この議論で、中心を避ける開集合上の切断の像の互いに素を証明した。
像の被覆も明示すれば、制限切断の非交和からの射が同型になる。
有限非交和の universal colimit 性を成分ごとの開制限の引き戻し正方形に適用した。
これにより、制限の非交和と非交和射の制限の二つを同じ引き戻しの表示として比較した。
標準同型と指定射の可換式により、軌道射自体の制限の同型性も得た。
この過程に前層の降下を仮定していない。
`orbitAbstractBlowup` は中心 V ×_B Z を引き戻しの構造のまま保持する。
中心を V 上でさらに被約化していないため、原典の軌道正方形の幾何に対応する。

一般のスキームの reduction について、被約な始域からの一意な持ち上げを証明した。
その普遍性から関手と包含の自然性、自己同型群を通した G 作用を構成した。
これらの普遍性にはアフィン性も Noether 性も不要。
核の冪零性は Noether スキーム全体で証明した。
有限アフィン部分被覆上の指数の最大値を取り、イデアル層の零を被覆上で判定する。
さらに、有限型の圏内の reduction 関手とその G 作用・包含の同変性を構成した。
Noether 基底上有限型なら各対象が Noether であることを使い、両包含に公理 (3) を適用した。
同変な全単射の不変部分への制限も全単射であることと、指定比較の可換性から、
`Nilinvariant.piDescent_iff_reduction` が「一般 → 被約」の全次数還元を与える。
これは任意の群について成立し、有限群の平均作用素に頼らない。
一般の thickening の底変換、被約な場合の主定理の証明、E の冪零不変性は残る。

## 22. 実際の同変軌道正方形と境界の責務

有限型の圏内の軌道射の始域 W に、コピーの添字を置換する G 作用を構成した。
section の族の同変性から W の構造射が保存され、基底上の自己同型となることを確認する。
中心 V ×_B Z には V の作用と B・Z の自明作用から誘導される作用を構成した。
例外部分 W ×_V (V ×_B Z) には、三頂点の作用を含む cospan の引き戻し作用を用いる。
逆元による逆写像と群の法則、両射影の同変性を普遍性で証明した。
`orbitAbstractBlowupAction` が四頂点と四辺を保持する。

任意の前層 L の逆元の引き戻し表現を適用すると、指定された制限とその差が同変となる。
これは四辺の可換式と反変関手の合成保存から証明した。
`SquareMayerVietoris.withSquareAction` は、境界が同変であることを入力すれば、
既存の `GradedMayerVietoris.Action` に接続する。
その後は有限群の有理不変部分を取った全次数の完全列が利用できる。
境界の同変性は、公理 (2) の実降下から得る長完全列の自然性で供給すべき責務である。
幾何の射の同変性だけで境界も同変だと仮定せず、この入力を明示的に残す。

## 23. 境界の自然性と実際の軌道比較から PiDescent への接続

`NaturalBlowupSequences` は、各抽象 blowup の指定された長完全列と、幾何正方形の
射全体に対する境界の自然性を保持する。
このデータの存在は、L9 の実際の fiber・長完全列と、公理 (2) の実降下から供給する。
群ごとの列の存在をホモトピー引き戻し性の定義へ置き換えたものではない。
群元の逆元が定める正方形の自己射に自然性を適用し、境界の同変性を導いた。
有限群の有理不変部分を取ることで、全次数の完全列とその自然な比較が得られる。

軌道正方形の右下の射 V → B と、中心の第二射影 V ×_B Z → Z から、
基底の恒等中心正方形への実際の立方体を構成した。
上の二頂点の射は正方形の辺との合成で指定し、四つの面の可換性を証明した。
さらに、この立方体の四頂点の射が同変であることを示した。
恒等中心正方形の境界は、指定された差の全射性と完全性から零となる。

`orbit_piDescent_of_fixed_components` は、実際の比較の中項と例外部分の不変部分の
同型性を全次数で供給すれば、公開する `L.PiDescent p action over_base` を結論する。
基底の自明作用の不変部分を元の L(B) と同定し、終域の不変部分の二つの記述を
移す際、比較の値が元の幾何射 p の引き戻しそのものであることも確認した。
中項の比較は、コピーの有限積保存と (3.8)、中心上の降下から供給できるようになった。
例外部分の比較も実際の同変コピー分解から供給できるようになった。
中心上の降下を次元帰納から供給する作業は残る。
この条件付きの軌道段階を、最小公理からの定理 3.1 全体の証明とは数えない。

## 24. 実際のコピー評価と (3.8) の中項比較

`orbitComponent` は W = ⊔_I B の各包含を有限型の圏内に構成する。
軌道射との合成が指定 section、fold との合成が恒等射、作用との合成が添字の置換である。
`orbitSourceIsCoproduct` は、スキームの非交和の desc を基底上の射へ持ち上げ、
その存在と一意性を有限型の圏内で証明する。
コピーを並べた対象だけを非交和と呼び、普遍性を仮定して済ませてはいない。

前層の `copyEvaluation` は、各包含による実際の引き戻しを並べた指定線形写像。
これは逆元の添字置換への同変写像で、fold の固定比較との合成が指定対角写像となる。
この錐が積なら、有理数の自由加群からの射の普遍性で評価の全単射性を証明できる。
ULift ℚ を使い、コピーの添字の宇宙と前層の値の宇宙を無理に同一視していない。
反対圏のコピーの有限積を前層の各次数が保存すれば、この錐が積となる。
ここでの通常の積は有限非交和の値に限り、Čech Tot の代用ではない。
この有限積保存を実際の Zariski 降下から導く責務は残る。

推移的で非空なコピーの置換作用に対し、fold の全次数の指定比較は (3.8) から全単射。
これと中心 V ×_B Z → Z の降下を、幾何的な自明作用の不変部分の比較に移す。
積の不変部分の具体的な同型を通し、実際の比較立方体の中項が全単射となる。
従って中項全体の同型性を追加仮定にする必要はなくなった。
例外部分 W ×_V (V ×_B Z) のコピー分解と、その作用・指定射との両立も証明した（§25）。

## 25. 例外部分のコピーと実際の軌道段階

閉中心の引き戻しに対し、有限型の圏内の持ち上げと両射影の公式を構成した。
またスキームの cofan が非交和なら、有限型の圏内の cofan も非交和となることを、
Over の忘却と充満部分圏の余極限の反映を通じて証明した。

例外正方形と中心の正方形を合成し、E = W ×_V (V ×_B Z) が W ×_B Z の
普遍性も持つことを、スキームの圏と有限型の圏内の両方で証明した。
Z → B → W と Z の恒等射を持ち上げ、各 Z のコピーの E への指定包含を構成した。
スキームの有限非交和の底変換を適用し、これらの包含が非交和の普遍性を持つことを示した。
E と中心の非被約な構造を変更していない。

例外部分の既存の引き戻し作用は、これらの包含を g 倍の添字の包含へ写す。
E → Z は不変で、各コピー上では恒等射となる。
従って Z のコピーの有限積を前層の各次数が保存すれば、(3.8) が実際の E → Z に適用できる。
この指定比較を実際の固定部分の列の例外部分の写像へ移し、その全単射性を証明した。

`orbit_piDescent_of_center` は、中項・例外部分の同型性を個別の仮定に持たず、
自然な blowup 列、B と Z の二つのコピーの積保存、中心上の降下から全次数の降下を結論する。
`Theorem31.lean` もこの実際の軌道段階を公開する。
実降下からの自然な列と有限積保存の構成、一般の基底変更後の切断の被覆を得ること、
有限忠実平坦の Čech 還元と真閉中心上への次元帰納は引き続き未完。

## 26. 閉中心の冪零不変性と被約な始域への移行

Noether な終域への点全射な閉埋め込みの核は、台の判定から nilradical に含まれる。
大域的な nilradical の冪零指数を核へ移し、この射が冪零 thickening であることを証明した。
閉埋め込みと点全射性の底変換安定性を使い、Noether な対象への底変換の第一射影も
冪零 thickening となる。終域の Noether 性のない一般の底変換安定性は主張していない。

有限型の圏内で実際の閉埋め込みの引き戻しを用い、公理 (3) を第一射影と基底の包含へ適用した。
基底と閉部分の自明作用から引き戻し作用を構成し、指定された PiDescent が
冪零な基底変更の前後で同値であることを、任意の係数と整数次数について証明した。
この比較には群の有限性は不要である。

中心の帰納では基底 Z を固定する必要があるため、別に始域だけの被約化の比較を構成した。
始域の Noether 性から被約化の包含に公理 (3) を適用し、基底の恒等射との同変正方形で比較する。
`orbit_piDescent_of_reduced_center` はこの比較を実際の中心 V ×_B Z → Z に適用する。
被約化した始域から同じ Z への降下があれば、構成済みの軌道段階へ入力できる。
正方形そのものの中心を被約化して Cartesian 性を壊す操作はしていない。
被約化した中心の射に対する帰納仮定を、幾何的推移性と次元低下から供給する責務は残る。

## 27. 相異なる移動切断の有限推移的な添字

`TranslatedSectionIndex action s` は、実際の射 s ≫ g の集合の部分型である。
群元をそのまま添字にして切断の重複を許す方式では、一致中心の真閉性を使えない。
この部分型への作用を後合成から構成し、群の積の向きを自己同型の合成と合わせた。
有限性・非空性・推移性を証明し、射の族の単射性も Over の射として証明した。
安定化群による商との同型は使わず、軌道の部分型を直接用いる証明経路である。

元の射 p が作用の基底上にあり s が切断なら、族の全ての射が p の切断である。
有限群、既約被約な基底、分離な終域の構造射、明示した有限次元上界のもとで、
この族の一致中心が次元の下がる実際の被約閉中心となる。

`translatedSection_covering` は、基礎点の各ファイバーの推移性を入力すると、
各点 y と s(p(y)) を結ぶ群元から、重複を除いた切断族の像の被覆を結論する。
この入力は基礎点の性質であり、既存の `IsGeometricallyTransitive` の定義そのものではない。
環のテンソル積上の幾何ファイバーからこの入力を導くことは §28 で実装した。
係数拡大による幾何的推移性の保存と始域の被約化後の被覆は §29 で実装した。
一般の閉中心に対する帰納仮定の構成は残る。

## 28. 既存の幾何的推移性からアフィンの移動切断の被覆へ

`exists_common_geometric_points` は同じ基底点の上にある二点を引き戻しの点へ持ち上げ、
その剰余体の代数閉包を使い、共通の代数閉体からの二つの射として表示する。
両射の基底への合成はスキームの射として等しく、選んだ一点の像は元の二点である。

アフィンの場合、Spec の充満忠実性によりこの二つの射を T から体 Ω への環準同型へ移す。
基底への合成の等式から同じ A 代数構造を使えることを確認し、テンソル積からの射に拡張する。
既存の `IsGeometricallyTransitive A T G` をこの二つの素イデアルへ適用し、
左因子への射影から、同じ基底点上の元の二つの素イデアルを群元で結ぶ。
新たな推移性の公理や、代数閉体の選択を仮説に追加していない。

Spec の反変性に合わせて g の作用を g⁻¹ の環作用の comap とし、左群作用を構成した。
その作用が Spec A 上にあることを代数射の係数の保存から証明する。
有限型 A 代数を前層の定義域内の有限型アフィン対象とし、この作用を持ち上げた。
`affine_translatedSection_covering` は、既存の幾何的推移性と実際の切断から、
重複を除いた移動切断の像が全体を覆うことを結論する。
基底変更後と始域の被約化後の被覆へは §29 で接続した。
有限忠実平坦な Čech 還元による切断の存在、一般の閉中心への帰納の適用、
主定理全体の証明は未完である。

## 29. 係数拡大と始域の被約化後の被覆

B ⊗_A T では B を固定し T を動かす群作用を実際のテンソル積の map から構成した。
作用の法則と B 線形性を証明し、標準の B 代数構造を保持した。
幾何ファイバー (B ⊗_A T) ⊗_B Ω と T ⊗_A Ω の A 代数同型を、
因子の交換と係数拡大の打ち消しから構成し、その指定同型が群作用と可換であることを証明した。
この同型の素イデアル上の写像を使い、既存の `IsGeometricallyTransitive` が
任意の A 代数 B への係数拡大で保存されることを証明した。
B の平坦性、有限型性、Noether 性はこの保存に不要である。

有限型 A 代数 T に対しては、変更後の B 代数も有限型となる既存定理を使う。
従って変更後に切断があれば、実際の有限型アフィン対象の移動切断で全体を覆える。
ここまででは係数拡大前の切断から変更後の切断を構成する Čech 還元は扱っていない。

別に、基底を固定した始域の被約化は、同変な包含の点の単射性から
基礎点の各ファイバーの推移性を保つことを証明した。この点の比較に Noether 性は不要。
被約な始域からの射の reduction への持ち上げを有限型の圏内にも構成し、包含との合成公式を証明した。
基底が被約なら元の切断は始域の被約化へ持ち上がり、同じ基底上の切断となる。
`affine_baseChange_liftedSection_covering` は、元の切断から構成したこの切断の移動が
被約化した始域全体を覆うことを、既存の幾何的推移性から結論する。
実際の閉中心への幾何的入力は §30 の直接的な経路でも供給した。
次元帰納を閉じる責務は残る。

## 30. 実際の閉中心への直接移行と閉和の正方形

閉埋め込みの底変換である第一射影は、基礎点上で単射である。
従って元の射の点のファイバーを結ぶ群元を選び、第一射影の同変性と単射性を使うと、
閉中心への実際の引き戻しの点のファイバーの推移性を直接証明できる。
中心のアフィン表示やテンソル積との別の同型を構成する必要は、この幾何的入力にはない。
これは閉底変換の点の推移性に関する証明経路であり、一般の基底変更の幾何的推移性を
単なる基礎点の推移性で置き換える主張ではない。

元の切断は、中心の包含との合成と中心の恒等射を引き戻しへ持ち上げることで、
中心上の実際の切断となる。第二射影との合成の恒等式も証明した。
中心が被約ならこの切断を引き戻しの始域の被約化へ持ち上げ、
構成済みの作用の移動による被覆を得る。
これらを一致中心の包含へ適用し、`orbitCenterAction`、実際の第二射影、
`orbitCenterSection` に対して直接証明した。中心の非被約な構造は変更していない。

また被約な終域を二つの閉部分が覆うとき、一方の閉部分の補集合では他方の閉埋め込みが
点全射となる。その開集合の被約性から制限は同型であり、閉埋め込みの固有性と合わせて
`closedCoverAbstractBlowup` を構成した。交わりは元の二つの閉埋め込みの実際の引き戻し。
`NaturalBlowupSequences.closedCoverSequence` は、この正方形へ指定データを適用し、
境界と三箇所の完全性を持つ全整数次数の列を供給する。
閉和の同変な比較と、三つの局所降下からの貼り合わせは §31 で実装した。
実降下から自然な列のデータを供給する責務、および次元帰納は残る。

## 31. 閉和の同変な比較と指定降下の貼り合わせ

二つの閉部分 Y・Z が基底 B を覆うとき、任意の射 f : V → B への引き戻しの
第一射影の像は元の像の逆像である。この公式から、始域 V も二つの実際の閉部分で覆われる。
V が被約なら、この引き戻した閉被覆も抽象 blowup 正方形を与える。
元の被覆の正方形への比較では、三頂点の射は f と二つの第二射影で指定する。
残る交わりの射は引き戻しの普遍性で構成し、四つの面の可換性を証明した。

f が基底上の群作用を持つとき、引き戻した二つの閉部分と交わりに既存の引き戻し作用を入れる。
元の閉被覆の四頂点には自明に作用する。二つの第二射影と f の不変性から、
交わりへの射の不変性も比較先の引き戻しの普遍性で導く。
四つの比較の同変性を入力仮定として追加してはいない。

自然な blowup 列のデータにこの同変な立方体を適用し、有理不変部分を取ることで、
境界も含む全整数次数の列の比較を得る。
`closedCover_piDescent` は、二つの第二射影と交わりへの指定射の三つの PiDescent を入力し、
中項を二つの局所比較の積、交わりを三つ目の比較として五項補題を適用する。
最後に自明作用の不変部分と指定比較の同定を通じ、元の幾何射 f の PiDescent を結論する。
元の射の降下や無関係な中項全体の同型性を追加仮定にはしていない。

基底 B と始域 V の被約性は閉被覆の抽象 blowup を作るために明示する。
二つの部分と交わりは非被約でもよく、必要なら構成済みの reduction の比較を適用する。
有限な既約成分分解と次元低下を組み合わせて三つの局所降下を供給すること、
実降下から自然な列を構成すること、Čech 還元と主定理全体の証明は残る。

## 32. 整成分の有限閉被覆と二つの帰納の幾何データ

`IrreducibleComponentIndex` は基礎空間の既約成分の部分型である。
各成分に消滅イデアル層による被約閉構造を入れ、台との同相から既約性を移すことで、
同じ基底 S 上の整な有限型対象 `integralComponent` を構成した。
Noether 空間では添字は有限であり、各成分の閉包含の像が元の対象全体を覆う。
元の対象の被約性はこの構成そのものには不要である。

一つの成分 c を選び、他の全成分の有限和を `componentRemainder` とする。
既約な閉集合が有限和に含まれるとき一つの項に含まれることと、成分の極大性から、
c は残りに含まれない。従って残りは真閉で、元の対象が既約でない場合には c の像も真閉である。
この二つの部分は全体を覆い、被約な元の対象に対する実際の抽象 blowup 正方形を与える。

実際の交わりを c へ送る第一射影は閉埋め込みで、その像は真閉である。
閉像との同相により、交わりが非被約のままでも次元低下を証明した。
元の対象の次元が自然数 d 以下なら、各整成分の次元も d 以下で、交わりの次元は d 未満となる。
空の交わりの次元を零へ丸めてはいない。

残りには被約閉構造を入れる。閉集合の包含が与えるイデアル層の包含を使い、
各 d ≠ c の整成分から残りへの実際の射 `componentToRemainder` を構成した。
元の対象への合成が成分の閉包含であることから、この射も閉埋め込みである。
これらの像が残り全体を覆うことを、元の対象への包含の点の単射性で証明した。
残りを覆う元の成分の集合は有限で、その個数は一つ減る。
これは新しいスキームの既約成分との同一視を仮定することなく、有限被覆の個数を使う帰納へ入力できる。

これらの幾何データを閉和の三つの局所降下へ供給して、
次元と有限被覆の個数による帰納を閉じる工程は残る。
自然な blowup 列と有限積保存を実降下から構成する工程、Čech 還元、(3.6) の接続も未完である。

## 33. 交わりの帰納入力と被約化・空の基底

`fiberTransitivity_of_injective_square` は、同変な可換正方形で始域側の射が点上単射なら、
元の射の点のファイバーの推移性を新しい射へ移す。
基底側の射が単射または全射であることは要求しない。
被約化の包含の正方形に適用し、始域と基底の両方を被約化した射でも点の推移性が保たれることを証明した。
元の切断の恒等式には被約化関手を適用でき、被約化した射の切断を得る。
被約化の次元保存も、台との同相から有限次元や Noether 性を使わずに証明した。

閉和の交わりへの指定比較の切断は、二つの閉部分上の切断を交わりへ持ち上げて構成する。
比較先の二つの射影で検査し、指定比較との合成が恒等射であることを、有限型の圏内の等式として証明した。
推移性は、左側の閉部分上の点の推移性と、交わりからの第一射影の同変性・点の単射性から移す。
これらは比較立方体の指定射そのものについての証明であり、別の同型なモデルへ変更していない。

`closedCoverIntersection_reduced_covering` は、構成した切断と点の推移性を両側の被約化へ移し、
その切断の移動による実際の像の被覆を得る。
従って非被約な交わり上の局所降下を被約な場合の帰納へ戻す際、
切断・推移性・次元の幾何条件を追加仮定にする必要がない。
PiDescent 自体の被約化との同値には、既存の公理 (3) と Noether 性に関する定理を適用する。

また、指定引き戻しが全次数で全単射なら不変部分への値域制限も全単射となることを証明した。
同型射の場合は前層の同型保存からこれを適用できる。
空の基底へのスキームの射は同型であり、有限型の圏への忘却が同型を反映することから、
元の有限型の圏内の射も同型である。これにより空の基底の PiDescent を得る。
空対象での前層の値を零とする公理や有限積保存は、この始点には使っていない。
有限閉被覆と次元の帰納を閉じる工程、および実降下・Čech 還元・(3.6) の接続は残る。

## 34. 整な基底の段階を低次元から閉じる

`SectionedDescentBelow L G d` は、基底次元が自然数 d 未満である切断を持つ射に対する
指定 PiDescent の帰納仮定を量化する。始域は S 上分離な有限型対象で、
指定作用・基底上の不変性・切断・点のファイバーの推移性を保持する。
これは最小公理の一つでも追加公理でもなく、厳密に低い次元だけに適用する帰納仮定の型である。

整な基底 B、被約な始域 V、元の切断 s に対し、相異なる移動切断の添字を実際に選ぶ。
族の単射性・有限性・推移性・像の被覆を構成済みの証明から供給する。
一致中心 Z の実際の被約閉構造は B より次元が低い。
V ×_B Z の指定作用と射影には元の切断から切断と点の推移性を供給し、
その始域が S 上分離であることも閉埋め込みの合成から確認する。
従って低次元の帰納仮定を中心の射に適用でき、中心上の PiDescent を得る。
既存の実際の軌道段階へこれを入力して、V → B の全次数 PiDescent を結論する。
中心上の降下を、低次元とは独立した入力仮定に残してはいない。

この段階で使う有限積保存は、前層の各次数の有限非交和に対する実降下から供給すべき条件である。
通常の有限積を Čech Tot の代用品として使ってはいない。
自然な blowup 列も、実際の降下と L9 の長完全列から供給すべき条件として明示する。

Noether な S と公理 (3) があれば、始域 V が被約でない場合も扱える。
整な B は被約なので s を V_red へ持ち上げ、始域だけを被約化した射に被約な場合を適用する。
包含の同変性による点の推移性の移行、切断の合成公式、始域の分離性を実際に確認し、
公理 (3) の指定比較で元の V → B へ戻す。

`sectionedDescentBelow_zero` は、零より低い次元の仮定が空の基底の場合だけであることを使う。
点が存在すればその一点の閉包が既約閉集合となり、Krull 次元は非負となる。
したがって空の基底の指定降下から、この帰納の始点を供給できる。
被約で可約な基底の有限閉和を組み合わせる成分数と次元の帰納は §35 で完了した。
実降下からの条件の供給、Čech 還元、(3.6) と E への接続も未完である。

## 35. 成分数と次元の二つの帰納の完了（切断を持つ場合）

有限な既約閉被覆の各既約成分は、被覆の一項に含まれ、極大性によりその項と等しい。
この項を各成分について選ぶと、成分の添字から被覆の添字への単射が得られる。
これにより既約成分数は有限被覆の項数以下であることを、空の場合も含めて証明した。
残りの閉和に他の元の整成分による被覆を適用し、残り自身の既約成分数が元より少ないことを証明した。
新旧の既約成分を同一視する仮定は使っていない。

被約な基底と被約な始域について、一つの整成分・残り・交わりの三つの局所降下を供給する。
整成分には §34 の整な段階、残りには厳密に少ない成分数の仮定、
交わりには厳密に低い次元の仮定を適用する。
引き戻した始域と交わりの S 上の分離性も、閉包含の合成から確認した。
構成済みの閉和の貼り合わせに三つを入力して元の射の指定降下を得る。
始域の被約性は、被約な基底からの切断の持ち上げと冪零不変性で外す。

`reducedBase_piDescent_of_below` は実際に成分数の強い自然数帰納を実行する。
残り自身の成分数の減少を使うので、成分数に関する仮定は結論に残らない。
さらに始域と基底を同時に被約化して、切断・点の推移性・次元を保ちながら被約な場合へ戻す。
公理 (3) の指定比較で元に戻すと、一般の基底に対する `piDescent_of_below` を得る。

`sectionedDescentBelow` は外側の次元上界に関する自然数帰納を実行する。
零の始点は空の基底から得る。次の段階では、次元が d + 1 未満なら d 以下であることを使い、
直前までに構成した低次元の仮定を一般の基底の一段へ適用する。
従って全ての自然数 d に対する帰納仮定が実際に構成される。

`sectioned_piDescent` の結論は、指定された切断を持つ射の全係数・全整数次数の PiDescent。
中心上・閉部分上・交わり上の降下、低次元の帰納仮定、成分数の帰納仮定を外部入力には残さない。
数学的入力は Noether な S、S 上分離な始域、有限な群、基底上の指定作用、
切断、点の各ファイバーの推移性、明示した有限な基底次元上界である。
前層に関する入力は、自然な blowup 列のデータ・各次数の有限積保存・冪零不変性。
自然な列と有限積保存を実際の降下から供給すること、切断を持たない射への Čech 還元、
最小公理 (1)–(8) 全体、(3.6) と K0・T2・E の接続は未完である。
この条件付きの切断を持つ段階の完成を、定理 3.1 全体の完成とは呼ばない。

## 36. 環の分裂とアフィン底変換の全次数降下

`affineOverObject` と `affineAlgebraOverObject` は、任意の固定した S 上で
Spec A と Spec T を有限型の圏の対象にする。構造射を保持したまま、
指定射影と元の環の群作用も同じ圏内に構成する。
A 代数射 r : T → A の係数保存から Spec r が実際の切断となることを証明した。
`affine_split_piDescent` はこの切断と元の幾何的推移性を使い、§35 の完成した帰納を適用する。
前層を別の基底上の任意の前層に交換する操作はしていない。

A 代数射 φ : T → B があれば、テンソル積の普遍性により
`tensorBaseChangeRetraction φ : B ⊗_A T →ₐ[B] B` を実際に構成できる。
純テンソル b ⊗ t の像は b · φ(t) である。
既存の係数拡大の推移性と組み合わせ、Spec B が同じ S 上の有限型かつ分離な対象で、
その次元に明示した有限上界があれば、Spec(B ⊗_A T) → Spec B の指定された
全係数・全整数次数の PiDescent を元の L に対して証明した。
自己底変換では φ を T の恒等射とし、乗法による分裂から同じ結論を得る。
左因子 B または T は固定し、右因子だけに元の群作用を適用する。

`tensorSpecSquare_isPullback` は Mathlib の `pullbackSpecIso` の二射影の公式を使い、
指定された係数射影と右射影が実際のスキームの Cartesian 正方形を成すことを証明する。
右射影は元の Spec T の作用と同変であり、左射影は Spec B 上の作用である。
単なる対象同型の存在だけを使って引き戻しであると称してはいない。

ここで完成したのは、分裂を持つ底変換の全次数降下と、その幾何的な正方形である。
有限型の圏内の Čech 各段との関手的な比較、Tot と引き戻しの Fubini、
分裂余単体対象の実降下、細分補題、および元の切断を持たない射への還元は残る。
自然な blowup 列・有限積保存を実降下から供給する工程と、有限次元上界の接続も残る。
最小公理 (1)–(8) 全体、(3.6)、K0・T2・E の接続も未完であり、
本段階を論文 補題 3.2 または定理 3.1 全体の完成とは呼ばない。

## 37. 前層の定義域内の同変な底変換正方形

`affineTensorObject` は Spec(B ⊗_A T) を、左因子 B を通る構造射で同じ S 上の
有限型対象にする。`affineTensorFst` と `affineTensorSnd` はそれぞれ実際の
係数射影と右因子への射影をこの圏内に持ち上げた射である。
右射影の構造射との可換性は §36 の Spec の正方形から導出する。
Over の忘却と充満部分圏の包含は極限を反映するので、
指定された四辺がこの有限型の圏内でも引き戻しを成すことを証明した。
従って、単にスキームとして同型な対象へ前層を勝手に適用しているのではない。

`affineTensorAction` は左因子を固定した右因子上の既存の作用を持ち上げる。
第一射影の基底上の不変性と、第二射影の元の作用との同変性をこの圏内の等式で証明した。
指定された A 代数射 T → B から `affineTensorSection` を構成し、
第一射影との合成が恒等射であることもこの圏内で証明した。
有限型対象に保存済みの局所有限型性と準コンパクト性の証明は、
反復するアフィン底変換の構成に明示的に渡している。

`affineTensorFst_piDescent` は、指定されたこの第一射影そのものについて、
元の L の全係数・全整数次数の降下を結論する。
基底の明示した有限次元上界、Noether な S と分離な構造射、
有限な群、幾何的推移性、自然な blowup 列・有限積保存・冪零不変性が入力である。
Čech 各段の関手的な比較、分裂余単体対象の実降下、Fubini・細分による
元の切断を持たない射への還元は引き続き未完である。

## 38. 有限型の圏内の実際の二重 Čech 図式

有限型対象間の射は局所有限型である。これは基底への合成の局所有限型性から導き、
Noether 性を必要としない。Noether 基底上では有限型対象の underlying scheme は Noether であり、
その始域を持つ全てのスキームの射は準コンパクトとなる。
従って任意の二射の実際の引き戻しも同じ基底上の有限型対象として構成できる。
第一・第二射影を Over の射に持ち上げ、スキームへの忘却による極限の反映から
有限型の圏内での引き戻しの普遍性を証明した。
基底自身の恒等構造射はこの圏の終対象である。
終対象と全ての引き戻しから `finiteTypeSchemes_hasFiniteLimits` を得る。

この有限極限により、`finiteTypeAugmentedCech` は元の前層の定義域内の
実際の増強 Čech nerve となる。各非増強段には零番目の射影から X への射がある。
増強の成分で元の f を底変換し、この零番目の射影を持ち上げに使うと、
`finiteTypeCechStageSplitEpi` の実際の切断を構成できる。
この切断を使い、各行の Čech nerve の全次数の extra degeneracy を構成した。
同じ反変前層を適用した像にも extra degeneracy と全ての分裂の恒等式が移る。

`finiteTypeCechBaseChange` は各段の底変換の Arrow を、全ての単体射に対する
引き戻しの map で束ねた実際の関手である。
恒等射と合成の保存は二射影と元の Čech の関手性を用いて検査した。
増強 Čech nerve 関手を合成して `finiteTypeDoubleCech` を構成し、
さらに元の前層を適用して二重図式全体の像を構成した。
零番目の射影を選ぶ切断の外側の単体射についての自然性は主張していない。
二重図式の射の構成に切断の自然性は使っていない。

ここで作った極限は幾何的な通常の極限であり、前層の値域の Tot の代用ではない。
各段での作用・推移性・分離性・有限次元上界を既存の切断つき全次数降下へ渡す工程、
実際の Tot の分裂降下・Fubini・細分による元の射への還元は残る。
自然な blowup 列・有限積保存の導出と、最小公理全体・(3.6)・E の実現も残る。

## 39. 指定引き戻しへの同変な移行と Čech 比較の自然性

`isPullback_isoPullback_equivariant` は任意の圏で、四頂点の指定作用と
二射影の同変性から、Cartesian モデルと指定引き戻しの標準同型の同変性を証明する。
比較先の作用を共役で新しく定義する方法は使っていない。
比較先は既存の `pullbackAction` であり、同変性を二射影で実際に検査する。

アフィン底変換に適用すると、テンソル積モデルの作用と指定引き戻しの作用を
`affineTensorPullbackIso_equivariant` で結べる。
指定第一射影への比較は元の L を適用した同変正方形を成す。
標準同型の引き戻しの全単射性と不変部分の比較の自然性により、
モデルの PiDescent を実際の引き戻しの第一射影へ移した。
`affine_pullback_piDescent` は指定された作用と幾何射の全係数・全整数次数の主張である。
環の射 T → B による分裂、明示した次元上界、有限型性・分離性・Noether 性、
有限な群と幾何的推移性、自然な blowup 列・有限積保存・冪零不変性を入力する。

`finiteTypeCechStageAction` は実際の Čech 各段で底変換した元の始域に作用する。
Čech の基底の段自身は固定する。これは Čech の全座標への対角作用とは異なる。
第二射影はこの作用について基底上にある。
`pullbackAction_map_trivialBase` は基底変更の射と元の始域の作用の可換性を、
二つの pullback.map の合成公式から証明する一般補題である。
これを適用して、全ての外側の単体射について段間の射の同変性を証明した。
切断を選ぶ零番目の射影が外側の射について自然であることは使わない。

この同変性を指定比較の一般の自然性へ渡し、元の L の全係数・全整数次数について
`finiteTypeCechStageComparison_naturality` を得る。
各段の比較の左辺・右辺はいずれも元の前層の幾何射からの引き戻しであり、
無関係な群の抽象同型に置き換えてはいない。

一般の実際の Čech 各段に対する幾何的推移性の移行、分離性と有限次元上界の供給は残る。
通常の点のファイバーの推移性だけを任意の底変換で保存すると仮定してはいない。
実際の Tot の分裂降下・Fubini・細分、実降下からの自然な列と有限積保存、
最小公理全体、(3.6)、K0・T2・E の接続も引き続き未完である。

## 40. 実際の Čech 各段のアフィン性・分離性・有限次元

`finiteTypeOverInclusion` は同じ S 上の有限型の圏から Over S への包含である。
構成済みの引き戻しモデルは両圏で Cartesian であり、基底の恒等構造射による
終対象も保たれる。従ってこの包含は有限極限を保つ。
Over からスキームへの忘却は連結極限を保つので、合成により
`finiteTypeSchemesForget_preservesFiniteConnectedLimits` を得る。
スキームへの忘却は終対象を保つとは主張しない。

`finiteTypeLimit_isAffine` は、元の有限型の圏で指定した有限連結な極限錐を
スキームの極限錐に写し、Mathlib のアフィン対象の極限の定理を適用する。
Čech の有限 wide pullback では図式の全頂点が元の始域または基底である。
両者がアフィンなら、実際の各非増強段もアフィンとなる。
各段への底変換の始域についても、三頂点の cospan に同じ議論を適用する。
アフィンなスキームは絶対分離的なので、底変換の始域の S への構造射も分離的である。
S 自身の分離性は入力していない。

Noether 環 A に自然数の次元上界 d があるとする。
有限型 A 代数 T を有限変数多項式環の商として表示し、全射による次元の不増大と
dim A[X₁,…,Xₙ] = dim A + n を使って、Spec T の自然数上界を実際に供給した。
A が局所 Noether の場合、Krull の高さ定理から極大イデアルの最小生成元数が上界となる。
一般の Noether 環の有限次元性を主張していない。

実際のアフィンスキーム X の有限型射 X → Spec A については、
isoSpec の逆射と構造射の合成の Spec.preimage により Γ(X,⊤) に A 代数構造を入れる。
この射の局所有限型性から座標環の有限型性を証明し、上記の環論的な上界を適用する。
isoSpec の同相による次元の等式で、指定された X 自身の上界へ戻す。
従って座標環の有限型性や始域の有限次元性は追加仮定に残らない。

`localNoether_finiteTypeCechStage_dimension_bound` は、局所 Noether な A の Spec を基底とする
実際の Čech 各段へこれを適用する。
増強射の局所有限型性は、同じ S 上の有限型対象間の射であることから導く。
各段の有限次元上界を結論として供給するので、後の次元帰納へそのまま渡せる。

幾何的推移性を実際の各段の底変換へ移す工程は残る。
これを供給して完成した切断つき降下を各段へ適用し、さらに Tot の実降下・Fubini・細分で
元の射へ戻す必要がある。最小公理全体・(3.6)・K0・T2・E の接続も未完である。

## 41. 幾何的推移性の実際の Čech 各段への供給と全次数降下

同変な始域・基底の同型の正方形で、点のファイバーの推移性を移せることを証明した。
逆同型で二点を戻し、基底同型の点の単射性で同じファイバーにあることを検査する。
始域だけが点上単射の正方形による移行も、underlying scheme に対して証明した。
これらは通常の点の推移性の任意の底変換での保存を仮定する補題ではない。

元の環 A → T の幾何的推移性を、任意の A 代数 B へ係数拡大する。
既存の環論的な係数拡大の定理により、B ⊗_A T の Spec B 上で点のファイバーは推移的になる。
基底 Z に Spec B からの構造射を保つ同型があれば、テンソル積の二射影の
Cartesian 正方形を Z 上へ移せる。
モデルの両射影の同変性から指定引き戻しへの標準同型も同変となり、
実際の pullbackAction の点の推移性を得る。

アフィンな Z → Spec A では、Γ(Z,⊤) に構造射から A 代数構造を入れ、
isoSpec の逆を使って上記の表示を実際に供給する。
従って座標環の表示や底変換後の推移性を追加仮定に残さず、
任意のアフィン基底変更の点の推移性を元の幾何的推移性から証明できた。
この段階には有限型性・Noether 性・群の有限性は不要である。

有限型の圏の指定引き戻しの Cartesian 性を、忘却の極限保存でスキームへ移す。
有限型の圏の pullbackAction の二射影の同変性も忘却し、
underlying scheme の指定引き戻しへの標準同型との同変性を検査した。
この同型の点の単射性で推移性を元の有限型対象へ反映する。
従って作用を別の共役作用へ置き換えることなく、元の圏の指定作用を保持できる。

実際の Čech 各非増強段は §40 でアフィンと証明済みであり、
この任意のアフィン基底変更の推移性を各段の指定射へ適用できる。
`affineCechStage_transitive` は、元の幾何的推移性から実際の各段の推移性を導く。

`affineCechStage_piDescent` は、局所 Noether な A の Spec 上の有限型アフィン射について、
実際の各非増強 Čech 段での底変換の全係数・全整数次数の PiDescent を証明する。
切断は零番目の射影、点の推移性は本節、始域の分離性と自然数の次元上界は §40 から供給する。
段ごとの切断・推移性・分離性・有限次元上界・降下のいずれも独立した仮定に残らない。
自然な blowup 列・各次数の有限積保存・冪零不変性は、引き続き明示した前層の条件である。
自然な列と有限積保存は実際の導来降下から供給すべき帰結であり、その導出は未完である。

本節で完了したのは、実際の二重 Čech 図式の各行の切断つき全次数降下である。
元の射への Tot・Fubini・細分による還元、有限平坦 transfer の導来図式への接続、
最小公理全体・(3.6)・K0・T2・E の接続は残る。
各行の次数ごとの同型から Tot と π_* の交換を仮定してはいない。

## 42. Čech の底変換と二重図式全体の軸交換

L9 の現在の計画では L9e の Tot・hG は未着手であることを確認した。
L8 側ではそれらの実構成を置き換えず、先行できる幾何的な Čech 比較を証明する。
通常の極限を Tot と呼ぶ代用品は導入しない。

Arrow の正方形が Cartesian であることは、その始域・終域の正方形で検査できる。
Comma の二射影による極限の共同反映でこれを証明した。
底変換の射 X ×_Y Z → Z は、Arrow 内で元の f と恒等射 𝟙 Z の引き戻しとなる。
増強 Čech nerve は既存の右随伴であり、従ってこの引き戻しを保つ。
これにより増強図式全体の実際の Cartesian 正方形を得た。

恒等射の Čech nerve の各段は、恒等射の族の wide pullback である。
普遍性から増強成分の逆射を構成し、全ての成分が同型であることを証明した。
従って指定増強を hom とする `identityCechIso` は定数図式との自然同型となる。
増強を忘れる関手の引き戻し保存も検査し、この同型で底変換の正方形の基底を移す。
`baseChangeCechIso` は、底変換した射の実際の Čech nerve と、
元の Čech nerve の定数図式による引き戻しとの図式全体の標準同型である。

元の有限型の圏の二重 Čech に適用すると、各二重次数の対象は
二つの元の Čech 段の増強のファイバー積となる。
指定二射影を保持して交換同型を構成し、二回の合成が恒等となることを証明した。
二射影の内側・外側の全ての単体射についての自然性も証明し、
交換が両方向の単体射と可換することを検査した。
積添字に uncurry した `doubleCechBifunctor` に対して、
`doubleCechSwapNatIso` は二重図式全体と軸を交換した図式との自然同型となる。
段ごとの同型の存在だけを図式全体の同型と呼んではいない。

本節の結果は、Fubini・細分に使う幾何的な比較の入力である。
値域の実際の Tot の Fubini、分裂降下、有限平坦 transfer の図式との接続、
元の切断を持たない射への還元は残る。
実降下からの自然な blowup 列と有限積保存、最小公理全体・(3.6)・K0・T2・E も未完である。

## 43. 平行な細分比較のホモトピーと相互細分のホモトピー逆

同じ基底 Y への二つの射 f : X → Y、g : W → Y と、
基底上の二つの持ち上げ a,b : X → W を取る。
`refinementCechMap` は指定された持ち上げからの実際の Čech 比較である。
持ち上げの一致は要求せず、この二つの比較の間に実際の単体ホモトピーを構成した。

ホモトピーの射は、出力座標を一つ重複させ、切替位置の左側では a、右側では b を使う。
`cechMixIndex` は元の座標と、どちらの比較射を使うかのタグを保持する。
最初・最後の面、切替位置の前・中央・後の面、前後の退化射の七つの関係を
有限順序集合の算術に還元して証明した。
実際のスキームの射の証明では、この有限添字の等式を使って各射影を検査する。
共通の基底へも lift の合成公式で一致し、wide pullback の普遍性で射の等式となる。

`refinementCechHomotopy` は Mathlib の `SimplicialObject.Homotopy` の全ての条件を満たす。
各次数の写像の存在だけをホモトピーと呼んではいない。
全ての面射・退化射の整合性と、二つの指定比較への端点の恒等式を検査済みである。

さらに基底上の持ち上げ a : X → W と b : W → X が両方向に存在するとする。
これらの合成が恒等射であることは仮定しない。
`refinementCechMap_id` と `refinementCechMap_comp` で比較の恒等射・合成の保存を確認し、
合成持ち上げと恒等持ち上げの間のホモトピーを適用する。
これにより Čech 比較の二つの合成はそれぞれ恒等写像にホモトピックとなる。

任意の同じ反変前層を、その反対圏への共変関手として適用できる。
実際の単体ホモトピーを写すことで、前層の像でも両側のホモトピー逆を得る。
これらは実際の Tot のホモトピー不変性に供給する細分比較の入力である。
Tot の実降下や任意の細分の降下保存を、この結果だけで結論してはいない。
L9 の実際の Tot・hG とその性質、Fubini、transfer の自然な図式、
実降下からの自然な列・有限積保存、最小公理全体・(3.6)・K0・T2・E の接続は残る。


## 44. 元の前層の実際の底変換と Čech transfer retract

固定した f : X → Y に対し、Over Y の底変換関手は Z → Y を Z ×_Y X → Y に写す。
元の反変前層をこの関手で制限して `baseChangedPresheaf` を構成した。
Over の底変換随伴の余単位を元の前層で写すことで、全ての基底変更とその射に自然な
`baseChangePresheafPullback` を得る。その成分は実際の第一射影の引き戻しである。
基底自身の底変換と X の標準同型も、現在選択された引き戻しの二射影から直接構成した。
この同型のもとで基底での pullback は元の f の引き戻しと一致する。

`BaseChangeTransfer` は底変換後から元への自然変換を保持する。
これは公理 (4) の自然性部分の入力であり、有限平坦 transfer の存在や射影公式の証明ではない。
局所自明化後の正の rank について rank 公式が与えられると、有理数で正規化して
前層そのものの retract を構成する。一般の有限平坦射に大域的な定数 rank 公式を仮定してはいない。

基底上の任意の図式について、その構造射から指定増強を作り、前層についての自然性を証明した。
この自然性により前層 retract は増強比較の矢の圏の retract へ移る。
実際の Čech nerve の指定増強を Over の構造射にした図式へ適用し、
`BaseChangeTransfer.cechAugmentationRetract` を得た。増強先の基底の値も同時に含む。
任意の図式関手で写しても retract は保たれ、底変換後の比較が全次数観測で同型なら
元の指定比較も全次数で同型となる。

この結果だけで補題 3.2 の実降下が完成したとはしない。
底変換後の係数図式と底変換した被覆の Čech 図式との増強を保つ自然同型、
L9 の実際の Tot・π_*・hG とホモトピー不変性、Fubini・分裂降下を接続する必要がある。
§44–45 の正規化経路では有理線形値域の実現が別途必要で、L9 のスペクトル圏の線形性を仮定しない。
§46 では代わりに観測後の両端の rank 公式から正規化する経路を追加する。
有限平坦 transfer 自体、射影公式、自然な blowup 列と有限積保存の実降下からの導出、
最小公理全体・(3.6)・K0・T2・E の接続は残る。


## 45. transfer 図式と実際の底変換被覆の増強 Čech の接続

§44 に残していた底変換係数図式と実際の底変換被覆の Čech 図式の同型を構成した。
`baseChangeCech_isPullback` を各単体次数で評価し、実際の底変換被覆の段と
元の増強段の引き戻しとの標準同型を得る。
この同型は元の Čech への指定比較と、底変換基底 X への指定増強を保つ。
Over の底変換関手の射は実際の二射影による lift なので、
その二射影で検査することで、全ての面射・退化射を含む自然性を証明した。
`cechBaseChangeGeometryIso` は二つの幾何図式全体の自然同型となる。

さらに底変換された増強は、基底自身の引き戻しから X への標準同型のもとで
実際の底変換被覆の増強と可換することを証明した。
元の同じ反変前層でこれを写し、増強先の値の同型と図式全体の自然同型を組み合わせる。
`cechBaseChangeAugmentationIso` は指定増強比較の矢の圏の同型である。
したがって各段の値の同型だけから増強や全図式の同型性を主張してはいない。

transfer の比較射 retract とこの矢の圏の同型を合成し、
元の被覆の指定 Čech 比較が、実際の底変換被覆の指定比較の retract となることを証明した。
実際の図式関手の像で底変換被覆の比較が全次数同型であれば、元の比較も全次数同型となる。
ここでは底変換被覆そのものの降下は入力であり、実際の Tot の分裂降下は未接続である。
通常の極限を Tot と呼ぶ置換も π_* と Tot の無証明の交換も行っていない。

L9 の実際の Tot・π_*・hG、ホモトピー不変性、Fubini・分裂降下、
有理線形値域での実際の transfer と局所 rank 公式の供給、
実降下から自然な blowup 列と有限積保存を導出する部分、
最小公理全体・(3.6)・K0・T2・E の接続は引き続き残る。

§45 の保存検証：集約対象ビルド成功。公理監査は 115 モジュール・1420 宣言で標準三公理のみ。
全体ビルドも 10024 ジョブで成功し、全て `set -eo pipefail` で終了コード 0 を確認した。


## 46. 元の値域の線形性を要求しない観測後の正規化

§44–45 の rank の逆数倍による正規化は、前層の値域の有理線形性を使っていた。
L9 の実際のスペクトル圏の線形性を L8 側で仮定することを避けるため、
元の圏には単に射・自然変換を要求する別の正規化経路を証明した。

一般の圏で i : A → B、r : B → A の合成 i ≫ r が同型なら、
r にその合成の逆を後合成することで A を B の retract にできる。
自然な比較の両端で往復の合成の像が同型であれば、
往復の二つの自然性正方形の合成は矢の圏の同型となり、比較射の retract が得られる。
これを各整数次数の観測先で実行し、観測後に両端の合成が同型なら、
比較先の全次数同型から元の比較の全次数同型を導いた。
有理加群値の観測後に正の局所 rank 倍の公式があれば、この合成は同型である。

この操作を実際の Čech 増強比較に適用した。
増強先の定数図式と Čech 図式に実際の図式関手を適用した二つの関手を定義し、
それらの自然な増強比較に観測後の rank 正規化を適用する。
§45 の増強比較の矢の圏の同型により、底変換被覆の実際の比較の降下を入力できる。
`BaseChangeTransfer.piCechComparison_of_observedRank` は、
前層の値域 V と図式関手の値域 D の加法性・有理線形性を要求しない。

二つの rank 公式は実際の図式関手の像を観測した後の公式として明示する。
各段の rank 公式から Tot の像の公式を無証明で推論してはいない。
実際の有理化・transfer・図式関手からこの公式を供給する部分は残る。
この経路は π_* と Tot の交換も通常の極限による Tot の置換も行わない。
L9 の実際の Tot・hG と分裂降下・Fubini、実降下からの自然な列・有限積保存、
最小公理全体・(3.6)・K0・T2・E の接続は引き続き未完である。

§46 の保存検証：集約対象ビルドと公理監査が成功。116 モジュール・1433 宣言、標準三公理のみ。
§45 の全体ビルド成功後、今回の保存単位では全体ビルドを反復しない。


## 47. 補題 3.3 の有限全射の strict transform と有限忠実平坦な細分

L9 の現状を再確認し、L9e の Tot・hG は引き続き未着手である。
一方、SchemeLemmas 側の実際の strict transform は、
元の空間と blowup のファイバー積における開部分のスキーム論的像として構成されている。
その閉包含と構造射を読み取り、L8 の補題 3.3 の幾何に接続した。
他レーンのファイルは変更していない。

有限射 f : X → Y の strict transform の構造射は、
有限射の引き戻しに実際の閉包含を合成したものなので有限である。
元の f が全射なら、その引き戻しも全射であり、制限した射も全射となる。
strict transform の閉包含は定義に用いた開部分で同型なので、
構造射のその開部分上の制限も全射となる。
ここで元の f が開部分で同型になるという仮定は不要である。

固有射の稠密な開部分上の全射性から全体の全射性を導く補題を証明した。
制限射の各点の持ち上げから開部分を像に含め、固有性による閉像性で閉包も含める。
実際の blowup の中心外の逆像は常に稠密なので、
中心外を用いて構成した有限全射の strict transform は全射となる。
平坦化や降下の結論をこの全射性の仮定としては使っていない。

局所 Noether 基底では blowup も局所 Noether であり、有限射の有限型性から
strict transform の構造射の局所有限表示性を導いた。
したがって、この実際の構造射が平坦になっていれば、
有限・平坦・全射・局所有限表示な射と元の X への射、および基底上の可換式を取り出せる。
`exists_finiteFlat_refinement_of_flat_strictTransform` はこの実際の空間と射を返す。

これは平坦化後から有限忠実平坦細分までの幾何的な段階を完了するものである。
公理 (6) の平坦化中心の存在、整な基底を支配する被約既約成分の選択、
元の有限型の圏内の全図式への持ち上げ、Čech 細分と中心上の帰納の接続は残る。
SchemeLemmas の有限加群のチャート平坦化を直ちに strict transform のスキームの平坦性と
同一視してはいない。実際の同定が必要である。
最小公理全体、実際の Tot・hG、自然な blowup 列と有限積保存の導出、(3.6)・K0・T2・E も未完である。

§47 の保存検証：集約対象ビルドと公理監査が成功。117 モジュール・1440 宣言、標準三公理のみ。


## 48. 同じ有限型の圏の平坦細分と実際の blowup 正方形

§47 の幾何はスキームの圏で記述していた。
元の前層は固定した S 上の有限型対象を定義域とするので、その圏内へ持ち上げる必要がある。
Noether な S 上の有限型対象 Y は Noether スキームであり、
Y の実際の blowup は固有であることから、同じ S 上有限型の対象となる。
`finiteTypeBlowup` とその指定構造射を構成した。
有限射の実際の strict transform の構造射も有限なので、
これを同じ有限型の圏の対象とし、blowup と元の X への二つの射を構成した。
実際の二射影の可換式から、S 上の可換性と有限型の圏内の可換正方形を証明した。

元の f と blowup 構造射の実際の引き戻しは、既に有限型の圏内で構成されている。
その普遍性に strict transform の二つの射を入れ、
元の f の底変換被覆への細分射を構成した。
この細分射は blowup 基底への構造射を保ち、実際の Čech nerve 関手で写すと
`finiteTypeStrictTransformCechRefinement` という全単体射を保持する比較となる。
この比較が指定増強も保つことを増強 Čech の同じ Arrow の射から証明した。
同じ前層の定義域を全スキームの圏へ変更してはいない。

中心外を用いた有限全射の strict transform については、
同じ指定射の有限性・全射性を確認し、平坦化後の実際の平坦性が与えられれば
有限忠実平坦で局所有限表示な被覆となることを元の有限型の圏内で公開した。
この Čech 比較そのものが降下を保つことは、Tot の細分計算で別途示す必要がある。

さらに、中心の台を被約閉中心として、その実際の引き戻し・blowup の固有性・
中心外の同型性を組み合わせ、`finiteTypeBlowupSquare` を構成した。
これは既存の `AbstractBlowupSquare` の全ての幾何条件を満たす。
中心の冪零構造を保存した正方形であるとは主張せず、
明示した被約中心を使う抽象 blowup 降下と中心上の帰納の入力である。

平坦化中心の存在、整な基底を支配する被約既約成分の選択、
Čech 細分の実降下と中心上の帰納による元の有限全射の降下への還元は残る。
実際の Tot・hG、最小公理全体、自然な blowup 列と有限積保存の導出、(3.6)・K0・T2・E も未完である。

§48 の保存検証：集約対象ビルドと公理監査が成功。118 モジュール・1467 宣言、標準三公理のみ。
§48 の幾何接続の区切りの全体ビルドも成功（10100 ジョブ）。
`set -eo pipefail` で終了コード 0、ログは `/tmp/l8-strict-transform-refinement-full-build.log`。


## 49. 整な基底を支配する成分の選択と元の有限全射への細分

補題 3.3 の前段として、既約な基底への固有全射から、
基底に全射な被約既約成分を実際に選ぶ部分を証明した。
基底の生成点の持ち上げ x を取り、x を含む既約成分に既存の被約閉構造を入れる。
この成分の像は固有性で閉じており、基底の生成点を含むので全ての特殊化を含む。
したがってその指定射は全射である。
この選択には Noether 性や既約成分の有限個性は不要である。
始域が既に被約であるという仮定も置かない。

指定射 `integralComponentMap` は元の有限型の圏内の実際の閉包含と元の射の合成である。
元の射が有限ならこの射も有限なので、整基底への有限全射から
平坦化する整な有限全射成分を選べる。
成分の存在や支配性を未証明のフィールドとして新たに要求してはいない。

この成分と中心 J を固定し、その実際の strict transform の構造射が平坦であるとする。
§47–48 の有限性・全射性・局所有限表示性をその指定射に適用する。
strict transform から成分への射に、成分の元の X への閉包含を合成すると、
元の f と blowup の構造射の上で可換する。
この可換式を、元の f の実際の引き戻しの普遍性に入れ、
有限忠実平坦被覆から元の有限射の底変換への細分射を構成した。
`exists_finiteFlat_cover_refining_blowup` は同じ有限型の圏内の被覆とこの細分射、
その有限性・平坦性・全射性・局所有限表示性、および基底上の指定可換式を返す。

これにより「支配する整成分の選択」と「その成分の平坦化後から元の被覆への細分」が接続した。
適切な平坦化中心の存在は引き続き未証明であり、
SchemeLemmas の有限加群のチャート平坦化を strict transform の平坦性と同一視してはいない。
この実際の同定と、Čech 細分の実降下・中心上の帰納による有限全射降下への還元が残る。
実際の Tot・hG、最小公理全体、自然な blowup 列・有限積保存の導出、(3.6)・K0・T2・E も未完である。

§49 の保存検証：集約対象ビルドと公理監査が成功。120 モジュール・1473 宣言、標準三公理のみ。
§49 の区切りの全体ビルドも成功（10118 ジョブ）。`set -eo pipefail` で終了コード 0。
ログは `/tmp/l8-dominating-component-full-build.log`。


## 50. 生成点付近の自由化から実際の有限加群のチャート平坦化中心へ

SchemeLemmas の有限加群の平坦化中心の存在定理は、
正則な境界元 r と、r の外での加群の平坦性を入力としていた。
整なアフィン基底でこの入力を実際に供給するため、
Noether 整域 R 上の有限加群 M について生成点付近の自由化を証明した。
元の M の平坦性・捩れなし性は要求しない。

有限加群は Noether 性から有限表示である。
分数体 K への基底変更 K ⊗_R M は K 上のベクトル空間なので自由となる。
有限表示加群の局所化の自由基底を一つの分母へ広げる Mathlib の定理を適用し、
非零元 r で局所化した M が R[1/r] 上自由になることを得た。
この自由性から境界外の平坦性を導出した。

その実際の局所化と非零元を既存の有限加群の平坦化中心の構成へ渡した。
`exists_nonzero_finite_module_flattening_center` は、
非零元 r と有限生成イデアル J、D(r) を避ける中心という条件、および
全ての実際の blowup チャート上の加群の純変換の平坦性を返す。
境界外の平坦性を追加仮定として残していない。
新しい平坦化公理や未証明の中心の存在のフィールドは導入していない。

結論は基礎環上有限な加群のチャート純変換に関するものに限る。
有限型代数上でのみ有限な一般の加群や、スキームの strict transform の平坦性を
この加群の結論だけから推論してはいない。
有限代数の純変換との環としての同定、実際の strict transform のアフィンチャートとの同型、
開被覆によるスキームの平坦性の貼り合わせを通して §47–49 に接続する必要がある。
Čech 細分の実降下・中心上の帰納、実際の Tot・hG、最小公理全体、
自然な blowup 列と有限積保存の導出、(3.6)・K0・T2・E も未完である。

§50 の保存検証：集約対象ビルドと公理監査が成功。121 モジュール・1476 宣言、標準三公理のみ。
§49 で全体ビルドを確認済みなので、この代数入力の保存単位では反復しない。


## 51. 純変換商の Spec と基本開の実際のスキーム論的像

§50 の加群の平坦化を実際のスキーム射に移すため、
境界ねじれを除く商を実際の可換代数として構成した。
R 代数 B と f ∈ R について、B 自身上の境界元の像のねじれ部分加群は B のイデアルである。
`boundaryTorsionIdeal` はこのイデアル、`algebraPureTransform` はその実際の商環である。
スカラー制限の同型を使い、この商環の R 加群と既存の `modulePureTransform f B` を
代表元を保つ線形同型で結んだ。したがって加群の有限性と平坦性を商代数へ移せる。

環の局所化と加群の局所化の核は、同じ冪消滅条件で記述される。
これにより境界ねじれイデアルが B → B[1/f] の環準同型の核であることを証明した。
商代数からこの一元局所化への実際の環準同型を構成し、その単射性を示した。
局所化全体との同型や、この写像の全射性は主張していない。

商代数の Spec と B への閉包含、R への構造射を構成した。
加群の平坦性・有限性から、これらの実際のスキームの射の平坦性・有限性を得た。
Spec のイデアル対応を使い、商写像の Spec と局所化の Spec の核イデアル層が一致することを示す。
二つの閉埋め込みの lift の普遍性により、商の Spec と局所化の実際のスキーム論的像の
閉包含を保つ標準同型を構成した。

基本開 D(f) と局所化の Spec の標準同型は元の B の Spec への射を保つ。
この同型を通して核を比較し、商の Spec と基本開の実際のスキーム論的像の標準同型も構成した。
この同型は閉包含と R への構造射を保つ。
その逆射と商の Spec の構造射の合成を使い、
基本開の実際のスキーム論的像の平坦性・有限性へ移した。
点集合の閉包による代用や、構造層を忘れた同定は行っていない。

最後に Noether 整域 R 上有限な代数 B について、§50 の実際の中心を選び、
各 blowup チャート C 上の B の基底変更 C ⊗_R B に以上の同定を適用した。
全ての実際のチャートで、境界基本開のスキーム論的像の構造射が有限平坦になる。
これは実際のスキームの射についての結論であり、各チャートでの加群の平坦性だけには留めない。

ここで定義したアフィン像を、元の global strict transform の各チャートへ引き戻したものと
同定する部分はまだ残る。像の形成と開埋め込みによる底変換の両立、
実際のテンソル積のアフィン引き戻しとの比較、境界基本開の一致、
開被覆上の平坦性の貼り合わせを行う必要がある。
全射性は §47–49 の global な判定へ接続して供給し、現在の局所像について独立に仮定しない。
Čech 細分の実降下・中心上の帰納、実際の Tot・hG、最小公理全体、
自然な blowup 列と有限積保存の導出、(3.6)・K0・T2・E も未完である。

§51 の保存検証：集約対象ビルドと公理監査が成功。125 モジュール・1517 宣言、標準三公理のみ。
§51 の区切りの全体ビルドも成功（10179 ジョブ）。`set -eo pipefail` で終了コード 0。
ログは `/tmp/l8-affine-pure-transform-full-build.log`。


## 52. 像の開底変換と global strict transform のチャートでの平坦性の貼り合わせ

準コンパクトな射 f と開埋め込み g の実際の Cartesian 正方形について、
底変換後の核イデアル層が元の核の引き戻しと一致することを証明した。
各アフィン開集合で Mathlib の核の公式とイデアル層の引き戻しの公式が一致することを使う。
選択された引き戻しだけでなく、具体的な Cartesian モデルにも適用できる。
これと閉包含の引き戻しの核の公式を合わせ、
局所のスキーム論的像と元の像の実際の引き戻しの間に、閉包含を保つ標準同型を構成した。
像を点集合の閉包で代用せず、構造層を持つ閉スキームとして比較している。

strict transform を定義する開包含の準コンパクト性も供給した。
局所 Noether 基底上の有限型射では、blowup と周辺空間が局所 Noether なので、
その実際の開包含は準コンパクトである。
したがってこの像の開底変換の定理を実際の strict transform に適用できる。

blowup の開チャート j に対し、周辺空間の実際の底変換と、
strict transform を定義する開部分のその逆像を構成した。
この開部分の像は、元の strict transform の閉包含を周辺チャートへ引き戻したものと同型になる。
二射影の交換と二段の Cartesian 正方形の貼り合わせを通して、
`strictTransformOpenChartIso` はこれを元の構造射 `strictTransformπ` の実際の底変換に結ぶ。
この同型がチャート基底への指定構造射を保つことも全ての射影公式から証明した。
別の引き戻しの型クラスを選んで対象を変更してはいない。

この同型の逆を使い、周辺チャートの像の平坦性から
元の strict transform の構造射のそのチャート上での平坦性を得た。
平坦性の標的上の Zariski 局所性により、実際の開被覆の全ての像が平坦なら
元の global な `strictTransformπ` が平坦となる。
型クラス探索が Mathlib の一般の局所性を自動取得できない箇所では、
`HasRingHomProperty.instIsZariskiLocalAtTarget` の既存の証明を明示して適用した。
新しい平坦性の局所性の仮定や公理は導入していない。

§51 のテンソル積のアフィン像を、この周辺チャートの像と同定する工程は残る。
実際のテンソル積 Spec のファイバー積表示と、境界基本開の一致を使って
二つの具体的なチャートを対応させる必要がある。
その後、既に証明したこの貼り合わせと §47–49 の全射性・有限平坦細分へ接続する。
Čech 細分の実降下・中心上の帰納、実際の Tot・hG、最小公理全体、
自然な blowup 列と有限積保存の導出、(3.6)・K0・T2・E も未完である。

§52 の保存検証：集約対象ビルドと公理監査が成功。127 モジュール・1549 宣言、標準三公理のみ。
§52 の区切りの全体ビルドも成功（10226 ジョブ）。`set -eo pipefail` で終了コード 0。
ログは `/tmp/l8-strict-transform-open-charts-full-build.log`。

後続の接続で区別する開部分：§50–51 が返す中心 J は D(r) を避けるので、
D(r) ≤ centerComplement J であるが、両者の等号は主張していない。
加群の r-ねじれを除く計算は U = D(r) の像に対応する。
§47 の中心外を使う全射性をそのまま無証明で適用してはならない。
blowup 上の D(r) の逆像の稠密性を証明して一般の稠密開版へ渡すか、
支配する整成分で開部分の拡大に対する strict transform の不変性を証明する必要がある。


## 53. 平坦化に使う境界基本開の逆像の稠密性と同じ境界での有限平坦細分

§52 の末尾で区別した D(r) と中心補集合の問題について、
今回は blowup 上の D(r) の逆像の稠密性を直接証明する経路を実装した。
D(r) = centerComplement J という未証明の等号は使わない。

任意の可換環の非零因子 r に対し、局所化 R → R[1/r] は単射である。
Spec の稠密像の判定と局所化の像の公式から、基本開 D(r) の稠密性を得た。
これは零環の場合も含み、Noether 性や被約性は不要である。
非零因子は実際の全 blowup チャートへの係数写像で非零因子に保たれるので、
各チャートの境界基本開も稠密になる。
各点の標準チャートによる表示と連続写像による閉包の包含を使い、
アフィン blowup 全体で境界基本開の逆像が稠密となることを証明した。
中心の有限生成性も必要ない。

さらにアフィン基底 S の全体のアフィンモデルから global な実際の blowup への
標準射が全射であることを像の公式から得た。
その構造射との可換性と基本開の逆像の公式を使い、
`blowup_boundary_dense_of_isAffine` は実際の global blowup 上の稠密性を与える。

この結果を既存の稠密開の全射性判定へ渡し、
有限全射 f の strict transform を平坦化に使った同じ U = D(r) で定義した場合に、
その実際の構造射が全射であることを得た。
元の有限全射の開部分上の同型性や D(r) と中心補集合の一致は不要である。
したがって、選んだ支配する整成分のこの同じ D(r) による strict transform が平坦なら、
元の有限射の底変換を細分する有限忠実平坦・局所有限表示被覆を同じ有限型の圏内で取り出せる。
`exists_finiteFlat_cover_refining_boundary` はこの被覆と指定細分射・可換式を返す。

残る幾何接続は、§51 のテンソル積のアフィン像と §52 の周辺チャートの像の一致である。
その一致と貼り合わせで同じ境界の実際の平坦性を供給すれば、今回の全射性の結果を適用できる。
Čech 細分の実降下・中心上の帰納、実際の Tot・hG、最小公理全体、
自然な blowup 列と有限積保存の導出、(3.6)・K0・T2・E も未完である。

§53 の保存検証：集約対象ビルドと公理監査が成功。129 モジュール・1554 宣言、標準三公理のみ。
全体ビルドは §52 の区切りで成功済み。この保存単位では対象ビルドと監査を実行した。


## 54. テンソル積の Spec と実際の周辺チャートの同型と境界の保存

アフィン射 Spec B → Spec R と、blowup 上のチャート j : Spec C → Bl_J を取る。
R から C の係数射の Spec が j と blowup 構造射の合成に一致するという式を明示する。
この式は実際の blowup チャートで検証して適用すべき幾何条件であり、
チャートや底変換を任意の別のものへ交換する仮定ではない。

C を左因子とするテンソル積 C ⊗_R B の Spec の指定二射影の Cartesian 性を使い、
この Spec が元の射と j の基底への合成の引き戻しを表すことを証明した。
一方、実際の strict transform の周辺チャートは二段の選択された引き戻しである。
その二つの Cartesian 正方形を縦に貼り合わせ、同じ引き戻しを表すことを検査した。
両者の同じ引き戻しへの標準同型を合成して `strictTransformTensorChartIso` を構成した。
別の引き戻しの型クラスを選んで対象を変更してはいない。

この標準同型は C への射影を保つ。
元の二つの引き戻しの可換性とチャートの係数射との可換式を組み合わせると、
R の Spec への構造射も保つことが分かる。
この構造射の等式で境界 D(r) を引き戻し、
周辺チャートの strict transform を定義する開部分が、
テンソル積の係数の像による基本開 `algebraBoundaryOpen C (C ⊗_R B) (r の C での像)` に
対応することを証明した。

これにより §51 のアフィン像と §52 の周辺チャートの像を比較するための
実際の周辺空間の同型と開部分の対応が揃った。
この周辺同型のもとでスキーム論的像を移す比較を構成し、構造射の可換性を使って
平坦性を移す工程を続ける必要がある。
実際の全 blowup チャートの係数射の公式を適用して §52 の貼り合わせに渡し、
§53 の同じ境界の全射性と有限忠実平坦細分へ接続する工程はまだ残る。
Čech 細分の実降下・中心上の帰納、実際の Tot・hG、最小公理全体、
自然な blowup 列と有限積保存の導出、(3.6)・K0・T2・E も未完である。

§54 の保存検証：集約対象ビルドと公理監査が成功。130 モジュール・1564 宣言、標準三公理のみ。
全体ビルドはアフィン平坦化の global 接続の区切りで再確認する。
