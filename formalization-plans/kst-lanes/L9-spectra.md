# K-L9（Sp・ホモトピー群）

## 所有するもの・借りるもの

- 所有：Kan 複体の π_n とその群構造・自然性・ホモトピー不変性。
- 所有：Kan fibration の連結射とホモトピー長完全列。
- 所有：γ-B の Ω スペクトル、その単体的圏と coherent nerve。
- 所有：整数次数のスペクトルの π_n。
- 所有：有理化、hG、Tot の Kan 複体による実構成。
- 借用：H_* は K-L2 が所有する。
- 借用：pro 形式は K-L6 が所有する。
- 借用：γ1 は N レーンの局所 Kan coherent nerve 定理。
- 借用：γ3 は N レーンのホモトピー極限と ∞ 極限の比較。
- 借用：Core の pinched 写像空間とその Kan 性。
- 既存 Spectra は比較用に読むだけで編集しない。
- 既存 Spectra の `PointedSimplicialSet.Basic` と `Pointed.InternalHom` の基礎定義を借りる。
- この借用は Under による点つき対象と等化子による Hom のみで、安定モデル構造は含まない。
- suspension・loop では既存 Spectra の円、smash、閉対称モノイダル構造の通常の圏論的構成も借りる。
- 豊穣構造の移送は既存 CategoryTheory の通常の lax monoidal 関手の補題を借りる。
- 既存 HomotopicalAlgebra は読むだけで編集しない。
- 借用：同ディレクトリの基点を含む指定部分を固定する垂直ホモトピー充填。
- 借用：`AnodyneKanReplacement` のホーンの小対象論法と `Generators` の境界生成定理。
- これらはモデル構造を仮定しない充填と因子分解で、HT-KQ の import は含まない。
- 既存 InfinityCategories は読むだけで編集しない。

## 1. 正本と目的

作成日：2026-10-18。
状態：L9a・L9b・L9c 完了。L9d 着手。
Sp、自然な任意段表示、置換、任意の射の homotopy fiber と整数次数の長完全列まで検証済み。
対象ビルド・198 モジュール 2692 宣言の公理監査成功。
直近の工程区切りの全体ビルド（L9c、9543 jobs）成功。
L9c の BF cofibrant–fibrant 方式への改訂を承認済み。
正本：[KST 経路](../k-theory-kst-route.md) §5、§13 決定 3・4。
基盤の正本：[foundations](../foundations.md) §1 の F3・γ。
本文は実装順と検証状態を管理する。
実施の経緯はコミットメッセージに記録する。
証明できた宣言だけを完了表に記載する。
設計案は実装済み宣言と区別する。
全体の到達点は定理 3.1 の全次数 π_* 同型である。
本レーン単独で定理 3.1 全体を証明したとは主張しない。
`theorem_3_1_K0` の置換は合流先の仕事である。
`supportedRankK0_descent` の置換も合流先の仕事である。
本レーンはそのための Sp と π_* を供給する。

## 2. 編集範囲

Lean の作業場所は `SerrePositivity/KST/Spectra/`。
namespace は `SerrePositivity.KST.Spectra`。
集約入口は `SerrePositivity/KST/Spectra.lean`。
ルートへの変更はこの入口の public import 一行のみ。
監査入口は `scripts/audit_kst_spectra.lean`。
この計画以外のレーン計画を編集しない。
共有ファイルの既存の未コミット変更を保存する。
他者の新規ファイルをコミットしない。
他者の作業を修正してビルドを迂回しない。
import 閉包の破損はそのまま報告する。

## 3. 原典の対応

| 対象 | 原典 | 適用の範囲 |
| --- | --- | --- |
| Kan 複体 | Kerodon §3.1 | ホーンの充填 |
| pointed homotopy | Kerodon §3.2.1 | 基点を固定したホモトピー |
| π_n の定義 | Kerodon §3.2.2 | 境界が定数の単体の商 |
| π_n の積 | Kerodon §3.2.3 | 充填で定義する群構造 |
| 可換性 | Kerodon §3.2.3 | n ≥ 2 の二つの積の比較 |
| π_* による検出 | Kerodon Theorem 3.2.7.1 | Kan 複体の同値 |
| coherent nerve | HTT Proposition 1.1.5.10 | 局所 Kan から quasicategory |
| coherent nerve | Kerodon Proposition 2.4.5.1 | γ1 の既存実装 |
| pinched Hom | HTT Proposition 1.2.2.3 | 右写像空間 |
| pinched Hom | Kerodon Proposition 4.6.5.5 | Core の Kan 性 |
| spectra | HA §1.4.2 | spectrum objects |
| spaces の spectra | HA §1.4.3 | 安定ホモトピー群との接続 |
| 比較 | HTT Theorem 4.2.4.1 | γ3 後の ∞ 極限の比較 |
| 単体的 π_* | Goerss–Jardine, I §7 | 古典的ホモトピー群 |
| fiber の連結射 | Kerodon §3.2.5、Goerss–Jardine, I §§7–8 | 相対ホーンと完全性 |
| 長完全列 | Kerodon Theorem 3.2.6.1 | kernel と image の比較 |
| スペクトルの比較 | Bousfield–Friedlander, §2 | 古典的スペクトル |

原典の定理番号が未確認の場合は節番号を使う。
原典の主張を公理として持ち込まない。
原典への参照は証明義務の代わりにしない。
Mathlib の既存証明は依存公理まで監査する。

## 4. 全体の設計決定

γ は γ-B を採用する。
HT-KQ の引用を使わない。
`Inputs/Homotopy/KanQuillen` を import しない。
既存の対称スペクトルを Sp の定義に置き換えない。
Sp の入口は Mathlib の `SimplicialNerve`。
γ1 の既存定理で quasicategory を得る。
その前に豊穣 Hom の Kan 性を証明する。
Kan 性を新しい入力仮定として隠さない。
群の法則を未証明の入力構造にしない。
fiber 長完全列を仮説として構造に入れない。
有理化の π_* 計算を入力として構造に入れない。
π_* 同型が第 1 段の公開界面となる。
Sp の ∞ 極限という主張は γ3 後に分離する。

## 5. 次数と基点

Kan 複体の次数は自然数。
次数ゼロは pointed set で、一般には群でない。
群構造は正の次数だけに付ける。
可換群構造は二以上の次数に付ける。
基点は `X _⦋0⦌` の元。
射の像の基点は自然変換の零成分で与える。
基点を固定する射と、基点を動かす道を区別する。
ホモトピー不変性はまず基点固定で証明する。
非可換な π_1 の積の向きを明記する。
スペクトルの次数は整数。
負次数を自然数への切り捨てで定義しない。
段の選択への独立性を遷移同型で証明する。

## 6. L9a：代表と関係

Mathlib の `SSet.PtSimplex` を使う。
境界定数条件は `RelativeMorphism` の条件に従う。
本レーン固有の名前で商を定義する。
Mathlib の将来の `π_n` と衝突させない。
`RelStruct` のホーンによる関係を使う。
正次数では `MulStruct .const f g i` との比較を使う。
反射性は退化単体から得る。
対称性は `oneMulEqSymm` から得る。
推移性は `oneMulEqTrans` から得る。
各面添字の関係が一致することは別途証明する。
零次数は `PiZero` と照合する。
商の等式から関係の証人へ戻す補題を用意する。
代表の変更が積に影響しないことを先に証明する。

## 7. L9a：群構造

積の候補は `MulStruct.nonempty` から選ぶ。
選択の依存を商で消す。
積の候補の一意性は商でだけ主張する。
代表単体の一意性は主張しない。
単位元は定数単体の類。
左単位は `oneMul` から得る。
右単位は `mulOne` から得る。
結合則は `MulStruct.assoc` と `assoc'` を使う。
左逆元は `exists_left_inverse` から選ぶ。
群構造を商の上に構成する。
逆元の代表選択は群法則による一意性で処理する。
隣接する積の反転を四面の比較ホーンの充填で証明する。
四面の消去と正順・逆順の充填の比較により二以上の次数の可換性を得る。
可換性の具体的証明は Kerodon §3.2.3 の四面の議論に合わせる。
可換性に π_* の安定化を先取りしない。

## 8. L9a：自然性とホモトピー

単体集合の射による代表単体の後合成を定義する。
境界定数条件の保存を証明する。
`RelStruct` の後合成を定義する。
`MulStruct` の後合成を定義する。
商上の写像を定義する。
恒等射の保存を証明する。
合成の保存を証明する。
積の保存を証明する。
基点付き同型が誘導する群同型を構成する。
相対ホモトピーから代表単体間の関係を得る。
ホモトピーの両端の誘導写像が一致すると示す。
ホモトピー同値から群同型を得る。
ここまでを L9a の完了条件とする。

## 9. L9b：fiber と連結射

対象は Kan fibration。
基点は全空間で選び、底の基点へ送る。
fiber は基点への引き戻し。
fiber の Kan 性を引き戻しから証明する。
底の代表単体をホーンに沿って持ち上げる。
欠けた面が fiber の代表単体となることを示す。
持ち上げの選択が商上で独立であると示す。
連結射の基点保存を示す。
適切な正次数で群準同型性を示す。
fiber → 全空間 → 底の誘導射を定義する。
連続する射の合成が零となると示す。
各箇所で kernel = image を証明する。
π_1 と π_0 の端は pointed set の完全性で述べる。
fibration 間の射に対する自然性を示す。
ここまでを L9b の完了条件とする。

## 10. L9c：ループ空間

基点付き Kan 複体のループ対象を具体的に固定する。
区間の両端の制限の fiber とする候補がある。
Core の pinched Hom を使う候補もある。
二つの具体モデルを無言で同一視しない。
Kan 性は端点制限の fibration 性から得る。
基点は定数ループ。
ループ構成の関手性を証明する。
π_n(ΩX) と π_(n+1)(X) の比較を証明する。
比較は基点と積を保存する。
Ω の enriched functor としての振る舞いも必要となる。

## 11. L9c：スペクトルと写像空間

対象は点つき Kan 複体の列 X_n と構造写像 σ_n : ΣX_n → X_(n+1)。
σ_n は単射とし、随伴 X_n → ΩX_(n+1) は全基点で π_* 同型とする。
これは Bousfield–Friedlander 1978 の安定モデル構造の cofibrant–fibrant モデルである。
原典は Bousfield–Friedlander 1978 と HTT A.3.3。
厳密な構造同型 X_n ≅ ΩX_(n+1) は要求しない。
厳密同型を外した理由は、従来の Hom の厳密極限の Kan 性の証明が得られないため。
構造写像と可換な段ごとの点つき射をスペクトルの射とする。
豊穣 Hom は有限切断への写像空間の塔の極限とする。
各段の制限は Hom_*(X_(n+1),Y_(n+1)) → Hom_*(ΣX_n,Y_(n+1)) の引き戻し。
源の単射 σ_n と標的の Kan 性によりこの制限は Kan fibration。
Kan fibration の引き戻しと塔の極限についての閉性を RLP から証明する。
従って Hom(X,Y) → Hom_*(X_0,Y_0) は Kan fibration となる。
始段の Kan 性と合わせて Hom(X,Y) の Kan 性を得る。
この Kan 性の証明には Ω 条件を使わない。
Ω 条件はスペクトルの正しいホモトピー型を表すための条件である。
合成と単位は厳密な段ごとの合成と単位から作る。
Sp はこの単体的圏の coherent nerve とし、γ1 を適用する。
この nerve が導来写像空間を持つ正しい Sp であることの比較は γ3 後に扱う。
第 1 段の π_* の証明にその比較を使わない。
非単射の構造射は境界生成の cell 分解によって直接 cofibrant 置換する（§32）。
各段の Kan 置換には既存 AnodyneKanReplacement の実構成を使う。
両置換の存在と π_* の保存を本レーンで証明し、入力にしない。
fiber 列の各段の fiber は構造射の単射性を保つとは限らないので置換を挟む。
K 理論の反復 delooping もこの対象仕様に直接合わせる。
単射の cell 分解は Mathlib の relativeCellComplexOfMono により得る。
整数次数 π_* とその自然性を構成する。
fiber 列の定義と長完全列を実装する。
ここまでを L9c の完了条件とする。

## 12. L9d：有理化

自然数による乗法写像の telescope を構成する。
全ての正整数を反転する列を明示する。
通常の余極限と homotopy telescope を区別する。
構成した対象の Kan 性を証明する。
ループ構造との整合を示す。
π_* が必要な telescope と可換すると示す。
アーベル群の有理化との比較を構成する。
比較の対象は π_*(X) ⊗ ℚ。
自然性と加法性を証明する。
有理化写像の π_* を明記する。
ここまでを L9d の完了条件とする。

## 13. L9e：作用と Tot

有限群の作用を実際の作用図式として与える。
homotopy fixed points と通常の fixed points を区別する。
cosimplicial replacement の全ての構造射を構成する。
Tot は段ごとの Kan 複体で構成する。
Tot の Kan 性を Reedy 型の充填で証明する。
極限という語だけから Kan 性を主張しない。
有理係数の有限群コホモロジー消滅を実証する。
平均化に使う群の位数が可逆であることを明示する。
自明作用の有理スペクトル M の比較射を作る。
π_* 上で M → M^{hG} の同型を証明する。
任意の非有理 M に同じ結論を主張しない。
γ3 前は Sp の ∞ 極限の普遍性を主張しない。
ここまでを L9e の完了条件とする。

## 14. 検証と保存

保存単位ごとに対象の `lake build` を実行する。
保存単位ごとに専用の公理監査を実行する。
許容公理は `propext`、`Classical.choice`、`Quot.sound` のみ。
`sorryAx` を拒否する。
追加公理を拒否する。
HT-KQ への依存を認めない。
監査は公開定理だけでなく本レーンの全宣言を対象とする。
検証シェルでは `set -o pipefail` を指定する。
パイプを通したログの見かけの成功に依存しない。
工程完了時だけ全体ビルドを行う。
`git diff --check` を行う。
コミットは自分の検証済みファイルだけ。
`git commit --only` を使う。
ルートの既存変更を巻き込まない。
amend・rebase・reset を使わない。

## 15. 現在地

| 工程 | 状態 | 残る証明 |
| --- | --- | --- |
| 計画 | 作成 | 実装と同期する |
| L9a | 完了 | 全体ビルドも L9b の区切りで成功 |
| L9b | 完了・対象ビルド、公理監査、全体ビルド成功 | なし |
| L9c | 完了・対象ビルド、公理監査、全体ビルド成功 | γ3 後の導来 Sp・∞ 極限との比較は別工程 |
| L9d | 進行中 | スペクトルの乗法射、telescope、群の計算との接続 |
| L9e | 未着手 | Tot、hG、有理自明作用の比較 |

## 16. 主要宣言

以下は検証済みの宣言だけを記載する。
名前の共通接頭辞は `SerrePositivity.KST.Spectra`。
最初の表の宣言は `SerrePositivity/KST/Spectra/HomotopyGroups.lean` に置く。
補助の幾何的構成と全自然数次数の界面は後続の四モジュールに分割する。

| 宣言 | 内容 |
| --- | --- |
| `simplexRel` | 最後の面の単位積による関係 |
| `simplexSetoid` | Kan 性から同値関係を実証 |
| `shiftRelStruct` | 隣接する面の関係を前へ移す |
| `unshiftRelStruct` | 隣接する面の関係を後ろへ移す |
| `nonempty_relStruct_iff_zero` | RelStruct の存在の面添字独立性 |
| `simplexRel_iff_relStruct` | 商の関係と任意の RelStruct の比較 |
| `KanHomotopyGroup` | 次数 n + 1 のホモトピー類の商 |
| `KanHomotopyGroup.mk_eq_iff` | 商の等式と充填関係の同値 |
| `KanHomotopyGroup.sound` | 任意の RelStruct を類の等式へ送る |
| `KanHomotopyGroup.mul_unique` | 積の充填の類の一意性 |
| `KanHomotopyGroup.mul_congr_left` | 左代表の独立性 |
| `KanHomotopyGroup.mul_congr_right` | 右代表の独立性 |
| `KanHomotopyGroup.mul_eq` | 指定した充填による積の計算 |
| `KanHomotopyGroup.exists_left_inverse` | 外側ホーンによる左逆元 |
| `KanHomotopyGroup.instGroup` | 商の群構造 |
| `mapSimplex` | 基点を保つ後合成 |
| `mapRelStruct` | 関係の充填の後合成 |
| `mapMulStruct` | 積の充填の後合成 |
| `KanHomotopyGroup.map` | 誘導群準同型 |
| `KanHomotopyGroup.map_id` | 恒等射の保存 |
| `KanHomotopyGroup.map_comp` | 合成の保存 |

追加の主要宣言：

| ファイル | 宣言（共通接頭辞は同じ） | 内容 |
| --- | --- | --- |
| `HomotopyDegreeZero.lean` | `KanHomotopyZero` | RelStruct₀ の商による零次数 |
| 同上 | `KanHomotopyZero.equivPiZero` | Mathlib の π₀ との全単射 |
| 同上 | `KanHomotopyZero.equivPiZero_map` | π₀ との比較の自然性 |
| `HomotopyInvariance.lean` | `RelativePrism.sectionRel` | prism の隣接断面の RelStruct |
| 同上 | `KanHomotopyGroup.eq_of_relativeHomotopy` | 相対ホモトピーを類の等式へ送る |
| 同上 | `KanHomotopyGroup.map_eq_of_basedHomotopy` | 基点固定ホモトピーによる群準同型の不変性 |
| 同上 | `KanHomotopyGroup.equivOfBasedHomotopyInverse` | ホモトピー逆が誘導する群同型 |
| 同上 | `KanHomotopyZero.map_eq_of_homotopy` | 零次数のホモトピー不変性 |
| `Commutativity.lean` | `AdjacentProduct.flip` | 隣接する面の積の反転の充填 |
| 同上 | `FourStruct.exists_fill` | 四面の指定を持つ Kan 充填の存在 |
| 同上 | `FourReduction.class_eq` | 四面から積の式を得る |
| 同上 | `FourComparison.compare` | 正順・逆順の充填の比較 |
| 同上 | `KanHomotopyGroup.mul_comm` | 二以上の次数での可換性 |
| `HomotopyIndexing.lean` | `KanHomotopy` | 実際の自然数次数で添字付けした π_n |
| 同上 | `KanHomotopy.map` | 全自然数次数の誘導写像 |
| 同上 | `KanHomotopy.map_id`、`map_comp` | 全次数の関手性 |
| 同上 | `KanHomotopy.map_point` | 全次数の基点保存 |
| 同上 | `KanHomotopy.map_eq_of_basedHomotopy` | 全次数のホモトピー不変性 |

L9b の公開入口は `FibrationSequence.lean`。fiber と連結射の実構成は
`FibrationBoundary.lean`、完全性は `FibrationExactness.lean`、自然性は
`FibrationNaturality.lean`、群準同型性は `FibrationMultiplication.lean` に分ける。

| 宣言 | 内容 |
| --- | --- |
| `fibration_pullback_snd` | ホーンの RLP による fibration の引き戻し閉性 |
| `KanFiber`、`fiberι`、`fiberPoint` | 点からの実際の引き戻しとその基点 |
| `fiberLift`、`fiber_hom_ext` | fiber の普遍性 |
| `BoundaryLift`、`boundaryLift_nonempty` | 定数ホーンの相対持ち上げの存在 |
| `BoundaryLift.boundary` | 最後の面を fiber の代表へ送る |
| `BoundaryLiftComparison.rel` | 二つの持ち上げの境界を fiber 内の RelStruct で結ぶ |
| `BoundaryLift.boundary_class_eq` | 持ち上げの選択独立性 |
| `BoundaryLift.transport` | 底の RelStruct に沿う境界保存の持ち上げ |
| `connecting` | π_(n+1)(B) → π_n(fiber) の商上の写像 |
| `connecting_eq` | 任意の持ち上げによる連結写像の計算 |
| `connecting_one` | 連結写像の基点保存 |
| `fiber_map_connecting` | 包含の誘導写像と連結射の合成は基点に定数 |
| `connecting_map` | 射影の誘導写像と連結射の合成は基点に定数 |

L9b の追加の公開宣言：

| 宣言 | 内容 |
| --- | --- |
| `ZeroRelations.symm`、`trans` | 二次元ホーンから零次数の関係の対称性・推移性 |
| `KanHomotopyZero.mk_eq_iff` | 零次数でも単一の RelStruct₀ で商の等式を検出 |
| `KanHomotopy.mk_eq_iff_relStruct` | 全自然数次数で商の等式と RelStruct の存在の同値 |
| `exact_connecting_fiber_all` | fiber の零次数を含む全次数の完全性 |
| `exact_fiber_total_all` | 全空間の零次数を含む全次数の完全性 |
| `exact_total_base_all` | 底の全正次数の完全性、π₁(B) → π₀(fiber) を含む |
| `FibrationSquare.fiberMap` | 可換四角形から fiber 列の射を作る |
| `FibrationSquare.connecting_natural` | 全次数の連結写像の自然性 |
| `ConnectingProduct.exists_product_lift` | fiber の積を境界に持つ相対持ち上げ |
| `connecting_mul` | 標的が正次数の連結写像の積保存 |
| `connectingHom` | π_(n+2)(B) → π_(n+1)(fiber) の群準同型 |
| `fiberLongExact` | 零次数を含む全箇所の完全性の集約定理 |

原像は零ホモトピーの相対充填によって実際に構成する。
群の法則、完全性、自然性を入力構造に移していない。
L9b の完了は、Kan fibration の具体的な fiber 列のホモトピー長完全列の完成を意味する。
スペクトルの fiber 列への昇格は L9c の工程であり、まだ主張しない。

`KanHomotopy X (n + 1) x` は群、`KanHomotopy X (n + 2) x` は可換群。
正次数の群準同型としての界面は `KanHomotopyGroup.map`。
零次数には群を付けない。
相対ホモトピーから類の等式への向きと、任意の面添字の RelStruct との比較を証明済み。
一般の相対写像のホモトピー類との圏論的同定はここでは主張しない。

検証コマンド：

```sh
set -o pipefail
lake build SerrePositivity.KST.Spectra
lake env lean scripts/audit_kst_spectra.lean
```

L9a 保存時の結果：対象ビルド成功。監査は私有宣言を含め 367 宣言、5 モジュールで標準三公理のみ。
L9b の連結写像の保存時：対象ビルド成功。476 宣言、6 モジュールで標準三公理のみ。
L9b の正次数の完全性の保存時：対象ビルド成功。517 宣言、7 モジュールで標準三公理のみ。
L9b 完了時：対象ビルド成功。631 宣言、11 モジュールで標準三公理のみ。
工程区切りの全体ビルドも終了コード 0、8370 jobs で成功。
ルートには指定の public import 一行を追加済み。
ルートは他レーンの未コミット変更を含むので、この保存ではコミット対象から外す。

## 17. 公開時の注意

工程の部分成果を全工程の完了として報告しない。
構造の定義だけを存在証明として報告しない。
入力された法則を証明したと報告しない。
有理化は実際の π_* の計算まで必要。
局所 Kan 性は γ1 の実質的な適用条件である。
π_* の長完全列は実際の連結射を伴う。
共有 import の破損時は依存箇所とエラーを報告する。
設計変更の提案時は変更箇所と理由を明記する。
通常の工程報告後は承認を待たず次の工程へ進む。

## 18. L9c の改訂仕様（ユーザー承認済み）

2026-10-18 のユーザー承認により §11 の BF cofibrant–fibrant 方式を採用した。
厳密な Ω 同型の仕様は置き換える。
全基点での π_* 同型、構造写像の単射性、Hom の塔の引き戻し表示を同時に保持する。
これらの条件を追加公理にせず、必要な存在・置換・充填を実証する。
π_j(X) は k ≥ −j に対する π_(j+k)(X_k) とし、段の選択独立性を証明する。
零次数が群となる点もループ構造と比較して証明する。

参照：

- Bousfield–Friedlander, *Homotopy theory of Γ-spaces, spectra, and bisimplicial sets*
  (1978), §2。安定モデル構造の cofibrant–fibrant モデル。
- [HTT](https://www.math.ias.edu/~lurie/papers/HTT.pdf), A.3.3。単体的図式のモデルと写像空間。
- [HA](https://www.math.ias.edu/~lurie/papers/HA.pdf), §1.4.2 と Proposition 1.4.3.6 の証明。
- [Kerodon の塔の補題](https://kerodon.net/tag/0194), Corollary 11.9.7.2
  （retired subsection の現行番号）。
- Mathlib `AnodyneExtensions/PushoutProduct.lean`, `fibration_pullbackObjObjπ`。
- Mathlib `Skeleton.lean`, `relativeCellComplexOfMono`。
- 既存 `HomotopicalAlgebra/Simplicial/AnodyneKanReplacement.lean`。

γ1 による quasicategory 性と、導来写像空間を持つ正しい Sp との比較を区別する。
後者は γ3 後の工程であり、第 1 段の主張には含めない。
HT-KQ は使わない。共有正本 §13-3 はユーザーが更新する。

## 19. L9c の写像空間の相対充填

`PointedMapping.lean` に次の補題を証明済み。

| 主要宣言 | 内容 |
| --- | --- |
| `PointedMapping.basepoint_mono` | 基点包含は単射 |
| `PointedMapping.restriction_fibration` | Kan な標的への指数の基点制限は fibration |
| `PointedMapping.basedHom_kanComplex` | 点つき Hom の Kan 性 |
| `PointedMapping.pre_restriction` | 点つき射の制限と基点評価の可換性 |
| `PointedMapping.pre` | 源に沿う点つき Hom の制限 |
| `PointedMapping.pre_hasLiftingProperty` | 基礎指数から点つき Hom への相対充填の移送 |
| `PointedMapping.pre_fibration` | 単射に沿う点つき Hom の制限は Kan fibration |

源の Kan 性や Ω 条件を用いず、指数版 pushout-product から証明した。
既存 Spectra の点つき対象と等化子の基礎定義のみを借りる。
既存の安定モデル構造の定理は import していない。
保存単位の検証：対象ビルド 1522 jobs 成功。
私有宣言を含む 12 モジュール 644 宣言で標準三公理のみ。
L9c 全体は未完了。次は fibration の塔の極限への相対充填を構成する。

## 20. L9c の塔の極限

`FibrationTower.lean` に自然数で添字づけた逆向きの塔の極限を構成した。
各次数の単体は、隣接段の遷移と整合する元の族である。
一般の厳密極限の Kan 性を仮定していない。

| 主要宣言 | 内容 |
| --- | --- |
| `FibrationTower.limit` | 次数ごとの整合族による単体集合 |
| `FibrationTower.projection` | 各段への自然な射影 |
| `FibrationTower.lift` | 整合する射の族の普遍的持ち上げ |
| `FibrationTower.hom_ext` | 射影による射の一意性 |
| `FibrationTower.stages` | 初段の指定充填からの帰納的な相対充填 |
| `FibrationTower.stages_comp` | 帰納的充填の遷移との整合性 |
| `FibrationTower.projection_zero_hasLiftingProperty` | 右持ち上げ性の初段射影への移送 |
| `FibrationTower.projection_zero_fibration` | fibration の塔の初段射影は fibration |
| `FibrationTower.limit_kanComplex` | 初段 Kan・遷移 fibration の塔の極限は Kan |

参照：Kerodon Corollary 11.9.7.2、HTT A.3.3、BF 1978 §2。
保存単位の対象ビルド 1523 jobs 成功。
私有宣言を含む 13 モジュール 672 宣言で標準三公理のみ。
L9c 全体は未完了。次は切断スペクトルの Hom の塔を実装する。

## 21. L9c の切断写像空間の構成部品

`TruncatedMapping.lean` に境界比較射を持つ点つき写像空間の塔を構成した。
これは具体的な単体集合の射 `step` に対する一般構成である。
スペクトルの suspension が誘導する `step` の実装は次の工程に残る。
一般構成をもってスペクトルの写像空間の実装完了とはしない。

| 主要宣言 | 内容 |
| --- | --- |
| `TruncatedMapping.stage` | 切断写像空間と最終段の評価を同時に帰納構成 |
| `TruncatedMapping.space` | 切断写像空間の基礎単体集合 |
| `TruncatedMapping.evaluation` | 最終段への評価 |
| `TruncatedMapping.restriction` | 引き戻しの第二射影による遷移 |
| `TruncatedMapping.evaluation_condition` | 境界比較との整合条件 |
| `TruncatedMapping.restriction_fibration` | 単射の制限を引き戻した遷移の fibration 性 |
| `TruncatedMapping.total` | 全切断の整合族の単体集合 |
| `TruncatedMapping.total_projection_fibration` | 初段への射影の fibration 性 |
| `TruncatedMapping.total_kanComplex` | 源の構造単射・標的各段 Kan による極限の Kan 性 |

参照：BF 1978 §2、HTT A.3.3。
保存単位の対象ビルド 1524 jobs 成功。
私有宣言を含む 14 モジュール 688 宣言で標準三公理のみ。
次は suspension・loop の随伴と、実際のスペクトルからの境界比較射を実装する。

## 22. L9c の Ω スペクトルの対象と具体的写像空間

`SuspensionLoop.lean` に円との smash、円からの内部 Hom と随伴を接続した。
`HomotopyIsomorphism.lean` に全基点での π_* 同型を全単射性の述語として定義した。
この述語は既に構成したホモトピー群の誘導写像に関する条件である。
`OmegaSpectrum.lean` の対象は、各段 Kan・構造射単射・随伴構造射 π_* 同型を保持する。
構造射から具体的な `mappingStep` を構成し、切断写像空間の一般構成に代入した。
この写像空間の Kan 性まで証明済み。

| 主要宣言 | 内容 |
| --- | --- |
| `suspension` | 単体的円との reduced smash |
| `loopSpace` | 単体的円からの点つき内部 Hom |
| `loopSpace_kanComplex` | Kan な標的の loop は Kan |
| `suspensionLoopEquiv` | suspension・loop の通常の Hom 随伴 |
| `suspensionHom` | suspension が誘導する写像空間の射 |
| `suspensionHom_curry'` | 通常の射への suspension の作用との一致 |
| `KanPiIsomorphism` | 全基点・全自然数次数の π_* 同型という条件 |
| `KanPiIsomorphism.id` / `.comp` | 恒等・合成に関する閉性 |
| `PointedKanComplex` | 点つき Kan 複体 |
| `OmegaSpectrum` | 承認済み BF 方式の対象 |
| `OmegaSpectrum.mappingStep` | 実際の構造射からの境界比較 |
| `OmegaSpectrum.truncatedHom` | 切断写像空間 |
| `OmegaSpectrum.mappingSpace` | 全切断の整合族 |
| `OmegaSpectrum.mappingSpace_kanComplex` | 構成した写像空間の Kan 性 |
| `TruncatedMapping.totalEvaluation_condition` | 各段の評価の厳密な境界整合性 |

参照：BF 1978 §2、HTT A.3.3、HA §1.4.2。
保存単位の対象ビルド 1556 jobs 成功。
私有宣言を含む 17 モジュール 747 宣言で標準三公理のみ。
既存 Spectra の通常の圏論的な円・smash・内部 Hom の構成を借りている。
安定モデル構造や HT-KQ は import していない。
未完了：厳密なスペクトルの射との同定、厳密合成、単体的圏、coherent nerve。
未完了：loop のホモトピー群の次数移動、整数次数 π_*、段の選択独立性。
未完了：置換補題、スペクトルの fiber 列と長完全列、L9d・L9e。
次は構成した写像空間の各段評価と通常の点つき射との比較を証明する。

## 23. L9c の厳密射と写像空間の零次単体

等化子で構成した源の制限と、点つき閉構造から得る pre が一致することを証明した。
随伴を構成する Hom 同値は命題として比較し、定義的な一致を仮定しない。
切断写像空間の極限へ整合族を持ち上げる普遍性を任意の単体集合パラメータで証明した。
全段への評価による極限への射の一意性も証明済み。
厳密可換なスペクトルの射を定義し、段ごとの合成で通常の圏を構成した。
その射と構成済みの Kan 写像空間の零次単体を実際の同値で比較した。

| 主要宣言 | 内容 |
| --- | --- |
| `PointedMapping.prePointed` | 源の制限を点つき射として扱う |
| `PointedMapping.smashCurry_pre` | smash 第一変数と源の制限の随伴の自然性 |
| `PointedMapping.prePointed_eq_closedPre` | 等化子の制限と閉構造の pre の一致 |
| `PointedMapping.curry'_pre` | 頂点表示への源の制限の作用 |
| `TruncatedMapping.familyStage` | 整合族の切断への持ち上げ |
| `TruncatedMapping.familyLift` | 任意のパラメータから極限への持ち上げ |
| `TruncatedMapping.familyLift_evaluation` | 持ち上げの評価の計算 |
| `TruncatedMapping.total_hom_ext` | 全段評価による極限への射の一意性 |
| `pointedHomVertexEquiv` | 点つき射と点つき内部 Hom の頂点の同値 |
| `OmegaSpectrum.Hom` | 構造射と厳密可換な点つき射の族 |
| `OmegaSpectrum.category` | 段ごとの合成による通常の圏 |
| `OmegaSpectrum.evaluation` | 写像空間から段ごとの Hom への評価 |
| `OmegaSpectrum.mappingStep_vertex` | 境界比較の頂点への作用 |
| `OmegaSpectrum.homOfVertex` | 写像空間の頂点から厳密な射を復元 |
| `OmegaSpectrum.vertexOfHom` | 厳密な射を整合族の頂点へ移す |
| `OmegaSpectrum.vertex_ext` | 全段評価による頂点の一意性 |
| `OmegaSpectrum.homVertexEquiv` | 厳密な射と写像空間の零次単体の同値 |

参照：BF 1978 §2、HTT A.3.3。
保存単位の対象ビルド 1561 jobs 成功。
私有宣言を含む 21 モジュール 821 宣言で標準三公理のみ。
未完了：単体的合成の極限への持ち上げと単位律・結合律、γ1 の適用。
整数次数群・置換・fiber 列・有理化・hG・Tot は引き続き未完了。
次は各段の点つき Hom の単体的合成を構成し、極限の普遍性で写像空間へ持ち上げる。

## 24. L9c の各段の単体的合成と suspension の豊穣性

点つき閉 smash の自己豊穣を、忘却の lax monoidal 関手で単体的豊穣へ移した。
その Hom と零次単体の同値は既存の等化子・頂点表示と一致する。
源と標的への豊穣作用を、相対充填に使った pre と後合成に比較した。
左テンソルの写像対象への作用が豊穣合成を保つことを一般の閉モノイダル圏で証明した。
これを suspension に特殊化し、単体的豊穣関手として構成した。
構造射と整合する二つのパラメータ付き写像の合成の整合性も一般に証明した。

| 主要宣言 | 内容 |
| --- | --- |
| `PointedEnrichment.simplicialCategory` | 点つき単体集合の単体的圏 |
| `PointedEnrichment.hom_eq` | 等化子による Hom との一致 |
| `PointedEnrichment.vertexEquiv_eq` | 点つき射と頂点の同値との一致 |
| `PointedEnrichment.whiskerRight_eq` / `.whiskerLeft_eq` | 源と標的への作用の比較 |
| `TensorMapping.map` | 一般の閉モノイダル圏での左テンソルの写像対象への作用 |
| `TensorMapping.comp` | 一般の左テンソルの豊穣合成保存 |
| `suspensionHom_id` / `suspensionHom_comp` | 点つき豊穣の単位・合成の保存 |
| `suspensionHom_simplicial_comp` | 単体的豊穣の合成保存 |
| `suspensionEnrichedFunctor` | 単体的豊穣関手としての suspension |
| `enriched_comp_middle` | 中間の射の前合成と後合成の整合性 |
| `enriched_compatible_comp` | 構造射との整合条件の合成に関する閉性 |

参照：BF 1978 §2、HTT A.3.3。
保存単位の対象ビルド 1573 jobs 成功。
私有宣言を含む 25 モジュール 844 宣言で標準三公理のみ。
次はこの合成の整合性をスペクトルの評価族へ適用し、極限へ合成を持ち上げる。
スペクトルの単体的圏と coherent nerve の構成は引き続き未完了。

## 25. L9c の局所 Kan な単体的圏と coherent nerve

各段の単体的合成を切断写像空間の極限へ持ち上げた。
構造整合性は豊穣関手としての suspension と中間の射の移動から証明した。
全段評価による外延性で単位律と結合律を証明した。
通常の厳密な射の恒等・合成との比較を行い、単体的圏に束ねた。
構成済みの Kan 写像空間に N レーンの γ1 を適用した。
`Sp := SimplicialNerve OmegaSpectrum` の quasicategory 性を証明済み。

| 主要宣言 | 内容 |
| --- | --- |
| `OmegaSpectrum.compositionFamily` | 各段評価後の単体的合成 |
| `OmegaSpectrum.compositionFamily_condition` | 合成の構造射との整合性 |
| `OmegaSpectrum.mappingComposition` | 極限へ持ち上げた合成 |
| `OmegaSpectrum.mappingComposition_evaluation` | 合成の各段評価 |
| `OmegaSpectrum.mappingIdentity` | 恒等射の終対象パラメータによる単位 |
| `OmegaSpectrum.mappingIdentity_evaluation` | 単位の各段評価 |
| `OmegaSpectrum.mappingIdentity_comp` / `.mappingComposition_identity` | 左右の単位律 |
| `OmegaSpectrum.mappingComposition_assoc` | 結合律 |
| `OmegaSpectrum.vertexOfHomMap_comp` | 通常の合成と単体的合成の一致 |
| `OmegaSpectrum.mappingEnrichedCategory` | 単体集合に豊穣化した圏 |
| `OmegaSpectrum.simplicialCategory` | 通常の射と接続した単体的圏 |
| `Sp` | BF 方式の Ω スペクトルの coherent nerve |
| `sp_quasicategory` | γ1 による quasicategory 性 |

参照：BF 1978 §2、HTT A.3.3、HTT 1.1.5.10、Kerodon 2.4.5.1、HA §1.4.2。
保存単位の対象ビルド 1618 jobs 成功。
私有宣言を含む 29 モジュール 876 宣言で標準三公理のみ。
Sp の構成の区切りで全体ビルドも実行したが終了コード 1。
L9 の import 閉包外の `InfinityCategories/F1.lean:1` で
`F1/CoherentOrderDiagrams.olean` が見つからないというエラーだった。
他レーンを編集せず、L9 自身の対象ビルド成功と区別して記録する。
導来写像空間を持つ正しい Sp との比較は主張しない。これは γ3 後の工程。
未完了：loop のホモトピー群の次数移動、整数次数 π_* と段の選択独立性。
未完了：cofibrant・Kan 置換、スペクトルの fiber 列と長完全列。
L9d の telescope 有理化、L9e の hG・Tot・有理 Shapiro も未完了。
次は path space の fiber 列と収縮から loop の次数移動を証明する。

## 26. L9c の path fibration の構成

始点を基点とする区間と、零次球面からの終点包含を構成した。
終点包含の単射性は、各次数の自由基点の二成分の像を頂点値で比較して証明した。
区間からの点つき Hom を path space とし、終点の制限と閉構造の単位同型を合成した。
標的が Kan のとき終点評価は Kan fibration である。

| 主要宣言 | 内容 |
| --- | --- |
| `pointedInterval` | 始点を基点とする Δ[1] |
| `intervalEndpoint` | 点つき零次球面からの終点包含 |
| `coprod_simplex_cases` | 余積の単体の二成分への分解 |
| `intervalEndpoint_mono` | 終点包含の単射性 |
| `basedPathSpace` | 基点に始まる path の単体集合 |
| `basedPathSpace_kanComplex` | Kan 標的の path space の Kan 性 |
| `pathEndpoint` | 終点評価 |
| `pathEndpoint_fibration` | 終点評価の Kan fibration 性 |

参照：Goerss–Jardine I §7、Kerodon §§3.1.3、3.2.5。
保存単位の対象ビルド 1620 jobs 成功。
私有宣言を含む 31 モジュール 895 宣言で標準三公理のみ。
未完了：path space の収縮、終点 fiber と loopSpace の同定、次数移動の同型。
次は既存 Core の標準単体の先頭頂点への収縮を借りて path space を収縮する。
§25 の対象ビルドの jobs 数はログの実数 1618 に訂正した。

## 27. L9c の path space の基点固定収縮

任意の単体集合パラメータから点つき Hom への curry を等化子で構成した。
Core の区間の先頭頂点への収縮を借り、全時刻で基点を固定することを検査した。
path の区間変数を収縮する再パラメータ付けと評価を合成した。
これを curry して path space の収縮を作った。
時刻零が定数 path、時刻一が恒等射、全時刻で定数 path の基点を固定する。
基点生成部分複体に相対的なホモトピーに移し、全自然数次数のホモトピー類を消去した。

| 主要宣言 | 内容 |
| --- | --- |
| `PointedMapping.paramCurry` | 基点を保つパラメータ付き写像族の curry |
| `PointedMapping.uncurry_basepoint` | 評価の源の基点での定数性 |
| `PointedMapping.uncurry_parameter_basepoint` | 定数写像のパラメータ上の評価 |
| `intervalContractionMap` / `intervalContraction` | 区間の基点固定収縮 |
| `intervalContraction_zero` / `.intervalContraction_one` | 区間の収縮の端点 |
| `pathReparametrization` | path の区間変数の収縮 |
| `pathEvaluation` | curry 前の path の評価 |
| `pathContractionBody` | 再パラメータ付けした評価族 |
| `pathContraction` | path space の収縮写像 |
| `pathContraction_zero` / `.pathContraction_one` | path space の収縮の端点 |
| `pathContraction_constant` | 定数 path の基点の固定 |
| `KanHomotopy.map_const` | 定数射の全次数の誘導写像 |
| `pathContraction_basedHomotopy` | 基点生成部分複体に相対的な収縮 |
| `basedPathSpace_homotopy_eq_point` | 全自然数次数のホモトピー類の自明性 |
| `basedPathSpace_homotopy_subsingleton` | 零次数を含む一元性 |

参照：Goerss–Jardine I §7、Kerodon §3.2.5、HTT A.3.3。
保存単位の対象ビルド 1643 jobs 成功。
私有宣言を含む 38 モジュール 943 宣言で標準三公理のみ。
未完了：終点 fiber と loopSpace の同定、次数移動の同型、整数次数群と段の独立性。
次は終点 fiber を円からの点つき Hom に同定する。

## 28. L9c の loop と path 終点 fiber の同定

区間の境界を、終点と始点の余積と全単体次数で同定した。
二端点を潰した cofiber と標準の単体的円の点つき同型を構成した。
一般の点つき射の基礎 cofiber が点つき pushout になることを証明した。
内部 Hom の反変関手の極限保存と基点忘却の右随伴性から、Hom の pullback を得た。
零対象からの Hom の終対象性と、単位からの Hom の同型を使って path の終点 fiber に移した。
円からの点つき Hom とこの fiber は実際の単体集合として同型である。
L9b の fiberPoint を用いる形への基点の移送も行い、定数 loop の基点保存を証明した。

| 主要宣言 | 内容 |
| --- | --- |
| `intervalBoundaryMap` | 二端点の余積から境界への自然な射 |
| `intervalBoundaryMap_isIso` | 全次数の単射・全射性による同型性 |
| `endpointCircleIso` | 二端点の商と標準の円の点つき同型 |
| `pointedCofiberProjection` / `.pointedCofiberDesc` | 点つき商と降下 |
| `pointedCofiber_isPushout` | 点つき cofiber の pushout 表示 |
| `cofiberMappingFunctor_preservesLimitsOfShape` | 反変 Hom の極限保存 |
| `cofiberMapping_isPullback` | cofiber からの Hom の pullback 表示 |
| `homPointIsTerminal` | 零対象からの点つき Hom の終対象性 |
| `endpointCircleMapping_isPullback` | path の終点評価の基点上の pullback |
| `loopPathFiberIso` | loop と基点上の path fiber の同型 |
| `fiberIsoOfEq` | fiber の基点の等式による移送 |
| `loopBasedPathFiberIso` | L9b の fiber と一致する形の同型 |
| `loopBasedPathFiberIso_basepoint` | 定数 loop と fiberPoint の基点の一致 |

参照：Goerss–Jardine I §7、Kerodon §3.2.5、HTT A.3.3。
保存単位の対象ビルド 1648 jobs 成功。
私有宣言を含む 43 モジュール 1023 宣言で標準三公理のみ。
次は構成済みの path fiber 列と収縮から連結射の全単射性と loop の次数移動を導く。
整数次数群・段の選択独立性・置換とスペクトルの fiber 列は未完了。

## 29. L9c の正次数の loop 同型と段の比較

単体集合の同型と全基点 π_* 同型から、指定基点の群同型を作る界面を構成した。
全空間の隣接二次数の群が自明な場合、長完全列から連結準同型の全単射性を導いた。
これを path fibration に適用し、正次数の loop の次数移動を群同型として証明した。
Ω 条件の随伴構造射の群同型と合成し、スペクトルの隣接段の正次数の比較を得た。
次段の二以上の次数へ移すことで、各段の一次も含む全ての正次数の群の可換性を得た。
元の群演算を保持し、可換群構造を付けた。

| 主要宣言 | 内容 |
| --- | --- |
| `KanHomotopy.equivOfIso` | 零次数を含む同型によるホモトピー類の同値 |
| `KanHomotopyGroup.equivOfIso` | 指定基点の正次数の群同型 |
| `KanHomotopyGroup.equivOfPiIsomorphism` | 全基点 π_* 同型からの群同型 |
| `connectingHom_bijective_of_total_subsingleton` | 長完全列による連結準同型の全単射性 |
| `connectingHomEquivOfTotalSubsingleton` | 連結準同型による群同型 |
| `loopPositiveHomotopyEquiv` | π_(n+1)(ΩY) ≃ π_(n+2)(Y) |
| `OmegaSpectrum.positiveTransition` | π_(n+1)(X_k) ≃ π_(n+2)(X_(k+1)) |
| `OmegaSpectrum.levelHomotopy_mul_comm` | 各段の一次を含む正次数の可換性 |
| `OmegaSpectrum.levelHomotopyCommGroup` | 元の演算による可換群構造 |

参照：Goerss–Jardine I §7、Kerodon §3.2.5、BF 1978 §2、HA §1.4.2。
保存単位の対象ビルド 1652 jobs 成功。
私有宣言を含む 47 モジュール 1050 宣言で標準三公理のみ。
零次数の loop 比較はまだ未完了。正次数の核と像だけから零次数の全単射性を推論しない。
次は path space の全境界充填から零次数の連結写像の単射性も幾何的に証明する。

## 30. L9c の零次数・整数次数と群への関手

区間の始点の包含が anodyne であることをホーンから証明した。
pushout product の持ち上げ対応により、path space の終対象への射は全単射に対して RLP を持つ。
全境界を面の余等化子として貼り合わせ、指定された全ての面を持つ単体を構成した。
零次数の連結写像の像が等しい場合、二つの境界持ち上げと fiber の道を三角形の全境界に貼る。
その充填から基底の一次の類の等しさを得て、零次数の連結写像の単射性を証明した。
長完全列の全射性と合わせ、π₀(ΩY) ≃ π₁(Y) を得た。
定数 loop は単位へ移ることも証明した。
Ω 条件と合成し、スペクトルの各段の零次数にも可換群構造を移した。
隣接段の比較はこれで全自然数次数で群同型となった。
整数次数 j の標準段を |j|+1 とし、隣接比較の反復で任意の k≥−j の表示との群同型を構成した。
標準段の正次数の誘導準同型から、整数次数ごとに可換群への関手を構成した。
段の比較の合成整合性と射に関する自然性は引き続き証明する。

| 主要宣言 | 内容 |
| --- | --- |
| `pointedInterval_basepoint_anodyne` | 区間の始点の anodyne 包含 |
| `basedHom_terminal_rlp_monomorphisms` | anodyne 源の点つき Hom の全境界充填 |
| `BoundaryFaces.isColimit` / `.desc` | 全境界の面の貼り合わせ |
| `BoundaryFaces.exists_filler` | 全境界 RLP による指定面の充填 |
| `connecting_zero_injective` | 零次数の連結写像の単射性 |
| `loopZeroHomotopyEquiv` | π₀(ΩY) ≃ π₁(Y) |
| `loopHomotopyEquiv` | 全自然数次数の loop 比較 |
| `OmegaSpectrum.zeroTransition` | 零次数から次段の一次への群同型 |
| `OmegaSpectrum.levelNaturalCommGroup` | 各段の零次数を含む可換群構造 |
| `OmegaSpectrum.transition` | 全次数の隣接段の群同型 |
| `OmegaSpectrum.iterateTransition` / `.compareLevels` | 隣接比較の反復と共通段での比較 |
| `OmegaSpectrum.homotopyGroup` / `.homotopyGroupEquivAt` | 整数次数の群と任意の許される段での計算 |
| `OmegaSpectrum.homotopyFunctor` | Ω スペクトルから可換群への関手 |

参照：Goerss–Jardine I §7、Kerodon §3.2.5、BF 1978 §2、HA §1.4.2。
保存単位の対象ビルド 1665 jobs 成功。
私有宣言を含む 56 モジュール 1166 宣言で標準三公理のみ。
L9c は未完了。置換、スペクトルの fiber 列と長完全列が残る。

## 31. L9c の π_* 同型と置換の基礎補題

整数次数の π_* 同型の性質を構成済みの群準同型の全単射性として定義した。
各段の全基点 π_* 同型から整数次数の π_* 同型が従うことを証明した。
基点固定ホモトピーの相対表示と、点つき射の全自然数次数の誘導写像を整理した。
各段の基点固定ホモトピーから整数次数の準同型の等式を得た。
全ての単射に対する RLP を持つ射では、基点を保つ切断と垂直ホモトピーを実際に充填した。
anodyne な射では Kan な源へのレトラクションと、包含上で固定されたホモトピーを充填した。
両端が Kan の場合、それぞれ全基点 π_* 同型であることを L9 のホモトピー類で証明した。
ホーンの Kan 置換を点つき関手と自然な単位に拡張した。
元の対象が Kan ならその単位は全基点 π_* 同型である。
境界の小対象論法による分解も点つき対象に移した。
標的が Kan なら中間対象は Kan、左因子は単射、右因子は全基点 π_* 同型である。
これは置換の各段に用いる基礎補題であり、スペクトル全体の置換はまだ構成していない。
coherent nerve の導来写像空間との比較は引き続き γ3 後に扱う。

| 主要宣言 | 内容 |
| --- | --- |
| `OmegaSpectrum.PiIsomorphism` | 全整数次数の誘導準同型の全単射性 |
| `OmegaSpectrum.PiIsomorphism.groupEquiv` | その各次数の群同型 |
| `OmegaSpectrum.piIsomorphism_of_levelwise` | 各段の π_* 同型からの帰結 |
| `pointedRelativeHomotopy` | 全区間の基点固定式から相対ホモトピーへ |
| `OmegaSpectrum.homotopyMap_eq_of_levelHomotopy` | 各段の基点固定ホモトピーによる不変性 |
| `kanPiIsomorphism_of_monoRight` | 全ての単射への RLP から全基点 π_* 同型 |
| `kanPiIsomorphism_of_anodyne` | Kan 複体間の anodyne 射の全基点 π_* 同型 |
| `PointedKanReplacement.functor` / `.unit` | 点つき Kan 置換と自然な比較射 |
| `PointedKanReplacement.obj_kanComplex` | 置換の値の Kan 性 |
| `PointedKanReplacement.unit_piIsomorphism` | 元が Kan の場合の単位の π_* 保存 |
| `PointedFactorization.middle` / `.left` / `.right` | 点つき射の境界による分解 |
| `PointedFactorization.right_rlp` | 右因子の全ての単射への RLP |
| `PointedFactorization.middle_kanComplex` | 標的が Kan の場合の中間対象の Kan 性 |
| `PointedFactorization.right_piIsomorphism` | 右因子の全基点 π_* 同型性 |

参照：Goerss–Jardine I §7、Kerodon §3.2.1、BF 1978 §2、HTT A.3.3、HA §1.4.2。
保存単位の対象ビルド 1832 jobs 成功。
私有宣言を含む 62 モジュール 1221 宣言で標準三公理のみ。
L9c は未完了。段の比較の整合性、列全体の置換、スペクトルの fiber 列と長完全列が残る。

## 32. L9c の Kan Ω 列の cofibrant 置換

構造射に単射性を要求しない `KanSequence` と、その随伴構造射による Ω 条件を定義した。
厳密な列の射は随伴構造射に関しても可換であることを証明した。
零段を元の段とし、各後続段で前段の比較射を suspension して元の構造射と合成する。
その射の境界の小対象論法による分解を取り、中間対象を次の段、左因子を新しい構造射とした。
写像柱に続けて単射化する代わりに、同じ BF の単射条件を境界 cell 分解で直接実現した。
対象と Hom と Ω 条件の承認済み仕様に変更はない。
元の標的段が Kan なので各中間段も Kan、各比較射は全ての単射への RLP を持つ。
比較射は全基点 π_* 同型である。
点つき Hom の後合成も全ての単射への RLP を保つことを相対積の充填から証明した。
したがって比較射を loop に移しても全基点 π_* 同型である。
随伴構造射の可換正方形と後の射の打ち消しから、置換した列の Ω 条件を証明した。
構造射が単射でない Kan Ω 列から、承認済みの BF 対象への実際の置換が得られた。
元がすでに Ω スペクトルの場合は厳密な比較射をスペクトルの射として束ねた。
その比較射の全整数次数の π_* 同型性を証明した。
また、L9b の fiber に点つき構造を付け、点つき包含と普遍的な持ち上げを構成した。
スペクトルの fiber 列の Ω 条件と整数次数長完全列はまだ未完了。
Kan でない列全体の fibrant 置換の構造射への接続も未完了。

| 主要宣言 | 内容 |
| --- | --- |
| `KanSequence` / `.OmegaCondition` | 単射性を要求しない Kan 列と Ω 条件 |
| `KanSequence.replacementStage` | 境界 cell 分解による各段の帰納構成 |
| `KanSequence.cofibrantReplacement` | 構造射が単射な Kan 列への置換 |
| `KanSequence.replacementProjection` | 元の列への厳密な比較射 |
| `KanSequence.replacementProjection_piIsomorphism` | 各段の全基点 π_* 同型 |
| `PointedMapping.post_rlp_monomorphisms` | 点つき Hom の後合成による RLP 保存 |
| `KanPiIsomorphism.of_comp` | 後の π_* 同型の打ち消し |
| `KanSequence.Hom.adjoint_comm` | 随伴構造射に関する可換性 |
| `KanSequence.Hom.omegaCondition_of_target` | RLP 比較射による Ω 条件の移送 |
| `KanSequence.cofibrantOmegaSpectrum` | Kan Ω 列から BF 対象への置換 |
| `OmegaSpectrum.cofibrantProjection_piIsomorphism` | 置換比較の全整数次数の π_* 同型 |
| `pointedFiber` / `pointedFiberι` / `pointedFiberLift` | 点つき fiber と普遍性 |

参照：Goerss–Jardine I §7、BF 1978 §2、HTT A.3.3、HA §1.4.2。
保存単位の対象ビルド 1840 jobs 成功。
私有宣言を含む 67 モジュール 1320 宣言で標準三公理のみ。
L9c は未完了。次は段ごとの fiber を列にして Ω 条件と長完全列へ接続する。

## 33. L9c の fiber の Kan 列と正次数の比較

点つき fiber の包含と元の射の合成が零射であることを証明した。
零合成からの点つき持ち上げを用意し、suspension が零射を保つことを左随伴性から得た。
各段が Kan fibration である列の射について、各段の fiber の suspension 構造射を構成した。
各 fiber は Kan なので、単射性と Ω 条件をまだ要求しない Kan 列を得た。
包含は列の厳密な射である。
さらに、可換性を要求しない群の二つの完全な五項列について五項補題を証明した。
全空間と底の全基点 π_* 同型を、L9b の自然な長完全列の五項へ適用した。
その結果、fiber 間の誘導写像は全ての正次数で全単射であることを証明した。
零次数の fiber の比較は未完了であり、正次数の五項補題からは推論しない。
fiber の Ω 条件と整数次数長完全列もまだ完了扱いにしない。

| 主要宣言 | 内容 |
| --- | --- |
| `pointedFiberι_comp` | fiber 包含と元の射の零合成 |
| `pointedFiberLiftOfZero` | 零合成から点つき fiber への持ち上げ |
| `KanSequence.Hom.fiberSigma` | fiber の suspension 構造射 |
| `KanSequence.Hom.fiber` | 各段の fiber を束ねた Kan 列 |
| `KanSequence.Hom.fiberInclusion` | 全空間の列への厳密な包含 |
| `group_five_lemma` | 非可換群でも有効な五項補題 |
| `KanHomotopyGroup.map_square` | 基点を明示した群の可換正方形 |
| `FibrationSquare.fiberMap_positive_bijective` | 全空間・底の π_* 同型から fiber の正次数の全単射 |

参照：Goerss–Jardine I §§7–8、Kerodon §3.2.6、BF 1978 §2、HA §1.4.2。
保存単位の対象ビルド 1844 jobs 成功。
私有宣言を含む 71 モジュール 1341 宣言で標準三公理のみ。

## 34. L9c の段の比較の合成整合性

整数次数 j の許される最小段を (−j).toNat とした。
その段から各段への隣接比較の反復を共通の源とし、各段同士の比較を定義した。
標準の計算段 |j|+1 と整数次数群の定義は変わらない。
比較の恒等法則、逆法則、三段の合成法則を証明した。
整数次数群から任意段への表示も、この合成法則を満たす。
射に関する自然性と隣接構造射との計算式は引き続き扱う。

| 主要宣言 | 内容 |
| --- | --- |
| `OmegaSpectrum.initialLevel` | 最小の許される計算段 |
| `OmegaSpectrum.initialLevel_admissible` / `.initialLevel_le` | 非負次数と最小性 |
| `OmegaSpectrum.compareLevels_refl` | 同じ段の比較は恒等 |
| `OmegaSpectrum.compareLevels_symm` | 逆向きの比較は逆同型 |
| `OmegaSpectrum.compareLevels_trans` | 三段の比較の合成整合性 |
| `OmegaSpectrum.homotopyGroupEquivAt_canonical` | 標準段の表示は恒等 |
| `OmegaSpectrum.homotopyGroupEquivAt_trans` | 任意段での表示と段の比較の整合性 |

参照：BF 1978 §2、HA §1.4.2。
保存単位の対象ビルド 1845 jobs 成功。
私有宣言を含む 72 モジュール 1359 宣言で標準三公理のみ。
L9c は未完了。loop と段の比較の自然性、零次数の fiber 比較、fiber の Ω 条件、
Kan でない列の置換の構造射への接続、整数次数長完全列が残る。

## 35. L9c の loop・隣接比較・任意段表示の自然性

長完全列の自然性を、標的の指定基点の等式による移送を含む界面へ延ばした。
path の終点評価と、loop の円の表示・fiber 表示が標的の射に関して自然であることを証明した。
path の連結写像による同値を全自然数次数の集合の同値としてまとめた。
連結同値、loop の fiber 同型、標的の基点への移送の三つの可換図式を合成した。
これにより π_n(ΩY) ≃ π_(n+1)(Y) の自然性を零次数も含めて証明した。
随伴構造射の可換式と合成し、Ω スペクトルの隣接段の全次数の比較の自然性を得た。
零次数で移した群演算が、元の連結成分の誘導写像で保たれることをこの自然性から証明した。
各段・各自然数次数の可換群への関手は、順写像として元の KanHomotopy.map を持つ。
反復比較、添字の等式の移送、逆比較へ自然性を延ばした。
整数次数群の任意の許される段による表示を、可換群への関手の自然同型として束ねた。
その帰結として、整数次数の誘導写像の全単射性は任意の許される段の誘導写像で検証できる。

| 主要宣言 | 内容 |
| --- | --- |
| `FibrationSquare.fiberMapAt` / `.connecting_natural_at` | 指定基点の fiber 射と連結写像の自然性 |
| `pathEndpoint_natural` / `pathFiberMap` | path fibration の自然な可換正方形 |
| `loopBasedPathFiberIso_natural` | loop の fiber 表示の自然性 |
| `pathConnectingEquiv` / `.pathConnectingEquiv_natural` | path の全次数の連結同値と自然性 |
| `loopHomotopyEquiv_natural` | 零次数を含む loop の次数移動の自然性 |
| `OmegaSpectrum.transition_formula` / `.transition_natural` | 隣接比較の計算式と自然性 |
| `OmegaSpectrum.levelMap` / `.levelFunctor` | 零次数を含む各段の可換群への関手 |
| `OmegaSpectrum.iterateTransition_natural` | 反復比較の自然性 |
| `OmegaSpectrum.compareLevels_natural` | 任意の二段の比較の自然性 |
| `OmegaSpectrum.homotopyFunctorIsoAt` | 整数次数群と任意段の群の関手の自然同型 |
| `OmegaSpectrum.homotopyMap_bijective_iff_levelMap` | π_* 同型性の任意段での検証 |

参照：Goerss–Jardine I §7、BF 1978 §2、HA §1.4.2。
保存単位の対象ビルド 1851 jobs 成功。
私有宣言を含む 78 モジュール 1425 宣言で標準三公理のみ。
L9c は未完了。零次数の fiber 比較、fiber の Ω 条件、Kan でない列の構造射を含む置換、
整数次数長完全列、反復比較の隣接構造射との添字正規化が残る。

## 36. L9c の構造射を含む段ごとの Kan 置換

Kan 性をまだ要求しない `PointedSequence` を定義した。
anodyne な点つき射に沿う Kan 標的への延長を、元の基点を保つ点つき射として構成した。
元の構造射を次段の Kan 置換へ合成し、その随伴を次段の loop に取った。
この loop は Kan なので、anodyne な現段の置換単位に沿って随伴構造射を延長できる。
uncurry によって置換した二段の suspension 構造射を得た。
置換単位との厳密可換性を、延長の制限式と随伴の逆関係から証明した。
任意の点つき列から、構造射を持つ Kan 列への実際の比較射を得た。
延長の選択に列の関手性は主張しない。
任意の入力について Ω 条件が成立するとは主張しない。
元の段が Kan である場合は、比較射の全基点 π_* 同型性を証明した。

| 主要宣言 | 内容 |
| --- | --- |
| `PointedExtension.exists_extension` / `.extend` | anodyne 射に沿う点つき延長 |
| `PointedSequence` / `.Hom` | Kan 条件を持たない列と厳密射 |
| `PointedSequence.kanReplacementAdjoint` / `.kanReplacementSigma` | 延長された随伴と構造射 |
| `PointedSequence.kanReplacement_unit_comm` | 単位と構造射との厳密可換性 |
| `PointedSequence.kanReplacement` / `.kanReplacementUnit` | Kan 列への置換と比較射 |
| `PointedSequence.kanReplacementUnit_piIsomorphism` | 元の段が Kan の場合の π_* 保存 |

参照：Goerss–Jardine I §7、BF 1978 §2、HTT A.3.3。

## 37. L9c の fiber の零次数と全基点 π_* 比較

零次数の基点付きの類と基点を選ばない連結成分の界面を整えた。
全基点 π_* 条件から連結成分の全単射性を得る際には、源の指定頂点の存在を明示した。
全空間の参照頂点を任意に選び直し、固定 fiber の連結成分へ値を持つ連結写像を定義した。
零次数の完全性と自然性をこの表示へ移した。
fiber の零次数比較の単射性では、第一の原像の頂点を参照基点に取った。
底の基本群からの連結写像で第二の原像を表示し、標的の全空間の基本群へ戻した。
全空間の基本群の全射性と底の基本群の単射性を使って、元の連結成分が一致すると示した。
全射性では、先に全空間の連結成分を持ち上げた。
底の連結成分の単射性と零次数の完全性で源の fiber の頂点を選び、参照基点をそこへ移した。
標的の残りの成分を底の基本群の全射性と連結写像の自然性で持ち上げた。
この零次数の全単射性と正次数の五項補題を合わせ、fiber の全基点・全次数の π_* 同型性を得た。
任意の包含と可換な fiber 射にも、普遍性の一意性で移せる形にした。

| 主要宣言 | 内容 |
| --- | --- |
| `KanHomotopyZero.map_bijective_iff_piZero` | 基点付き零次数と連結成分の全単射性の同値 |
| `KanPiIsomorphism.piZero_bijective_at` | 指定頂点を持つ源での連結成分の全単射性 |
| `componentConnecting` | 固定 fiber の連結成分への連結写像 |
| `componentConnecting_exact` / `.componentConnecting_kernel` | 参照基点を変えられる零次数の完全性 |
| `componentFiber_exact` | 全空間の連結成分の位置での完全性 |
| `FibrationSquare.componentConnecting_natural` | 固定 fiber の連結写像の自然性 |
| `FibrationSquare.fiberMap_piZero_bijective` | fiber の連結成分の全単射性 |
| `FibrationSquare.fiberMap_piIsomorphism` | fiber の全基点 π_* 同型 |
| `FibrationSquare.fiberMapOver_piIsomorphism` | 包含と可換な固定 fiber 射での比較 |

参照：Goerss–Jardine I §§7–8、Kerodon §3.2.6、BF 1978 §2。
保存単位の対象ビルド 1859 jobs 成功。
私有宣言を含む 86 モジュール 1494 宣言で標準三公理のみ。
L9c は未完了。次は loop と fiber の比較を用いて fiber 列の Ω 条件を証明する。
整数次数長完全列と反復比較の隣接構造射との添字正規化も残る。

## 38. L9c の fiber の Ω 条件と BF 対象

点つき fiber の既存の普遍性から kernel fork の極限性を証明した。
円からの点つき内部 Hom は右随伴なので、この kernel を保存する。
これにより fiber の loop と loop した射の fiber の点つき同型を構成した。
この同型は全空間への包含と可換である。
また、基点包含とホーンの pushout product の充填から、点つき Hom の後合成が
Kan fibration を保つことを証明した。
各段が Kan fibration である Ω 列の射について、fiber の随伴構造射を上の同型へ合成した。
全空間と底の随伴構造射の π_* 同型性を、fiber の全基点比較定理へ適用した。
その合成は π_* 同型であり、厳密同型を打ち消して fiber 自身の Ω 条件を得た。
fiber の Kan 列へ単射置換を施し、承認済みの BF 対象として fiber を定義した。
全空間への包含は厳密なスペクトルの射で、各段で元の射との合成が零である。
置換した fiber の各段から実際の fiber への比較射は全基点 π_* 同型である。
現時点の fiber 構成は各段が Kan fibration である射に対して与える。
任意のスペクトルの射をその形へ置換する工程と、整数次数長完全列は引き続き扱う。
Sp の ∞ 極限という主張は含めず、γ3 後に扱う。

| 主要宣言 | 内容 |
| --- | --- |
| `pointedFiberKernelIsLimit` | 点つき fiber の kernel としての普遍性 |
| `loopPointedFiberIso` / `.loopPointedFiberIso_hom_ι` | loop と fiber の厳密な同型と包含との可換性 |
| `PointedMapping.post_hasLiftingProperty` | 基点とパラメータの pushout product による後合成の充填 |
| `PointedMapping.post_fibration` | 後合成による Kan fibration の保存 |
| `KanSequence.Hom.fiber_omegaCondition` | fiber の全基点 Ω 条件 |
| `KanSequence.Hom.fiberOmegaSpectrum` | fiber の Kan 列から BF 対象への置換 |
| `OmegaSpectrum.fiber` | 段ごとの Kan fibration の fiber 対象 |
| `OmegaSpectrum.fiberLevelProjection_piIsomorphism` | 実際の段の fiber への全基点 π_* 同型 |
| `OmegaSpectrum.fiberInclusion` / `.fiberInclusion_comp_app` | 厳密な包含と各段の零合成 |

参照：Goerss–Jardine I §§7–8、Kerodon §3.1.3、BF 1978 §2、HTT A.3.3、HA §1.4.2。
保存単位の対象ビルド 1863 jobs 成功。
私有宣言を含む 89 モジュール 1523 宣言で標準三公理のみ。
L9c は未完了。整数次数長完全列、任意の射の段ごとの fibration への置換、
反復比較の隣接構造射との添字正規化が残る。

## 39. L9c の整数次数の連結準同型と長完全列

整数次数群の正次数の段による表示を整理した。
置換した fiber の段から実際の fiber の群への同型を、実際の fiberPoint を基点に構成した。
整数次数の包含と射影が、これらの表示で段の実際の fiber 列の射へ移ることを証明した。
連結射 δ_j : π_(j+1)(Y) → π_j(fiber) は、段 |j|+2 の正次数の連結準同型を移して定義した。
底と fiber の計算次数はそれぞれ boundaryIndex j + 2 と boundaryIndex j + 1 である。
全ての整数 j で群準同型が使える。
単なる定義に留めず、段の連結準同型で計算する式を証明した。
群同型によって核と像の完全性を移す一般補題を証明した。
これを段の完全列の fiber・全空間・底の三つの位置へ適用した。
整数次数の長完全列は全ての整数で完全であり、隣接射の合成も自明である。
対象の fiber は単射置換を挟んだ BF 対象で、射は元のホモトピー群の誘導準同型である。
現時点では各段が Kan fibration である射についての長完全列である。

| 主要宣言 | 内容 |
| --- | --- |
| `OmegaSpectrum.positiveStageEquiv` | 整数次数群の正次数の段表示 |
| `OmegaSpectrum.fiberPositiveStageEquiv` | 整数次数の fiber 群と実際の段の fiber 群の同型 |
| `OmegaSpectrum.fiberPositiveStageEquiv_inclusion` | 包含との可換性 |
| `OmegaSpectrum.positiveStageEquiv_projection` | 基点を像へ移した射影との可換性 |
| `OmegaSpectrum.boundaryStage` / `.boundaryIndex` | 連結準同型を計算する段と次数 |
| `OmegaSpectrum.stableConnectingHom` | 全整数次数の連結準同型 |
| `OmegaSpectrum.stableConnectingHom_compute` | 実際の段の連結準同型による計算式 |
| `group_exact_of_equivalences` | 群同型で可換に対応する完全性の移送 |
| `OmegaSpectrum.stableFiberLongExact` | 全整数次数の三つの位置での核と像の一致 |
| `OmegaSpectrum.stableConnectingHom_inclusion` / `.stableConnectingHom_projection` | 連結準同型との零合成 |
| `OmegaSpectrum.homotopyMap_fiberInclusion` | 包含と射影の零合成 |

参照：Goerss–Jardine I §7、BF 1978 §2、HA §1.4.2。
保存単位の対象ビルド 1867 jobs 成功。
私有宣言を含む 93 モジュール 1574 宣言で標準三公理のみ。
L9c は未完了。任意の射の段ごとの fibration への置換と、
反復比較の隣接構造射との添字正規化を引き続き進める。

## 40. L9c の隣接構造射と任意段表示の一致

段と次数の等式による移送の合成と、隣接比較との可換性を証明した。
k+r=l を使って前進比較を指定した反復回数で表示した。
減算を含む添字を等式の移送の内部で書き換える代わりに、この表示で正規化した。
前進比較を一段延ばす式を、構造射の比較とその後の次数の移送の合成として証明した。
最小段からの比較を打ち消し、隣接する二段の比較が構造射の隣接比較に一致すると示した。
終点の段に関する帰納により、任意の前進比較は既存の二段比較と一致する。
構造射の反復も、次数を整えると任意段の比較と一致する。
これで整数次数群の段の選択独立性は、合成整合性・自然性・実際の構造射との一致まで揃った。

| 主要宣言 | 内容 |
| --- | --- |
| `OmegaSpectrum.levelHomotopyCongr_trans_apply` | 二回の添字移送の合成 |
| `OmegaSpectrum.transition_congr_apply` | 添字移送と隣接比較の可換性 |
| `OmegaSpectrum.advanceTo_eq_iterate` | 指定反復回数による前進比較の表示 |
| `OmegaSpectrum.advanceTo_self` / `.advanceTo_succ` | 前進比較の開始点と後続式 |
| `OmegaSpectrum.compareLevels_succ` | 隣接二段の比較と構造射の一致 |
| `OmegaSpectrum.advanceTo_eq_compareLevels` | 前進比較と任意段比較の一致 |
| `OmegaSpectrum.iterateTransition_eq_compareLevels` | 反復構造射と任意段表示の一致 |

参照：BF 1978 §2、HA §1.4.2。
保存単位の対象ビルド 1868 jobs 成功。
私有宣言を含む 94 モジュール 1597 宣言で標準三公理のみ。
L9c の残りとして、任意の射を段ごとの Kan fibration へ置換する。
自由な区間の mapping path と、単射置換の比較射に対する cofibrant な源からの持ち上げを使う方針。


## 41. L9c の自由な path と cofibrant な源からの持ち上げ

自由な基点を加えた区間と二つの端点包含を構成した。
両端点の基礎射は anodyne であり、基点追加と余積の持ち上げで証明した。
単射と恒等射との余積の単射性も、境界生成の左クラスの押し出し閉性から証明した。
自由区間からの点つき内部 Hom を自由な path space とした。
端点評価は全ての単射に対する RLP を持ち、特に Kan fibration である。
定数 path の両端点の評価は厳密に恒等射である。
別に、構造射が単射な Kan 列から、各段で全単射への RLP を持つ射へ厳密に持ち上げる構成を証明した。
零段は基点包含、後続段は構造射を左辺として充填する。
これに Ω 条件は必要ない。
任意の射の mapping path を単射置換した後にも、元の射の厳密な因子分解を得るために使う。

| 主要宣言 | 内容 |
| --- | --- |
| `freeIntervalEndpoint_anodyne` | 自由な区間の両端点の anodyne 性 |
| `mono_coprod_map_id` | 基点追加による単射の保存 |
| `PointedMapping.anodyne_prePointed_rlp` | anodyne 制限の全単射への RLP |
| `freePathSpace` / `freePathEndpoint` | 自由な path と端点評価 |
| `freePathEndpoint_rlp` | 端点評価の全単射への RLP |
| `freeConstantPath_endpoint` | 定数 path の両端点の計算 |
| `pointedSquareLift` / `pointedMapLift` | 点つきの相対持ち上げ |
| `KanSequence.liftHom` / `.liftHom_fac` | 単射な構造射を持つ列からの厳密な持ち上げ |

参照：Goerss–Jardine I §7、BF 1978 §2、HTT A.3.3。
保存単位の対象ビルド 1873 jobs 成功。
私有宣言を含む 97 モジュール 1652 宣言で標準三公理のみ。
L9c は未完了。両端点同時評価の fibration 性と、path 列の構造射を続けて構成する。


## 42. L9c の自由な path 列と両端点の同時評価

閉 braided 圏で K ⊗ Hom(A,Y) → Hom(A,K ⊗ Y) を構成した。
内部 Hom の源の制限・標的の後合成に関する自然性を証明した。
単位からの内部 Hom の標準同型を評価射で表示し、交換射がこの同型と可換であることも示した。
これを使って、任意の点つき対象 A からの内部 Hom を Kan 列の各段に施した列を構成した。
源の制限と標的の後合成はいずれも厳密な列の射となる。
特に自由な path 列、二つの端点評価、定数 path が厳密な列の射として得られた。
自由区間の境界は点つき単位二つの余積で、その包含は単射である。
反変内部 Hom の極限保存により、境界からの写像空間を標的の二項積へ同定した。
境界への制限とこの同型の合成が、両端点の同時評価の Kan fibration を与える。
二つの射影が既存の始点・終点評価に一致することまで計算した。

| 主要宣言 | 内容 |
| --- | --- |
| `HomTensorStrength.map` | テンソルと内部 Hom の交換射 |
| `HomTensorStrength.natural_pre` / `.natural_post` | 両変数についての自然性 |
| `HomTensorStrength.map_unit` | 単位の内部 Hom の標準同型との整合性 |
| `KanSequence.mapping` / `.mappingPre` / `.mappingPost` | 内部 Hom の列と厳密な射 |
| `KanSequence.freePathEvaluation` / `.freePathConstant` | path 列の端点と定数 path |
| `KanSequence.freePathConstant_evaluation` | 定数 path の厳密な端点計算 |
| `freeBoundaryIsColimit` | 自由な境界の点つき余積の普遍性 |
| `freeBoundaryEvaluationIso` | 境界からの Hom と標的の二項積の同型 |
| `freePathEndpoints_fibration` | 両端点同時評価の Kan fibration 性 |
| `freePathEndpoints_fst` / `.freePathEndpoints_snd` | 二つの射影の計算 |

参照：Goerss–Jardine I §7、BF 1978 §2、HTT A.3.3。
保存単位の対象ビルド 1876 jobs 成功。
私有宣言を含む 100 モジュール 1728 宣言で標準三公理のみ。
L9c は未完了。段ごとの引き戻しを用いて任意の射の mapping path 列を構成する。


## 43. L9c 完了：任意の射の fibration 置換と homotopy fiber の長完全列

段ごとの Kan fibration に沿う引き戻しを点つき圏で取り、Kan 列として束ねた。
構造射は二つの射影から普遍性で作り、射影と持ち上げは厳密な列の射である。
自由な path の始点評価を任意の射に沿って引き戻して mapping path を構成した。
源への射影は全単射への RLP を持つ。
終点射のホーン充填は、まず元の源の成分を充填し、次に両端点を同時に充填して証明した。
定数 path による比較射と終点射の合成は厳密に元の射である。
源が Ω 条件を持つと、中間列も源への射影の RLP を通して Ω 条件を持つ。
この列を境界 cell 分解で単射置換し、元の cofibrant な源から厳密に持ち上げた。
従って元の任意の射は、段ごとの全基点 π_* 同型と段ごとの Kan fibration の厳密な合成となる。
中間対象は本レーンで固定した BF cofibrant–fibrant 対象である。
元の源への厳密な射影も構成し、整数次数群では比較射の逆写像になることを証明した。

置換した右因子の fiber を単射置換し、任意の射の homotopy fiber を BF 対象として定義した。
包含は置換後の fiber 包含と元の源への射影の合成であり、実際の厳密なスペクトルの射である。
連結射は置換後の段の連結準同型から来る。
比較群同型を通して、fiber・全空間・底の三つの位置の完全性を元の射の誘導準同型へ移した。
全ての整数次数で核と像が一致し、隣接射の合成が自明である。
Sp の ∞ 極限としての普遍性、正しい導来写像空間との比較はこの主張に含めていない。
これらは承認済みの仕様どおり γ3 後の別工程である。
L9c の本工程は完了とし、L9d の telescope 有理化へ進む。

| 主要宣言 | 内容 |
| --- | --- |
| `pointedPullback_isPullback` / `.pointedPullback_snd_rlp` | 基礎引き戻しと全単射 RLP の保存 |
| `KanSequence.pullbackSequence` / `.pullbackLift` | Kan 列の引き戻しと厳密な普遍射 |
| `mappingPathProjection_fibration` | 任意の点つき Kan 射の終点射の相対ホーン充填 |
| `KanSequence.mappingPathSequence_omegaCondition` | mapping path 列の Ω 条件 |
| `OmegaSpectrum.fibrationReplacement` | BF 対象としての中間対象 |
| `OmegaSpectrum.fibrationReplacement_fac` | 元の射の厳密な因子分解 |
| `OmegaSpectrum.fibrationReplacementProjection_fibration` | 右因子の各段の Kan fibration 性 |
| `OmegaSpectrum.fibrationReplacementUnit_piIsomorphism` | 左因子の全整数次数 π_* 同型 |
| `OmegaSpectrum.fibrationReplacementRetraction` | 元の源への厳密な射影 |
| `OmegaSpectrum.homotopyFiber` / `.homotopyFiberInclusion` | 任意の射の homotopy fiber と包含 |
| `OmegaSpectrum.homotopyFiberBoundary` | 全整数次数の連結準同型 |
| `OmegaSpectrum.homotopyFiberLongExact` | 任意の射の三つの位置での長完全性 |
| `OmegaSpectrum.homotopyFiberBoundary_inclusion` / `.homotopyFiberInclusion_projection` / `.homotopyFiberBoundary_projection` | 隣接射の零合成 |

参照：Goerss–Jardine I §§7–8、BF 1978 §2、HTT A.3.3、HA §1.4.2。
保存単位の対象ビルド 1881 jobs 成功。
私有宣言を含む 105 モジュール 1819 宣言で標準三公理のみ。
工程区切りの全体ビルド 9543 jobs 成功。
L9d・L9e は未完了であり、全体目標の完了は主張しない。


## 44. L9d の filtered colimit と Kan 性・ホモトピー群

有限な相対写像データを一つの後続段へ移す補題を証明した。
有限個の制限の等式は、定義域の有限余積を使って同時に移せる。
有限ホーンからの射を段へ下ろして充填することで、Kan 複体の filtered colimit の Kan 性を示した。
遷移射の単射性は仮定していない。
境界定数単体は基点を含む相対因子分解で後続段に実現できる。
RelStruct は隣接二面と残りの定数面を同時に指定して後続段へ移せる。
従って零次数を含む全自然数次数で、全ての類が段から来て、類の等式が後続段で成立する。

点つき diagram の π_n の図式と cocone を実際に構成した。
基点忘却が filtered colimit を保存することから、点つき余極限の Kan 性を証明した。
代表と関係の有限性から、ホモトピー類の cocone が型の圏の余極限であることを証明した。
正次数については群準同型の図式を作り、群の filtered colimit の普遍性と比較群同型を構成した。
比較同型を各段に制限した準同型は、元の cocone 射の誘導準同型に一致する。
π_1 の非可換性を許す群の圏で主張しており、零次数は集合として扱う。
`Rationalization.lean` を L9d の集約入口とした。
有理化対象、telescope との比較、ℚ テンソルの計算は引き続き未完了。

| 主要宣言 | 内容 |
| --- | --- |
| `finite_relative_factorization` / `.finite_equations_factorization` | 有限な境界条件・面条件を保つ後続段への因子分解 |
| `kanComplex_of_filtered_isColimit` | Kan 複体の filtered colimit の Kan 性 |
| `ptSimplex_filtered_factorization` | 基点を保つ代表単体の有限段での実現 |
| `relStruct_filtered_factorization` | ホモトピー関係の有限段での実現 |
| `homotopy_filtered_surjective` / `.homotopy_filtered_eq_eventually` | 全自然数次数の代表と等式の後続段での実現 |
| `pointedFilteredColimit_kanComplex` | 点つき filtered colimit の Kan 性 |
| `pointedHomotopyIsColimit` | 全自然数次数のホモトピー類と filtered colimit の可換性 |
| `pointedHomotopyGroupIsColimit` | 正次数群の余極限の普遍性 |
| `pointedHomotopyGroupColimitIso` / `.pointedHomotopyGroupColimitIso_ι` | 比較群同型と各段での計算 |
| `filteredPointedHomotopyGroupIso` | 選ばれた点つき余極限の正次数群の比較同型 |

参照：Goerss–Jardine I §7、BF 1978 §2、HA §1.4.2。
保存単位の対象ビルド 1888 jobs 成功。
私有宣言を含む 109 モジュール 1864 宣言で標準三公理のみ。
次は有限な源からの点つき内部 Hom と filtered colimit の比較を進め、loop と colimit を整合させる。


## 45. L9d の有限な内部 Hom と loop の filtered colimit 保存

有限な点つき源と有限パラメータの写像族を uncurry した。
基点包含に対する相対因子分解により、基点条件を保つ写像族を一つの段に実現できる。
二つの族が余極限で一致すれば、有限なテンソル積からの射の等式を後続段へ移せる。
ここには Kan 性も遷移射の単射性も不要である。

各単体次数で Yoneda の同値を使い、これらの二つの事実から写像空間の余極限性を証明した。
基点忘却の同型反映で点つき圏へ戻し、有限な源からの内部 Hom が filtered colimit を保存すると示した。
標準単体の境界を潰した球面は、有限な対象の押し出しとして有限である。
特に単体的円が有限なので、点つき loop 関手は filtered colimit を保存する。
loop 対象の余極限と余極限の loop 対象との標準同型、および各段での計算式を構成した。
この同型は通常の点つき単体集合の同型であり、Sp の ∞ 余極限の普遍性を先取りしない。

| 主要宣言 | 内容 |
| --- | --- |
| `PointedMapping.finite_basedHom_factorization` | 基点条件を保つ有限な写像族の後続段での実現 |
| `PointedMapping.finite_basedHom_eq_eventually` | 写像族の等式の後続段での実現 |
| `PointedMapping.finite_basedHom_isColimit` | 各次数の写像空間の余極限性 |
| `PointedMapping.finite_basedHom_preservesColimit` | 有限な点つき源からの内部 Hom の filtered colimit 保存 |
| `pointedSphere_finite` | 境界を潰した単体的球面の有限性 |
| `loop_preservesFilteredDiagram` | loop 関手の filtered colimit 保存 |
| `loopFilteredColimitIso` / `.loopFilteredColimitIso_ι` | loop と余極限の比較同型と各段の計算 |

参照：Goerss–Jardine I §7、BF 1978 §2、HTT A.3.3、HA §1.4.2。
保存単位の対象ビルド 1891 jobs 成功。
私有宣言を含む 112 モジュール 1880 宣言で標準三公理のみ。
次は段ごとの全基点 π_* 同型の filtered colimit 保存を示し、Ω 条件を移す。
有理化の対象、telescope の比較、ℚ テンソルの計算は引き続き未完了。


## 46. L9d の全基点 π_* 同型と filtered Ω 列の整数次数群

まず点つき Kan 図式の指定基点のホモトピー類の自然変換を構成した。
段ごとの全単射は自然同型となり、余極限の射も全単射になることを実証した。
任意の余極限の頂点を一段から取った後、その段の under 圏で後続段に基点を付けた。
under 圏からの forget の final 性により元の余極限を保つ。
これにより、段ごとの全基点 π_* 同型が filtered colimit で保存されることを証明した。
零次数を含む。空な段があっても追加の非空仮定を置かない。

Ω スペクトルの図式を各段の点つき Kan 図式へ評価した。
suspension が余極限を保存することから、段ごとの Kan 余極限に構造射を入れた。
各元のスペクトルからこの Kan 列への射は厳密である。
随伴構造射は、元の随伴構造射の余極限と loop の比較同型の合成に厳密に一致する。
全基点 π_* 同型の保存をこの式へ適用し、余極限列の Ω 条件を証明した。
構造射には境界 cell 分解の単射置換を施し、BF 対象を得た。

各整数次数の群の図式と、任意の許容正次数の段の群の図式との自然同型を構成した。
段の群と filtered colimit の可換性、単射置換の各段の比較同型を合成した。
結果として、構成した BF 対象の全整数次数の群は、元の整数次数群の図式の余極限と同型である。
この比較を各段から計算する式も証明した。
これらは通常の段ごとの構成と π_* の計算であり、Sp の ∞ 余極限としての普遍性は含まない。
有理化用の乗法射の列、homotopy telescope と通常の余極限の比較、ℚ テンソルの計算はまだ未完了。

| 主要宣言 | 内容 |
| --- | --- |
| `pointedHomotopyMap_bijective_of_filtered` | 指定基点の段ごとの π_n 同型の保存 |
| `pointFromStage` / `.pointFromStageCocone` / `.pointFromStageIsColimit` | under 圏での任意基点の後続段への移送 |
| `kanPiIsomorphism_of_filtered` | 全基点・全次数の π_* 同型の filtered colimit 保存 |
| `pointedColimMap_kanPiIsomorphism` | 点つき余極限射への適用 |
| `OmegaSpectrum.filteredKanSequence` / `.filteredKanInjection` | 段ごとの Kan 余極限列と厳密な射 |
| `OmegaSpectrum.filteredAdjoint_formula` | 余極限の随伴構造射の計算 |
| `OmegaSpectrum.filteredKanSequence_omegaCondition` | 全基点での Ω 条件 |
| `OmegaSpectrum.filteredOmegaSpectrum` | 単射置換した BF 対象 |
| `OmegaSpectrum.spectrumHomotopyDiagramStageIso` | 整数次数群の図式と段表示の自然同型 |
| `OmegaSpectrum.filteredLevelComparison_piIsomorphism` | 単射置換の各段の π_* 比較 |
| `OmegaSpectrum.filteredSpectrumHomotopyIso` | 全整数次数の群と群の filtered colimit の比較同型 |
| `OmegaSpectrum.filteredSpectrumHomotopyIso_ι_stage` | 比較同型の各段での計算 |

参照：Goerss–Jardine I §7、BF 1978 §2、HA §1.4.2。
保存単位の対象ビルド 1896 jobs 成功。
私有宣言を含む 117 モジュール 1955 宣言で標準三公理のみ。
L9d は進行中。次は有理化の telescope に対応する群の局所化の計算を進める。


## 47. L9d の乗法列の群の局所化と ℚ テンソル

2,3,4,… の整数乗法を遷移とするアーベル群の列を構成した。
二段間の係数は整数区間の積であり、零段からの係数は (i+1)! に一致する。
任意の非零整数は十分先の遷移係数を割ることを証明した。
直極限の代表と等式の検出から、非零整数倍が直極限で全単射になることを示した。
元の群のねじれを仮定しない。

零段からの標準射について、整数の非零元による加群の局所化の三条件を証明した。
有理テンソル積の標準射も同じ局所化なので、普遍性から線形同型を得た。
この同型は零段の a を a⊗1 に送り、加法準同型に関して自然である。
直極限の cocone がアーベル群の圏の余極限を与えることも証明した。
これにより圏論的な乗法列の余極限も A⊗ℚ と同定できる。

| 主要宣言 | 内容 |
| --- | --- |
| `RationalTelescope.coefficient_comp` / `.coefficient_zero` | 遷移係数の合成則と階乗表示 |
| `RationalTelescope.exists_dvd_integerCoefficient` | 任意の非零整数の後続段での可除性 |
| `RationalTelescope.additiveLimit_smul_bijective` | 直極限での非零整数倍の全単射性 |
| `RationalTelescope.additiveLimit_isLocalizedModule` | 零段の標準射の局所化条件 |
| `RationalTelescope.additiveLimitTensorEquiv` | 直極限と A⊗ℚ の線形同型 |
| `RationalTelescope.additiveDiagramTensorIso` / `.additiveDiagramTensorIso_zero` | 群の圏の余極限の比較と零段の計算 |
| `RationalTelescope.limitMap` | 加法準同型の直極限への誘導と関手法則 |
| `RationalTelescope.additiveLimitTensorEquiv_natural` | テンソル比較の自然性 |

参照：BF 1978 §2、HA §1.4.2。
保存単位の対象ビルド 2319 jobs 成功。
私有宣言を含む 122 モジュール 2019 宣言で標準三公理のみ。
L9d は進行中。スペクトルの実際の乗法射と telescope の構成および比較は未完了。
群の計算だけでスペクトルの有理化の完成を主張しない。


## 48. L9d の filtered BF 対象への射と置換比較

元の各対象の cofibrant 性を使い、各段の余極限への射を BF 置換へ厳密に持ち上げた。
段ごとの比較射へ戻すと元の余極限の標準射に一致する。
この式と正次数の段表示の自然性により、整数次数の余極限同型が選んだ射を誘導すると証明した。
持ち上げの選択の厳密な自然性は要求しないが、π_* 上では cocone の自然性が成立する。

図式の自然変換から、段ごとの Kan 余極限列の厳密な射も構成した。
その射を標的の BF 置換へ持ち上げ、実際の Ω スペクトル間の比較射を得た。
元の自然変換が各段で全基点 π_* 同型なら、この比較射も各段および全整数次数で π_* 同型である。
通常の余極限模型を置換して比較するための結果であり、∞ 余極限の普遍性は含まない。

乗法射の実現のため、π_* 同型である Kan fibration の fiber の消滅も長完全列から証明した。
零次数を含む任意の fiber 基点で全ホモトピー類は一元である。
対応する境界定数単体の RelStruct も存在する。
この消滅から実際の境界充填を導く逆向きの Whitehead 補題は後続部分で実証する。

| 主要宣言 | 内容 |
| --- | --- |
| `OmegaSpectrum.filteredSpectrumInjection` | 元の各対象から BF 余極限対象への厳密な射 |
| `OmegaSpectrum.filteredSpectrumInjection_comparison` | 各段の余極限射との整合性 |
| `OmegaSpectrum.filteredSpectrumHomotopyIso_ι` | 群の余極限同型の各段での計算 |
| `OmegaSpectrum.filteredSpectrumInjection_natural` | 誘導する整数次数群の写像の自然性 |
| `OmegaSpectrum.filteredKanMap` / `.filteredSpectrumMap` | 自然変換からの Kan 列と BF 対象の比較射 |
| `OmegaSpectrum.filteredSpectrumMap_levelwise` / `.filteredSpectrumMap_piIsomorphism` | 段ごとおよび整数次数の π_* 同型の保存 |
| `fiberHomotopy_eq_point` / `.fiberHomotopySubsingleton_at` | acyclic fiber の零次数を含む全類の一意性 |
| `fiberRelStruct_nonempty` | acyclic fiber の境界定数単体間の関係の存在 |

参照：Goerss–Jardine I §§7–8、Kerodon §3.2.6、BF 1978 §2、HTT A.3.3、HA §1.4.2。
保存単位の対象ビルド 2322 jobs 成功。
私有宣言を含む 125 モジュール 2046 宣言で標準三公理のみ。
L9d は進行中。次はホモトピー類の消滅を境界の充填へ戻す幾何的補題を進める。


## 49. L9d の消滅からの実際の境界充填と相対 Whitehead

標準単体の単体を、区間の値が零の間は元の値、その後は最後の頂点とする収縮を構成した。
この収縮は最後のホーンを保つ。ホーンの収縮を相対区間充填で境界全体へ延長する。
その結果、任意の Kan 値の境界射を最後のホーン上で定数となる射へホモトピーで移せる。
最後の面は PtSimplex となり、その類が零なら定数単体との RelStruct が全境界の充填を与える。
さらに、境界のホモトピーを標準単体へ延長し、元の境界の充填へ戻せる。

従って、非空な Kan 複体で全基点・全自然数次数の類が一元なら、終対象射は全単射 RLP を持つ。
単射への拡張には境界 cell 分解に対する RLP の閉性だけを使った。
Kan fibration の π₀ 全射性から頂点そのものの全射性を、RelStruct の辺の持ち上げで証明した。

相対版では、底の標準単体の収縮を境界で持ち上げた。
終点での境界は一つの fiber 内に入り、その fiber の充填後、区間の相対延長で元の底へ戻す。
これにより、全ての fiber の終対象射が全単射 RLP を持てば、元の fibration 自身も全単射 RLP を持つ。
長完全列からの fiber の消滅と合わせ、非空な Kan 複体間の Kan fibration の π_* 同型性と全単射 RLP の同値を実証した。
HT-KQ の引用も新しい弱同値公理も用いない。

| 主要宣言 | 内容 |
| --- | --- |
| `SimplexLastContraction.map` / `.homotopy` | 標準単体の明示的な区間収縮 |
| `LastHornContraction.map` / `.homotopy` | 最後のホーンへの制限と端点の式 |
| `BoundaryNormalization.exists_normalization` | 境界のホーン上での定数化と実ホモトピー |
| `BoundaryNormalization.lastSimplex` | 正規化した境界の最後の面の PtSimplex 表示 |
| `BoundaryNormalization.exists_filler_of_lastSimplex` | 最後の面の類の消滅からの充填 |
| `terminal_rlp_of_homotopySubsingleton` | 全ホモトピー類の消滅から全単射 RLP |
| `fiber_terminal_rlp_of_piIsomorphism` | acyclic fiber の実際の充填性 |
| `exists_fibration_interval_lift` | 指定始点からの区間の持ち上げ |
| `fibration_surjective_vertices_of_zero` | π₀ 全射性からの頂点の全射性 |
| `exists_boundary_lift_of_fiber_lifting` | fiber の充填から相対境界充填 |
| `fibration_rlp_of_piIsomorphism` / `.fibration_piIsomorphism_iff_rlp` | Kan fibration の相対 Whitehead |

参照：Goerss–Jardine I §§7–8、Kerodon §§3.2.2・3.2.6、BF 1978 §2。
保存単位の対象ビルド 2331 jobs 成功。
私有宣言を含む 132 モジュール 2102 宣言で標準三公理のみ。
L9d は進行中。任意の Kan 射の π_* 同型からの逆射の実現と乗法 telescope は引き続き未完了。


## 50. L9d の一般の Kan Whitehead と内部 Hom の π_* 保存

基点を固定しない指数 path 対象を構成し、端点評価が全単射 RLP を持つことを証明した。
ホモトピーをこの対象へ転置すると、両端点で元の二つの射を得る。
端点の全基点 π_* 同型を打ち消すことで、一般の区間ホモトピーによる同型性の不変性を得た。
ここでは異なる終点基点の類の写像が同じだとは主張しない。

点つき Kan 射の mapping path は、源への射影と二つの端点評価で比較できる。
元の射が全基点 π_* 同型なら、mapping path の終点射もそうである。
相対 Whitehead により終点射が全単射 RLP を持ち、点つき切断を選べる。
二つの RLP 射の下で等しい射の間の相対ホモトピーを構成した。
これらから元の射の点つき逆射と、両方向で基点を固定する実際の区間ホモトピーを得た。

点つき内部 Hom の標的変数についても全基点 π_* 同型の保存を証明した。
mapping path の源射影と終点射の RLP を内部 Hom へ移し、切断と源射影の厳密な合成を打ち消す。
源となる点つき対象に有限性や Kan 性は不要である。

| 主要宣言 | 内容 |
| --- | --- |
| `KanPath.evaluation_rlp` / `.evaluation_piIsomorphism` | 基点を固定しない path の端点の比較 |
| `KanPath.transpose` / `.transpose_zero` / `.transpose_one` | 一般のホモトピーの転置と端点の計算 |
| `kanPiIsomorphism_iff_of_homotopy` | 基点を固定しないホモトピーによる π_* 同型性の保存 |
| `mappingPathProjection_piIsomorphism` / `.mappingPathProjection_rlp_of_piIsomorphism` | Kan 射の fibration 置換の全単射 RLP |
| `exists_pointedHomotopy_of_comp_eq` | RLP 射の下で等しい点つき射間の相対ホモトピー |
| `exists_pointedHomotopyInverse` | 点つき Kan Whitehead の実際の逆射と両方向の基点固定ホモトピー |
| `PointedMapping.post_piIsomorphism` | 点つき内部 Hom の標的変数の π_* 同型の保存 |

参照：Goerss–Jardine I §§7–8、Kerodon §§3.2.1・3.2.6、BF 1978 §2、HA §1.4.2。
保存単位の対象ビルド 2335 jobs 成功。
私有宣言を含む 136 モジュール 2125 宣言で標準三公理のみ。
L9d は進行中。次は二つの内部 Hom の交換と Kan 列の Ω 条件を整合させる。


## 51. L9d の cotensor の BF 対象と loop の整数次数群

閉 braided 圏の二つの内部 Hom を、二重 curry と源の braiding により同型で交換した。
二重評価での計算式を証明し、テンソル交換による列の構造射の随伴が、元の随伴構造射の Hom と交換同型の合成に一致すると示した。
標的変数の π_* 同型保存をこの式へ適用し、任意の点つき源 A からの内部 Hom の Kan 列の Ω 条件を得た。
構造射は境界 cell 分解で単射に置換し、本レーンの BF 対象を実際に構成した。

源の射による制限を、cofibrant な BF 対象から比較射へ持ち上げた。
各段で実際の内部 Hom の制限と可換する。
源の射が anodyne なら、この射は各段および全整数次数で π_* 同型である。
この結果には源の Kan 性や有限性を要求しない。

任意の許容正次数の段で cotensor の整数次数群を実際の内部 Hom の群へ表示した。
円を源とする場合、loop の群の同型を用いて π_j(cotensor(S¹,X))≃π_{j+1}(X) と計算した。
零段を落とす通常の厳密な関手 tail も構成し、π_j(tail X)≃π_{j-1}(X) と示した。
この二つの操作を合成した対象は元と同じ整数次数群を持つ。
群の同型から対象間の厳密な同型や射を推論しない。
∞ 圏での cotensor や suspension の普遍性は γ3 後の比較へ留保する。

| 主要宣言 | 内容 |
| --- | --- |
| `InternalHomExchange.iso` / `.uncurry_uncurry_hom` | 二つの内部 Hom の交換同型と二重評価式 |
| `InternalHomExchange.curry_strength` | 構造射の随伴と交換同型の整合性 |
| `KanSequence.mapping_adjoint` / `.mapping_omegaCondition` | 内部 Hom の Kan 列の随伴構造射と Ω 条件 |
| `OmegaSpectrum.cotensor` / `.cotensorProjection` | cotensor の BF 対象と元の Kan 列への比較 |
| `OmegaSpectrum.cotensorPre` / `.cotensorPre_comparison` | 源の射による厳密な比較射と段の計算 |
| `OmegaSpectrum.cotensorPre_piIsomorphism_of_anodyne` | 源の anodyne 置換の全整数次数での保存 |
| `OmegaSpectrum.cotensorStageEquiv` / `.cotensorLoopHomotopyEquiv` | 段表示と円による一次数移動 |
| `OmegaSpectrum.tailFunctor` / `.tailHomotopyEquiv` | 零段を落とす関手と整数次数の計算 |
| `OmegaSpectrum.tailCotensorLoopHomotopyEquiv` | 二つの操作の整数次数群の相殺 |

参照：BF 1978 §2、HTT A.3.3、HA §1.4.2。
保存単位の対象ビルド 2341 jobs 成功。
私有宣言を含む 141 モジュール 2183 宣言で標準三公理のみ。
L9d は進行中。次は円の Kan 置換上の実際の自己射と、その写像空間の群への作用を進める。


## 52. L9d の球面の単体表示と円の Kan 置換上の実際の自己射

境界を潰す実際の cofiber の普遍性により、点つき球面からの射と PtSimplex の同値を構成した。
基点の表示を頂点の定数射へ直し、後合成についての自然性も証明した。
この同値には標的の Kan 性を仮定しない。

円の Kan 置換の単位が定める基本群の指定類を取った。
その自然数 m 乗の代表を選び、球面の射へ戻した。
Kan 置換単位の anodyne 性に沿って延長し、円の Kan 置換上の点つき自己射を実際に構成した。
単位へ前合成すると選んだ代表に厳密に一致する。
誘導準同型が指定類を m 乗へ送り、任意の Kan 値の点つき射の後でも同じ計算となることを証明した。

ここでは指定類の計算だけを実証している。
基本群全体の巡回性、高次写像空間の群への m 倍作用、スペクトルの有理化の完成は主張しない。
後続部分で写像空間の類との比較を進める。

| 主要宣言 | 内容 |
| --- | --- |
| `SphereSimplex.equiv` / `.equiv_comp` | 球面からの点つき射と境界定数単体の同値と自然性 |
| `CirclePower.space` / `.unit` / `.generator` | 円の Kan 置換と指定した基本類 |
| `CirclePower.representative_class` | 指定基本類の冪の実際の単体の代表 |
| `CirclePower.powerMap` / `.unit_powerMap` | 円の Kan 置換上の自己射と単位上の厳密な計算 |
| `CirclePower.powerMap_generator` | 指定基本類の冪への作用 |
| `CirclePower.evaluateGenerator_power` | 任意の Kan 値の後合成後での指定基本類の計算 |

参照：Goerss–Jardine I §7、Kerodon §§3.2.2–3.2.3、BF 1978 §2。
保存単位の対象ビルド 2343 jobs 成功。
私有宣言を含む 143 モジュール 2208 宣言で標準三公理のみ。
L9d は進行中。次は RelStruct を実際の球面のホモトピーへ移す幾何的補題を進める。


## 53. L9d の RelStruct の実際の相対ホモトピーによる表示

隣接する穴の位置の二つの単調埋め込みを、区間の値に応じて切り替える prism を構成した。
端点は i.succ の面と i.castSucc の面である。
各境界面の制限を、切り替え位置の前・後・一致に分けて計算した。
前後の面は低次元の prism を経由し、一致する面では区間変数が消える。

RelStruct の充填単体へこの prism を後合成した。
各境界面は RelStruct の定数面、または二つの指定単体の共通境界へ入り、基点に固定される。
任意の境界単体を一つの面から因子分解して、全区間の相対条件を実証した。
零次元では境界が空なので同じ構成が成立する。
この構成自体には標的の Kan 性は不要である。
Kan 複体の正次数では、ホモトピー類の等式と境界固定ホモトピーの存在が同値になることを証明した。

| 主要宣言 | 内容 |
| --- | --- |
| `AdjacentFacePrism.map` / `.zero` / `.one` | 隣接二面の明示的な prism と端点の式 |
| `AdjacentFacePrism.face_of_lt` / `.face_of_gt` / `.face_self` | 各境界面への制限の三場合 |
| `relStruct_prism_face` | RelStruct の prism の各面の定数性 |
| `relStructHomotopy` | RelStruct から境界固定の実区間ホモトピーへの変換 |
| `KanHomotopyGroup.mk_eq_iff_relativeHomotopy` | 正次数の類の等式と相対ホモトピーの同値 |

参照：Goerss–Jardine I §7、Kerodon §3.2.2。
保存単位の対象ビルド 2346 jobs 成功。
私有宣言を含む 146 モジュール 2275 宣言で標準三公理のみ。
L9d は進行中。次はこれらの相対ホモトピーを球面の商へ降ろし、写像空間の連結成分と比較する。


## 54. L9d の球面と円からの写像空間の成分の計算

境界固定の単体ホモトピーを、球面の cofiber の積の pushout に沿って降ろした。
写像空間の頂点と点つき射の同値、辺と基点固定ホモトピーの相互変換を構成した。
Kan 複体の同じ成分の二頂点を一つの辺で結び、成分の等式と点つきホモトピーの存在を比較した。
これにより球面からの写像空間の π₀ と通常の正次数のホモトピー群の集合の同値を証明した。

円の Kan 置換の単位への制限は anodyne な源の置換なので、同じ比較を Kan 置換した円へ移した。
指定基本類の像による表示と一致し、powerMap m の前合成がすべての成分で m 乗になる。
球面と円の成分比較は標的の点つき射について自然である。
内部 Hom の交換についても最初の源の制限自然性を二重評価により証明した。
高次群での powerMap の作用と有理化の対象の完成はまだ主張しない。

| 主要宣言 | 内容 |
| --- | --- |
| `SphereSimplex.homotopy` / `.pullHomotopy` | 球面の商と境界固定ホモトピーの往復 |
| `PointedMapping.familyVertexEquiv` | 実際の点つき射と写像空間の頂点の同値 |
| `PointedMapping.edgeOfHomotopy` / `.homotopyOfEdge` | 基点固定ホモトピーと写像空間の辺の比較 |
| `PointedMapping.piZero_eq_iff_pointedHomotopy` | 成分の等式と基点固定ホモトピーの存在の同値 |
| `SphereSimplex.componentEquiv` / `.componentClass_natural` | 球面からの写像空間の成分と通常のホモトピー群 |
| `CirclePower.componentEquiv` / `.componentEquiv_pre_power` | 円の Kan 置換の写像空間の成分と冪の作用 |
| `CirclePower.componentEquiv_natural` | 円の成分比較の標的に関する自然性 |
| `InternalHomExchange.natural_pre_left` | 交換同型と最初の源の制限の可換性 |

参照：Goerss–Jardine I §7、Kerodon §§3.2.2–3.2.3、BF 1978 §2、HA §1.4.2。
保存単位の対象ビルド 2353 jobs 成功。
私有宣言を含む 153 モジュール 2346 宣言で標準三公理のみ。
L9d は進行中。次は loop を値とする写像の群演算と高次ホモトピー群の演算を比較する。


## 55. L9d の実際の loop の積と次数射の全正次数での計算

円の Kan 置換を値とする内部 Hom への点つき射のホモトピー類に群構造を与えた。
パラメータ源の制限は群準同型となり、零射の類は単位元となる。
第二の源の制限と内部 Hom の交換の自然性も証明し、円の次数 m の自己射が
任意のパラメータを持つ loop の類に m 乗で作用することを実証した。

二つの射影の類の積の代表を選び、loop の積を表す実際の単体的な射を構成した。
その左右の軸への制限は恒等射と点つきホモトピックである。
直積の RelStruct を成分ごとに組み合わせ、直積のホモトピー類を二つの射影で識別した。
これにより直積への誘導像を二つの軸の積に分解した。
積の射の誘導作用は、RelStruct・MulStruct から構成した通常の群の積に一致する。
反復積の実際の自己射と円の次数射を点つきホモトピー類で比較し、
円の Kan 置換の次数 m の自己射の前合成がすべての正次数の群に m 乗で作用すると証明した。
これは特定の基本類だけの計算ではなく、通常の群のすべての元に対する計算である。

| 主要宣言 | 内容 |
| --- | --- |
| `LoopMappingClasses.classEquiv` / `.groupEquiv` | loop 値の写像の類と基本群の同値と群構造 |
| `LoopMappingClasses.preHom` / `.preHom_classOf` | パラメータ源の制限準同型と実際の射の前合成 |
| `InternalHomExchange.natural_pre_right` | 第二の源の制限についての交換同型の自然性 |
| `LoopMappingClasses.classOf_zero` / `.post_power` | 零射の類と任意のパラメータでの円の冪作用 |
| `KanHomotopyGroup.prod_kanComplex` / `.prod_map_injective` | 直積の Kan 性と射影による類の識別 |
| `pointedGroupMap_prodLift` | 直積への誘導像の二つの軸による分解 |
| `LoopMappingClasses.multiplication` / `.classOf_pair_multiplication` | 類の積を表す実際の射 |
| `LoopMappingClasses.groupMap_pair_multiplication` | 通常の正次数群での積の作用 |
| `LoopMappingClasses.groupMap_pre_power` | 円の次数射の全正次数の群での冪作用 |

参照：Goerss–Jardine I §7、Kerodon §§3.1・3.2.2、BF 1978 §2、HA §1.4.2。
保存単位の対象ビルド 2360 jobs 成功。
私有宣言を含む 160 モジュール 2406 宣言で標準三公理のみ。
L9d は進行中。次は BF cotensor へこの作用を移して整数次数の telescope を構成する。


## 56. L9d の実際の BF telescope の対象と全整数次数のテンソル比較

円の Kan 置換の次数射の前合成を BF cotensor へ持ち上げた。
比較射との厳密な可換式を任意段表示へ送り、全整数次数の群で m 乗になることを証明した。
この実際の厳密な自己射を次数 2,3,4,… の順に並べ、自然数の圏の関手を構成した。
長い遷移射は厳密な合成であり、群では区間係数の冪となる。
AsSmall ℕ に添字を拡大して universe を合わせ、filtered Kan 余極限と cofibrant 置換を適用した。

群の図式の cocone を整数乗法の加法直極限へ構成した。
代表の存在と等式の後続段での検出から、集合および群の圏で余極限であることを実証した。
filtered スペクトルの群の比較と整数乗法直極限の局所化を合成し、loop telescope の群を計算した。
円の anodyne な置換単位、loop の次数移動、tail の次数補正により、
実際に構成した対象の全整数次数群と元の群の ℚ テンソルとの群同型・ℤ 線形同型を得た。
loop telescope の零段の実際の注入射が a↦a⊗1 を誘導することも証明した。

現時点で `rationalization` はこの実際の BF 対象の名称である。
この名称から ∞ 圏の局所化の普遍性を主張しない。
元の X からの標準射は、元と同じ群を持つ loop 模型の群同型からは得られない。
L9d の完了条件である元の X からの有理化写像と自然性は、引き続き実構成が必要である。
工程は未完了のままとし、L9e にはまだ進まない。

| 主要宣言 | 内容 |
| --- | --- |
| `OmegaSpectrum.cotensorStageEquiv_pre` | BF cotensor の任意段表示と源の制限の整合 |
| `OmegaSpectrum.cotensorPre_power_homotopyMap` | 円の次数射の全整数次数の冪作用 |
| `OmegaSpectrum.rationalSequence` / `.rationalDiagram` | 実際の厳密な自己射の有理化図式 |
| `OmegaSpectrum.rationalDiagram_homotopyMap` | 長い遷移射の区間係数の冪の式 |
| `OmegaSpectrum.rationalLoopTelescope` | 段ごとの Kan 余極限の BF 置換 |
| `OmegaSpectrum.rationalGroupCoconeUnderlyingIsColimit` | 群の図式の underlying での余極限性 |
| `OmegaSpectrum.rationalGroupCoconeIsColimit` | 群の圏の余極限性 |
| `OmegaSpectrum.rationalLoopTensorEquiv` | loop telescope の整数次数群の有理テンソル比較 |
| `OmegaSpectrum.rationalLoopTensorEquiv_injection_zero` | 零段の実際の射の a⊗1 の式 |
| `OmegaSpectrum.rationalization` | 次数を補正した実際の BF telescope 対象 |
| `OmegaSpectrum.rationalizationHomotopyEquiv` / `.rationalizationTensorEquiv` | 全整数次数の群同型・ℤ 線形同型 |

参照：BF 1978 §2、HTT A.3.3、HA §1.4.2。
保存単位の対象ビルド 2365 jobs 成功。
私有宣言を含む 165 モジュール 2441 宣言で標準三公理のみ。
L9d は進行中。次は次数補正した模型からの実際の射と、元の X からの標準射を扱う。


## 57. L9d の次数補正した模型からの実際の射の計算

零段を落とす tail の整数次数群の比較は、厳密なスペクトルの射に関して自然である。
同じ正次数を表す元の一段先の表示へ移し、既存の任意段表示の自然性で検証した。
これにより次数補正した loop 模型から有理化対象への実際の厳密な射を構成し、
始域の群を元の X の群へ同定した下で a↦a⊗1 を誘導すると証明した。

この模型からの射と元の X からの射を区別する。
群同型だけから両対象の間の厳密な射を得ることはできない。
次は元の X とこの模型を結ぶ実際の比較を構成するため、loop の符号を扱う。

| 主要宣言 | 内容 |
| --- | --- |
| `OmegaSpectrum.tailHomotopyEquiv_natural` | tail の群の比較の厳密な射についての自然性 |
| `OmegaSpectrum.rationalizationModel` / `.rationalizationModelHomotopyEquiv` | 次数を合わせた loop 模型と元の整数次数群の表示 |
| `OmegaSpectrum.rationalizationModelMap` | loop 模型から有理 telescope への厳密な射 |
| `OmegaSpectrum.rationalizationModelMap_homotopy` | 全整数次数の a⊗1 の計算 |

参照：BF 1978 §2、HA §1.4.2。
保存単位の対象ビルド 2367 jobs 成功。
私有宣言を含む 167 モジュール 2449 宣言で標準三公理のみ。
L9d は進行中。元の X からの標準射と自然性は未完了。


## 58. L9d の整数次数射と構造射の符号変更の実際の比較

円の Kan 置換の指定基本類を任意の基本群の元へ送る実際の自己射を構成した。
これを整数冪へ適用し、負の次数も含む円の自己射と、その全正次数群での整数冪の作用を証明した。
loop の逆元を表す実際の射を選び、その誘導準同型が通常の逆元になることを検査した。
符号反転の二回合成は恒等射と基点固定でホモトピックになる。
自己合成から全基点の同型性を検出する補題により、符号反転は全基点の π_* 同型である。
これは定数 loop の基点だけの計算ではない。

厳密な自己射 r により構造射を σ_n≫r_(n+1) に変える一般の Kan 列を構成した。
n 段の比較射に r の n 回反復を使えば、厳密な比較射が得られる。
対合性を厳密な等式で要求する必要はない。
r が各段の全基点 π_* 同型なら、変更後も Ω 条件が保たれる。
変更後の列を cofibrant に置換し、元の単射構造射に沿って比較を持ち上げた。
この BF 対象間の比較射は、各段および全整数次数で π_* 同型である。
loop cotensor の符号反転へ適用し、構造射の符号を変えた実際の BF 模型への比較を得た。

| 主要宣言 | 内容 |
| --- | --- |
| `CirclePower.classMap` / `.integerPowerMap` | 指定基本類および整数次数を実現する円の自己射 |
| `LoopMappingClasses.post_integerPower` | 任意のパラメータでの整数冪の作用 |
| `LoopMappingClasses.inversion` / `.groupMap_inversion` | 実際の逆元の射と通常の正次数群の逆元 |
| `LoopMappingClasses.groupMap_pre_integer` | 円の整数次数射の全正次数群での作用 |
| `LoopMappingClasses.pre_neg_one_twice_homotopy` / `.pre_neg_one_piIsomorphism` | 符号反転の対合性と全基点の同型性 |
| `KanPiIsomorphism.of_self_comp` | 自己合成から全基点の同型性を検出 |
| `KanSequence.twist` / `.twistMap` / `.twist_omegaCondition` | 構造射の変更と反復による厳密比較、Ω 条件の保存 |
| `OmegaSpectrum.twistComparison` / `.twistComparison_piIsomorphism` | 変更後の BF 対象への厳密な π_* 同型 |
| `OmegaSpectrum.negatedCotensor` / `.negatedCotensorComparison_piIsomorphism` | 符号を変えた loop 模型の実際の比較 |

参照：Goerss–Jardine I §7、Kerodon §3.2.3、BF 1978 §2、HTT A.3.3、HA §1.4.2。
保存単位の対象ビルド 2375 jobs 成功。
私有宣言を含む 175 モジュール 2502 宣言で標準三公理のみ。
L9d は進行中。次はホモトピー可換な段の比較を厳密な射へ直す相対充填を扱う。


## 59. L9d のホモトピー可換な段の比較の厳密化

単射な点つき部分対象上の基点固定ホモトピーを、指定した始点を保って全体へ延長した。
延長したホモトピーの基点の固定は、部分対象の基点から回収される。
通常のパラメータ族による頂点と点つき閉構造による頂点を、smash の非基点側の単位の評価で比較した。
この二つの頂点表示は厳密に一致する。
その結果、射の成分の等式は前合成・後合成・suspension で保たれる。

単射な構造射を持つ源から Kan 列への段ごとの比較について、
成分での構造可換式から実際の厳密な列の射を構成した。
零段を保ち、修正した n 段を固定するように次段のホモトピーを延長する。
各段は指定した元の射と同じ成分を保ち、全基点の π_* 同型性も保つ。
標的が Ω 列なら、さらに cofibrant 置換へ持ち上げ、実際の BF 対象間の π_* 同型を得られる。

この一般補題を元の X の有理化写像へ適用するには、
符号を調整した loop 模型への随伴構造射の成分での可換性の幾何的な証明がまだ必要である。
特に二つの円の変数の交換と符号反転を実際のホモトピーで比較する部分を残している。
この未証明の条件を追加公理や入力構造として有理化の完成に組み込まない。

| 主要宣言 | 内容 |
| --- | --- |
| `PointedExtension.exists_homotopy_from_zero` / `.exists_adjustment` | 始点を保つ相対ホモトピー延長と制限を厳密にする修正 |
| `PointedMapping.pointFamily_closed` / `.familyVertex_eq_pointedHomVertex` | 頂点の二つの表示の厳密な一致 |
| `PointedMapping.componentOf_suspension` | suspension による成分の等式の保存 |
| `KanSequence.rectify` / `.rectify_component` | 段ごとのホモトピー可換な比較の厳密化 |
| `KanSequence.rectify_levelwise` | 厳密化による全基点の同型性の保存 |
| `OmegaSpectrum.rectifyInto` / `.rectifyInto_projection` | 標的の BF 置換への実際の射と因子分解 |
| `OmegaSpectrum.rectifyInto_piIsomorphism` | 厳密化した BF 射の全整数次数の同型性 |

参照：Goerss–Jardine I §7、BF 1978 §2、HTT A.3.3、HA §1.4.2。
保存単位の対象ビルド 2380 jobs 成功。
私有宣言を含む 180 モジュール 2543 宣言で標準三公理のみ。
L9d は進行中。次は二つの円の変数の交換の符号を幾何的に比較する。


## 60. L9d の二つの三角形による符号比較の幾何的な補助対象

区間の正方形への上側・下側の三角形の射と共通の対角辺を構成した。
座標の交換は二つの三角形を厳密に交換し、両三角形の中間の面は同じ対角辺となる。
ホーン Λ[2,1] を潰した相対三角形を作り、残る辺を円からの点つき射として構成した。
この相対三角形の基点包含は anodyne であり、Kan 値の点つき写像空間は全単射への RLP を持つ。
さらにその写像空間の恒等射と零射を結ぶ、基点固定の実際の収縮も充填した。

ホーンに欠けた面を引き戻すとその面の境界になることを全次元で証明した。
ホーンと欠けた面の和が全境界となることを使い、境界を二つの部分の pushout として表示した。
共通部分を面の境界へ戻す射を作り、ホーンを潰して残る面を球面へ送る付着写像を構成した。
二次元で円へ cell を付けた対象と相対三角形を、通常の点つき同型で比較した。
この同型から対角辺の円からの射の単射性が従う。
よって相対三角形から対角 loop への写像空間の制限は Kan fibration である。

二つの三角形を共通の対角辺で貼り合わせた表示と、そこでの交換の逆元の計算は未完了である。
これを証明して元の X からの標準射へ適用するまで L9d は進行中とする。

| 主要宣言 | 内容 |
| --- | --- |
| `SquareTriangles.upper` / `.lower` / `.upper_diagonal` / `.upper_swap` | 正方形の二つの三角形と対角辺・交換 |
| `triangleDisk` / `triangleDiskDiagonal` | ホーンを潰した相対三角形と対角辺の円 |
| `triangleDiskHom_terminal_rlp` / `triangleDiskHom_exists_contraction` | Kan 値写像空間の全単射 RLP と基点固定の収縮 |
| `preimage_horn_face` / `hornBoundaryPushout` | 欠けた面との交わりと全境界の pushout 表示 |
| `boundaryFaceCollapse` / `boundaryFaceCollapse_face` | ホーンを潰す付着写像と残る面での計算 |
| `triangleCellIso` | 相対三角形と円への二次元 cell 付着の同型 |
| `triangleDiskDiagonal_mono` / `triangleDisk_restriction_fibration` | 対角辺の単射性と写像空間の Kan fibration |

参照：Goerss–Jardine I §7、Kerodon §§3.1・3.2.3、BF 1978 §2、HTT A.3.3。
保存単位の対象ビルド 2389 jobs 成功。
私有宣言を含む 189 モジュール 2624 宣言で標準三公理のみ。
L9d は進行中。次は正方形の二つの三角形の貼り合わせと交換の符号を計算する。

## 61. L9d の正方形の厳密な三角形分割

二つの三角形の包含の単射性を、頂点の座標の和から回収した。
区間値の二つの単調写像は一方が他方以下となるため、全ての正方形の単体はどちらかの三角形に属する。
両方に属する単体は共通の対角辺から来ることも示した。
各単体次数での pullback と被覆から型の pushout を得て、評価関手によって単体集合の pushout へ戻した。
外側の四辺を座標軸の射として厳密に計算した。

| 主要宣言 | 内容 |
| --- | --- |
| `SquareTriangles.upper_mono` / `.lower_mono` | 二つの三角形の包含の単射性 |
| `SquareTriangles.upper_lower_cover` | 全単体次数での二つの三角形の被覆 |
| `SquareTriangles.upper_lower_intersection` | 交わりの対角辺への因子分解 |
| `SquareTriangles.app_isPullback` / `.app_isPushout` | 単体次数ごとの普遍性 |
| `SquareTriangles.isPushout` | 正方形の厳密な三角形分割 |
| `SquareTriangles.upper_face_zero` / `.lower_face_last` | 外側の辺の座標表示 |

参照：Goerss–Jardine I §7、Kerodon §3.2.3、BF 1978 §2。
保存単位の対象ビルド 2394 jobs 成功。
私有宣言を含む 194 モジュール 2660 宣言で標準三公理のみ。
L9d は進行中。次は外側の境界を潰した点つきの貼り合わせを構成する。

## 62. L9d の正方形の境界の二方向の商

境界で定数な単体のパラメータ族を球面との積へ降ろす一般構成を作った。
商射上での復元と球面の基点での定数性を厳密に計算した。
パラメータの指定部分での定数性も降下後に保たれ、この指定部分の射には単射性を要しない。
この構成を二度適用して正方形の四辺を潰し、二つの円の積からの reduced map を得た。
両軸の定数性から smash 積からの実際の点つき射へ降ろした。
二つの商射と smash の商射を前合成すると元の正方形の写像へ戻る。

| 主要宣言 | 内容 |
| --- | --- |
| `SphereSimplex.productDesc` | 境界定数な単体の族の球面への降下 |
| `SphereSimplex.quotient_productDesc` / `.base_productDesc` | 商射上の復元と基点条件 |
| `SphereSimplex.productDesc_parameter_constant` | パラメータの指定部分の定数性の保存 |
| `SphereSimplex.squareDesc` / `.squareDesc_quotient` | 正方形から円の積への降下と復元 |
| `SphereSimplex.squareDesc_base_left` / `.squareDesc_base_right` | 両軸での定数性 |
| `SphereSimplex.squareSmashDesc` / `.squareSmashDesc_quotient` | smash 積への点つき降下と復元 |

参照：Goerss–Jardine I §7、Kerodon §3.2.3、BF 1978 §2。
保存単位の対象ビルド 2396 jobs 成功。
私有宣言を含む 196 モジュール 2685 宣言で標準三公理のみ。
L9d は進行中。次は相対三角形の貼り合わせとの比較の存在と一意性を示す。

## 63. L9d の正方形上での一意性の判定

境界の頂点を使い、円の商射が全射であることを pushout の全射性から証明した。
閉構造の積関手が全射を保つことにより、二つの円の商射の積も全射となる。
smash の商の普遍性と合わせて、二つの円の smash 積からの点つき射は正方形上で判定できる。
また境界との積からの射を、境界の各面との積上で判定する補題を構成した。

| 主要宣言 | 内容 |
| --- | --- |
| `circleQuotient_epi` / `squareCircleQuotient_epi` | 円の商射とその積の全射性 |
| `squareSmash_hom_ext` | 正方形上での smash 積からの射の一意性 |
| `boundary_tensor_hom_ext` | 境界との積における面ごとの等式判定 |

参照：Goerss–Jardine I §7、Kerodon §3.2.3。
保存単位の対象ビルド 2398 jobs 成功。
私有宣言を含む 198 モジュール 2692 宣言で標準三公理のみ。
L9d は進行中。次は二つの相対三角形から貼る写像の四辺の条件を検証する。
