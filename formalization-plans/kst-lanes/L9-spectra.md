# K-L9（Sp・ホモトピー群）

> **v2 の位置づけ（2026-10-19）**：foundations.md §6 の K-Sp。L9e の後、γ3 を使って Sp の ∞ 極限と安定 ∞ 圏としての Sp（局所化不変量の値域）。

## 引き継ぎ（2026-10-19）

### 現在地
- L9a・L9b・改訂 L9c・L9d 完了。L9e は未完。
- Sp の quasicategory 性、全整数次数の群、置換、homotopy fiber の長完全列、有理 telescope とテンソル表示を構成済み。
- hG と homotopy Tot の段ごとの Kan 構成・BF 置換・比較射、および自明作用の標準射の全整数次数 π の単射性まで証明済み。
- 有理化各段の高次群係数で BG の通常の正規化 cochain の正次数 cohomology が消滅することを証明済み。
- 球面的境界の交代関係と充填判定、骨格の一段の厳密な延長と通常の cocycle 条件の同値、任意の cochain・cocycle の骨格の射による実現まで完了。
- 最新の実装保存：`c5872423`。直前の保存：`e4bb0902`、`9c9a3de5`。詳細の到達点は既存本文 §116–119。
- 停止前の対象ビルド：`lake build SerrePositivity.KST.Spectra`、3979 jobs、終了コード 0。
- 停止前の公理監査：`lake env lean scripts/audit_kst_spectra.lean`、511 モジュール・4951 宣言、標準三公理のみ、終了コード 0。

### 残り（依存順）
- 以下は粗い実作業時間の見積もりであり、外部待ちと全体合流の時間を含めない。
- 骨格の射の係数表示を写像空間の連結成分へ移し、正次数群の既存表示・連結準同型・球面の向きと整合させる。
  原典：Goerss–Jardine I §7、VIII §1、Kerodon §3.2.3。24–60 時間。
- 上の比較を使い `coefficientDifferential` と通常の正規化交代微分を同定し、零性だけでなく像・係数同型の符号も照合する。
  原典：Goerss–Jardine VIII §§1–2、III §2。24–60 時間。
- 塔の完備性、必要な逐次充填・lim¹ の制御を含む収束を証明し、cohomology の消滅を写像空間の π の消滅へ移す。
  原典：Goerss–Jardine VIII §§1–2。24–80 時間。E₂ の消滅だけで収束を仮定しない。
- 有限群の有理自明作用について標準射の全射性を証明し、既証の単射性と合わせて全整数次数の有理 Shapiro を完成させる。
  原典：Goerss–Jardine VIII §2、Bousfield–Friedlander 1978 §2。上記の後で 8–24 時間。
- 通常の余単体 Tot と一般の BF 置換した homotopy Tot の比較を完了する。
  原典：Goerss–Jardine VII §4、VIII §1、HTT A.3.3。12–32 時間。
- γ3 後の導来写像空間を持つ正しい Sp との比較・Sp の ∞ 極限性は後続範囲であり、現段階の主張に含めない。
  原典：HTT Theorem 4.2.4.1、HA §1.4.2。γ3 完了後 16–40 時間。

### 主要宣言（共通接頭辞 `SerrePositivity.KST.Spectra`、以下は名前のみ）
- `KanHomotopyGroup`
- `OmegaSpectrum`
- `Sp`
- `OmegaSpectrum.homotopyGroupEquivAt`
- `OmegaSpectrum.homotopyFiberLongExact`
- `OmegaSpectrum.rationalization`
- `OmegaSpectrum.rationalizationTensorEquiv`
- `homotopyFixedPoints`
- `homotopyTotalization`
- `homotopyFixedPointsUnit_homotopyMap_injective`
- `SkeletalCellAttachment.stageFiberCoefficientEquiv`
- `SkeletalCellAttachment.coefficientDifferential`
- `RationalLevelNormalizedCochains.positive_cohomology_isZero`
- `SphericalBoundary.boundary_filler_iff`
- `SkeletalSphericalCochain.extension_iff_differential_eq_zero`
- `SkeletalSphericalRealization.exists_extended_realization`

### 依存と提供
- 読取専用：Mathlib の PtSimplex・RelStruct・MulStruct、pushout-product、骨格の相対セル分解、正規化鎖、群 cochain。
- 読取専用：既存 Spectra/ の点つき単体集合・閉構造・通常の cofiber。安定モデル構造の結果は借用しない。
- 読取専用：HomotopicalAlgebra/Simplicial/ のホーン充填・因子分解・AnodyneKanReplacement と一般の Reedy 因子分解。
- 読取専用：InfinityCategories/ の coherent nerve の γ1、Core の Kan 性、HomotopyLimits の Bousfield–Kan end。
- 提供：π_n と関手性・長完全列、BF 対象と Sp、整数 π、置換、有理化、hG/Tot の具体的な模型、骨格の障害計算。
- H_* は K-L2、pro 形式は K-L6、γ3 は N 所有。K 理論の主定理への合流は他レーンの仕事。

### 未コミット
- 本節の保存後、K-L9 所有ファイルに未コミットなし。Lean の最後の保存は `c5872423`。
- 共有ルート `SerrePositivity.lean` および他レーンの既存差分は触らず、今回のコミット対象にも含めない。

### 既知の問題
- 自分の import 閉包と対象ビルドは成功。全体ビルドは今回再実行していない。
- 前回の L9d 全体ビルドは共有ルートの `relativeFunctorVertex` 重複で失敗した。今回その衝突の解消は未確認。
- 所有ソースの sorry・追加 axiom はなし。所有宣言の型に `HomotopicalAlgebra.ModelCategory` 定数がないことも Lean 環境を走査して確認済み。
- import 閉包に KanQuillen モジュールなし。`SSet.modelCategoryQuillen` 名前空間は Mathlib のホーン生成射・Fibration の既存 API に使うが、`ModelCategory SSet` は仮定しない。
- 公理監査は私有宣言と推移的な公理依存も調べる。標準三公理の検査だけでは instance 仮定を検出しないため、上記の型走査は別途実行した。
- BF cofibrant–fibrant 仕様を承認済み。構造射は単射、随伴は全基点 π_* 同型。厳密 Ω 同型は要求しない。
- 厳密 Ω 同型と厳密極限だけからの局所 Kan 性は未解決だったため改訂した。現仕様では単射の指数版・引き戻し・塔の RLP 閉性で証明する。
- cohomology の消滅と骨格の延長判定は証明済みだが、有理 Shapiro の全射性・収束・塔の微分の交代式を完了扱いにしない。

### 次の一手
- `FunctionComplexPointedSimplex` と `SphereMappingComponents` を読み、関数複体の π₀ と座標ごとの π₀ の同値を Kan 充填で構成する。
- それをセルの fiber 表示へ合成し、§119 の骨格上の係数と写像空間の連結成分の係数を同一の代表で比較する。この工程は未着手。

## 所有するもの・借りるもの

- 所有：Kan 複体の π_n とその群構造・自然性・ホモトピー不変性。
- 所有：Kan fibration の連結射とホモトピー長完全列。
- 所有：γ-B の Ω スペクトル、その単体的圏と coherent nerve。
- 所有：整数次数のスペクトルの π_n。
- 所有：有理化、hG、Tot の Kan 複体による実構成。
- 借用：Mathlib の EG の自由 G 集合の単体的図式と、斉次・非斉次座標の作用の同型。
- 借用：H_* は K-L2 が所有する。
- 借用：Mathlib の正規化鎖複体、非退化単体の余積表示、生成子の交代微分式。ここでは Hom による cochain の比較先の構成だけに使い、H_* の結果を追加しない。
- 借用：pro 形式は K-L6 が所有する。
- 借用：γ1 は N レーンの局所 Kan coherent nerve 定理。
- 借用：γ3 は N レーンのホモトピー極限と ∞ 極限の比較。
- 借用：N の HomotopyLimits の Bousfield–Kan end・ホーン充填による Kan 性・path 置換による係数のホモトピー不変性。
- この借用は段ごとの単体集合の実構成だけに使い、Sp の ∞ 極限性や導来写像空間の比較を主張しない。
- 借用：Core の pinched 写像空間とその Kan 性。
- 借用：既存 Pointed.CofiberPushout の通常の商の点つき pushout の普遍性。安定モデル構造は含まない。
- 既存 Spectra は比較用に読むだけで編集しない。
- 既存 Spectra の `PointedSimplicialSet.Basic` と `Pointed.InternalHom` の基礎定義を借りる。
- この借用は Under による点つき対象と等化子による Hom のみで、安定モデル構造は含まない。
- suspension・loop では既存 Spectra の円、smash、閉対称モノイダル構造の通常の圏論的構成も借りる。
- 借用：既存 Pointed の自由基点の追加、自由基点の smash と直積の同型、tensor した余積の普遍性。
- 豊穣構造の移送は既存 CategoryTheory の通常の lax monoidal 関手の補題を借りる。
- 既存 HomotopicalAlgebra は読むだけで編集しない。
- 借用：同ディレクトリの基点を含む指定部分を固定する垂直ホモトピー充填。
- 借用：`AnodyneKanReplacement` のホーンの小対象論法と `Generators` の境界生成定理。
- 借用：一般の Reedy 次数帰納による関手的因子分解、matching・latching の右類・左類閉性、simplex 圏の Reedy 構造。
- この借用は通常の因子分解と持ち上げ性だけであり、Reedy モデル圏や HT-KQ のインスタンスを用いない。
- これらはモデル構造を仮定しない充填と因子分解で、HT-KQ の import は含まない。
- 既存 InfinityCategories は読むだけで編集しない。

## 1. 正本と目的

作成日：2026-10-18。
状態：L9a・L9b・L9c・L9d 完了。L9e 進行中。
Sp、自然な任意段表示、置換、任意の射の homotopy fiber と整数次数の長完全列まで検証済み。
対象ビルド・511 モジュール 4951 宣言の公理監査成功。
直近の工程区切りの全体ビルド（L9d、12125 jobs）は共有ルートの他レーンの宣言重複で失敗。
`InfinityCategories.F1.RelativeFunctorVertices` と `F1B.RelativeFunctorHomotopyComposition` の
`relativeFunctorVertex` 重複。K-L9 の import 閉包と対象ビルドは成功。
最後に成功した全体ビルドは L9c、9543 jobs。
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
| L9d | 完了 | 実際の telescope 有理化・単位・射、全整数次数の自然なテンソル比較 |
| L9e | 進行中 | Tot、hG、有理自明作用の比較 |

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

## 記録の所在

実施記録・現在地の詳細・型一覧は [archive/L9-spectra-log.md](archive/L9-spectra-log.md) に移した（2026-10-19）。現在地は冒頭の引き継ぎ節が正本で、工程ごとの記録はコミットメッセージに置く。
