# K-L9（Sp・ホモトピー群）

> **v2 の位置づけ（2026-10-19）**：foundations.md §6 の K-Sp。L9e の後、γ3 を使って Sp の ∞ 極限と安定 ∞ 圏としての Sp（局所化不変量の値域）。

## 引き継ぎ（2026-10-19）

### 現在地
- L9a・L9b・改訂 L9c・L9d、Sp-1d（係数微分の値・符号・像の同定、10-19 14:07）完了。L9e 全体は未完。
- Sp の quasicategory 性、全整数次数の群、置換、homotopy fiber の長完全列、有理 telescope とテンソル表示を構成済み。
- hG と homotopy Tot の段ごとの Kan 構成・BF 置換・比較射、および自明作用の標準射の全整数次数 π の単射性まで証明済み。
- 有理化各段の高次群係数で BG の通常の正規化 cochain の正次数 cohomology が消滅することを証明済み。
- 球面的境界の交代関係と充填判定、骨格の一段の厳密な延長と通常の cocycle 条件の同値、任意の cochain・cocycle の骨格の射による実現まで完了。
- 関数複体の π₀ の座標表示を Kan 充填で構成し、骨格 fiber の係数へ合成済み。相対商の fiber 頂点とセル単体から復元する頂点も厳密に一致する。
- 復元した頂点を含めると元の射に戻り、成分係数は既存 cochain と一致する。成分と正次数群の係数は同じセル球面への制限で計算され、正規化微分の交代式も保持する。
- 反復 loop 値の fiber の π₀ と元の fiber の全正次数群を比較し、既存係数表示との正符号の可換式を証明済み。
- 同じ境界の二つの零ホモトピーの差を、一つ高いホモトピー群の類として Kan 充填から構成済み。充填選択からの独立性、自然性、自己差の単位元、逆元、三つの差の合成則を証明済み。
- 実際の塔の微分の各セルの係数を、セル境界の連結射とその cofiber 単体・零ホモトピーで計算済み。
- loop 交換の頂点を円の射と標準区間の辺で厳密に照合済み。骨格 fiber の通常の零 loop 比較の包含は明示した逆辺の類と一致し、実際の成分微分の係数を次数二以上の正規化交代微分と (-1)^(セル次元) で計算済み。
- Kan fibration の下で同じ downstairs の類を持つ代表を、射影が指定した単体と厳密に一致する upstairs の代表へ調整済み。整合する類の族を厳密に整合する代表へ直し、極限の群から段ごとの群の逆極限への比較準同型の全射性を証明済み。
- 整合する RelStruct を極限の RelStruct へ組み立てる式と、比較の核が各段で零となる類であることを証明済み。非可換 lim¹ を twisted 作用の軌道集合で構成し、全射な遷移のときの消滅を証明済み。固定した核の球面代表から lim¹ の障害を構成し、零ホモトピーの選択変更が twisted 作用になること、極限で零な代表の障害が基点となることを証明済み。球面代表変更への不変性、核から lim¹ への基点を保つ写像を証明済み。零障害から厳密に整合する零ホモトピーを逐次構成し、核上の障害が零であることと極限の類の零性の同値を証明済み。lim¹ 消滅時の比較の単射性、次の次数の遷移が全射な塔の比較群同型まで完了。核と lim¹ の全単射、および必要な骨格の塔での消滅は未完。
- 比較ホーンの fiber 内の終点を比較し、標準の接続準同型と loop 同型の反可換式を全正次数で証明済み。
- 標準の零次数接続写像とその厳密な正方形への自然性を構成し、正次数・零次数の塔の微分の loop 反可換式を証明済み。
- 骨格の零次数・π₀ の反可換式に加え、実際の成分微分のセルへの自然性と、入力を保持した相対商の射の代表を構成済み。
- path の収縮の終点を厳密に計算し、`loopZeroHomotopyEquiv` は通常の円の成分表示の逆元と証明済み。置換円の写像類・セル球面・骨格の各係数でもこの向きを照合済み。
- cochain 次数 d ≥ 1 の全高次数 r で、実際の群の `coefficientDifferential` は通常の正規化微分の (-1)^(d+2+r) 倍と証明済み。次数の標準同定を含む加法準同型の等式、および核・像の一致も証明済み。
- 検証：対象ビルド 4110 jobs、専用監査 638 モジュール・6185 宣言、標準三公理のみ。ともに終了コード 0。
- 全体ビルド：14658 jobs、終了コード 0。以前の共有 F1/F1B の import 衝突は今回再現しない。

### 残り（依存順）
- 以下は粗い実作業時間の見積もりであり、外部待ちと全体合流の時間を含めない。
- 塔の完備性、必要な逐次充填・lim¹ の制御を含む収束を証明し、cohomology の消滅を写像空間の π の消滅へ移す。正次数の比較の全射性、lim¹ 消滅からの単射性、全射遷移の lim¹ 消滅は証明済み。Mittag–Leffler 条件での lim¹ 消滅、核と lim¹ の全単射、必要な骨格の塔での収束を残す。
  原典：Goerss–Jardine VIII §§1–2。24–80 時間。E₂ の消滅だけで収束を仮定しない。
- 有限群の有理自明作用について標準射の全射性を証明し、既証の単射性と合わせて全整数次数の有理 Shapiro を完成させる。
  原典：Goerss–Jardine VIII §2、Bousfield–Friedlander 1978 §2。上記の後で 8–24 時間。
- 通常の余単体 Tot と一般の BF 置換した homotopy Tot の比較を完了する。
  原典：Goerss–Jardine VII §4、VIII §1、HTT A.3.3。12–32 時間。
- γ3 後の導来写像空間を持つ正しい Sp との比較、Sp の ∞ 極限と安定性、局所化不変量の値域としての界面を完成させる。
  これらは後続範囲であり、現段階の主張に含めない。
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
- `SimplicialFunctionComplex.componentEquiv`
- `SkeletalCellAttachment.stageFiberComponentEquiv`
- `PointedFibrationTower.limitGroupEquivOfSurjective`
- `NullHomotopyDifference.difference`
- `NullHomotopyDifference.difference_map`
- `PointedFibrationTower.kernelObstruction_eq_point_iff`
- `PointedFibrationTower.kernelObstruction`
- `PointedFibrationTower.limitGroupComparison`
- `PointedFibrationTower.limitGroupComparison_surjective`
- `SkeletalCellAttachment.coefficientDifferential_all_alternating`
- `SkeletalCellAttachment.positiveAdditiveCoefficientDifferential_eq`
- `TowerLimOne.subsingleton_of_surjective`
- `SkeletalCellAttachment.positiveAdditiveCoefficientDifferential_ker`
- `SkeletalCellAttachment.positiveAdditiveCoefficientDifferential_range`
- `SkeletalCellAttachment.coefficientDifferential_loopPositive`
- `SkeletalCellAttachment.coefficientDifferential`
- `RationalLevelNormalizedCochains.positive_cohomology_isZero`
- `SphericalBoundary.boundary_filler_iff`
- `SkeletalSphericalCochain.extension_iff_differential_eq_zero`
- `SkeletalSphericalRealization.exists_extended_realization`

### 依存と提供
- 読取専用：Mathlib の PtSimplex・RelStruct・MulStruct、pushout-product、骨格の相対セル分解、正規化鎖、群 cochain。
- 読取専用：既存 Spectra/ の点つき閉構造・cofiber、Comparison/BasedPathEndpoint の汎用評価式。安定モデル構造は借用しない。
- 読取専用：HomotopicalAlgebra/Simplicial/ のホーン充填・因子分解・AnodyneKanReplacement と一般の Reedy 因子分解。
- 読取専用：InfinityCategories/ の coherent nerve の γ1、Core の Kan 性、HomotopyLimits の Bousfield–Kan end。
- 提供：π_n と関手性・長完全列、BF 対象と Sp、整数 π、置換、有理化、hG/Tot の具体的な模型、骨格の障害計算。
- H_* は K-L2、pro 形式は K-L6、γ3 は N 所有。K 理論の主定理への合流は他レーンの仕事。

### 未コミット
- この保存単位の後、K-Sp 所有ファイルに未コミットなし。保存内容は最新の K-Sp コミットを参照。
- 共有ルート `SerrePositivity.lean` および他レーンの既存差分は触らず、今回のコミット対象にも含めない。

### 既知の問題
- 自分の import 閉包・対象ビルド・公理監査・全体ビルドは成功。既報の共有 F1/F1B の重複は今回再現しない。
- 所有ソースの sorry・追加 axiom はなし。所有宣言の型に `HomotopicalAlgebra.ModelCategory` 定数がないことも Lean 環境を走査して確認済み。
- import 閉包に KanQuillen モジュールなし。`SSet.modelCategoryQuillen` 名前空間は Mathlib のホーン生成射・Fibration の既存 API に使うが、`ModelCategory SSet` は仮定しない。
- 公理監査は私有宣言・推移的な公理依存と、宣言型の ModelCategory 定数を検査する。
- BF cofibrant–fibrant 仕様を承認済み。構造射は単射、随伴は全基点 π_* 同型。厳密 Ω 同型は要求しない。
- 厳密 Ω 同型と厳密極限だけからの局所 Kan 性は未解決だったため改訂した。現仕様では単射の指数版・引き戻し・塔の RLP 閉性で証明する。
- coefficientDifferential の交代式・符号・核・像は全添字で証明済み。cohomology の消滅だけで有理 Shapiro の全射性・収束を完了扱いにしない。

### 次の一手
- lim¹ の消滅を全射遷移から Mittag–Leffler 条件へ拡張し、実際の骨格の塔の遷移の像を係数微分の計算から制御する。零障害の判定・整合する零ホモトピー・比較の単射性は `TowerKernelNullCriterion` まで既証なので再構成しない。
- 核と lim¹ の全単射も残る。`kernelObstruction` の単位元の逆像が単位元だけとは証明済みだが、それだけで写像全体の単射性・全射性を主張しない。任意の差の類の実現と厳密な相対持ち上げは `NullDifferenceRealization`・`NullHomotopyStrictLifting` を使う。
- Sp-2 の収束、Shapiro 全射性、通常の Tot 比較、∞ 圏 Sp は未完。比較の全射性と整合する RelStruct の極限への組み立ては既証だが、段ごとの零性だけから整合する零ホモトピーを仮定しない。

## 範囲と所有

- 作業場所：`SerrePositivity/KST/Spectra/`、namespace `SerrePositivity.KST.Spectra`。
- 集約入口：`SerrePositivity/KST/Spectra.lean`、監査：`scripts/audit_kst_spectra.lean`。
- 共有ルート・他レーン・既存 Spectra/・HomotopicalAlgebra/・InfinityCategories/ は読むだけ。
- 既存の未コミット変更を保存し、他者の新規ファイルをコミットしない。
- 全体の正本は [foundations.md](../foundations.md)、K の正本は [経路](../k-theory-kst-route.md) §13。
- H_* と pro の旧レーンは凍結。γ3・γ4 は N 所有。K の合流は K-基盤レーンが担当する。

## 実装仕様

- Kan 複体の π_n は PtSimplex と RelStruct の商。零次数は pointed set、正次数は群、二以上は可換群。
- fiber と長完全列は実際の Kan fibration の充填から構成する。
- Sp は BF cofibrant–fibrant 型の Ω スペクトルの単体的圏の coherent nerve（γ-B）。
- 構造写像 ΣX_n → X_(n+1) は単射、随伴は全基点で π_* 同型。厳密な Ω 同型を要求しない。
- 写像空間は有限切断の Hom の fibration の塔の極限。指数・引き戻し・塔の相対 RLP で Kan 性を示す。
- π_j は十分高い段の π_(j+k)(X_k) と遷移同型で定義し、整数次数の自然性を保つ。
- 置換は写像柱・境界セル分解・AnodyneKanReplacement の実構成。
- 有理化は正整数の乗法の telescope と π_* のテンソル比較。
- Tot・hG は段ごとの Kan 模型。通常の Tot と BF 置換した homotopy Tot の比較を分ける。
- γ3 後に導来 Sp との比較と ∞ 極限性、続いて安定性と局所化不変量の値域を示す。
- cohomology 消滅だけから塔の収束や Shapiro 全射性を主張しない。
- coefficientDifferential の同定は零性だけでなく像と符号も比較する。

## 原典

| 対象 | 原典 |
| --- | --- |
| Kan、π_n、群の演算、fiber 長完全列 | Kerodon §§3.1–3.2、Goerss–Jardine I §§7–8 |
| セルの係数・正規化・塔の収束 | Goerss–Jardine III §2、VIII §§1–2 |
| 通常の Tot | Goerss–Jardine VII §4、VIII §1 |
| coherent nerve | HTT 1.1.5.10、Kerodon 2.4.5.1 |
| BF 模型 | Bousfield–Friedlander 1978 §2、HTT A.3.3 |
| Sp と ∞ 極限の比較 | HTT 4.2.4.1、HA §1.4.2 |

原典の主張を公理や未証明の入力構造にしない。未確認の定理番号は節番号で示す。

## 検証と保存

- 保存単位ごとに `lake build SerrePositivity.KST.Spectra` と専用公理監査。
- 許容公理は `propext`・`Classical.choice`・`Quot.sound` のみ。私有宣言と推移的依存も監査。
- 主経路の宣言の型に `HomotopicalAlgebra.ModelCategory` がないことを Lean 環境走査で確認。
- `ModelCategory SSet`・cofibrant generation・Quillen bifunctor を主経路の仮定にしない。
- KanQuillen の import は不可。Mathlib のホーン生成射・Fibration API は使用する。
- 工程区切りで全体ビルド。自分の import 閉包の破損を他者の修正で迂回しない。
- `git diff --check`。コミットは所有ファイルだけを `git commit --only`。amend・rebase・reset はしない。
- 本文 300 行以内、引き継ぎ 100 行以内。実施記録はコミットメッセージ。
- 旧本文・型一覧は [archive/L9-spectra-log.md](../archive/L9-spectra-log.md) に保存。
