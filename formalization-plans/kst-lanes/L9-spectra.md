# K-L9（Sp・ホモトピー群）

> **v2 の位置づけ（2026-10-19）**：foundations.md §6 の K-Sp。L9e の後、γ3 を使って Sp の ∞ 極限と安定 ∞ 圏としての Sp（局所化不変量の値域）。

## 引き継ぎ（2026-10-19）

### 現在地
- L9a・L9b・改訂 L9c・L9d 完了。L9e は未完。
- Sp の quasicategory 性、全整数次数の群、置換、homotopy fiber の長完全列、有理 telescope とテンソル表示を構成済み。
- hG と homotopy Tot の段ごとの Kan 構成・BF 置換・比較射、および自明作用の標準射の全整数次数 π の単射性まで証明済み。
- 有理化各段の高次群係数で BG の通常の正規化 cochain の正次数 cohomology が消滅することを証明済み。
- 球面的境界の交代関係と充填判定、骨格の一段の厳密な延長と通常の cocycle 条件の同値、任意の cochain・cocycle の骨格の射による実現まで完了。
- 関数複体の π₀ ≃ 座標ごとの π₀ を Kan 充填で構成し、骨格 fiber の成分係数表示へ合成済み。
- 元の骨格射の相対商が定める fiber 頂点と、指定したセル単体から復元する頂点の厳密な一致を証明済み。
- その頂点を写像空間へ含めると元の射に戻る。実際の成分係数は既存 cochain と一致し、正規化微分の交代式も保持する。
- 成分と正次数群の係数は同一のセル球面への制限射で計算できる。
- 反復 loop 値の fiber の π₀ と元の fiber の全正次数群を比較し、既存係数表示との正符号の可換式を証明済み。
- 源の正方形による相対商・fiber・連結射の自然性と、セル境界 fiber への制限を構成済み。
- 実際の塔の微分の各セルの係数を、そのセルの境界制限の連結準同型で表す厳密な式を証明済み。
- 旧実装保存：`c5872423`。従来の詳細は [記録](../archive/L9-spectra-log.md) §116–119。
- 停止前の対象ビルド：`lake build SerrePositivity.KST.Spectra`、3996 jobs、終了コード 0。
- 停止前の全体ビルド：`lake build`、13858 jobs、終了コード 0。
- 停止前の公理監査：`lake env lean scripts/audit_kst_spectra.lean`、528 モジュール・5108 宣言、標準三公理のみ、終了コード 0。

### 残り（依存順）
- 以下は粗い実作業時間の見積もりであり、外部待ちと全体合流の時間を含めない。
- セル境界の局所的な連結準同型を反復 loop の成分代表で計算し、球面的境界の向きと整合させる。
  全正次数の係数比較と微分のセル境界への帰着は比較済みだが、局所的な連結射の符号はまだ同定していない。
  原典：Goerss–Jardine I §7、VIII §1、Kerodon §3.2.3。24–60 時間。
- 上の比較を使い `coefficientDifferential` と通常の正規化交代微分を同定し、零性だけでなく像・係数同型の符号も照合する。
  原典：Goerss–Jardine VIII §§1–2、III §2。24–60 時間。
- 塔の完備性、必要な逐次充填・lim¹ の制御を含む収束を証明し、cohomology の消滅を写像空間の π の消滅へ移す。
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
- `SkeletalCellAttachment.stageFiberComponentEquiv_simplexVertex`
- `SkeletalCellAttachment.skeletalFiberVertex_eq_simplexVertex`
- `SkeletalCellAttachment.skeletalFiberVertex_cochain`
- `SkeletalCellAttachment.stageFiberIteratedLoopComponentEquiv`
- `SkeletalCellAttachment.stageFiberCoefficientEquiv_iteratedLoopComponent`
- `SkeletalCellAttachment.stageFiberDifferential_cellConnecting`
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
- この保存単位の後、K-Sp 所有ファイルに未コミットなし。保存内容は最新の K-Sp コミットを参照。
- 共有ルート `SerrePositivity.lean` および他レーンの既存差分は触らず、今回のコミット対象にも含めない。

### 既知の問題
- 自分の import 閉包・対象ビルド・全体ビルドは成功。以前の `relativeFunctorVertex` 重複は今回再現しない。
- 所有ソースの sorry・追加 axiom はなし。所有宣言の型に `HomotopicalAlgebra.ModelCategory` 定数がないことも Lean 環境を走査して確認済み。
- import 閉包に KanQuillen モジュールなし。`SSet.modelCategoryQuillen` 名前空間は Mathlib のホーン生成射・Fibration の既存 API に使うが、`ModelCategory SSet` は仮定しない。
- 公理監査は私有宣言・推移的な公理依存と、宣言型の ModelCategory 定数を検査する。
- BF cofibrant–fibrant 仕様を承認済み。構造射は単射、随伴は全基点 π_* 同型。厳密 Ω 同型は要求しない。
- 厳密 Ω 同型と厳密極限だけからの局所 Kan 性は未解決だったため改訂した。現仕様では単射の指数版・引き戻し・塔の RLP 閉性で証明する。
- cohomology の消滅と骨格の延長判定は証明済みだが、有理 Shapiro の全射性・収束・塔の微分の交代式を完了扱いにしない。

### 次の一手
- `stageFiberDifferential_cellConnecting` の右辺のセル境界の連結射を、`BoundaryLift` の最後の面で計算する。
- `stageFiberCoefficientEquiv_iteratedLoopComponent` でその代表を反復 loop 値の成分へ戻し、
  `skeletalFiberVertex_normalizedDifferential` の交代和と像・符号を照合する。
- loop と連結射の交換の符号を証明するまでは Sp-1c・Sp-1d を完了扱いにしない。
- 成分での延長障害や局所的な連結射への帰着だけから `coefficientDifferential` の同定・収束を主張しない。

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
