# K-L2（比較定理）

> **凍結（2026-10-19）**：foundations.md v2（Land–Tamme 採用）により plus 構成・古典比較は不要。既存コードは Auxiliary として保持し、再開しない。K₀ の同定は K-L1 が持つ。

## 引き継ぎ（2026-10-19）

### 現在地
- L2a 完了：SS03 (2.9) の Γ の環構造、ĜL の群状単体的モノイド、π₀ の GL との同定。
- L2b 完了：bar、Segal Proposition 1.5・1.6、KST Lemma 2.13 の実際の群同型。
- L2c 途中：正規化整数・局所係数ホモロジー、相対長完全列、anodyne・Kan 置換の保存まで証明済み。
- 相対局所係数の pushout 同型、二・三次数の可逆な境界による相殺も証明済み。
- 非退化単体複体と Moore 正規化複体の同型・逆射の自然性までで区切った。
- plus の存在・実際のセル添付の境界計算・π₁ の商は未証明。条件付きの相殺補題を plus と扱わない。
- 最新の実装保存は `266ca89d`、全局所係数の anodyne 保存は `561fc5c6`。
- 対象ビルド 4513 jobs 成功。主要 1499 宣言・名前空間 2732 宣言を標準三公理だけで監査済み。

### 残り（依存順、原典番号と時間見積もり）
見積もりは未供給の API を含む概算の実作業時間で、待機時間は含めない。
1. 標準セル ∂Δ[d]→Δ[d] の相対局所係数複体と境界の具体計算。
   Weibel K-book IV.1.5、Waldhausen LNM 1126 §1.7・§1.8。24–60 時間。
2. 必要な被覆、H₁ と π₁ のアーベル化の比較、単連結の場合の H₂ の球面的持ち上げ。
   Weibel K-book IV.1.5・Ex. IV.1.4 のセル証明で使う Hurewicz 部分。40–120 時間。
3. 二セルで完全正規部分群を殺し、三セルで相対複体を相殺する実際の plus 構成。
   全局所係数の acyclic 性、Kan 化、π₁ の商、KST Lemma 2.14 へ接続。
   Weibel K-book IV.1.5–IV.1.6、KST §2。48–120 時間。
4. K₀ 界面の S1 決定を確認し、冪等元の持ち上げと K₁ を比較。
   KST Theorem 2.16 の n=0,1、Weibel K-book III。40–100 時間。
5. 正本 §10-5 の紙上 Hurewicz・Künneth 型スペクトル系列の確認を完成し、実装へ移す。
   Waldhausen Theorem 1.7.1。紙上確認 8–24 時間、必要な新規形式化 80–200 時間。
6. K-L1 の K1a の供給を確認し、∞-S• と古典的比較を接続。
   Waldhausen 2.3.2、KST Proposition 2.15。供給後 40–120 時間。
7. 負の次数への接続は K-L3 の Bass 基本定理を借りる。
   KST Theorem 2.16 の n<0。界面供給後 8–24 時間。

### 主要宣言（名前のみ）
- `stableHatGLComponentsIso`
- `monoidGroupCompletionMap_localized_isIso`
- `lemma_2_13_pi_one`
- `lemma_2_13_higher`
- `integralHomologyFunctor`
- `LocalCoefficientSystem`
- `localCoefficientChainsMap`
- `localHomologyIsomorphism_of_anodyne`
- `kanReplacementUnit_localHomologyIsomorphism`
- `overLocalCoefficientChainsFunctor`
- `overHornGenerators_cellPresentation`
- `relativeOverLocalCoefficientSequence_shortExact`
- `relativeOverLocalCoefficientBoundary`
- `relativeOverLocalCoefficientPushoutIso`
- `twoCellComplex_acyclic`
- `overLocalHomologyEquivalence_of_twoCellCancellation`
- `nondegenerateCoefficientChainsIso`
- `nondegenerateCoefficientChainsIso_inv_naturality`

### 依存と提供
- K-L9 の `KST/Spectra/HomotopyGroups`・`LoopHomotopyGroups`・`FilteredHomotopyGroups` 等を読む。
- `HomotopicalAlgebra/Simplicial/AnodyneKanReplacement` と既存の局所化・Kan の API を読む。
- π_n を本レーンで再定義しない。K-L9 の群の添字 n は通常の π_(n+1) である。
- K-L1 から ∞-S•・連結 K、K-L3 から Bass、K-L6 から pro の界面を借りる。
- Γ・ĜL・bar・群完備化・KST Lemma 2.13・H_* と局所係数の保存を提供する。
- plus・K₀/K₁・Proposition 2.15 の完成版はまだ提供しない。

### 未コミット
- 本レーンの未コミットなし。本引き継ぎ節も自分の計画ファイルだけをコミットして停止する。
- 他レーンの未コミット変更には触れていない。

### 既知の問題
- 今回の対象 import 閉包はビルド・監査とも成功。追加公理・sorry は導入していない。
- 最後の全体ビルドはルート集約で `relativeFunctorVertex` の重複により失敗した。
  F1B.RelativeFunctorHomotopyComposition と F1.RelativeFunctorVertices の衝突（12355 jobs の最終集約）。
  α2b の改名後の全体ビルドは未確認。比較レーンで import の回避はしていない。
- 本レーンに `[ModelCategory SSet]` の明示的な仮定はない。実際の anodyne・Kan 模型を使う。
- 二・三セルの相殺補題の支持次数・境界の同型性は条件であり、実際のセル添付からの導出が残る。
- 局所係数の整数係数だけへの置換、plus の存在を仮定の構造体で代用する変更は採用していない。
- 全体目標は未完了。L2c の完了や K 理論比較の完了として読まないこと。

### 次の一手
- `nondegenerateCoefficientChainsIso` の比較を使い、標準セルの境界包含の相対複体を計算する。
  最初は定数係数の ∂Δ[2]→Δ[2] を扱い、その後に任意の次数・引き戻し局所係数へ拡張する。

## 所有するもの・借りるもの

本レーンは単体集合の整数ホモロジー H_* を所有する。
正規化 chain 複体と alternating face map complex の比較も所有する。
単体的モノイドの群完備化と分類空間を所有する。
完全正規部分群に関する plus 構成を所有する。
Dold–Kan の環への延長と ĜL の比較への適用を所有する。
Waldhausen の古典的比較から ∞-S• への移植を所有する。
π_n の定義・群構造・長完全列は K-L9 から借りる。
π_n が届くまでは具体的な数学的データを明示的な引数とする。
pro 圏と pro 同型の実装は K-L6 から借りる。
∞-S• と連結 K の構成は K-L1 から借りる。
Bass 基本定理と負の次数への延長は K-L3 から借りる。
K0 界面の正確な Lean 型は S1 で確定する。
K0 界面の未供給の性質を本レーンの定理として公開しない。

## 1. 正本・配置・規約

作成日：2026-10-18。
チャットのレーン名：K-L2（比較定理）。
正本は [KST 経路](k-theory-kst-route.md) と [基盤計画](../infinity-lanes/foundations.md)。
KST 経路の §2.5 P1、§4 D2、§5 K2、§10-5、§13 を参照する。
決定の衝突は foundations.md と KST 経路 §13 の優先順位で読む。
Lean の namespace は `SerrePositivity.KST.Comparison` とする。
Lean の所有ディレクトリは `SerrePositivity/KST/Comparison/` とする。
集約ファイルは `SerrePositivity/KST/Comparison.lean` とする。
監査ファイルは `scripts/audit_kst_comparison.lean` とする。
ルートへの変更は `public import SerrePositivity.KST.Comparison` の一行だけとする。
既存の KTheory、DifferentialGraded、Spectra は読み取り専用とする。
既存の InfinityCategories、HomotopicalAlgebra も読み取り専用とする。
他レーンの計画・監査ファイルは編集しない。
実施の経緯はコミットメッセージに書く。
本計画の現在地・宣言表は追記日誌ではなく現況に書き換える。
引用を説明に書くことと、引用を Lean の未証明入力にすることを区別する。
追加公理、sorry、原典の定理を仮定した存在証明は導入しない。
docstring は概要／方針／規約／使われ方を日本語で記す。

## 2. 目標と完成条件

最終目標は KST Proposition 2.15 の比較を完全に証明することである。
比較の形は Ω^∞ K(A) ≃ K₀(π₀A) × BĜL(A)⁺ である。
対象は connective な結合的単位的 dg 代数とする。
可換係数の場合だけに制限して非可換係数の必要性を隠さない。
KST Theorem 2.16 の次数 0 と 1 の比較を導く。
負の次数の比較は K-L3 の Bass 基本定理に接続する。
KST Lemma 2.13 の分類空間のホモトピー群を証明する。
この補題の π_n の基盤そのものは K-L9 の所有とする。
plus 構成の存在とその性質を区別して証明する。
群完備化の存在とホモロジー比較を区別して証明する。
ホモロジーを任意の関手として仮定して完成扱いにしない。
正規化複体と非正規化複体の準同型も証明対象に含める。
∞-S• の比較を古典的 Waldhausen 圏の比較で置換しない。
両者を接続する補題の仮定と出力を明記する。
標準三公理だけへの依存を保存単位ごとに確認する。
完成は全工程の実体と比較写像の自然性が供給された時点とする。

## 3. 原典対応

| 対象 | 原典 | 本レーンでの用途 |
| --- | --- | --- |
| Γ の環構造 | Schwede–Shipley 2003 §2.3、式 (2.8)–(2.9) | Alexander–Whitney 積 |
| Γ の忠実充満性 | 同 Proposition 2.13 | 正規化との整合 |
| ĜL_n | KST §2.2、式 (2.2) | π₀ の単元成分の逆像 |
| 安定 ĜL | KST 式 (2.3) | rank に関する安定化 |
| BĜL の π_n | KST Lemma 2.13 | 分類空間との比較 |
| 分類空間の群完備化 | Segal 1974 Proposition 1.5 | 群状モノイドへの適用 |
| plus と K₁ | KST Lemma 2.14 | π₁ の商 |
| K の比較 | KST Proposition 2.15 | 主比較定理 |
| 低次数の不変性 | KST Theorem 2.16 | 次数 0、1 |
| 球状対象 | Waldhausen LNM 1126 Theorem 1.7.1 | セル濾過と Hurewicz |
| 比較定理の部品 | Waldhausen §1.8、Theorem 1.8.1 | S• との比較 |
| strict cofinality | Waldhausen Proposition 1.5.9 | 自由対象からの比較 |
| GL と有限自由対象 | Waldhausen Proposition 2.3.5 | 分類空間の同定 |
| 主比較 | Waldhausen Theorem 2.3.2 | ∞-S• への移植 |
| 古典的 K₁ | Weibel K-book III | 離散環の比較先 |
| plus の原典番号 | Weibel K-book IV.1 | acyclic map の構成 |

KST は arXiv:1611.08466v4 を用いる。
KST §2.2 の該当箇所は本文頁 9–10 にある。
Schwede–Shipley は Equivalences of monoidal model categories を用いる。
掲載は Algebraic & Geometric Topology 3 (2003), 287–334 である。
その Proposition 2.13 は単体的環 ΓA を扱う。
同命題は ĜL が各次数で群であるとは述べない。
Segal 1974 Proposition 1.5、本文頁 296–297 を照合した。
A₀ の可縮性と Segal 写像 A_n → A₁^n のホモトピー同値が仮定。
結論は A₁ → Ω|A| がホモトピー同値となることと homotopy inverse の存在の同値。
証明は path-space PA と Proposition 1.6 の homotopy-cartesian な実現の比較による。
単体的模型では二重単体的 bar の対角を用い、この比較部分を別途証明する。
Waldhausen の原典本文の精査は §10-5 の記録に反映する。
Weibel III と IV.1 の用途を混同しない。

## 4. 次数と connective の読み替え

リポジトリの dg 代数は cochain 規約で読む。
connective は H^i(A) = 0 for i > 0 を意味する。
chain 側は C_n = A^(−n) とする。
したがって H_n(C) は H^(−n)(A) に対応する。
π₀A の比較先は H⁰(A) である。
H⁰ の消滅や空間の連結性を connective の定義に加えない。
単に connective な Z 次数 dg 代数は項ごとに非正とは限らない。
Γ の入力には非負 chain 複体が必要である。
一般の A には乗法を保つ good truncation τ≤0 を用いる。
truncation の零次項は Z⁰(A) とする。
負次数項は元の A の項とする。
truncation の包含が擬同型になることを connective 性から示す。
乗法と単位が truncation に制限することを証明する。
厳密に非正次数の入力と一般の connective 入力を区別する。
次数反転の differential の型と符号は個別に確認する。
cochain の Leibniz 則を chain の Leibniz 則へ輸送する。
Γ の乗法は AW に由来する結合的乗法である。
AW は対称でないので可換性を自動的に付けない。

## 記録の所在

実施記録・現在地の詳細・型一覧は [archive/L2-comparison-log.md](../../L2-comparison-log.md) に移した（2026-10-19）。現在地は冒頭の引き継ぎ節が正本で、工程ごとの記録はコミットメッセージに置く。
