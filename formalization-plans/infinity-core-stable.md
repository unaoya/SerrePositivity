# D レーン：D7 → β3 → β5 → β4

> **v2 の位置づけ（2026-10-19）**：foundations.md §6 の D。D7 の後、β3（Drinfeld 商 = Verdier 商）、β5（D(A)・⊗_A）、β4（gluing = lax pullback）。

## 引き継ぎ（2026-10-19）

### 現在地

- α-S。S1〜S6 完了。安定 ∞ 圏の h の三角構造（TR1〜TR4）と完全関手の三角性を公開済み。
- S7／D7 は途中。D(S) の零対象、任意の cospan の極限、指定した全辺の fiber は完成。
- 標準 cofiber の正方形・余錐、coslice 境界の左右のデータ、共通面、六つの残差と全微分整合条件は完成。
- 実境界から Q・A の二未知 cochain を構成。q=−n−1 の符号照合、Q・A の微分式、Q と二包含・ホモトピー・対角との合成式を検証済み。
- Q・A を挿入した左右の SimplexData を構成。既知面・既知方程式の保存、左右の共通面の一致、後続・A・B/C の未知方程式を証明済み。
- 三角形側を含む全ての未知方程式を証明し、左右の実際の dg nerve 単体を構成。二セルの join への貼合せと全境界面の保存を検証済み。
- 標準 cofiber 余錐の coslice 初期性と標準 cofiber 正方形の ∞ 押し出し性を直接証明。充満部分 dg 圏への反映と Semifree の標準 cofiber 押し出しも完成。
- 任意の span の鎖写像表示、指定 span 上の標準 cofiber 押し出し、D(S) の全 span の余極限・全辺の cofiber を構成済み。
- 任意の正方形の標準 cofiber 比較射を構成し、押し出し性と比較射の擬同型性の同値を証明済み。
- 標準 cofiber から二包含の fiber への明示的な比較鎖写像を構成。二脚・零ホモトピーの厳密な保存、回転同値の順射との一致と擬同型性まで証明済み。
- 任意の dg nerve 単体の始点への閉零射の前合成と、始点を落とす面・始点を保つ単射への制限との両立を証明済み。始点を複製した比較単体とその零面・一面も構成済み。
- 上下の比較三単体の全方程式・両端面・共通面を検証し、join に貼って実際の slice 比較辺を構成。射影が明示的比較の辺と一致することも証明済み。
- 比較辺の可逆性から標準 cofiber 正方形の ∞ 引き戻し性を証明。充満部分 dg 圏・Semifree・任意の D(S) の span の標準 cofiber 正方形にも反映済み。
- 双対の標準 fiber の押し出し性、任意の零角四角形での fiber/cofiber の一致、IsStable・D3 の三角比較は未完了。
- 今回の入口は `CofiberFiberComparisonSlice.lean`、`CofiberFiberComparisonProjection.lean`、`StandardCofiberPullback.lean`。
- 対象＋Stable・Derived 集約ビルド：5,753 jobs 成功。今回の保存単位は新規 7 モジュール。
- 公理監査：Derived 180 modules／2,560 宣言、Stable 449 modules／3,667 宣言。標準三公理のみ。
- 本文・archive への実施記録の追記はしていない。今回の到達点はこの節を正本とする。

### 残り（依存順、時間は推定）

- 標準 fiber の押し出し性を双対に証明し、任意の零角四角形へ二方向の判定を移して D(S) の IsStable を構成。HA Definition 1.1.1.9、Proposition 1.1.3.4：4〜8 時間。
- D3 の同値・D2f の CommShift を使い、h D(S) と Mathlib DerivedCategory の三角構造を照合。HA Theorem 1.1.2.14、§1.1.4：4〜8 時間。

### 主要宣言（名前のみ。正確な型は Lean）

- `IsStable`、`suspensionEquivalence`、`pretriangulated_ho`、`isTriangulated_ho`、`exactFunctor_isTriangulated`。
- `derivedInfinityCategory_hasZeroVertex`、`derivedInfinityCategory_hasLimit_cospan`、`derivedInfinityCategory_fiber_exists`。
- `standardCofiberSquare`、`standardCofiberCocone`、`cofiberBoundaryDegree`。
- `cofiberBoundaryRhs0`、`cofiberBoundaryRhsA`、`cofiberBoundaryRhsB`、`cofiberBoundaryRhsC`、`cofiberBoundaryRhsAB`、`cofiberBoundaryRhsAC`。
- `cofiberBoundaryRhsB_differential`、`cofiberBoundaryRhsC_differential`、`cofiberBoundaryRhsAB_differential`、`cofiberBoundaryRhsAC_differential`。
- `biproductFromHomCoordinates`、`pushoutHomCoordinates`、`pushoutHomCoordinates_symm_differential`。
- `pushoutHomBoundaryLift`、`pushoutResidual_matrix`、`pushoutHomBoundaryLift_differential_of_residuals`、`pushoutBoundary_A_equation`。
- `cofiberBoundaryDegree_negOnePow`、`cofiberBoundaryLiftQ`、`cofiberBoundaryLiftA`、`cofiberBoundaryLiftQ_differential`、`cofiberBoundaryLiftA_differential`。
- `cofiberBoundaryLiftQ_inclusionB`、`cofiberBoundaryLiftQ_inclusionC`、`cofiberBoundaryLiftQ_homotopy`、`cofiberBoundaryLiftQ_diagonal`。
- `spanInsertUnknowns`、`cofiberBoundaryLeftCandidate`、`cofiberBoundaryRightCandidate`、`cofiberBoundaryCandidate_common`。
- `cofiberBoundaryLeftCandidate_suffix_equation`、`cofiberBoundaryRightCandidate_suffix_equation`、`cofiberBoundaryLeftCandidate_first_equation`、`cofiberBoundaryRightCandidate_first_equation`。
- `cofiberBoundaryLeftCandidate_second_equation`、`cofiberBoundaryRightCandidate_second_equation`、`spanTwoPrefixRhs_replace_suffix`、`spanTwoPrefixRhs_replace_first`。
- `cofiberBoundaryLeftSimplex`、`cofiberBoundaryRightSimplex`、`cofiberBoundarySimplex_common`、`cofiberBoundaryJoinFiller`、`cofiberBoundaryJoinFiller_faces`。
- `standardCofiberCocone_isColimit`、`standardCofiberSquare_isPushout`、`isColimitCone_of_fullInclusion`、`fullCofiberSquare_isPushout`、`semifreeCofiberSquare_isPushout`。
- `ComplexSpanPresentation`、`presentComplexSpan`、`derivedSpanCofiberSquare`、`derivedInfinityCategory_hasColimit_span`、`derivedInfinityCategory_cofiber_exists`。
- `derivedSquareCofiberComparison`、`derived_isPushoutSquare_iff_quasiIso`、`cofiberOutputConeIso`、`cofiberFiberRotationEquiv`。
- `cofiberFiberLift`、`cofiberFiberLift_projectionB`、`cofiberFiberLift_projectionC`、`cofiberFiberLift_homotopy`。
- `cofiberFiberRotation_hom_eq_lift`、`cofiberFiberLift_homotopyEquivalence`、`cofiberFiberLift_quasiIso`。
- `SourcePrecomposition.simplex`、`SourcePrecomposition.simplex_pullback_succ`、`SourcePrecomposition.simplex_pullback_extend`、`SourcePrecomposition.prepend`。
- `cofiberFiberComparisonLower`、`cofiberFiberComparisonUpper`、`cofiberFiberComparison_common`、`cofiberFiberComparisonJoin`。
- `cofiberFiberComparisonSliceEdge`、`cofiberFiberComparisonSliceEdge_projection`、`cofiberFiberComparisonSliceEdge_invertible`。
- `standardCofiberSquare_isPullback`、`fullCofiberSquare_isPullback`、`semifreeCofiberSquare_isPullback`、`derivedSpanCofiberSquare_isPullback`。

### 依存と提供

- Core・F1・DGNerve・DoldKanComparison・HomotopyLimits・DifferentialGraded は読み取り専用。他レーンのファイルは編集しない。
- fiber 側は N7 の `semifreeFiberSquare_isPullback` を利用。cofiber 押し出し性は本レーンの `Derived/CofiberPushout` と `SemifreeColimits` で独立に証明済み。
- 提供：Stable の S1〜S6、Derived/StableLimits、標準 cofiber と境界残差・Hom 座標の界面。
- 編集対象は Stable/・Derived/、両集約と両監査、計画 `infinity-core-stable.md`。明示指示により Derived 計画の D7 状態も更新する。

### 未コミット

- 今回の新規モジュール・Derived 集約・両監査・二計画は所有ファイルだけで保存。自分の未コミットなし。
- 他レーンの変更・未追跡ファイルは残したまま。本節には列挙せず、それらを取り込んでいない。

### 既知の問題

- 今回の対象・集約ビルドと両公理監査は成功。既知の新規名前衝突なし。
- 今回の構成は可換環上の任意の非有界複体・整数次数を扱い、`ModelCategory SSet` の追加 instance 仮定なし。
- 一般の明示解は残差整合条件を仮定するが、実境界の Q・A の微分定理はこれらを既存 Bianchi 定理から証明し、追加仮定にしない。
- Q 側は逆座標、A 側は右三角形残差の符号倍、他四成分は零とする明示解について、最上位を含む全方程式と共通面を検証済み。
- 標準 cofiber 正方形の引き戻し性は実際の slice 比較辺から証明済み。任意の零角四角形での双方向判定は未証明で、これだけから IsStable を主張しない。
- 安定性の一般論から cofiber の普遍性を逆用しない。直接 coslice を充填して証明する設計を維持する。
- import 閉包が再度壊れたら、他レーンを変更して迂回せず停止して報告する。

### 次の一手

- 標準 fiber の二射影の cofiber から元の終域への明示的比較を `mappingCone.desc` で作り、二脚とホモトピーの保存・ホモトピー同値性を証明する。末頂点への後合成による比較単体を作り、標準 fiber の押し出し性へ接続する。

作成日：2026-10-18。状態：S1〜S6 完了。S7（D7）実装中。
全体の正本は [foundations.md](foundations.md) §1（F3）・§4。
担当は旧 α の A4・A5 と D7。実施経緯・検証結果は各保存単位のコミットメッセージに記す。

## 目標と原典

| 主張 | 原典 | 完成の条件 |
| --- | --- | --- |
| 安定 ∞ 圏の定義 | HA Definition 1.1.1.9 | 零対象、全射の fiber/cofiber の存在、零角の fiber/cofiber 列の同値 |
| 有限極限・余極限による判定 | HA Proposition 1.1.3.4 | S1・S2 以降で実際に使う向きを証明し、未証明の逆向きを主張しない |
| h C の三角構造 | HA Theorem 1.1.2.14 | cofiber 列の像による distinguished triangle、TR1〜TR4、Mathlib Pretriangulated instance |
| 完全関手と自然変換 | HA §1.1.4 | 零・fiber/cofiber 四角形の保存、h の三角関手、完全関手間の自然変換 |
| 四角形の貼り合わせ | HTT Lemma 4.4.2.1 | A2 の join・slice による証明。A6 待ちの箇所が生じれば正確に特定 |
| D(S) の安定性と三角構造の一致 | 上記と D3・N7 | cofiber 四角形の押し出し性も coslice で直接証明し、D3 を三角比較へ昇格 |

HA §1.1 に対応する Kerodon の章はない。原典は定義と命題の照合に用い、引用公理にはしない。

## 工程

| 工程 | ファイル | 必須の到達点 | 状態 |
| --- | --- | --- | --- |
| S1 | `Stable/Pointed.lean` | 零対象、coslice の始対象としての IsColimitCone、IsPushoutSquare、fiber/cofiber 四角形 | 完了 |
| S2 | `Stable/Definition.lean` | HA 1.1.1.9 の安定性、HA 1.1.3.4 の必要な向き | 完了 |
| S3 | `Stable/Suspension.lean` | h C の Σ・Ω 関手、選択の比較、安定な場合の自己同値 | 完了 |
| S4 | `Stable/Pasting.lean`、`Stable/Triangulated.lean` | 四角形の貼り合わせ、cofiber 三角形、TR1〜TR4、Pretriangulated | 完了（貼り合わせ、TR1〜TR4、Pretriangulated・IsTriangulated instance） |
| S5 | `Stable/LongExactSequence.lean` | fiber 列に Hom を適用した長完全列 | 完了（共変・反変、全整数次数、六項部分列の完全性、接続準同型の評価式） |
| S6 | `Stable/ExactFunctor.lean` と関連モジュール | 完全関手、h の三角関手、完全関手間の自然変換 | 完了。零対象・cofiber/fiber 列・全押し出し／引き戻しの保存、CommShift ℤ、IsTriangulated、加法性、自然変換の全整数シフトとの両立・三角形の像の自然変換まで公開 |
| S7（D7） | `Derived/Stable.lean` | D(S) の安定性と D3 による通常の導来圏の三角構造との一致 | 進行中。零対象・fiber と標準 cofiber の普遍性完成。全辺の cofiber 完成。fiber/cofiber の一致と安定性・三角比較は未完了 |

## 設計上の決定

- namespace は `SerrePositivity.InfinityCategories`。SSet の実際の頂点・辺・単体的四角形を用いる。
- 零対象は A2e の `IsInitialVertex` と `IsTerminalVertex` の両方を満たす頂点。
- 余極限錐は `sliceUnder`・`sliceUnderEquiv` による coslice の始対象で定義する。
  押し出しは A2g の双対と照合し、単に h C の押し出しへ置き換えない。
- 安定性の定義に三角圏の公理や Σ の自己同値性を入力として追加しない。
- Σ・Ω は極限・余極限の選択から h C 上に構成し、A2f・A3d で選択の比較を証明する。
- distinguished triangle は cofiber 列の像を条件にする。TR4 も独立に受入基準へ含める。
- N7f を既提供とせず、S7 の coslice の直接充填で標準 cofiber の押し出し性を証明した。
- D3 の同値だけで安定性を定義したり、通常の導来圏の三角構造を無条件に移したりしない。
  実際の fiber/cofiber 列との一致を証明し、D2f の CommShift と照合する。
- 公理監査は `scripts/audit_infinity_stable.lean`。許されるのは propext・Classical.choice・Quot.sound。
- 集約 `InfinityCategories/Stable.lean` を作り、共有ルートへの追記はその public import 一行だけ。
  他チャットの変更・既存の未保存差分をコミットに含めない。


## β3：Drinfeld 商と ∞ 圏的 Verdier 商

D7 の後に着手。原典は Drinfeld Thm 3.4・Lemma 13.5、HA §1.1.4、Kerodon §6.3。
F1b の `Localization.lean` の `IsLocalization` を入口とし、同じ宇宙の標的への
`localizationPrecomposition` が反転関手の全部分 ∞ 圏との同値になることを証明する。

- L4 §26（archive に移管）の半自由 dg 圏分解・Hom の K-flat 性・商の H⁰ 比較を読むだけで使う。
- 必要な平坦分解を先行し、未分解の path 商が無条件に Verdier 商であるとはしない。
- 前三角 dg 圏と安定な充満部分圏について、商の dg nerve の安定性、商関手の完全性、
  零化する完全関手への前合成の同値、Verdier 列を構成する（見積もり 1〜2 万行）。
- H⁰ の Verdier 商の同値だけで ∞ 関手圏の普遍性を済ませない。

## β5：非可換 dg 代数の導来 ∞ 圏

β3 の後。L4 §26 の dg 圏分解と既存の dg 加群の半自由分解を区別し、
一般化は `InfinityCategories/Derived/` に置く（見積もり 1〜3 万行）。

- 非可換 dg 代数 A の半自由 dg 加群から `D(A) := N_dg(Semifree(A))` と Perf(A) を構成する。
- 双加群による相対テンソル・Hom に必要な分解と閉性を証明し、dg 関手を dg nerve に移す。
- 単位・合成・随伴の整合性、Morita 同値による D(A)・Perf(A) の同値を証明する。
- 単体環の Dold–Kan による dg 代数化を確認する。HA §7.1.2 は比較目標であり引用公理にしない。

## β4：dg gluing と lax pullback

β5 の後、α2b の Cat_∞ の極限・lax pullback の実装を待って接続する。
原典は Tamme 2018 §1、Kuznetsov–Lunts。見積もり 1〜2 万行。

- 双加群に沿う gluing の対象・写像複体・合成・微分を具体的に構成する。
- dg nerve から二射影と構造変換を作り、α2b の Fun(Δ¹,−) による lax pullback への比較を作る。
- 比較の完全忠実性・本質的全射性と ∞ 圏的普遍性を証明し、安定性・完全射影を供給する。
- α2b の未提供の極限や h の通常の pullback を完成済みの ∞ lax pullback と扱わない。

## 記録の所在

実施記録・現在地の詳細・型一覧は [archive/infinity-core-stable-log.md](archive/infinity-core-stable-log.md) に移した（2026-10-19）。現在地は冒頭の引き継ぎ節が正本で、工程ごとの記録はコミットメッセージに置く。
