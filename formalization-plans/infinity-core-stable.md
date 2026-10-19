# D レーン：D7 → β3 → β5 → β4

> **v2 の位置づけ（2026-10-19）**：foundations.md §6 の D。D7 の後、β3（Drinfeld 商 = Verdier 商）、β5（D(A)・⊗_A）、β4（gluing = lax pullback）。

## 引き継ぎ（2026-10-19）

### 現在地

- S1〜S6 完了。安定 ∞ 圏の h の三角構造（TR1〜TR4）、完全関手の CommShift・三角性を公開済み。
- D7 の零対象、全 cospan の極限・全辺の fiber、全 span の余極限・全辺の cofiber は完成。
- 実境界から Q・A の二未知 cochain と全微分式・合成式を証明し、coslice を直接充填して標準 cofiber の押し出し性を証明済み。
- 明示的な双対比較 `cofiberFiberLift`・`fiberCofiberDesc` の二脚・対角・ホモトピー保存とホモトピー同値性を証明済み。
- 実際の slice/coslice 比較辺と射影を構成し、可逆性から標準 cofiber の引き戻し性と標準 fiber の押し出し性を証明済み。充満部分 dg 圏・Semifree に反映済み。
- 相対始点・終点境界充填の可逆辺に沿う輸送を Stable 側で証明。KST 側の汎用証明を参照したが KST のファイルは変更せず、基盤から KST への import も追加していない。
- 全錐／余錐と四角形全体の関手同型による極限性／余極限性の保存を証明。
- 標準四角形と任意の同じ span/cospan の四角形の比較から、任意の D(S) の四角形の引き戻し性と押し出し性の同値を証明済み。
- `derivedInfinityCategory_isStable` を構成済み。HA 1.1.1.9 の三条件を実際の ∞ 圏の普遍性から満たす。
- 通常の道の商による h D(S) に既存 Stable の三角構造が入り、二切断の D3 へ接続する `derivedStableHomotopyEquivalence` も構成済み。三角関手性は未証明。
- 今回の入口は `Derived/Stability.lean`、`Derived/StableHomotopyComparison.lean`、`Stable/SquareFunctorTransport.lean`。
- 対象＋Stable・Derived 集約ビルド：5,779 jobs 成功。今回の保存単位は新規 7 モジュール。
- 公理監査：Derived 204 modules／2,755 宣言、Stable 473 modules／3,862 宣言。標準三公理のみ。

### 残り（依存順、時間は推定）

- 安定性から得る suspension と D2f の複体シフトを自然に照合し、cofiber の接続射も同定して D3 を三角同値へ昇格。HA Theorem 1.1.2.14、§1.1.4：4〜8 時間。
- β3 → β5 → β4。受入条件・原典・読み取り専用依存は後続の各節を正本とする。

### 主要宣言（名前のみ。正確な型は Lean）

- `IsStable`、`suspensionEquivalence`、`pretriangulated_ho`、`isTriangulated_ho`、`exactFunctor_isTriangulated`。
- `derivedInfinityCategory_hasZeroVertex`、`derivedInfinityCategory_hasLimit_cospan`、`derivedInfinityCategory_fiber_exists`。
- `derivedInfinityCategory_hasColimit_span`、`derivedInfinityCategory_cofiber_exists`。
- `cofiberBoundaryLiftQ`、`cofiberBoundaryLiftA`、`cofiberBoundaryLiftQ_differential`、`cofiberBoundaryLiftA_differential`。
- `cofiberBoundaryLeftSimplex`、`cofiberBoundaryRightSimplex`、`cofiberBoundaryJoinFiller_faces`、`standardCofiberCocone_isColimit`。
- `derivedSquareCofiberComparison`、`derived_isPushoutSquare_iff_quasiIso`、`derived_isPullbackSquare_iff_quasiIso`。
- `cofiberFiberLift`、`cofiberFiberLift_homotopyEquivalence`、`fiberCofiberDesc`、`fiberCofiberDesc_homotopyEquivalence`。
- `cofiberFiberComparisonSliceEdge_projection`、`fiberCofiberComparisonSliceEdge_projection`。
- `complexTriangleAppend`、`complexTriangleAppend_face_two`、`complexTriangleAppend_lastEdge`。
- `standardCofiberSquare_isPullback`、`derivedSpanCofiberSquare_isPullback`、`standardFiberSquare_isPushout`、`derivedCospanFiberSquare_isPushout`。
- `InitialBoundaryLifting.of_vertexIso`、`TerminalBoundaryLifting.of_vertexIso`、`IsPullbackSquare.of_functorIso`、`IsPushoutSquare.of_functorIso`。
- `coneFunctorIsoOfVertexIso`、`coconeFunctorIsoOfVertexIso`、`derived_isPullbackSquare_iff_isPushoutSquare`。
- `derivedInfinityCategory_isStable`、`derivedStableHomotopyBridge`、`derivedStableHomotopyEquivalence`。

### 依存と提供

- Core・F1・DGNerve・DoldKanComparison・HomotopyLimits・DifferentialGraded・KST は読み取り専用。他レーンのファイルは編集しない。
- fiber 側は N7 の極限性を利用。cofiber 押し出し性は Derived/CofiberPushout の直接証明を使う。
- 提供：Stable の S1〜S6、D(S) の安定性、任意四角形の双カルテジアン判定。
- 編集対象は Stable/・Derived/、両集約と両監査、本計画。明示指示により Derived 計画の D7 状態も更新する。

### 未コミット

- 今回の所有ファイルだけを保存。自分の未コミットなし。他レーンの変更は残したまま取り込んでいない。

### 既知の問題

- 対象・集約ビルドと両公理監査は成功。主要宣言に `ModelCategory SSet` の追加 instance 仮定なし。
- h D(S) の Stable のシフトは suspension に由来し、D3 の二切断のシフトは複体シフトからの誘導。この二つを同一視せず、次工程で自然同型と接続射を照合する。
- 通常の導来圏の三角構造の引き戻しだけで三角比較を完了とはしない。実際の cofiber 列の像との一致を要する。
- import 閉包が壊れたら他レーンを変更して迂回せず停止して報告する。

### 次の一手

- Semifree の suspension の span `0 ← X → 0` の標準 cofiber 四角形を明示し、その終点と `X⟦1⟧` の比較を構成する。普遍余錐の比較を使って suspensionFunctor と複体シフトの自然同型へ束ね、`derivedStableHomotopyEquivalence` の CommShift と cofiber 三角形の像の distinguished 性へ進む。

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
| S7（D7） | `Derived/Stability.lean` | D(S) の安定性と D3 による通常の導来圏の三角構造との一致 | 進行中。零対象・全射の fiber/cofiber、任意四角形の双方向判定と IsStable 完成。通常の h D(S) と D3 の圏同値を接続済み。suspension と複体シフト・接続射の照合、D3 の三角同値化が残る |

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
