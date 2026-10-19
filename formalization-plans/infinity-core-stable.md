# α-S：安定 ∞ 圏と D(S) の安定性

> **v2 の位置づけ（2026-10-19）**：foundations.md §6 の D。D7 の後、β3（Drinfeld 商 = Verdier 商）、β5（D(A)・⊗_A）、β4（gluing = lax pullback）。

## 引き継ぎ（2026-10-19）

### 現在地

- α-S。S1〜S6 完了。安定 ∞ 圏の h の三角構造（TR1〜TR4）と完全関手の三角性を公開済み。
- S7／D7 は途中。D(S) の零対象、任意の cospan の極限、指定した全辺の fiber は完成。
- 標準 cofiber の正方形・余錐、coslice 境界の左右のデータ、共通面、六つの残差と全微分整合条件は完成。
- 今回は Hom の三成分座標・逆座標と微分、整合条件を仮定した明示的持ち上げ、二包含・ホモトピー・対角との合成、二つの微分方程式まで検証した。
- 実際の境界残差への代入、未知成分を含む SimplexData、coslice の充填、cofiber の押し出し性、D(S) の安定性は未完了。
- 実装・集約・監査は `c371e6b6` に保存済み。
- 対象＋Stable・Derived 集約ビルド：5,712 jobs 成功。新規公開 20 宣言の型検査も成功。
- 公理監査：Stable 408 modules／3,197 宣言。Derived 139 modules／2,090 宣言。標準三公理のみ。
- 本文・archive への実施記録の追記はしていない。今回の到達点はこの節を正本とする。

### 残り（依存順、時間は推定）

- 実境界の六残差を明示解へ代入し、q=−n−1 の符号を照合。HA Proposition 1.3.1.10、HTT §1.2.13：1〜3 時間。
- 未知成分を SimplexData に組み込み、既知面の保存、右辺の変化、四種類の未知集合の全方程式、左右の共通面を証明。HA Proposition 1.3.1.10：8〜16 時間。
- coslice 境界を貼り、標準余錐の始対象性と標準 cofiber 正方形の押し出し性を証明。HTT §1.2.13、HA Proposition 1.3.1.10：4〜8 時間。
- semifree へ移し、全辺の cofiber と fiber/cofiber 列の一致から D(S) の IsStable を構成。HA Definition 1.1.1.9、Proposition 1.1.3.4：4〜8 時間。
- D3 の同値・D2f の CommShift を使い、h D(S) と Mathlib DerivedCategory の三角構造を照合。HA Theorem 1.1.2.14、§1.1.4：4〜8 時間。

### 主要宣言（名前のみ。正確な型は Lean）

- `IsStable`、`suspensionEquivalence`、`pretriangulated_ho`、`isTriangulated_ho`、`exactFunctor_isTriangulated`。
- `derivedInfinityCategory_hasZeroVertex`、`derivedInfinityCategory_hasLimit_cospan`、`derivedInfinityCategory_fiber_exists`。
- `standardCofiberSquare`、`standardCofiberCocone`、`cofiberBoundaryDegree`。
- `cofiberBoundaryRhs0`、`cofiberBoundaryRhsA`、`cofiberBoundaryRhsB`、`cofiberBoundaryRhsC`、`cofiberBoundaryRhsAB`、`cofiberBoundaryRhsAC`。
- `cofiberBoundaryRhsB_differential`、`cofiberBoundaryRhsC_differential`、`cofiberBoundaryRhsAB_differential`、`cofiberBoundaryRhsAC_differential`。
- `biproductFromHomCoordinates`、`pushoutHomCoordinates`、`pushoutHomCoordinates_symm_differential`。
- `pushoutHomBoundaryLift`、`pushoutResidual_matrix`、`pushoutHomBoundaryLift_differential_of_residuals`、`pushoutBoundary_A_equation`。

### 依存と提供

- Core・F1・DGNerve・DoldKanComparison・HomotopyLimits・DifferentialGraded は読み取り専用。他レーンのファイルは編集しない。
- fiber 側は N7 の `semifreeFiberSquare_isPullback` を利用。N7f の cofiber 押し出し性は未実施で、到着を仮定しない。
- 提供：Stable の S1〜S6、Derived/StableLimits、標準 cofiber と境界残差・Hom 座標の界面。
- 編集対象は Stable/・Derived/、両集約と両監査、計画 `infinity-core-stable.md`。Derived 計画は他レーン所有。

### 未コミット

- 自分のファイルは実装・監査と本引き継ぎ節をそれぞれ `git commit --only` で保存し、未コミットなし。
- 他レーンの変更・未追跡ファイルは残したまま。本節には列挙せず、それらを取り込んでいない。

### 既知の問題

- 今回の対象・集約ビルドおよび監査に失敗なし。既知の新規名前衝突なし。
- 今回の五ファイルは可換環上の任意の非有界複体・整数次数を扱い、`ModelCategory SSet` の追加 instance 仮定なし。
- 明示解の微分定理は四つの残差整合条件を仮定する。実境界が条件を満たす既存定理との接続は未実装。
- 六未知成分のうち Q 側を逆座標、A 側を右三角形残差の符号倍、他四成分を零にする予定。単体の全方程式はまだ保証していない。
- 安定性の一般論から cofiber の普遍性を逆用しない。直接 coslice を充填して証明する設計を維持する。
- import 閉包が再度壊れたら、他レーンを変更して迂回せず停止して報告する。

### 次の一手

- `CofiberBoundaryTriangleCompatibility` と `PushoutBoundaryEquations` を接続し、実際の境界から Q・A の二未知 cochain と微分式を定義・証明する一工程から再開する。

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
| S7（D7） | `Derived/Stable.lean` | D(S) の安定性と D3 による通常の導来圏の三角構造との一致 | 進行中。零対象・fiber 完成、cofiber の普遍性を構成中 |

## 設計上の決定

- namespace は `SerrePositivity.InfinityCategories`。SSet の実際の頂点・辺・単体的四角形を用いる。
- 零対象は A2e の `IsInitialVertex` と `IsTerminalVertex` の両方を満たす頂点。
- 余極限錐は `sliceUnder`・`sliceUnderEquiv` による coslice の始対象で定義する。
  押し出しは A2g の双対と照合し、単に h C の押し出しへ置き換えない。
- 安定性の定義に三角圏の公理や Σ の自己同値性を入力として追加しない。
- Σ・Ω は極限・余極限の選択から h C 上に構成し、A2f・A3d で選択の比較を証明する。
- distinguished triangle は cofiber 列の像を条件にする。TR4 も独立に受入基準へ含める。
- N7f（cofiber 四角形の押し出し性）は未実施。S7 で既証明として扱わず、coslice の充填を構成する。
- D3 の同値だけで安定性を定義したり、通常の導来圏の三角構造を無条件に移したりしない。
  実際の fiber/cofiber 列との一致を証明し、D2f の CommShift と照合する。
- 公理監査は `scripts/audit_infinity_stable.lean`。許されるのは propext・Classical.choice・Quot.sound。
- 集約 `InfinityCategories/Stable.lean` を作り、共有ルートへの追記はその public import 一行だけ。
  他チャットの変更・既存の未保存差分をコミットに含めない。

## 記録の所在

実施記録・現在地の詳細・型一覧は [archive/infinity-core-stable-log.md](archive/infinity-core-stable-log.md) に移した（2026-10-19）。現在地は冒頭の引き継ぎ節が正本で、工程ごとの記録はコミットメッセージに置く。
