# P レーン：presentable ∞ 圏（HTT 5.4〜5.5）

> 計画 v2 の P（foundations.md §2・§6）。第 II 段の animated 環・降下の基盤。
> 配置は `SerrePositivity/InfinityCategories/F2/Presentable/`、集約は `F2/Presentable.lean`。

## 引き継ぎ（2026-10-23、コーディネータ停止指示）

### 現在地
- コーディネータ停止指示でこのチャットを終了する。再開は新しいチャットで行う。工程 (1) 完了、工程 (2) 途中、工程 (3)〜(7) は未完。
- κ-accessible を正則 κ・小さい κ-filtered 余極限・小さい κ-compact 全部分生成圏で定義した。
  生成は各指定対象を厳密な頂点とする全余錐。比較の充満忠実性や Ind 同値を定義の仮定には入れていない。
- 小さい生成圏から Ind 比較を構成し、元の任意の二対象の pinched Hom 同値・全充満忠実性・本質的全射性を実証。
  `IsKappaAccessible.exists_indEquivalence` と `isKappaAccessible_iff_indEquivalence`、存在量化版の iff まで証明済み。
- accessible 関手の恒等・合成・全自然同型不変性、圏の同値不変性・同値による共役不変性を証明済み。
- `IsCardinalChangeBound κ μ`（κ < μ と冪の評価）から圏自身の μ-accessibility を証明した。
  小さい κ-filtered 部分 poset の μ-filtered 全表示・元の指定頂点への回収・小さい μ-compact 生成圏を実際に構成した。
- μ-small poset の極限と、一般の μ-filtered ∞ 添字の空間余極限との coherent な交換を証明済み。
  宇宙移送、μ-small poset 余極限の μ-compact 閉性、任意の上限超え・小さい族の共通 accessibility 濃度を提供する。
- `IsPresentable` は accessibility と全小余極限で定義。同値不変性と、小余極限を持つ Ind 模型による特徴づけを証明した。
  前層・空間の全小極限と全小余極限を提供。任意の小さい A の Indκ(A) を無条件に presentable とは主張しない。
- 空間は有限単体集合の共通の小さい符号族の Kan 置換から小さい compact 全部分生成圏を構成し、presentable 性を実証した。
  有限部分複体の Kan 置換の filtered 全表示は各指定 Kan 空間そのものを厳密な頂点に持つ。
- 一般の前層に向け、底上の有限全空間の有限表示性、有限底上模型の共通の小さい符号型を構成した。
  具体的な左ホーン付加の可算反復が filtered 余極限を保つ left fibration 置換であり、元の単位が左アノダインと証明した。
- 置換前後の相対 Hom は全 coherent な関手として同型。有限始域の元の相対 Hom は通常の filtered 余極限を保つ。
  底上の strict filtered 全余錐の相対 Hom 像は、空間の native な余極限。全 join 射の等式で元の余錐と比較した。
- 有限底上模型の通常の filtered 全表示・符号族との底上の同型・left fibration の filtered 余極限閉性を証明した。
  底上の全表示自身の native 性、一般 coherent 添字での相対 Hom 保存、有限模型の compact 性、前層の accessibility は未証明。
- 今回の `leftFibrationPointEvaluationIso` は、一点始域の相対 Hom と同じ底の頂点 fiber 評価の全関手同型。
  単体ビルド成功（5140 jobs）。直前コミット `c542c9a4d` の六モジュールは個別チェック・独立監査 128 宣言が標準三公理のみ。
- 停止前の所有集約ビルド成功（7750 jobs）、全体公理監査 852 宣言は標準三公理のみ。

### 残り（依存順）
1. 工程 (1)：定義・Ind iff・関手・同値不変性・正則濃度変更は完了。
2. 工程 (2)：一般の前層の小さい compact 生成、accessibility、適切な条件下の Ind の presentable 性、局所小ささ。
3. presentable の極限・余極限（HTT 5.5.2.4、5.5.3.13）。
4. 随伴関手定理（5.5.2.9）：余極限保存から左随伴、accessible かつ極限保存から右随伴。
5. Pr^L／Pr^R の双対性（5.5.3.4）。
6. Bousfield 局所化の存在（5.5.4.15）。N の局所対象・強飽和性・条件付き反射を再利用し、局所置換の存在を実証する。
7. P_Σ の普遍性と sifted 生成（5.5.8.14〜15）。N の `SigmaPresheafInfinity` を再利用する。

### 主要宣言
- `IsKappaAccessible`、`IsAccessible`、`IsKappaCompactGenerating`、`IsKappaAccessibleFunctor`、`IsAccessibleFunctor`
- `IsKappaAccessible.exists_indEquivalence`、`isKappaAccessible_iff_indEquivalence`、`IsKappaCompactGenerating.compact_iff_retract`
- `IsCardinalChangeBound`、`exists_filteredPartialPresentation`、`coherentCardinalFilteredLimitExchange_poset`、`IsKappaAccessible.of_cardinalChangeBound`
- `IsPresentable`、`isPresentable_iff_cocompleteIndEquivalence`、`smallKanObject_isKappaCompact`、`space_isPresentable`
- `FiniteOverCode`、`finiteOver_isFinitelyPresentable`、`continuousLeftFibrationReplacement`、`continuousLeftFibrationReplacementUnit_leftAnodyne`
- `continuousLeftFibrationHomIso`、`finiteRelativeOverHom_preservesFilteredColimits`、`finiteRelativeHom_preserves_strictCocone`
- `finiteOverReplacementCocone_isColimit`、`finiteOverReplacementDiagram_in_family`、`leftFibration_of_filtered_isColimit`、`leftFibrationPointEvaluationIso`

### 依存と提供
- 読み取り専用：F2/Ind（F1）、F2/Idempotent・F2/Compact・HomotopyLimits（N）、F1・F1B・Core、使用する Stable の界面。
- F1 の分類：`leftStraighteningInfinityMap_isQCatEquivalence`、`leftStraighteningInfinityMap_evaluateIso`、`relativeFunctorEvaluationComparisonIso`。
- N の compact 定義へは所有ファイル `RelativeHomModel.lean` の `relativeHom_covariantModelIso` で元の大きい共変 Hom と全自然比較済み。
- 供給先は第 II 段の animated 環・降下・K。一般の前層の presentable 性はまだ提供できない。

### 未コミット
- `SerrePositivity/InfinityCategories/F2/Presentable/LeftFibrationStrictColimit.lean` を未検証の作業中ファイルとして残す。
  直近の単体検証は `Presentable/Accessible.olean` 欠落で import に失敗。停止前の集約で依存は再構築済みだが、証明本体は未検証。集約・公理監査には一切接続していない。
- 他レーンの変更には触れていない。停止コミットに含めるのは検証済みの一点評価・所有集約・監査・この計画だけ。

### 既知の問題
- 停止前の全体検証は成功。ログは `/tmp/p-stop-aggregate.log`（7750 jobs）と `/tmp/p-stop-audit.log`（852 宣言、標準三公理のみ）。未接続の作業中ファイルは監査範囲外。
- 旧集約セッション 77644 は再照会で Unknown process id。成功終了は確認していない。終了操作の承認呼び出しも中断されたため、実行成否は不明。
- 濃度変更の単調性は κ ≤ μ だけでは主張しない。`IsCardinalChangeBound κ μ` と μ の正則性が必要。
- 任意の小さい A の Indκ(A) は一般には presentable でない。必要な小余極限の条件を明示する。

### 次の一手（新しいチャット）
1. 所有集約と `scripts/audit_infinity_presentable.lean` の全体検証状態を確認し、必要なら依存を順番に再ビルドする。
2. 作業中の `LeftFibrationStrictColimit.lean` を検証する。分類同値で元の strict 全余錐を写し、全頂点で一点相対 Hom に比較する構成。
   `leftFibrationPointEvaluationIso` と `leftStraighteningInfinityMap_evaluateIso` を余錐全体へ前合成し、`F2.isColimitCone_of_pointwise` と同値反映を使う。
3. 有限模型の置換の通常の全表示を LeftFibrationObject の strict 全余錐に持ち上げ、同じ余錐の native 性を示す。
   置換対象だけでなく元の指定 left fibration 自身への頂点同型で表示を厳密に戻す必要がある。
4. 一般の coherent filtered 添字での相対 Hom 保存と compact 性、小さい生成圏を閉じ、分類で一般の前層の accessibility へ移す。

## 規約
- foundations.md §8。所有ファイルだけ `set -o pipefail` のうえ `git commit --only`。新規 sorry・公理・引用なし、他レーン不変。
- 結論を仮定する instance を主経路へ入れない。Ind・標的は u+1、添字と有限符号は u。本文 300 行以内、引き継ぎ 100 行以内。
