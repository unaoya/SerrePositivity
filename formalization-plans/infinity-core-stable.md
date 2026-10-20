# D レーン：D7 → β3 → β5 → β4

> **v2 の位置づけ（2026-10-19）**：foundations.md §6 の D。D7 の後、β3（Drinfeld 商 = Verdier 商）、β5（D(A)・⊗_A）、β4（gluing = lax pullback）。

## 引き継ぎ（2026-10-20）

### 現在地

- S1〜S7（D7）完了。安定 ∞ 圏の h の三角構造（TR1〜TR4）、完全関手の全整数 CommShift・三角性を公開済み。
- D(S) の実境界から Q・A と二微分式を構成し、coslice の直接充填で cofiber の普遍性を証明。全 fiber/cofiber・有限極限余極限、任意四角形の双カルテジアン判定と安定性まで完成。
- 実 suspension・複体シフト・接続射の符号を照合し、標準 cofiber 三角形の D3 像を cone 三角形と同定。全 distinguished triangle の保存・反映、逆関手の三角性、単位・余単位のシフト整合性を持つ D3 の三角同値を公開済み。
- β3：F1B の局所化と L4 §26〜27 を読了。商の実零化、平坦分解の実 ∞ 圏同値、dg 加群・前三角 dg 圏・平坦分解後の商の実安定性、商関手の完全性と実分母の反転まで完成。
- 実 Verdier over 上の屋根対応・pinched Hom fiber・商側の両側 fibration を構成。固定商 Hom の商屋根全空間への包含の right cofinality・弱同値を証明。実屋根比較自体は π₀ 全射までで、弱同値性は未証明。境界固定の有限相対充填・prism・同時輸送は完成。
- 全次元の最後外ホーンから R・K を回収し、dR=0・dK=−最後辺∘R を証明。実 Hom cone の指定閉残差の原始元と Q・A の二未知解を双方向に接続。有限混合次元族に一つの追加実閉分母と全実充填を供給する。
- 全次数の over 単体と実 Verdier 部分圏内の閉始点細分を構成。零面保存、零固定・正番号非零の全順序写像との可換性、全正番号面・退化・共有面の厳密一致を証明。
- `TruncatedJoinConeData f N` と有限頂点からの N=0 の実初期値を構成。錐全体を一つの追加実閉分母で更新し、同じ apex・全面・全正番号退化条件を保つ操作まで完成。
- 次次数の零面 f σ と既存錐の正番号面から実境界写像を貼る。有限族を一つの分母後に同時充填し、その全面・共有面・実 apex を更新済み下次数錐へ厳密に一致させた。基本退化表示の標準錐の一致・全面保存・退化正規化も完成。`dgVerdierTruncatedConeSuccessor_nonempty` は次次数有限なら N+1 の錐を、`dgVerdierTruncatedConeData_nonempty` は各次数有限なら任意有限次数の錐を供給する。
- 次元上界までの切断写像の一意な全次数延長を標準 splitting から構成。切断錐の全順序写像への自然性、実 coslice への切断写像と射影の厳密一致、実 join 写像の左右制限・apex・全低次数単体との一致を証明。`dgVerdierFiniteJoinCone_nonempty` は任意の有限単体集合からの実分母図式に同じ部分圏内の実 join 錐を供給する。`dgVerdierOver_op_isFilteredInfinity` により実分母 over 圏の反転は filtered ∞ 圏。
- 任意の有限商屋根図式と指定元境界を、共通の実分母 fiber 上の厳密な相対問題へ還元。元境界を先に右持ち上げし、その比較像を全境界で固定して商全体を右持ち上げする。二輸送の終端・全底・境界全時刻の一致を証明。共通頂点を同じ実辺の閉分母へ戻し、元・商の pinched Hom 係数正方形と実屋根像を同定した。正次数の還元問題は一つの追加閉分母後に実充填と全境界付き輸送を持つ。二段階輸送も実合成三角形ごと相対構成し、任意の正次数標準単体境界の比較正方形に、元の全境界・全時刻で整合するホモトピー相対充填を供給した。一般有限対への拡張と屋根比較の弱同値判定は未完。
- 入口：D7 は `Derived/StableTriangulatedEquivalence.lean`。β3 は `Derived/DGVerdierConeRefinement.lean`・`Derived/TruncatedConeNextBoundary.lean`・`Derived/DGActualRoofHomotopyFillers.lean`・`Derived/RoofCompatibleTransportComposite.lean`・`Derived/DGActualRoofFiberReduction.lean`。

### 残り（依存順、時間は推定）

- β3：Drinfeld 商の dg nerve の局所化普遍性と Verdier 列。平坦分解後の商の安定性と商関手の完全性は完成。Drinfeld Thm 3.4・Lemma 13.5、HA §1.1.4、Kerodon §6.3。残り 1〜2 万行、複数日。
- β5：非可換 dg 代数の D(A)、相対 tensor・Hom の ∞ 関手化、Morita 不変性。L4 §26、HA §7.1.2。1〜3 万行、複数日。
- β4：dg gluing の nerve と安定 ∞ 圏の lax pullback の同値。α2b の提供済み lax pullback を読み取り専用で使う。Tamme §1、Kuznetsov–Lunts。1〜2 万行、複数日。

### 主要宣言（名前のみ。正確な型は Lean）

- `IsStable`・`suspensionEquivalence`・`pretriangulated_ho`・`isTriangulated_ho`・`exactFunctor_isTriangulated`。
- `cofiberBoundaryLiftQ_differential`・`cofiberBoundaryLiftA_differential`・`standardCofiberCocone_isColimit`・`derivedInfinityCategory_isStable`。
- `derivedStableHomotopyEquivalenceCommShift`・`derivedStableHomotopyEquivalenceIsTriangulated`。
- `dgModuleNerve_isStable`・`dgRoofCorrespondenceMap`・`dgRoofCorrespondenceFiberIso`・`dgQuotientRoofCorrespondenceProjection_leftFibration`。
- `dgQuotientFixedHomRoofMap_isRightCofinal`・`dgQuotientFixedHomRoofMap_isWeakHomotopyEquivalence`・`dgRoofCorrespondenceMap_piZero_surjective`。
- `dgGeneralLastHornTopResidual_differential`・`dgGeneralLastHornConeResidual_closed`・`dgGeneralLastHornSolution_nonempty_iff_coneResidual_boundary`。
- `DGGeneralLastHornResidualRefinement.solution`・`dgGeneralLastHornFinite_exists_sourceRefinement_fillers`・`dgVerdierBoundaryFinite_exists_refinedSimplexes`。
- `dgVerdierSimplexInitialRefinement_pullback_initial`・`dgVerdierSimplexInitialRefinement_congr`・`dgVerdierBoundaryRefinedSimplex_commonFace_eq`。
- `TruncatedJoinConeData`・`TruncatedJoinConeData.restrict`・`dgVerdierZeroConeData_nonempty`・`dgVerdierTruncatedConeRefinement`。
- `BoundaryFaceCompatible`・`boundaryFaceGluing_face`・`truncatedConeNextBoundary_face_zero`・`truncatedConeNextBoundary_face_positive`。
- `dgVerdierConeNextSimplex_face_positive`・`dgVerdierConeNextSimplex_first_vertex`・`dgVerdierConeNextSimplex_commonFace_eq`・`dgVerdierConeNextFinite_exists`。

- `truncatedConeDegeneracy_congr`・`truncatedConeNormalizeNext_face_positive`・`TruncatedJoinConeData.normalizedSuccessor`。
- `dgVerdierTruncatedConeSuccessor_nonempty`・`dgVerdierTruncatedConeData_nonempty`。

- `boundedSimplicialExtension`・`boundedSimplicialExtension_truncation`・`boundedSimplicialExtension_unique`。
- `TruncatedJoinConeData.naturality`・`TruncatedJoinConeData.cosliceMap_projection`・`TruncatedJoinConeData.joinMap_simplex`。
- `dgVerdierFiniteJoinCone_nonempty`・`finiteSimplicialOpposite`・`dgVerdierOver_op_isFilteredInfinity`。

- `roofRelativeFiberPrism_nonempty`・`RoofRelativeFiberPrism.fiber_square`・`RoofRelativeFiberPrism.homotopy_boundary`。
- `dgActualRoofFiberReduction_nonempty`・`dgActualRoofClosedCoefficient_square`・`dgActualRoofReducedFiller_exists`。
- `dgActualRoofClosedSourceCoefficient_inclusion`・`dgActualRoofClosedTargetCoefficient_inclusion`・`dgActualRoofClosedTransport_boundary`。

- `roofRelativeCompositionTriangle_exists`・`roofCompatibleTransportComposite_nonempty`・`RoofCompatibleTransportComposite.boundary`。
- `RoofHomotopyRelativeFiller`・`dgActualRoofHomotopyRelativeFiller_nonempty`。

### 依存と提供

- Core・F1・F1B・F2・DGNerve・DoldKanComparison・HomotopyLimits・DifferentialGraded・KST は読み取り専用。
- 提供：Stable の S1〜S6、D(S) の安定性、任意四角形の双カルテジアン判定、D3 の三角同値。
- 編集対象：Stable/・Derived/、両集約と両監査、本計画。明示指示により Derived 計画の D7 状態も更新する。

### 未コミット

- 今回の所有ファイルだけを保存。自分の未コミットなし。他レーンの変更は取り込んでいない。

### 既知の問題

- D7・β3 の零化・平坦模型の対象・集約ビルド成功（7386 jobs）。公理監査は Derived 9374 宣言／1025 モジュール、Stable 10489／1295。許容三公理のみ。今回の新規5モジュールは警告なし。主要宣言に `ModelCategory SSet` の追加 instance 仮定なし。
- Stable のシフトは実 suspension に由来する。D3 の二切断の誘導シフトとの混同を避け、通常の h の比較同値で三角同値を公開した。
- β3 は H⁰ の Verdier 商の同値や dg 関手の延長だけでは完成しない。実零化・平坦模型との比較、前三角性の cell 分解への反映、平坦分解後の商の実安定性と商関手の完全性は完成。全 ∞ 関手圏の局所化普遍性と Verdier 列は未完。
- import 閉包が壊れたら他レーンを変更して迂回せず停止して報告する。

### 次の一手

- β3：正次数標準単体境界の任意の実屋根比較正方形に、元の全境界付きホモトピー相対充填を供給済み。次は零次数の局所係数充填を公開する。`DGCommonRoofComparisonVertices.lean` の頂点持ち上げ証明は、`dgQuotientFinite_exists_pinchedRelativeHomotopies` に零 `LinearData` を与え、Fin 1 の非空集合が全体であることから真部分条件を消している。同じ構成を閉分母上の実充填・輸送として回収する。
- 一般の有限対 A⊂K の係数充填へ拡張する。共通 fiber 還元後は追加閉分母の前合成が全単体集合上の実写像なので、既構成の全下次数係数を一括更新できる。有限相対骨格で、部分元写像と全体商写像・比較ホモトピーを保持し、新セルの境界固定比較を Kan 標的の相対ホモトピー延長で全体へ移す方針。二輸送の合成は今回の `RoofCompatibleTransportComposite` を使う。
- 正次数境界の充填と π₀ 全射だけを一般の弱同値判定とはしない。必要な有限対・Kan 置換の検査範囲を実際に証明してから実屋根比較の弱同値性へ進む。その後、全標的の `F1B/Localization.IsLocalization`、Verdier 列、β5、β4。実分母添字の余 filtered 性は提供済み。厳密屋根添字との cofinality を使う場合は別に証明する。

作成日：2026-10-18。状態：S1〜S7（D7）完了。β3 に進む。
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
| S7（D7） | `Derived/StableTriangulatedEquivalence.lean` | D(S) の安定性と D3 による通常の導来圏の三角構造との一致 | 完了。cofiber の普遍性、任意四角形の双カルテジアン判定、IsStable、実 suspension 由来の全整数シフト、標準 cofiber 三角形の像の同型、全 distinguished triangle の保存・反映、単位・余単位と整合する三角同値 |

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

D7 の後に着手済み。実零化、平坦模型、Hom 準同型による充満忠実性、Yoneda 模型との同値、前三角 dg 圏と平坦分解後の商の実 dg nerve の安定性、商関手の完全性まで実装。原典は Drinfeld Thm 3.4・Lemma 13.5、HA §1.1.4、Kerodon §6.3。
F1b の `Localization.lean` の `IsLocalization` を入口とし、同じ宇宙の標的への
`localizationPrecomposition` が反転関手の全部分 ∞ 圏との同値になることを証明する。

- L4 §26（archive に移管）の半自由 dg 圏分解・Hom の K-flat 性・商の H⁰ 比較を読むだけで使う。
- 必要な平坦分解を先行し、未分解の path 商が無条件に Verdier 商であるとはしない。
- 前三角 dg 圏の平坦分解後の商の実安定性と商関手の完全性は完成。
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

β5 の後、提供済みの α2b の Cat_∞ の極限・安定な lax pullback に接続する。
原典は Tamme 2018 §1、Kuznetsov–Lunts。見積もり 1〜2 万行。

- 双加群に沿う gluing の対象・写像複体・合成・微分を具体的に構成する。
- dg nerve から二射影と構造変換を作り、α2b の Fun(Δ¹,−) による lax pullback への比較を作る。
- 比較の完全忠実性・本質的全射性と ∞ 圏的普遍性を証明し、安定性・完全射影を供給する。
- α2b の未提供の極限や h の通常の pullback を完成済みの ∞ lax pullback と扱わない。

## 記録の所在

実施記録・現在地の詳細・型一覧は [archive/infinity-core-stable-log.md](archive/infinity-core-stable-log.md) に移した（2026-10-19）。現在地は冒頭の引き継ぎ節が正本で、工程ごとの記録はコミットメッセージに置く。
