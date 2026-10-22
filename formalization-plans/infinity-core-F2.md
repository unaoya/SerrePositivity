# F2：F2-lite と presentable ∞ 圏（v2、F1b）

作成日：2026-10-18。更新日：2026-10-22。
正本は [foundations.md](foundations.md)。本書は F2-lite と F2 後半の正本。
F1b の前提工程は [infinity-core-F1b.md](infinity-core-F1b.md)、
N の γ3・γ4 は [e-infinity-algebras.md](e-infinity-algebras.md) を参照する。

## 引き継ぎ（2026-10-22）

### 現在地

- 第 1 部（B4・B5、F2L-1〜4）は完了。coherent nerve の Cat_∞、引き戻しと lax pullback、
  写像空間の普遍性、同値矢印の全部分圏との比較、安定性と完全な両射影まで証明済み。
- 第 2 部の正本は §3。10-22 12:35 改訂：F2N-1・3・5 は F1b、F2N-2（Ind）は F1、F2N-4 は N。
  正則 κ の小さい join・coslice、filtered 性と coslice の弱可縮性・対角の cofinality の双方向判定を証明。
  通常 filtered 図式の有限内部 Hom・path 引き戻しの交換、元の標準余錐の native 余極限性を証明。
  小さい底上の任意の coherent 空間値図式の HasColimit は全空間模型と元の単位から構成。
  元の全空間 Kan 積・引き戻し比較の弱同値性とホモトピー逆を証明。
  境界固定の相対有限検出・同時輸送・反映、境界移動の除去は元の値・円柱を保持。
  一般 coherent 図式の全空間模型の native 余極限性と filtered 有限検出を証明済み。
  a6 は元の模型 fiber・全空間比較の同値性、指定 path・二脚の整合まで完了。
  a7 は元の余極限頂点を持つ native 引き戻し極限錐、終対象・空形状・全単体の交換、
  形状接着の錐空間の native 極限性、finiteShape_cell_induction を整備済み。
  coherentColimitFunctor は元の全空間頂点・native 余錐を保ち、指定各点余錐による完成と全錐の像を比較。
  元の単位三角柱の三三単体・共有面・上下二面・六側面と、全係数 EF⊗K の実 pointed 持ち上げを保持。
  元の指定三角形比較の二辺・長辺を同じ普遍 prism へ厳密に回収し、全 prism 比較の指定自然性を証明。
  元の相対三角形比較の前合成を、同じ全実三角形の三辺の指定比較で値まで同定。
  六共有辺の実 prism・実始点・実終点・指定比較を保ち、四面を同じ共通四頂点と六比較へ正規化。
  CoherentColimitUnitTetrahedronBoundary.comparison_square は同じ全族の四面の厳密な可換性。
  二内部三角形は元の三単体の実共有面そのもの。元の定値余極限三角形・外側六面を保持して境界を構成。
  三つの coherentColimitUnit{First,Middle,Last}TotalRelation は同じ元の全空間・恒等初期値上の指定関係。
  coherentColimitUnitTriangleValue_coherence は二内部面を消去した元の上下二面・指定対角の整合式。
  a6 の元の比較と模型三角形の共有する普遍輸送成分を同定・消去。元の模型正方形へ接続し、残る fiber 因子は同じ指定共役。
  元の raw/native 区間族・単位の実二座標・成分の値を照合し、既存の下側因子を同じ実一点輸送比較へ同定。
  元の三辺・全三角形を保持した長辺輸送を指定比較へ入力し、同じ元の長辺 prism・全終点・curry・一点値を厳密に回収。
  未完：下側の指定輸送因子と上側の native 因子の整合・消去、二三角形・指定 path の全錐比較、引き戻し保存、
  部分極限 cospan の各点の極限性、有限和・単射側の接着の存在と交換の同時帰納。
  F1b は a7 後に F2N-3（κ-compact・Yoneda・retract）、F1 の Ind と N の冪等完備化完成後に F2N-5。
  検証：三集約同時ビルド9778 jobs、公理監査13261宣言・F1/F1B 同時 import 成功、標準三公理のみ。
  同じ区間作用による反映、共有する普遍成分の同定・消去、a6 の模型正方形と元の指定共役を含む追加23明示宣言を型検査。

### 残り（依存順、実作業時間の概算）
- F2N-1：𝒮 の一般 coherent filtered 余極限と有限極限との交換。全空間模型の native 余極限性は証明済み。
- F2N-2（F1）：前層内の Indκ、生成と保存関手の延長の普遍性。F2/Ind/・Ind.lean は読み取り専用。
- F2N-3（F1b）：compact・Yoneda・retract、30〜80 時間。F2N-4（N）：冪等完備化、所有外。
- F2N-5：Ind(C) の安定性、冪等完備 C の compact 生成。40〜100 時間。
- その後 F2 後半：presentable と随伴関手定理（F1b）。HTT §5.5、Kerodon 9。細分化は §4。
  Bousfield 局所化・P_Σ は従来どおり N の I-b の範囲。

### 主要宣言（検証済みのみ）

- `F2.IsKappaSmall` / `F2.IsFilteredInfinity` / `F2.IsKappaFiltered` / `F2.isKappaSmall_aleph0_iff` / `F2.isKappaFiltered_aleph0_iff` / `F2.isFilteredInfinity_of_retract`
- `F2.isKappaSmall_join` / `F2.isKappaFiltered_sliceUnder` / `F2.isFilteredInfinity_iff_isContractibleKan` / `F2.cosliceCoproduct_isPullback` / `F2.isRightCofinal_sliceUnderProjection_of_filtered`
- `F2.laxCosliceDiagonalCommaIso` / `F2.weaklyContractible_diagonalStandardComma_iff` / `F2.isFilteredInfinity_iff_of_equivalence` / `F2.isKappaFiltered_iff_of_equivalence`
- `F2.reflectedBousfieldKanAugmentation_isWeakHomotopyEquivalence_of_filtered` / `F2.filteredKanColimitComparison_factor` / `F2.filteredKanColimitCocone_isColimit`
- `F2.kanCoconeAugmentationComparison_factor` / `F2.filteredKanColimitOrdinaryCocone_isColimit` / `F2.intervalReplacementColimitIso` / `F2.intervalPullbackColimitIso`
- `F2.intervalPullbackCone_isLimit` / `F2.filteredIntervalPullbackExchange` / `F2.continuousKanLeftFibration_pair_relative_detection` / `F2.totalKanProductComparison_homotopyEquivalence`
- `F2.continuousKanLeftFibration_finite_relative_detection` / `F2.continuousKanLeftFibration_finite_boundary_detection`
- `F2.coherentSmallConstantTargetMap_isQCatEquivalence` / `F2.coherentDiagramTotalCocone_vertex`
- `F2.coconeTransformationMap_prism` / `F2.coconeTransformationMap_isQCatEquivalence`
- `F2.coherentCoconeTotalComparison_homotopyEquivalence` / `F2.coherentTotalCoconeUnitIso`
- `F2.unstraighteningMappingTriangleIso` / `F2.coherentTotalUnitHomComparison_homotopyEquivalence`
- `F2.coherentDiagramTotalCocone_isColimit` / `F2.hasColimit_coherentSpaceDiagram`
- `F2.exists_relativePathFiniteModelTransport` / `F2.relativePath_model_reflection`
- `F2.laxPullbackFst_isExactFunctor` / `F2.laxPullbackSnd_isExactFunctor` / `F2.laxPullback_isStable`
- `F2.fiberwisePullbackNativeCone_isLimit` / `F2.fiberwisePullbackCone_projection_commutativity` / `F2.fiberwisePullbackTotalRawPathHomotopy_curry` / `F2.coherentTotalMapNativeFiberTransportIso` / `F2.coherentTotalMapNativeValueIso` / `F2.coherentTransformationNativeCoconeIso` / `F2.coherentCospanConeNativeComparison` / `F2.coherentCospanConeValuePathHomotopy_unit` / `F2.coherentCospanConeTotalModelComparison_over_base` / `F2.coherentCospanConeTotalModelFiberComparison_path_ι` / `F2.coherentCospanConeRelativeValuePathIso_eq` / `F2.coherentCospanConePointwiseCone_vertex` / `F2.coherentCospanConePointwiseCone_leftTriangle` / `F2.unstraighteningMappingTrianglePrism` / `F2.coherentTransformationTriangleLift_long` / `F2.coherentTransformationPointedTriangle_projection` / `F2.relativeExtensionRestriction_vertex` / `F2.prismExtensionComparison_restrict` / `F2.coherentTriangleExtensionComparison_restrict` / `F2.coherentTriangleExtensionRestriction_long` / `F2.relativeFunctorBaseChangeInverse_overPre` / `F2.prismExtensionPullbackEndpoint_restrict` / `F2.prismExtensionPullbackComparison_restrict` / `F2.relativeFunctorCurryHom_pre` / `F2.relativeFunctorCurryHom_evaluate` / `F2.prismExtensionCurryWitnessIso_restrict` / `F2.unstraighteningSourceComparisonIso_app_pre` / `F2.coherentTriangleCurryIso_restrict` / `F2.unstraighteningTriangleRelativeVertexIso_pre` / `F2.coherentSmallTriangleRelativeIso_pre` / `F2.unstraighteningTriangleRelativeVertexIso_pre_eq` / `F2.coherentSmallTriangleRelativeIso_pre_heq_endpoint` / `F2.coherentSmallFiberPointedTriangle_projection` / `F2.coherentSmallTriangleRelativeIso_pre_eq_endpoint` / `F2.coherentTransformationTriangleFiberIso_heq_endpoint` / `F2.relativeIsoFiberHomotopy_hom` / `F2.coherentCospanConeFiberComparisonPathIso_eq` / `F2.coherentCospanNativeSectionFiberPathDownIso_eq_native` / `F2.coherentCospanModelFiberPathIso_eq_section_down` / `F2.coherentCospanNativeFiberCospanEndComparison_homotopyEquivalence` / `F2.coherentCospanNativeSectionEndComparison_homotopyEquivalence` / `F2.strictPullback_functorIso_exists` / `F2.kanHomotopyRectificationIso_image` / `F2.coherentCospanNativeLeftLegFinalImage_heq` / `F2.functorIsoDown_injective` / `F2.coherentCospanNormalizedModelPathLiftIso_eq_section` / `F2.coherentCospanCommonLeftIso` / `F2.coherentCospanCommonRightIso` / `F2.intervalReplacementSectionIso_endpoint` / `F2.coherentCospanConeNativePathDownIso_whisker` / `F2.coherentTotalNativeKanIso_postValueImage` / `F2.coherentCospanCommonRightImage` / `F2.cospanRectificationLeftIso_inverse_image` / `F2.coherentCospanNativeFirstPathIso_heq` / `F2.coherentCospanModelFirstPathIso_heq` / `F2.coherentCospanCommonComparisonIso` / `F2.coherentCospanConeNativeComparison_homotopyEquivalence` / `F2.coherentCospanConeNativeComparison_isWeakHomotopyEquivalence` / `F2.coherentCospanNativeLimitCone` / `F2.coherentCospanNativeLimitCone_isLimit` / `F2.coherentCospanNativeLimitCone_vertex` / `F2.coherentCospanNativeLimitConeFstIso` / `F2.coherentCospanNativeLimitConeSndIso` / `F2.coherentCospanNativeLimitCone_projection_commutativity` / `F2.coherentFilteredColimitVertex_isTerminal` / `F2.coneMappingShapePushoutIso` / `F2.coneMappingShapePushout_right_fibration` / `F2.coneMappingShapePushoutNativeCone_isLimit` / `F2.finiteShape_cell_induction` / `F2.CoherentFilteredLimitExchangeShape` / `F2.coherentColimitFunctor` / `F2.coherentCompletedLimit_iff_colimitFunctor` / `F2.coherentCospanOfFunctorTriangles` / `F2.functorCospanNativeLimitCone_isLimit` / `F2.exists_limitFamilyRestrictionTriangle` / `F2.coneFamilyReindex_apex` / `F2.exists_limitConeFamilyReplacement` / `F2.HasSpaceLimitsOfShape` / `F2.coherentFilteredLimitExchangeShape_simplex` / `F2.coherentFilteredLimitExchangeShape_of_empty`

- `F2.coherentColimitUnitValueAction_coherence` / `F2.coherentColimitUnitValueAction_total_heq_native` / `F2.coherentColimitUnitValueAction_precomp_firstEdge`

### 依存と提供

- N の HomotopyLimits（γ3c の 𝒮 の余極限）と F1 の straightening は読み取り専用。
  γ4 は前提として一括仮定せず、必要な公開界面と提供済みの範囲を確認する。
- D・K へ第 1 部と compact・安定性を提供。Ind は F1 の公開宣言を使い、必要時に未提供なら F1 に依頼して待つ。

### 未コミット

- 今回の所有変更は保存済み。F1 の Ind と N の Idempotent の集約・サブディレクトリは所有・保存対象外。

### 既知の問題

- F1 の前層・Yoneda は F1 計画の後続工程。Ind の存在を仮定して回避しない。F1B の intervalMinimum 複製は straightening 非依存の F1.IntervalMinimum import に置換。衝突ゼロ。
- 一般の coherent な図式の余極限と、通常の小圏による strict 図式の余極限を区別する。
- 既存 anodyneKanObject の保存性を仮定せず、連続な Q と単位の anodyne 性・弱同値性を具体的に証明。
  通常の指定余錐の全脚・高次の整合性を保持した native な普遍性まで証明済み。
  任意の二射の元の cospan の native な極限との比較は証明済み。一般 coherent filtered 図式の交換は残る。
  全空間模型の余錐全体・頂点・単位との比較は構成済み。余錐空間の比較同値と元の単位との同型は証明済み。
  元の全空間余錐への全 Hom 判定の適用は完了。必要な fiber 標的を明示し、小さい単位の比較から証明。
- 主経路に追加公理・sorry・ModelCategory SSet の instance 仮定を置かない。

### 次の一手

- F2N-1 a7：値へ写した全三角形の整合式の外側因子を消去し、a6 の指定 path と全錐へ接続する。
  元の五因子は UnitValueAction_triangle_cancel で元の定値三角形の同じ逆を左合成し、先頭因子を消去済み。
  長辺と最後辺は UnitValueAction_total_heq_native・precomp_firstEdge で元の a6 の中央比較へ接続できる。
  LowerTransportFactorIso_heq_constant_point_unit と ConstantTriangleValue_heq_fiber_unit で元の二因子を同じ単位・値へ照合済み。
  cancel_original_precomp_postcomp と UpperUnitFactor_triangle_cancel は同じ元の指定三角形・実終点の消去式。
  UpperNativeFactorIso_heq_components は同じ nativeActionComponentsIso の逆へ値まで同定済み。
  IntervalModel_square は a6 の元の比較を同じ全 Hom の模型成分へ接続。IntervalModelFiber_heq_conjugate は残る fiber 因子の元の指定共役。
  次は NativeUniversalSquare とこの模型正方形に同じ五因子の消去式を代入し、完成済み三角形との像を照合。IntervalTransportAction_iso_injective で反映する。
  下側輸送・上側単位・上側 native の元の外側因子を消去し、同じ三辺と指定三角形の関係を回収する。
  同じ余錐 fiber 写像の前合成の充満忠実性で整合を反映し、二三角形・指定 path を保つ全錐比較を束ねる。
  その極限性から引き戻し保存へ接続。値の整合式・辺ごとの同型だけでは全錐比較の完了としない。
  続いて部分極限 cospan の極限性、有限和・単射側の接着の存在と交換の同時帰納、finiteShape_cell_induction。
  HTT §5.3.3、a7 残り12〜24時間（暫定。三角形に沿う全指定因子の照合に不確実性）。strict 図式だけでは完了としない。
  a7 後は承認を待たず F2N-3 へ。その後 F1 の Ind・N の冪等完備化を利用して F2N-5。

## 0. 目標と範囲

| 工程 | 担当 | 到達点 | 原典 |
| --- | --- | --- | --- |
| F2L-1 | F1b | 完了：Cat_∞ の対象・辺・関手 core との写像空間比較、関手の同値の判定 | Kerodon §5.5.3 |
| F2L-2 | F1b | 完了：Cat_∞ の引き戻し、全試験写像空間の普遍性、二射影と指定 path の同時比較 | Kerodon §5.5.3、HTT §3.3.3 |
| F2L-3 | F1b | 完了：lax pullback、対象三つ組、native 極限錐、全試験関手 core、Remark 6 の写像空間の 𝒮 内の極限性 | Tamme §1 Definition 5・Remark 6 |
| F2L-4 | F1b（D と接続） | 完了：通常の引き戻しとの比較、安定性・完全な両射影、極限・余極限の成分判定 | Tamme §1 Remark 7・Lemma 8 |
| F2N-1〜5 | F1b（1・3・5）、F1（2）、N（4） | filtered、Ind、compact、冪等完備化、Ind の安定性 | HTT §5.1.4・§5.3、Kerodon 9 |
| F2 後半 | F1b（presentable・随伴関手定理）／N（Bousfield・P_Σ） | presentable、随伴関手定理、Bousfield 局所化、P_Σ | HTT §5.5、Kerodon 9 |

F2-lite の範囲に presentable・Pr^L のテンソル積・HA §4.8 は含めない。
Tamme の分裂定理・Verdier 列・Land–Tamme の主定理は K-基盤、dg gluing との比較は D の β4。

## 1. 設計と受入条件

- 新規配置は `SerrePositivity/InfinityCategories/F2/`。F1 の既存公開名を保持する。
- 宇宙：小 ∞ 圏の単体は `SSet.{u}`、`CatInfinity.{u}` は `SSet.{u+1}`。
  Cat_∞ 内の図式と、元の小 ∞ 圏間の関手の宇宙を明示する。
- `CatInfinity = SimplicialNerve QCat`、QCat の Hom は `core Fun(C,D)`。
  Hom に全ての自然変換を含む模型は別の構造なので代用しない。
- Cat_∞ の引き戻しの構成では、対象と射の表示に加えて、全ての試験 ∞ 圏からの
  写像空間が空間の引き戻しを与えることを証明する。hCat だけの普遍性で完了としない。
- `p : A → C`、`q : B → C` に対し、lax pullback は
  `(A × B) ×_(C × C) Fun(Δ¹,C)`。端点評価は `(source,target)`、矢印は `p(a) → q(b)`。
  元の引き戻しは、矢印が同値である対象の張る全部分 ∞ 圏として比較する。
- 単体集合の strict pullback が使える箇所では、端点評価の充填性と、その strict pullback が
  Cat_∞ の引き戻しを表すことを証明してから使う。
- 安定性は有限極限・有限余極限と exact 関手の保存を通じて接続し、
  dg gluing との比較・分裂定理を定義のフィールドとして仮定しない。
- 追加公理・sorry・文献入力は導入しない。許す公理は標準三公理のみ。
  新しい主経路に `ModelCategory SSet` 等の instance 仮定を置かない。
- 保存単位ごとに対象ビルド、公理監査、主経路の instance 仮定の検索を実施。
  検証済みの構成・普遍性・比較の範囲を別々に現在地へ反映する。

## 2. 原典

- [Kerodon §5.5.3](https://kerodon.net/tag/0208)：QCat の coherent nerve と ∞ 圏の ∞ 圏。
- [Kerodon Proposition 5.5.3.3](https://kerodon.net/tag/020B)：局所 Kan 性からの quasicategory 性。
- [Tamme 2018 §1](https://arxiv.org/html/1703.03331v3#S1)：Definition 5、Remarks 6–7、Lemma 8。
  Remark 6 の四角形は [PDF 第 5 頁](https://arxiv.org/pdf/1703.03331v3#page=5) で確認する。
- HTT §3.3.3（∞ 圏の極限）、§5.3（Ind・compact）、§5.5（presentable）。
- [Kerodon §4.9.4](https://kerodon.net/tag/03S1) の κ-small、[§9.1.1](https://kerodon.net/tag/02P8) の filtered ∞ 圏。
  9.1.1.16 の正則 κ 版 coslice、9.1.1.17 の弱可縮性、9.1.1.18 の対角判定、9.1.1.19 の同値不変性、9.1.1.20 の Kan 判定を証明済み。

## 3. F2-lite 第 2 部（10-22 12:35 分担改訂）

### 引き継ぎ（F1b：F2N-1・3・5、F1：F2N-2、N：F2N-4）

- 現在地：F1b は a7 → F2N-3 → F2N-5。Ind は F1、冪等完備化は N。第 1 部は完了済み。
  F2N-1 は正則 κ の小さい join・coslice、一般の弱可縮性、対角関手の cofinality とその逆の判定まで証明。
  通常の指定 filtered 余錐の native な普遍性、path 座標を保つ交換同型、任意の strict Kan cospan の native な比較を証明。
  相対有限検出と全空間模型の元の余錐の native 余極限性を証明。小さい底上の一般 coherent 図式の HasColimit を公開。
  元の積比較の弱同値性・ホモトピー逆を証明。定値底の有限関手比較は cofinal、各値の内部 Hom 表示と path 比較を構成。
  始点評価の底上の逆と両端固定の Kan path 比較のホモトピー逆、二入力・単位上の全 path を保つ Kan 引き戻し比較を構成。
  形状制限の相対内部 Hom による底変換、元の両端評価と二入力射・引き戻し底射の left fibration 性を証明。
  各 fiber と元の三値の path 引き戻しの厳密な同型、三座標を保つ包含と元の値による相対有限検出を証明。
  任意の有限標的射を元の一値で検出し、元の Kan 比較への有限持ち上げと有限写像空間の π₀ の全射性を証明。
  全相対境界の単射有限近似、模型本体までの同時輸送と元の値への反映を構成。反映後の境界は厳密に保持。
  中央の全境界円柱を保持する相対 zigzag 合成を証明。
  共通境界付きの二入力の同時検出と相対還元を構成。任意の有限標的射を元の一値の実際の比較像で相対検出。
  任意の Kan 始域境界への相対持ち上げと、その境界を厳密に固定する補正を構成。
  全標準境界の path 置換終点の自明 Kan 性から、元の比較の弱同値性と単体的ホモトピー逆を証明。
  元の引き戻し全空間を native 極限錐の頂点に構成し、全錐の可逆比較・元の比較の頂点辺・恒等図式辺・各脚の自然性を保持。
  一般 coherent 図式の全空間模型の native 余極限性と filtered 有限検出を証明済み。
  a6 は元の模型 fiber・全空間比較の同値性、指定 path・二脚の整合まで完了。
  a7 は元の余極限頂点を持つ native 引き戻し極限錐、終対象・空形状・全単体の交換、
  形状接着の錐空間の native 極限性、finiteShape_cell_induction を整備済み。
  coherentColimitFunctor は元の全空間頂点・native 余錐を保ち、指定各点余錐による完成と全錐の像を比較。
  元の単位三角柱の三三単体・共有面・上下二面・六側面と、全係数 EF⊗K の実 pointed 持ち上げを保持。
  元の指定三角形比較の二辺・長辺を同じ普遍 prism へ厳密に回収し、全 prism 比較の指定自然性を証明。
  元の相対三角形比較の前合成を、同じ全実三角形の三辺の指定比較で値まで同定。
  六共有辺の実 prism・実始点・実終点・指定比較を保ち、四面を同じ共通四頂点と六比較へ正規化。
  CoherentColimitUnitTetrahedronBoundary.comparison_square は同じ全族の四面の厳密な可換性。
  二内部三角形は元の三単体の実共有面そのもの。元の定値余極限三角形・外側六面を保持して境界を構成。
  三つの coherentColimitUnit{First,Middle,Last}TotalRelation は同じ元の全空間・恒等初期値上の指定関係。
  coherentColimitUnitTriangleValue_coherence は二内部面を消去した元の上下二面・指定対角の整合式。
  a6 の元の比較と模型三角形の共有する普遍輸送成分を同定・消去。元の模型正方形へ接続し、残る fiber 因子は同じ指定共役。
  元の raw/native 区間族・単位の実二座標・成分の値を照合し、既存の下側因子を同じ実一点輸送比較へ同定。
  元の三辺・全三角形を保持した長辺輸送を指定比較へ入力し、同じ元の長辺 prism・全終点・curry・一点値を厳密に回収。
  未完：下側の指定輸送因子と上側の native 因子の整合・消去、二三角形・指定 path の全錐比較、引き戻し保存、
  部分極限 cospan の各点の極限性、有限和・単射側の接着の存在と交換の同時帰納。
  F1b は a7 後に F2N-3（κ-compact・Yoneda・retract）、F1 の Ind と N の冪等完備化完成後に F2N-5。
- 残り：F1b は F2N-1 → F2N-3 → F2N-5。F2N-5 は F1 の F2N-2 と N の F2N-4 完成後。
- 依存：N の HomotopyLimits と F1 の straightening・前層・Yoneda は読み取り専用。
  F1 計画では前層・Yoneda は後続工程。提供済みの範囲をソースで確認し、存在を仮定して済ませない。
  N の一般の coherent 図式の余極限・γ4 の最新状況は e-infinity-algebras.md を参照。
  移管前の詳細は [archive/infinity-core-F2-N-handoff-2026-10-20.md](archive/infinity-core-F2-N-handoff-2026-10-20.md)。
- 提供：K-基盤へ κ-compact・retract 閉性と compact 生成、D へ安定性の界面。
- 所有：F2/ のうち Ind/・Ind.lean（F1）と Idempotent/・Idempotent.lean（N）を除く。F2 集約・監査と両計画も所有。
- 既知の問題：通常の小圏の strict 図式だけでは一般の filtered 図式を網羅しない。
  Ind の生成・普遍性、冪等完備化の普遍性は構造の仮定にせず証明する。
- 次の一手：F2N-1 a7：値へ写した全三角形の整合式の外側因子を消去し、a6 の指定 path と全錐へ接続する。
  元の五因子は UnitValueAction_triangle_cancel で元の定値三角形の同じ逆を左合成し、先頭因子を消去済み。
  長辺と最後辺は UnitValueAction_total_heq_native・precomp_firstEdge で元の a6 の中央比較へ接続できる。
  LowerTransportFactorIso_heq_constant_point_unit と ConstantTriangleValue_heq_fiber_unit で元の二因子を同じ単位・値へ照合済み。
  cancel_original_precomp_postcomp と UpperUnitFactor_triangle_cancel は同じ元の指定三角形・実終点の消去式。
  UpperNativeFactorIso_heq_components は同じ nativeActionComponentsIso の逆へ値まで同定済み。
  IntervalModel_square は a6 の元の比較を同じ全 Hom の模型成分へ接続。IntervalModelFiber_heq_conjugate は残る fiber 因子の元の指定共役。
  次は NativeUniversalSquare とこの模型正方形に同じ五因子の消去式を代入し、完成済み三角形との像を照合。IntervalTransportAction_iso_injective で反映する。
  下側輸送・上側単位・上側 native の元の外側因子を消去し、同じ三辺と指定三角形の関係を回収する。
  同じ余錐 fiber 写像の前合成の充満忠実性で整合を反映し、二三角形・指定 path を保つ全錐比較を束ねる。
  その極限性から引き戻し保存へ接続。値の整合式・辺ごとの同型だけでは全錐比較の完了としない。
  続いて部分極限 cospan の極限性、有限和・単射側の接着の存在と交換の同時帰納、finiteShape_cell_induction。
  HTT §5.3.3、a7 残り12〜24時間（暫定。三角形に沿う全指定因子の照合に不確実性）。strict 図式だけでは完了としない。
  a7 後は承認を待たず F2N-3 へ。その後 F1 の Ind・N の冪等完備化を利用して F2N-5。

| 工程 | 担当 | 内容と受入条件 | 原典 | 見積もり |
| --- | --- | --- | --- | --- |
| F2N-1 | F1b | filtered ∞ 圏と κ-filtered の定義、cofinality、𝒮 の filtered 余極限と有限極限の交換。一般の coherent な図式で証明する | HTT §5.3.1–3 | 40〜100 時間 |
| F2N-2 | F1（10-22 12:35 移管） | 前層の全部分 ∞ 圏として Indκ(C) を構成。filtered 余極限による生成と、保存関手の延長の普遍性を証明する | HTT 5.3.5.1–10 | 50〜120 時間 |
| F2N-3 | F1b | κ-compact、Yoneda 像の compact 性、retract による閉性、Ind の compact 対象の比較 | HTT §5.3.4、5.3.5.5・11 | 30〜80 時間 |
| F2N-4 | N | coherent な冪等図式と分裂、前層内の retract 閉包、冪等完備化の普遍性、compact 部分との同定 | HTT §5.1.4、5.3.4.17 | 40〜100 時間 |
| F2N-5 | F1b | C が小安定なら Ind(C) は安定。有限図式の filtered 表示と極限余極限の交換から証明し、冪等完備 C の compact 生成を公開 | HTT 5.3.3・5.3.5.15、HA §1.1.3 | 40〜100 時間 |

宇宙は第 1 部と共通。κ の正則性・図式の小ささを明示し、Indω と非連結 K 用の大きい κ を混同しない。
有限図式を C 内の図式の filtered 余極限で表示する際は、HTT 5.3.5.15 の有限半順序集合という条件を保持する。
presentable の一般論・随伴関手定理は F1b、Bousfield 局所化・P_Σ は N が I-b で分担する。
原典：[HTT](https://www.math.ias.edu/~lurie/papers/HTT.pdf) §5.1.4・§5.3。

## 4. F2 後半（第 2 部の後、F1b）

| 工程 | 内容と受入条件 | 原典 |
| --- | --- | --- |
| F2P-1 | accessible ∞ 圏・accessible 関手、κ-compact 生成の濃度変更と Ind の比較 | HTT §5.4 |
| F2P-2 | presentable ∞ 圏の構成と特徴づけ、小余極限と accessible 局所化の接続 | HTT §5.5.1 |
| F2P-3 | presentable 間の随伴関手定理、余極限保存と左随伴、accessible な極限保存と右随伴の判定 | HTT §5.5.2 |

Bousfield 局所化・P_Σ は N の分担。上表の定理の結論を構造のフィールドに仮定しない。
実施記録はコミットメッセージ。本書には現在地と設計を置き、長い型一覧を追記しない。
