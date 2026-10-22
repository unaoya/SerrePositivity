# F1b（旧 α2b）：随伴・局所化・Kan 拡張 → F2-lite

> **v2 の位置づけ（2026-10-19）**：foundations.md §6 の F1b → F2-lite。B4・B5 の後、Cat_∞ を ∞ 圏として（Kerodon 5.5）、Cat_∞ の極限、lax pullback。

## 引き継ぎ（2026-10-22、第 2 部）

### 現在地

- B1〜B5 は明示した模型・宇宙で完了。随伴・反射的局所化・左右 Quillen A・左右 Kan 拡張を構成。
  B4 は元の指定変換を保つ相対 join 表示・厳密化・局所判定・組み立て・一意性まで証明。
  B5 は nerve の通常随伴・指定局所 Kan 錐との双方向比較。一般の局所化の存在は F2 の範囲。
- F2 第 1 部 F2L-1〜4 は完了。coherent nerve の Cat_∞、引き戻しと lax pullback、
  全関手 core と写像空間の普遍性、二射影の指定比較と元の指定 path の整合を証明。
  laxPullback_isStable は元の三圏の安定性と二関手の完全性のみから安定性を構成し、両射影も完全。
- 第 2 部は F2N-1・3・5 を F1b が担当（10-22 12:35 改訂、Ind は F1、冪等完備化は N）。strict Kan cospan の filtered 比較は全 path 座標を保持。
  一般 coherent filtered 図式の相対有限検出は、元の値・全境界・元の円柱を保持。
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
  元の五因子全式を同じ固定 native 値へ写し、実三頂点・元の模型三角形を保って a6 の区間比較式へ代入済み。
  模型三角形式の下側輸送・上側単位を消去。残りの像を同じ raw fiber 二面比較の最後辺輸送で回収し、最初辺の元の模型比較への同じ射影と反映判定を証明。
  第一辺の模型比較への反映・最後辺輸送と、指定 path の四因子境界・候補の値の回収は完了。元の全 Space 単体上の独立の全反転 Hom の pointed 族、その標準初点と面を構成。元の初点 fiber への係数同値を用い、元の raw 普遍三角形との始点固定比較と同じ比較の任意制限を構成。三面を元の実 prism に同定し、二段の制限の自然性・同じ実制限を持つ二経路の像の一致・初点像の恒等性を一般形で証明。全反転 Hom の coslice 合成と固定 Kan 射の native な後合成作用の厳密な一致を証明。初点 coslice の中間・終点を元の第一・長辺の Hom 零成分へ同定し、全 pointed 族の三頂点の作用を計算。同じ全比較から元の実中間・終 fiber 内で第一・二辺合成の普遍輸送との同型を回収。候補と元の普遍比較の一致は未完。
  未完：同じ長辺輸送の残りと raw 二面比較の像の全区間族への照合・反映、二三角形・指定 path の全錐比較、引き戻し保存、
  部分極限 cospan の各点の極限性、有限和・単射側の接着の存在と交換の同時帰納。
  その後 F2N-3（κ-compact・Yoneda・retract）、F1 の Ind と N の冪等完備化を用いて F2N-5。
  各 fiber と元の三値の path 引き戻しの厳密な同型、三座標を保つ包含と元の値による境界固定の相対有限検出を証明。
  検証：三集約同時ビルド10021 jobs、公理監査16194宣言・F1/F1B 同時 import 成功、標準三公理のみ。
  元の三頂点の実 Hom 成分・全係数作用・元の実中間と終 fiber への係数射・同じ全比較の native 終点同型を含む追加27明示宣言を型検査。

### 残り（依存順、実作業時間の概算）

- 第 1 部は完了。F1b は a7 → F2N-3 → F2N-5（正本 F2 計画 §3、10-22 12:35 改訂）。
  F2N-2（Ind）は F1、F2N-4（冪等完備化）は N。Ind の必要時は公開 API を使い、未提供なら F1 に依頼して待つ。

### 主要宣言（名前のみ）

- `QCatAdjunction` / `F1B.kanNonempty_adjunction_iff_nerveAdjunction` / `RightKanRelativeJoinRealization.Strictification.isRightKanExtension_iff_local_limits`
- `LeftKanRelativeJoinRealization.Strictification.isLeftKanExtension_iff_local_colimits` / `F1B.exists_kanLeftExtension_iff_local_colimits` / `F1B.exists_kanRightExtension_iff_local_limits`
- `F1B.kanRelativeLeftMappingPullbackComparison_equivalence` / `F1B.kanRelativeRightMappingPullbackComparison_equivalence` / `F1B.kanNerve_leftKanHomUniversal_iff` / `F1B.kanNerve_rightKanHomUniversal_iff`
- `F1B.kanNerve_isLeftKanExtensionHom_iff_pointwise` / `F1B.kanNerve_isRightKanExtensionHom_iff_pointwise` / `F1B.kanNerveLeftCoconeTransport_cocone` / `F1B.kanNerveRightConeTransport_cone`
- `F2.catInfinityMappingEquivalence` / `F2.catInfinityEdge_isInvertible_iff` / `F2.catPullbackObject` / `F2.catPullbackFunctorIso` / `F2.catPullbackFunctorCoreIso`
- `F2.catPullbackReplacementDiagramIso` / `F2.catPullbackCone_isLimit` / `F2.catPullbackCone_vertex` / `F2.catPullbackConeHomotopy_apex` / `F2.catPullbackConeHomotopy_diagram`
- `F2.catPullbackConeLegSectionIso` / `F2.catPullbackConeFstIso` / `F2.catPullbackConeSndIso`
- `F2.laxPullback` / `F2.laxPullbackCone_isLimit` / `F2.laxPullbackCone_arrow` / `F2.laxPullbackCone_inputs`
- `F2.laxPullbackVertexEquiv` / `F2.laxPullbackMappingProduct_isPullback` / `F2.laxPullbackMappingEndpointMap_fibration`
- `F2.laxPullbackFst_isExactFunctor` / `F2.laxPullbackSnd_isExactFunctor` / `F2.laxPullback_isStable`

- `F2.fiberwisePullbackNativeCone_isLimit` / `F2.fiberwisePullbackNativeCone_vertex` / `F2.fiberwisePullbackNativeConeHomotopy_apexEdge` / `F2.coherentCospanNativeSectionFiberPathDownIso_eq_native` / `F2.coherentCospanModelFiberPathIso_eq_section_down` / `F2.coherentCospanNativeFiberCospanEndComparison_homotopyEquivalence` / `F2.coherentCospanNativeSectionEndComparison_homotopyEquivalence` / `F2.strictPullback_functorIso_exists` / `F2.kanHomotopyRectificationIso_image` / `F2.coherentCospanNativeLeftLegFinalImage_heq` / `F2.functorIsoDown_injective` / `F2.coherentCospanNormalizedModelPathLiftIso_eq_section` / `F2.coherentCospanCommonLeftIso` / `F2.coherentCospanCommonRightIso` / `F2.intervalReplacementSectionIso_endpoint` / `F2.coherentCospanConeNativePathDownIso_whisker` / `F2.coherentTotalNativeKanIso_postValueImage` / `F2.coherentCospanCommonRightImage` / `F2.cospanRectificationLeftIso_inverse_image` / `F2.coherentCospanNativeFirstPathIso_heq` / `F2.coherentCospanModelFirstPathIso_heq` / `F2.coherentCospanCommonComparisonIso` / `F2.coherentCospanConeNativeComparison_homotopyEquivalence` / `F2.coherentCospanConeNativeComparison_isWeakHomotopyEquivalence` / `F2.coherentCospanNativeLimitCone` / `F2.coherentCospanNativeLimitCone_isLimit` / `F2.coherentCospanNativeLimitCone_vertex` / `F2.coherentCospanNativeLimitConeFstIso` / `F2.coherentCospanNativeLimitConeSndIso` / `F2.coherentCospanNativeLimitCone_projection_commutativity` / `F2.coherentFilteredColimitVertex_isTerminal` / `F2.coneMappingShapePushoutIso` / `F2.coneMappingShapePushout_right_fibration` / `F2.coneMappingShapePushoutNativeCone_isLimit` / `F2.finiteShape_cell_induction` / `F2.CoherentFilteredLimitExchangeShape` / `F2.coherentColimitFunctor` / `F2.coherentCompletedLimit_iff_colimitFunctor` / `F2.coherentCospanOfFunctorTriangles` / `F2.functorCospanNativeLimitCone_isLimit` / `F2.exists_limitFamilyRestrictionTriangle` / `F2.coneFamilyReindex_apex` / `F2.exists_limitConeFamilyReplacement` / `F2.HasSpaceLimitsOfShape` / `F2.coherentFilteredLimitExchangeShape_simplex` / `F2.coherentFilteredLimitExchangeShape_of_empty`

- `F2.coherentColimitUnitValueAction_coherence` / `F2.coherentColimitUnitValueAction_total_heq_native` / `F2.coherentColimitUnitValueAction_precomp_firstEdge`
- `F2.coherentColimitApexRawTriangleBoundaryAt` / `F2.coherentColimitApexRawTriangleBoundaryAt_precomp` / `F2.coherentColimitApexRawTriangleCandidate_eq_universal_iff` / `F2.spaceSimplexPointedLift` / `F2.spaceSimplexPointedLift_projection` / `F2.spaceSimplexPointedFamily` / `F2.coherentColimitApexCoefficientMap` / `F2.coherentColimitApexPointedFamilyComparisonIso` / `F2.coherentColimitApexPointedFamilyRestrictionIso` / `F2.coherentColimitApexPointedFirstIso` / `F2.coherentColimitApexPointedLastIso` / `F2.coherentColimitApexPointedLongIso` / `F2.pointedCoherentSourcePrecomposition_fixed` / `F2.spaceTrianglePointedFamily_middle_action` / `F2.spaceTrianglePointedFamily_target_action` / `F2.coherentColimitApexMiddleCoefficientMap` / `F2.coherentColimitApexTargetCoefficientMap` / `F2.coherentColimitApexPointedMiddleEndpointIso` / `F2.coherentColimitApexPointedTargetEndpointIso`

### 依存と提供

- Core/・F1/・Stable/・HomotopyLimits/ の必要な閉包を読み取り専用で使用。F1B は推移的にも straightening に依存しない。
- 提供：F1B 集約、随伴・反射的局所化・Quillen A、左右 Kan の局所判定・相対制限・組み立て・一意性・古典比較。
- F2N-1・3・5 を担当。F1 の F2/Ind/・Ind.lean と N の F2/Idempotent/・Idempotent.lean は読み取り専用。

### 未コミット

- 今回の所有変更は保存済み。F1 の Ind と N の Idempotent の集約・サブディレクトリは所有・保存対象外。

### 既知の問題

- 保存 `43c25ad6` は D レーンの 9 ファイルも同梱。履歴は変更せず、以後 `git commit --only` で所有パスを限定。
- F1/F1B の同名宣言衝突は `efdd0fb3` で修正済み。F1B の intervalMinimum 複製は straightening 非依存の F1.IntervalMinimum import に置換。衝突ゼロ。所有ソースの名前衝突なし。
- 新規・再構成は F1B 名前空間。F1B のソースに `ModelCategory` 仮定なし。前提は Lean が正本。
- B1 の空間値二変数 Hom 関手との比較は F1h の範囲で未形式化。B2 は一般の局所化の存在を含まない。
- 右円柱の前合成同値は未証明だが B4・B5 の局所判定には不要。必要なら Kerodon Prop 5.2.4.5 の双対で構成する。
- 旧 N の詳細は F2 の archive へ保持。Cat_∞ の strict pullback と ∞ 圏内の引き戻しを区別する。

### 次の一手

- F2N-1 a7：ApexRawTriangleCandidate_eq_universal_iff の右辺（元の普遍比較の値＝同じ四因子境界式）を証明する。
  coherentColimitApexCoefficientMap は全反転 Hom から元の実初点 fiber への同値で包含を保持。
  coherentColimitApexPointedFamilyComparisonIso は元の raw 普遍三角形と spaceSimplexPointedFamily を同じ図式・初点を固定して比較する。
  PointedFirst/Last/LongIso は三面を元の実 prism に同定済み。RestrictionIso_precomp/shared と initial は二段制限・共有制限・初点の整合。
  三頂点の作用は SpaceTrianglePointedVertexActions で計算済み。Middle/TargetCoefficientMap は元の実 fiber 内の同じ全係数作用。
  PointedMiddle/TargetEndpointIso は同じ全比較の終点像。次は δ₁ ▷ A ≫ spaceSimplexPointedFamily s から、始点 q と終点 TargetCoefficientMap を持つ元の長区間の輸送証人を作る。
  同じ長辺延長空間への制限で、TargetEndpointIso ≪≫ 元の RawUniversalTriangleComparison B T q と、この明示した長辺証人の普遍比較の一致を証明する。右 Hom の元の成分との値の照合は未完で、既存の単位と元の係数の値像を使う。
  δ₀ の面の係数の標的は元の s.obj 0 のまま保持し、同じ三面の整合を境界式へ移して係数同値の前合成の忠実性で元の普遍比較へ反映する。
  RawUnitFiberComparison_eq_iff_model は元の最初辺模型比較への同じ射影で raw 比較を反映する。未完：長辺輸送の残りとの合成を同じ全族の三辺・指定三角形へ戻す。
  同じ余錐 fiber 写像の前合成の充満忠実性で整合を反映し、二三角形・指定 path を保つ全錐比較を束ねる。
  その極限性から引き戻し保存へ接続。値の整合式・辺ごとの同型だけでは全錐比較の完了としない。
  続いて部分極限 cospan の極限性、有限和・単射側の接着の存在と交換の同時帰納、finiteShape_cell_induction。
  HTT §5.3.3、a7 残り12〜24時間（暫定。三角形に沿う全指定因子の照合に不確実性）。strict 図式だけでは完了としない。
  a7 後は承認を待たず F2N-3 へ。その後 F1 の Ind・N の冪等完備化を利用して F2N-5。

## 0. 目標と範囲

正本は [infinity-core-F1.md](infinity-core-F1.md) の F1e〜F1g と [foundations.md](foundations.md) §6・§8。
本計画は目標・設計・現在地・主要宣言を管理し、実施記録はコミットメッセージに置く。

quasicategory の随伴、反射的局所化、cofinality、点ごとの左右 Kan 拡張を構成する。
Lean は `SerrePositivity/InfinityCategories/F1B/`、namespace は
新規・再構成は `SerrePositivity.InfinityCategories.F1B`、既存の親名前空間 API は保持。集約は `InfinityCategories/F1B.lean`。
Core/・F1/・Stable/ は読むだけ。straightening に推移的にも依存しない。
sorry・追加公理・文献入力を使わず、監査で許す公理は
`propext`・`Classical.choice`・`Quot.sound` のみ。

## 1. 原典と工程

| 工程 | 成果 | 原典 | 状態 |
| --- | --- | --- | --- |
| B1 / F1e | 単位・余単位と h Fun の三角恒等式、自然な写像空間対応との特徴づけ、合成、随伴関手の一意性 | Kerodon [Def 6.1.1.1](https://kerodon.net/tag/02CG)、[§6.1.3](https://kerodon.net/tag/02D5)、[§6.1.5](https://kerodon.net/tag/02DM)、[Def 6.2.1.1・Prop 6.2.1.17](https://kerodon.net/tag/02EJ)、[Prop 6.2.6.1](https://kerodon.net/tag/02FV)・[Cor 6.2.6.5](https://kerodon.net/tag/02FX) / HTT §5.2 | 完了（全パラメータの族の前層による自然性の模型） |
| B2 / F1f | 充満部分 ∞ 圏への反射、局所対象、冪等性、局所化の普遍性の型と反射的な場合の構成 | Kerodon [§6.2.2](https://kerodon.net/tag/02F5)、[Cor 6.2.2.26](https://kerodon.net/tag/02FF)、[Def 6.3.1.9・Prop 6.3.1.13](https://kerodon.net/tag/01ME)、[Prop 6.3.3.7](https://kerodon.net/tag/02FY) / HTT §5.2.7 | 完了（同じ宇宙の標的に対する普遍性） |
| B3 / F1g 前半 | right cofinal、Quillen A、A2h の始対象による limit 計算の双対的回収 | Kerodon [Def 7.2.1.1](https://kerodon.net/tag/02N1)、[Thm 7.2.3.1](https://kerodon.net/tag/02NX) / HTT Thm 4.1.3.1 | 完了（左右の Quillen A と二宇宙版 A2h の同じ制限写像の回収） |
| B4 / F1g 後半 | slice の極限による左右 Kan 拡張、h での一意性、各点の存在、関手全体への組み立て | Kerodon [Notation 7.3.1.1・Def 7.3.1.2](https://kerodon.net/tag/02Y7)、Variant 7.3.1.5、§7.3.5 / HTT §4.3 | 完了（同じ宇宙の quasicategory に対する局所判定・存在・Hom 普遍性と一意性。充満忠実 inner 単射に沿う相対厳密存在・制限定理、任意 U の写像空間の homotopy pullback を右 Kan fibration 上の厳密な引き戻しへの実際の比較同値で実現） |
| B5 | nerve による古典随伴・Kan 拡張の回収と監査 | 上記と通常の圏の随伴・Kan 拡張 | 完了（同じ宇宙の小さい圏。指定単位・余単位を保つ随伴、通常の Kan の大域的普遍性、pointwise な左右 Kan 条件を区別して双方向に比較。集約・公理・import・名前衝突を監査） |

## 2. 設計上の決定

- 随伴は `SSet.QCat.strictBicategory` 上の双圏随伴。二胞体は
  h((ihom X).obj Y) の射であり、hX と hY の間の随伴で代用しない。
  A1c の `homotopyNatTrans` と A3a の `FunctorIso` に接続する。
- 写像空間は右 `pinchedHom` を使い、中間模型に区間写像空間を使う。
  各点で独立に選んだ同値だけや π₀ の全単射だけを自然な対応と扱わない。
  同値条件は各点の実際のホモトピー逆の存在で述べる。
- 自然性の入力は、全ての単体集合パラメータ A と非定値端点図式 a,b の
  ホモトピー族の集合値前層の、端点を保つ通常の自然変換とする。
  その型と coherent 矢印空間の比較との厳密な全単射を証明した。
  各点の比較はこの同じ自然変換の作用から回収する。
  全パラメータの Hom 全単射は追加仮定ではなく、各点の同値性からの帰結である。
- 空間値 Hom 関手自体は正本の別レーン F1h に属し、left fibration の
  straightening で構成する工程である。その空間値二変数 ∞ 関手の自然変換と
  今回の模型との比較定理は未形式化で、証明済みとは主張しない。
  B1 は上の明示した族の前層の模型で構成・判定・自然性を完結している。
- 反射は頂点条件 P の張る全部分複体への包含の左随伴として指定する。
  余単位の可逆性・冪等性・局所化の普遍性をフィールドに加えない。
  P の同型不変性は不要。局所対象は単位成分の可逆性で定義し、包含の本質的な像と同定する。
- 局所化は W を反転する関手の全部分 ∞ 圏への前合成の同値で述べる。
  標的は元の単体集合と同じ宇宙 u の quasicategory。
  一般の C[W⁻¹] の存在は F2 に委ね、ここでは反射の場合だけを構成する。
- right cofinal は colimit を計算する向き。始対象による limit 計算は双対の
  left cofinal と対応する。Quillen A の fiber 条件は弱可縮性であり、
  Kan 性や ∞ 圏としての可縮性へ強めない。
- Kan 拡張では点ごとの slice 極限と関手全体への組み立てを区別する。
  後者は A6 の関手 ∞ 圏の極限 API を確認してから接続する。
- F1 からの再構成は `SerrePositivity.InfinityCategories.F1B` 名前空間に置く。
  保存前に `lake build SerrePositivity.InfinityCategories.F1 SerrePositivity.InfinityCategories.F1B` と
  `lake env lean scripts/audit_infinity_f1_f1b.lean` で同名宣言の衝突がないことを確認する。
- 各保存単位で集約ビルド、公理監査、推移的 import の検査を行う。
  監査は生成宣言を含む F1B の全宣言を宣言元モジュールで抽出し、
  読み込んだリポジトリ内の straightening 系モジュールを拒否する。

## 第 1 部の完了監査（2026-10-20）

| 受入条件 | 現在の証拠（F2 名前空間、B4・B5 は F1B 集約） |
| --- | --- |
| B4・B5 | 左右 Strictification の局所判定、元の変換を保つ存在・Hom 普遍性、nerve の指定随伴・Kan 比較を監査で再読込 |
| F2L-1 | catInfinityMappingEquivalence、catInfinityEdgeEquiv、catInfinityEdge_isInvertible_iff。F1 の coherent nerve を再利用 |
| F2L-2 | catPullbackCone_isLimit・vertex、全 K の catPullbackFunctorCoreIso、catPullbackCone_projection_commutativity |
| F2L-3 | laxPullbackCone_isLimit・arrow・inputs、laxPullbackVertexEquiv、laxPullbackMappingSpaceCone_isLimit と両脚の式 |
| F2L-4 | 同値矢印の全部分複体との射影・path を保つ同型、任意形状の極限・余極限の存在と成分判定、有限版、laxPullback_isStable、完全な両射影 |
| 保存条件 | F1・F1B・F2 同時ビルド、公理・import 監査、同名ソース宣言 0、新規 4 モジュールは各 100 行・100 桁以内。sorry・追加公理・ModelCategory 仮定なし |

N の第 2 部と I-b の presentable 以降は本監査の完了対象外。証明の仮定と宇宙は Lean の型が正本。

## 記録の所在

実施記録・現在地の詳細・型一覧は [archive/infinity-core-F1b-log.md](archive/infinity-core-F1b-log.md) に移した（2026-10-19）。現在地は冒頭の引き継ぎ節が正本で、工程ごとの記録はコミットメッセージに置く。
