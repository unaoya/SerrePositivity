# F1：straightening・Yoneda・Indκ（旧 α2）

> **v2 の位置づけ（2026-10-22 移管）**：F1-4 → F1-5 → F1-3b は完了。F2N-2（Indκ）の (a) 密度・(b) 最小閉包・(c) 単一 κ-filtered 表示・(d) 保存関手の延長普遍性まで完了。Cat∞ 値の一般底分類は第 II 段。

## 引き継ぎ：F2N-2（2026-10-23 完了）

### 現在地

- F1-4・F1-5・F1-3b は `6f10976ea` まで完了。F1 集約 7661 jobs、公理監査 16236 宣言、標準三公理のみ。
- **F2N-2(a) 完了**：元の前層 F 自体を頂点とする、元の小さい right unstraightening の元の圏上の
  表現可能図式の同じ native 密度余錐の余極限性と小さい表示。HTT 5.1.5.3。
  元の twisted-arrow 評価を一つの全変換に実現し、同じ値写像の全体比較・因子分解・余錐との一致も証明済み。
- **(b) 完了**：Yoneda 像の同型と小さい κ-filtered 余極限による最小閉包を全部分 ∞ 圏にした。
  前層への包含と Yoneda の厳密な因子化の充満忠実性、内在する κ-filtered 余極限と包含の保存・検出まで。
- **(c) 完了（正則 κ）**：最小閉包への所属は、元の right unstraightening の元の圏の κ-filtered 性と同値。
  `isIndVertex_iff_hasKappaFilteredElements` と、元の関手による `isIndVertex_functorVertex_iff`。
  `isIndVertex_iff_singleFilteredPresentation` は単一の小さい κ-filtered 表現可能図式による生成表示との同値。
  順方向は元の right unstraightening 上の同じ密度余錐を使い、元の前層頂点を厳密に保つ。HTT 5.3.5.4。
  逆方向の閉性は任意の小さい κ-filtered 添字・任意の coherent 前層図式・指定 native 余錐について証明した。
  小さい cofinal poset と、同じ写像の宇宙移送による同じ制限余錐の余極限性を使う。
  `presheafDiagramRightStrictClassificationIso` は元の F と実際の strict right 分類像の一つの大域同型。
  元の積上の scaffold・全単体切断の同じ実現・初頂点局所化・自然な底上の二重反転を保持している。
  同じ strict 分類余極限の元の全空間と脚の κ-filtered 性を使い、同じ頂点を保つ native 余錐で保存を結論。
- **(d) 完了（正則 κ）**：`indKappaContinuousRestriction_isQCatEquivalence` は、元の Yoneda による実際の
  制限射 Fun^κ(Indκ(C),D) → Fun(C,D) 自体の同値性。D は同じ小さい κ-filtered 余極限を持つ。HTT 5.3.5.10。
  κ・C・試験添字は宇宙 u、Indκ・D・関手空間は宇宙 u+1。追加の同値性・inner fibration・ModelCategory 仮定なし。
  `indKappaContinuousRestriction_isFullyFaithful` は同じ制限射の全写像空間の同値を証明済み。
  `ind_exists_leftKanExtension` は任意の元の C → D の指定単位付き左 Kan 延長を構成し、
  `indLeftKanExtensionRecoveryIso` は同じ指定単位の逆で元の Yoneda 上の図式を回収する。
  `weightedIndDensityRelativeDiagram` は元の weighted 密度と共同分類を両端に厳密に持つ同じ大域相対 join 族。
  同じ全図式と左 Kan 像の実際の全 fiber 余錐の余極限性から、native 全余錐の左制限同値を証明した。
  `relativeJoinInr_nativeRestriction_isQCatEquivalence` は単射性なしの円柱比較と右端の right anodyne 性から右制限同値を与える。
  `mapJoinCocone_isColimit_of_nativeRestrictions` は全余錐の同型を保持して両端の間で保存性を移す。
  `weightedIndClassification_image_isColimit` と `strictClassifiedIndCocone_image_isColimit` により、同じ全分類同型で指定標準余錐へ帰還。
  `indLeftKanExtension_preservesSmallKappaFilteredColimits` は任意の小さい κ-filtered 図式の指定 native 余錐の保存。
  係数全空間の κ-filtered 性は正則 κ と元の hF から回収。対象ごとの頂点同型で全余錐比較を代用しない。
  これで同じ制限射の本質的全射性を証明し、F0 の FF/ES 判定で閉じた。
  `indKappaContinuousRestrictionEquivalence` は同値データ、`_hom` は順射が元の制限写像である厳密な等式。
- 独立集約 7245 jobs、公理監査 2974 宣言、標準三公理のみ。
- `IsKappaFiltered` は F2N-1 の `F2/FilteredInfinity.lean` を使用。再実装しない。

### 残り（依存順）

1. **(a)** 完了。元の F 自体の小さい表現可能図式による密度。HTT 5.1.5.3。
2. **(b)** 完了。最小閉包・Yoneda の因子化・小さい κ-filtered 余極限の保存と検出。
3. **(c)** 完了（正則 κ）。単一 κ-filtered 表示と元の right fibration 定義との一致。HTT 5.3.5.4。
4. **(d)** 完了（正則 κ）。実際の制限射の同値と、元の制限写像を順射に持つ同値データ。HTT 5.3.5.10、Kerodon 9。残工程なし。

### 主要宣言（名前のみ）

- `presheafDensityCocone_isColimit`、`presheafDensityPresentation`、`presheafElementsYonedaSliceComparison`
- `IndInfinity`、`indYoneda`、`indInclusionPresheaf`、`ind_isColimit_iff_inclusion`
- `presheafDiagramRightStrictClassificationIso`、`hasKappaFilteredElements_of_ordinary_colimit`
- `exists_cofinal_kappaFiltered_poset`、`isRightCofinal_ulift`、`isColimitCone_iff_restrict_rightCofinal`
- `hasKappaFilteredElements_kappaColimitClosed`、`isIndVertex_iff_hasKappaFilteredElements`
- `isIndVertex_functorVertex_iff`、`HasSingleFilteredRepresentablePresentation`
- `isIndVertex_iff_singleFilteredPresentation`、`indKappaContinuousRestriction`
- `indVertexDensityCocone`、`indVertexDensity_image_isColimit`
- `indKappaContinuousRestriction_reflects_isInvertibleEdge`
- `presheafElementsYonedaSliceMapping_uncurry`、`presheafElementsYonedaSliceValue`
- `presheafDensityIdentityValue_isQCatEquivalence`
- `presheafDensityNativeIdentityValueIso`、`presheafDensityFiberIntervalIso`
- `presheafDensityIdentityReconstruction_pointed`、`presheafDensityIdentityLiftPrism_projection`
- `presheafElementsYonedaSliceValue_isQCatEquivalence`、`presheafElementsYonedaSliceComparison_isQCatEquivalence`
- `indElementsLeftKanComparison_isQCatEquivalence`、`indElementsLeftKanComparison_diagram`
- `indLeftKanDiagram_hasColimit`、`ind_exists_leftKanExtension`
- `indLeftKanCanonicalCocone_restrict_val`、`indContinuous_canonicalColimits`、`indKappaContinuousRestriction_isFullyFaithful`
- `indLeftKanExtensionRecoveryIso`、`ind_preservesSmallKappaFilteredColimits_iff_strictClassified`、`kanCanonical_isColimitCone_iff_restrict`、`strictRightFibrationTotalAssembly_isRightCofinal`、`weightedIndDensity_image_isColimit`、`weightedIndDensityCocone_vertex_eq_standard`、`cocartesianFibration_ulift`、`exists_weightedDensity_globalFamily_with_KanImage`、`exists_weightedDensity_globalFamily_with_universal_KanImage`、`weightedIndClassificationIso`、`strictRightTwistedComparison`、`weightedRightTwistedEvaluation_projection`、`weightedMap_trivialKanFibration`、`weightedTwistedSourceLift`、`weightedTwistedPullbackIso`、`weightedIndDensityHomotopy`、`weightedIndDensityCoefficientCocone`、`weightedTwistedCoefficientLift_canonicalIso`、`weightedLeftCoefficientRecovery_isPrecompositionEquivalence`、`weightedCoefficientJointEvaluation_factorization`
- `weightedCoefficientNativeValueComparisonIso`、`weightedIndDensityCoefficientCocone_isColimit`、`weightedIndDensityCoefficientCocone_image_isColimit`、`weightedIndDensityRelativeDiagram`、`weightedIndRelativeCoefficientCocone_isColimit`、`relativeJoinFiberEmbedding_prism`、`weightedIndDensityRelativeDiagram_allFibers_isColimit`、`exists_weightedDensity_classifiedFamily_with_universal_KanImage`
- `sliceUnderRestrict_isQCatEquivalence_of_precompositionEquivalence`、`relativeJoinInr_nativeRestriction_isQCatEquivalence`、`mapJoinCocone_isColimit_of_nativeRestrictions`、`weightedIndClassification_image_isColimit`、`strictClassifiedIndCocone_image_isColimit`、`indLeftKanExtension_preservesSmallKappaFilteredColimits`、`indKappaContinuousRestriction_isEssentiallySurjective`、`indKappaContinuousRestriction_isQCatEquivalence`、`indKappaContinuousRestrictionEquivalence`、`indKappaContinuousRestrictionEquivalence_hom`

### 依存と提供

- 所有は `InfinityCategories/F2/Ind/`、独立集約 `F2/Ind.lean`、`scripts/audit_f2_ind.lean`、本計画。
- F2 の既存ファイル・集約 F2.lean（F1b）と F2/Idempotent/（N）は読み取り専用。ルート集約を変更しない。
- F1 の前層・Yoneda・right unstraightening、F1b の filtered・κ-filtered・cofinality を再利用。
- κ・C・小さい添字は宇宙 u、前層と Indκ は宇宙 u+1。(d) の D と関手空間も対応する宇宙で明示。
- 新規 sorry・公理・引用なし。主経路に同値性や ModelCategory の追加 instance 仮定なし。
- 新規モジュールは 100 行以内、計画は 300 行・引き継ぎは 100 行以内。自分のファイルのみ `git commit --only`。

### 未コミット

- なし。通る区切りを独立集約と公理監査とともに保存する。

### 既知の問題

- F2N-2(a)〜(d) に未証明の主工程なし。(c)・(d) は正則 κ に対する定理。
- `Compact.PreservesKappaFilteredColimits` はさらに持ち上げた始域の関手を扱う。Ind の小さい添字版とは宇宙を照合して使う。
- Cat∞ 値の一般底分類は第 II 段の別工程。下記再開点を維持し、F2N-2 の完了と混同しない。

### 次の一手

F2N-2(a)〜(d) は完了。次の割り当てへ進む。
提供する主界面は `IndInfinity`、`indYoneda`、`isIndVertex_iff_singleFilteredPresentation`、
`indLeftKanExtension_preservesSmallKappaFilteredColimits`、`indKappaContinuousRestrictionEquivalence`。
`indKappaContinuousRestrictionEquivalence_hom` により、同値の順射は元の Yoneda 制限写像そのもの。
F2N-3（compact）は F1b、F2/Idempotent は N の所有。既存 F2.lean とルート集約は変更しない。

## F1 の完了済み範囲と第 II 段の再開点

- 空間値 straightening・right fibration 分類・Yoneda は完了。F1-4・F1-5・F1-3b は `6f10976ea` で完了。
- 前層の小さい極限・余極限、評価による保存・検出、表現可能関手による極限の特徴づけ、二変数 Hom を提供済み。
- Cat∞ 値分類は全有限単体底の `cocartesianStraighteningCoherentMap_finite_isQCatEquivalence` で区切る。

### 再開点（第 II 段、3行）

1. `dc768ab4b`：有限二単体の coherent 境界比較の同値と、元の大域作用への `cocartesianTwoBoundaryCoherentHomComparison_originalIso` まで保存済み。
2. 次は同じ比較を任意の底の二次元セルへ移し、局所比較の自然性と指定境界値の fiber 比較を揃える。
3. その後は高次境界・有限セル・骨格降下で一般充満忠実性を閉じ、本質的全射性・一般底・宇宙へ進む。

## 0. 目標と範囲

Kerodon 第 5・6・7.3・8 章の内容を、quasicategory の組み合わせ論だけで形式化する。
到達点は (i) straightening/unstraightening の同値（Kerodon Theorem 5.6.0.2）、(ii) 随伴と局所化、
(iii) Kan 拡張、(iv) twisted arrow ∞ 圏と Hom 関手、前層 ∞ 圏 Fun(C^op, 𝒮) と Yoneda 埋め込み。
𝒮 := N^hc(Kan)（γ1 により quasicategory。Kan 複体の内部 Hom が Kan であることは Mathlib の
pushout-product から）。𝒮 の極限・余極限は F2（γ3）に委ね、本レーンでは 𝒮 を対象としてだけ使う。

既存（読むだけ）：A2d の left/right fibration（`Core/RightFibration.lean`）、A3b の Joyal の定理、
A3c〜A3e の写像空間・同値、`Coherent/` の coherent nerve。

## 1. 工程

| 工程 | 内容 | 原典 |
| --- | --- | --- |
| F1a | cocartesian/cartesian 辺と fibration の定義、inner fibration との関係、left/right fibration との関係、合成・底変換での閉性、fiber が quasicategory | Kerodon 5.1 / HTT 2.4.1–2.4.2 |
| F1b | covariant transport：cocartesian fibration の辺に沿う fiber 間の関手、その一意性（可縮な選択空間）、ホモトピー圏への降下 | Kerodon 5.2 / HTT 2.4.4 |
| F1c | Cat_∞ := N^hc(QCat)（Kan 複体 core を Hom に取る単体的圏の coherent nerve。core は A3b の可逆辺）と Fun(C, Cat_∞) | Kerodon 5.5 / HTT 3.0 |
| F1d | **straightening**：cocartesian fibration U → N(C)（まず C が通常の圏）と関手 N(C) → Cat_∞ の対応、unstraightening の構成、同値（Theorem 5.6.0.2）。left fibration と 𝒮 値関手の場合を先に | Kerodon 5.6 / HTT 2.2.1.2、3.2 |
| F1e | 随伴（単位・余単位、写像空間での特徴づけ）、随伴関手の合成、Kan 拡張との関係 | Kerodon 6.1–6.2 / HTT 5.2 |
| F1f | 局所化 C → C[W⁻¹] の普遍性（Kerodon 6.3）と反射的部分 ∞ 圏 | Kerodon 6.3 / HTT 5.2.7 |
| F1g | 左右 Kan 拡張（点ごとの公式、存在と一意性）、cofinality の一般形（Quillen A） | Kerodon 7.2–7.3 / HTT 4.1.3、4.3 |
| F1h | twisted arrow ∞ 圏 Tw(C)、Hom 関手 C^op × C → 𝒮（F1d の left fibration 版で straighten）、前層 ∞ 圏 P(C) := Fun(C^op, 𝒮)、Yoneda 埋め込み、充満忠実性、表現可能関手と極限 | Kerodon 8.1–8.3 / HTT 5.1.3 |
| F1i | 検査：通常の圏の nerve で F1d・F1h が古典（Grothendieck 構成、Yoneda）に戻ること | — |

**分割（2026-10-18 15:40）：** F1e・F1f・F1g は straightening に依存しないので、レーン α2b（Π2 チャット、
計画は [infinity-core-F1b.md](infinity-core-F1b.md)、配置 `InfinityCategories/F1B/`）へ切り出した。
α2 の順序は F1a → F1b → F1c → F1d → F1h → F1i。F1h は α2b の Kan 拡張を使ってよい。F1d が最大の山で、
Kerodon 5.6 の証明（5.3 の「fibration の ∞ 圏」、5.4 の （∞,2）的道具を避ける経路）を
着手前に照合し、文言と証明方針を `Core/README.md` ではなく `InfinityCategories/F1/README.md` に記録する。

## 2. 設計上の決定

- 完了済み F1 は `InfinityCategories/F1/` と集約 `F1.lean`。
  F2N-2 は独立した `InfinityCategories/F2/Ind/` と `F2/Ind.lean`。既存の F2 集約と Idempotent は変更しない。
- fibration は `MorphismProperty.rlp` 流儀で定義し、A2d の left/right fibration と整合させる。
- Cat_∞ と 𝒮 は coherent nerve で定義する（γ1）。両者の極限・余極限は F2 まで主張しない。
- straightening は left fibration・𝒮 値の場合を先に完成させ、cocartesian・Cat_∞ 値へ拡張する。
- モデル構造（covariant/contravariant model structure）は使わない。Cisinski 流の代替は採らない。
- sorry・公理・引用は導入しない。実施記録はコミットメッセージ、宣言名と型の一覧は本文書 §3。

## 記録の所在

実施記録・現在地の詳細・型一覧は [archive/infinity-core-F1-log.md](archive/infinity-core-F1-log.md) に移した（2026-10-19）。現在地は冒頭の引き継ぎ節が正本で、工程ごとの記録はコミットメッセージに置く。
