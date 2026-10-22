# F1：straightening・Yoneda・Indκ（旧 α2）

> **v2 の位置づけ（2026-10-22 移管）**：F1-4 → F1-5 → F1-3b は完了。F2N-2（Indκ）の (a) 密度と (b) 最小閉包の構成を完了し、(c) を進める。Cat∞ 値の一般底分類は第 II 段。

## 引き継ぎ：F2N-2（2026-10-22）

### 現在地

- F1-4・F1-5・F1-3b は `6f10976ea` まで完了。F1 集約 7661 jobs、公理監査 16236 宣言、標準三公理のみ。
- **F2N-2(a) 完了**：元の前層 F 自体を頂点とする、元の小さい right unstraightening の元の圏上の
  表現可能図式の同じ native 密度余錐の余極限性と小さい表示。HTT 5.1.5.3。
  元の twisted-arrow 評価を一つの全変換に実現し、同じ値写像の全体比較・因子分解・余錐との一致も証明済み。
- **(b) 完了**：Yoneda 像の同型と小さい κ-filtered 余極限による最小閉包を全部分 ∞ 圏にした。
  前層への包含と Yoneda の厳密な因子化の充満忠実性、内在する κ-filtered 余極限と包含の保存・検出まで。
- **(c) 進行中**：元の right unstraightening の元の圏が κ-filtered なら、同じ密度余錐で最小閉包に属する。
  `HasKappaFilteredElements` は同じ頂点条件。同型閉性と元の Yoneda 像も証明済み（任意の κ）。
  κ-small な形状の通常の κ-presentability と境界・ホモトピーの相対因子分解も証明済み。
  元の脚と底射影を持つ `strictRightFibrationColimit`、全空間の κ-filtered 性の保存、同じ fiber 比較を構成。
  `strictRightStraighteningCocone_isColimit` は同じ strict 余極限の分類余錐の native な余極限性。
  元の全空間の脚・全評価 join 射・全高次を保持し、別の余錐の存在で代用しない。
  `rightStraighteningSmallRecovery` は元の全空間から同じ分類値の元の right 復元への底上の同値。
  分類値の条件と全空間の条件の一致、および正則 κ で同じ strict 分類図式の任意の native 余極限への保存まで。
  `exists_cofinal_kappaFiltered_poset` は任意の小さい κ-filtered ∞ 圏への小さい poset の cofinal map。
  通常の κ-filtered 性と nerve の全 κ-small 図式の κ-filtered 性を両方証明。HTT 5.3.1.18。
- **strict 化の現在地**：任意の coherent 前層図式の共同 unstraightening を、底を保つ under 切断図式へ写した。
  `presheafDiagramRightStrict` と、元の指定値の小さい right 復元への同じ底上の評価同値を構成済み。
  `underSectionScaffold` は全添字を同時に評価する大域射で、元の積の両射影を厳密に保つ。
  同じ大域射の各値の制限は、既存の trivial Kan 評価に厳密に一致する。
  `underSectionWeightedProjection` は同じ切断図式の weighted nerve の、元の積上の left fibration。
  元の大域評価と taut scaffold は同じ積上の射で、両方とも前合成同値まで証明済み。
  `underSectionReconstruction` は同じ inner anodyne 置換からの底上の同値 span。元の両 scaffold への制限も保持。
  `underSectionClassificationIso` はこの span を積上の一つの大域分類同型に移す。
  `presheafDiagramWeightedClassificationIso` は weighted nerve の共同分類を curry した図式と元の F の FunctorIso。
  `strictLeftClassificationSectionIso` は strict left 分類像を底の全単体の同じ相対切断の系へ戻す大域同型。
  `weightedLeftSectionEvaluation` は全切断の同じ共同 weighted nerve への評価で、底の任意の制限とも厳密に可換。
  `strictLeftTransportSectionDiagram` は全単体と元の添字を同時に動かす Kan 値図式 H。
  `sectionProductScaffold` は H の replacement から共同 weighted 射影の初頂点引き戻しへの大域射で、両射影を保持。
  同じ射の fiber 作用を元の初頂点評価と係数 fiber 同型へ同定し、前合成同値性まで証明済み。
  `sectionProductClassificationIso` は元の共同分類の初頂点制限と H の weighted 分類の一つの大域同型。
  Kan 図式値の実現との比較、right 反転との整合性、逆方向と単一 κ-filtered 表示は未証明。
- 独立集約 6720 jobs、公理監査 1396 宣言、標準三公理のみ。
- `IsKappaFiltered` は F2N-1 の `F2/FilteredInfinity.lean` を使用。再実装しない。

### 残り（依存順）

1. **(a)** 完了。元の F 自体の小さい表現可能図式による密度。HTT 5.1.5.3。
2. **(b)** 完了。最小閉包・Yoneda の因子化・小さい κ-filtered 余極限の保存と検出。
3. **(c)** 単一 κ-filtered 表示と右 fibration 定義との一致。逆方向が残る。HTT 5.3.5.4。16〜40時間（暫定）。
4. **(d)** κ-filtered 余極限を保つ延長の実際の制限関手の同値。HTT 5.3.5.10、Kerodon 9。32〜80時間（暫定）。

### 主要宣言（名前のみ）

- `presheafDensityCocone_isColimit`、`presheafDensityPresentation`、`presheafElementsYonedaSliceComparison`
- `presheafDensityEvaluationValueComparisonIso`、`presheafDensityRestrictedGlobalValueMap_factorization`
- `IsIndVertex`、`isIndVertex_minimal`、`isIndVertex_of_kappaFiltered_elements`、`HasKappaFilteredElements`
- `hasKappaFilteredElements_isoClosed`、`hasKappaFilteredElements_yoneda`、`rightStraighteningSmallRecovery`
- `strictRightFibrationColimit`、`strictRightFibrationColimit_isKappaFiltered`、`strictRightFibrationColimitFiberIso`
- `strictRightStraighteningCocone_isColimit`、`hasKappaFilteredElements_of_strictClassified_colimit`
- `terminalSubcomplexBaseMap_isRightCofinal`、`exists_cofinal_kappaFiltered_poset`
- `presheafDiagramRightStrict`、`presheafDiagramRightValueRecovery_isQCatEquivalence`
- `underSectionScaffold_over_product`、`underSectionScaffoldValueMap_eq`、`underSectionWeightedProjection`
- `underSectionScaffold_isPrecompositionEquivalence`、`underSectionReconstruction`
- `presheafDiagramWeightedClassificationIso`、`underSectionClassificationIso`
- `strictLeftClassificationSectionIso`、`weightedLeftSectionEvaluation_restriction`、`sectionProductScaffold`
- `IndInfinity`、`indInclusionPresheaf_isFullyFaithful`、`indYoneda_isFullyFaithful`、`ind_isColimit_iff_inclusion`

### 依存と提供

- 所有は `InfinityCategories/F2/Ind/`、独立集約 `F2/Ind.lean`、`scripts/audit_f2_ind.lean`、本計画。
- F2 の既存ファイル・集約 F2.lean（F1b）と F2/Idempotent/（N）は読み取り専用。ルート集約を変更しない。
- F1 の前層・Yoneda・right unstraightening、F1b の filtered・κ-filtered・cofinality を再利用。
- κ・C・小さい添字は宇宙 u、前層と Indκ は宇宙 u+1。(d) の D と関手空間も対応する宇宙で明示。
- 新規 sorry・公理・引用なし。主経路に同値性や ModelCategory の追加 instance 仮定なし。
- 新規モジュールは 100 行以内、計画は 300 行・引き継ぎは 100 行以内。自分のファイルのみ `git commit --only`。

### 未コミット

- なし。対象ビルドと独立公理監査の通る区切りを、独立集約とともに早めに保存する。

### 既知の問題

- 最小閉包だけでは (c) の単一表示も右 fibration 定義との一致も結論しない。
- (d) は対象の延長の存在だけでなく、元の制限写像 Fun^κ(Indκ(C),D) → Fun(C,D) 自体の同値を要する。
- 任意の大きい Kan 標的への弱同値の持ち上げは使わず、小さい標的の持ち上げへの前合成同値を使う。

### 次の一手

(c)：小さい通常の κ-filtered poset の nerve 上の一般 coherent 前層図式を strict 化する。
元の共同 left fibration と、元の under 切断の weighted nerve の間の底上の前合成同値 span まで証明済み。
この span の積上の分類同型と、共同分類を curry した図式と元の F の一つの FunctorIso まで証明済み。
次は `presheafDiagramWeightedClassification F` と、`strictCoherentDiagram (presheafDiagramRightStrict F)` を
`rightStraighteningInfinityMap C` で分類した実際の図式との大域比較を構成する。
strict left 分類像を底の全単体上の相対切断へ戻す大域同型と、共同 weighted 評価の全制限との可換性まで証明済み。
添字 (i,s) ∈ I × TransportSimplexCategory B の Kan 図式 H と、初頂点座標で評価する大域射まで構成済み。
`sectionProductScaffold` は H の replacement から元の共同 weighted fibration の同じ初頂点引き戻しへの射。
同じ射の係数作用を初頂点の相対切断評価と元の fiber 同型へ同定し、前合成同値性まで証明済み。
同じ scaffold と taut scaffold の共通置換により、元の共同分類の初頂点制限と H の weighted 分類は大域同型。
次は weighted の coherent 単位で H 自体の実現へ移し、`strictLeftClassificationSectionIso` の実現と照合して局所化で戻す。
left/right 二重反転の自然な底上の比較も保持して、元の F との既存の同型に接続する。
span の元の両 scaffold への制限を保持し、各値の同値だけで大域比較や元の余錐の比較を代用しない。
同じ余錐を cofinal 性・点ごとの検出で既存の strict 分類余極限へ移す。HTT 5.3.5.3、5.3.1.18。
`isIndVertex_minimal` で逆方向を得て、同じ密度表示により単一 κ-filtered 表示と右 fibration 定義との一致を結論する。
その後は (d) の実際の制限関手を構成し、対象・全写像空間の同値を証明する。

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
