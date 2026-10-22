# F1：straightening・Yoneda・Indκ（旧 α2）

> **v2 の位置づけ（2026-10-22 移管）**：F1-4 → F1-5 → F1-3b は完了。F2N-2（Indκ）の (a) 密度と (b) 最小閉包の構成を完了し、(c) を進める。Cat∞ 値の一般底分類は第 II 段。

## 引き継ぎ：F2N-2（2026-10-22）

### 現在地

- F1-4・F1-5・F1-3b は `6f10976ea` まで完了。F1 集約 7661 jobs、公理監査 16236 宣言、標準三公理のみ。
- **F2N-2(a) 完了**：`presheafDensityCocone_isColimit` は元の前層 F を指定頂点とする、
  元の小さい right unstraightening の元の圏上の表現可能図式の同じ native 密度余錐の余極限性。指定頂点と各項も照合済み。
  `presheafDensityPresentation` は元の F 自体の同じ小さい余極限表示。HTT 5.1.5.3。
- **(a) の比較の整合性**：元の大域 twisted-arrow 切断の評価を c1 で一つの全変換に実現。
  `presheafDensityEvaluationValueComparisonIso` は実際の評価 fiber 値写像の同じ復元射上での関手同型。
  `presheafDensityRestrictedGlobalValueMap_factorization` はその同じ値写像を、証明済みの始点固定評価と
  元の fiber 値比較の合成へ厳密に同定する。小さい弱同値を必要な持ち上げた Kan 標的への前合成同値へ移し、
  元の評価余錐の余極限性を検出。別の余錐の存在や頂点だけの同値で代用しない。
- `presheafElementsYonedaSliceComparison` は同じ小さい元の圏から元の Yoneda slice への底上の比較。
  その標準余錐を戻すと同じ `presheafDensityCocone` に厳密に一致する。
- **(b) 完了**：Yoneda 像の同型と小さい κ-filtered 余極限による最小閉包を全部分 ∞ 圏にした。
  `IndInfinity`、前層への包含の充満忠実性、元の全 Yoneda の厳密な因子化と充満忠実性まで。
  `ind_exists_colimitCone` と `ind_isColimit_iff_inclusion` は内在する小さい κ-filtered 余極限と包含の保存・検出。
  閉包の最小性は頂点条件の包含の主張であり、(d) の関手の延長の普遍性ではない。
- **(c) 進行中**：元の right unstraightening の元の圏が κ-filtered なら、同じ密度余錐で最小閉包に属する（任意の κ）。
  `HasKappaFilteredElements` は同じ頂点条件。その同型閉性と元の Yoneda 像についても証明済み。
  κ-small な形状の通常の κ-presentability、境界・ホモトピーの相対因子分解、直積の小ささを証明。
  `strictRightFibrationColimit` は元の脚と射影を持つ同じ固定底上の対象で、κ-filtered 性の保存も証明済み。
  `strictRightFibrationColimitFiberIso` は同じ fiber 余極限の比較。元の全空間の脚が誘導する写像に一致する。
  `strictRightStraighteningColimitFiberCoconeIso` は同じ前層余錐の全評価 join 射と実際の反転 fiber 余錐の関手同型。
  `strictRightStraighteningCocone_isColimit` は同じ strict filtered 余極限の分類余錐の native な余極限性。
  元の全空間の余極限の脚と全高次の整合性を保持し、別の余錐の存在で代用しない。
  `rightStraighteningSmallRecovery` は元の全空間から同じ分類値の元の right unstraightening への底上の同値。
  `hasKappaFilteredElements_rightStraightening_iff` は同じ分類値の条件と元の全空間の条件の一致。任意の κ。
  `hasKappaFilteredElements_of_strictClassified_colimit` は正則 κ で同じ strict 分類図式の任意の native 余極限への保存。
  `terminalSubcomplexBaseMap_isRightCofinal` は保存済みの同じ包含順の nerve から元の底への写像の cofinal 性。
  元の coslice 引き戻しの有限余錐を構成し、同じ実現空間の値写像と同じ射影の切断に Quillen A を適用。
  `exists_cofinal_kappaFiltered_poset` は任意の小さい κ-filtered ∞ 圏への小さい poset の cofinal map。
  添字の通常の κ-filtered 性と、その nerve の全 κ-small 図式に対する κ-filtered 性を両方証明。HTT 5.3.1.18。
  `underSectionStrictDiagram` は積 B × nerve I 上の left fibration を、B を保つ under 切断の strict 図式へ束ねる。
  `underSectionEvaluate` は同じ添字での元の引き戻しへの底上の評価で、trivial Kan fibration と同値性を証明。
  `presheafDiagramRightStrict` は任意の coherent 前層図式の共同 unstraightening から作る strict right fibration 図式。
  `presheafDiagramJointEvaluation_value` は共同評価の添字での制限と元の前層値そのものの等式。
  `presheafDiagramRightValueRecovery` は strict 値から元の値の小さい right 復元への底上の射で、同値性も証明。
  `underSectionScaffold` は under 切断の replacement から元の共同全空間への一つの大域射。
  `underSectionScaffold_over_product` は元の積の両射影を保つ底上の等式。
  `underSectionScaffoldValueMap_eq` はその同じ大域射の各値の制限と既存評価の厳密な一致。制限射は trivial Kan。
  この replacement と strict 分類図式との大域比較、逆方向と単一 κ-filtered 表示、右 fibration 定義との一致は未証明。
- 独立集約 6652 jobs、公理監査 1199 宣言、標準三公理のみ。
- `IsKappaFiltered` は F2N-1 の `F2/FilteredInfinity.lean` をそのまま使用。再実装しない。

### 残り（依存順）

1. **(a)** 完了。元の F 自体の小さい表現可能図式による密度。HTT 5.1.5.3。
2. **(b)** 完了。最小閉包としての構成・Yoneda の因子化・小さい κ-filtered 余極限の保存と検出。
3. **(c)** Indκ 対象の単一 κ-filtered 表示と右 fibration 定義との一致。逆方向が残る。HTT 5.3.5.4。16〜40時間（暫定）。
4. **(d)** κ-filtered 余極限を保つ延長の実際の制限関手の同値。HTT 5.3.5.10、Kerodon 9。32〜80時間（暫定）。

### 主要宣言（名前のみ）

- `presheafElementsYonedaDiagram`、`presheafElementsYonedaDiagram_vertex`
- `presheafDensityCocone`、`presheafDensityCocone_vertex`、`presheafDensityCocone_isColimit`
- `presheafDensityPresentation`、`presheafDensityEvaluationCocone_isColimit`
- `presheafDensityEvaluationValueComparisonIso`、`presheafDensityRestrictedGlobalValueMap_factorization`
- `presheafDensityEvaluationReconstruction_isPrecompositionEquivalence`、`presheafElementsYonedaSliceComparison`
- `isIndVertex_of_kappaFiltered_elements`、`IsIndVertex`、`isIndVertex_kappaColimitClosed`、`isIndVertex_minimal`
- `HasKappaFilteredElements`、`hasKappaFilteredElements_isoClosed`、`hasKappaFilteredElements_yoneda`
- `isCardinalPresentable_of_isKappaSmall`、`kappaSmall_relative_factorization_of_isColimit`
- `isKappaFiltered_of_strict_isColimit`、`rightFibration_of_filtered_isColimit`
- `strictRightFibrationColimit`、`strictRightFibrationColimitProjection_ι`
- `strictRightFibrationColimit_isKappaFiltered`
- `strictRightFibrationColimitFiberIso`、`strictRightFibrationFiberNativeCocone_isColimit`
- `strictRightStraighteningColimitFiberCoconeIso`、`strictRightStraighteningCocone_isColimit`
- `rightStraighteningSmallRecovery`、`hasKappaFilteredElements_rightStraightening_iff`
- `hasKappaFilteredElements_of_strictClassified_colimit`
- `smallSubcomplexFamilyCocone_isColimit`、`exists_fresh_vertex_label`、`exists_small_codiscreteConeRange`
- `terminalSubcomplexBaseMap_isRightCofinal`、`exists_cofinal_kappaFiltered_poset`
- `underSectionStrictDiagram`、`underSectionEvaluate`、`underSectionEvaluate_isQCatEquivalence`
- `presheafDiagramRightStrict`、`presheafDiagramRightValueRecovery_isQCatEquivalence`
- `underSectionScaffold_over_product`、`underSectionScaffoldValueMap_eq`
- `IndInfinity`、`indInclusionPresheaf`、`indInclusionPresheaf_isFullyFaithful`
- `indYoneda`、`indYoneda_inclusion`、`indYoneda_isFullyFaithful`
- `ind_exists_colimitCone`、`ind_hasColimit`、`ind_isColimit_iff_inclusion`

### 依存と提供

- 配置・所有は `InfinityCategories/F2/Ind/`、独立集約 `F2/Ind.lean`、`scripts/audit_f2_ind.lean`、本計画。
- F2 の既存ファイル・集約 F2.lean（F1b）と F2/Idempotent/（N）は読み取り専用。ルート集約を変更しない。
- F1 の前層・Yoneda・right unstraightening、F1b の filtered・κ-filtered・cofinality を再利用。
- κ・C・小さい添字は宇宙 u、前層と Indκ は宇宙 u+1。(d) の D と関手空間も対応する宇宙で明示する。
- 新規 sorry・公理・引用なし。主経路に同値性や ModelCategory の追加 instance 仮定なし。
- 新規モジュールは 100 行以内、計画は 300 行以内。自分のファイルのみ `git commit --only`。

### 未コミット

- なし。対象ビルドと独立公理監査の通る区切りを、独立集約とともに早めに保存する。

### 既知の問題

- 最小閉包の定義だけでは (c) の単一 κ-filtered 表示も、HTT の右 fibration 定義との一致も結論しない。
- (d) は対象の延長の存在だけでなく、元の制限写像 Fun^κ(Indκ(C),D) → Fun(C,D) 自体の同値を要する。
- 任意の大きい Kan 標的への弱同値の持ち上げは使わず、小さい標的の持ち上げへの前合成同値を使った。

### 次の一手

(c)：任意の小さい κ-filtered ∞ 圏への、小さい通常の κ-filtered poset からの cofinal map まで証明済み。
次はその nerve 上の一般 coherent 前層図式を strict right fibration 図式へ移す、同じ大域分類値の比較を構成する。
通常の under 圏上のパラメータ付き相対切断の strict 図式と、同じ各値への底上の評価の同値性まで証明済み。
反対化した strict right fibration 図式と、元の共同 unstraightening から各指定値への底上の比較同値まで証明済み。
パラメータ付き切断の全空間の図式を元の添字上の strict transport へ自然に写し、scaffold により元の共同全空間への
大域射を構成済み。元の積の両射影を保ち、各値の制限は元の同じ trivial Kan 評価に厳密に一致する。
次はこの replacement と weighted nerve 側の strict 分類図式を、元の前層変数の底を保つ大域比較で結ぶ。
底上の scaffold 比較の同値性と分類への移送を示し、元の coherent 前層図式との一つの FunctorIso を実現する。
replacement の全空間が left fibration であるとは仮定しない。既存の scaffold span と相対比較を再利用する。
各値の同値だけで大域の比較や元の余錐の比較を代用しない。
元の図式との全変換を実現し、同じ余錐を cofinal 性・点ごとの検出で既存の strict 分類余極限へ移す。
原典は HTT 5.3.5.3 と添字の比較 5.3.1.18。モデル圏の仮定を追加せず、元の余錐の余極限性を比較する。
`isIndVertex_minimal` に入れて Indκ 所属から元の圏の κ-filtered 性を得て、同じ密度表示を使う。
κ-filtered な表示と右 fibration 定義の一致を結論する。既存の filtered・cofinality を再実装しない。
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
