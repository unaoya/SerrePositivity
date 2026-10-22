# F1：straightening・Yoneda・Indκ（旧 α2）

> **v2 の位置づけ（2026-10-22 移管）**：F1-4 → F1-5 → F1-3b は完了。次は F2N-2（Indκ）を F1b から引き取る。Cat∞ 値の一般底分類は第 II 段。

## 引き継ぎ：F2N-2（2026-10-22）

### 現在地

- F1-4・F1-5・F1-3b は `6f10976ea` まで完了。F1 集約 7661 jobs、公理監査 16236 宣言、標準三公理のみ。
- **F2N-2(a) 進行中**：元の小さい right unstraightening を添字とする同じ Yoneda 図式を固定。
  `presheafElementsYonedaDiagram_vertex` で各項が元の表現可能前層であることを照合。
  同じ図式の native な各点余極限候補とは別に、元の F を頂点とする指定密度余錐を構成。余極限性は未証明。
- `presheafYonedaSliceCocone` は元の F 自体を指定頂点とする標準全余錐。
  `presheafYonedaSliceFiberValueEquivalence` は同じ射影の各 fiber を元の F(x) と比較する。
  `presheafElementsYonedaSliceComparison` は、小さい元の圏から同じ slice への一つの底上の比較。
  その比較から余錐を戻すと、構成した同じ `presheafDensityCocone` と厳密に一致する。
- **(a) の大域評価**：right fibration の相対 twisted arrow 右端比較の全境界充填を証明。
  `twistedArrowRightSection` は底の全 twisted arrow と指定終点を厳密に保つ一つの切断。
  `presheafTwistedElementsEvaluation` は同じ小さい元の圏を終点とする全族から元の F への pointed 評価。
  共同 Hom の底変換の復元同値を介して相対射を延長し、c1 で実際の自然変換へ実現。
  `presheafDensityCoconeRealization` を F2 の両端固定 fat join 実現へ精密化。同じ全変換の円柱への往復も照合。
  元の大域評価との相対写像空間内の同型も保存。比較の fiber 同値性と同じ密度余錐の余極限性が残る。
- **(a) の全空間側の弱同値**：`twistedIdentityFiberEvaluation_isQCatEquivalence` は同じ大域切断の恒等点上の作用を判定。
  `twistedSourceElementsComparison_identity` で、始対象上の標準 fiber 包含と同じ恒等点包含を厳密に照合。
  `twistedSourceElementsEvaluation_isWeakHomotopyEquivalence` は始点固定の全族の同じ評価の弱同値性。
  まだ native 密度余錐の `F2.coconeFiberMap` と同定していないので、密度定理は未完。
- **native 評価との接続**：`presheafDensityEvaluationFiberIso` は、同じ評価余錐の実際の
  `F2.coconeFiberValueMapAt` を `presheafDensityEvaluatedFiberMap` へ比較する関手同型。
  後者は元の大域密度変換を評価し、元の unstraightening 写像空間比較で写したもの。
  始点固定の全族の弱同値との接続が残る。余錐の余極限性はまだ主張しない。
  `presheafDensityEvaluationReconstruction` は同じ始点固定の全族から同じ評価図式への前合成同値。
  `presheafDensityEvaluationGlobalComparisonIso` はその上で同じ `imageIso` と `evaluationIso` を合成。
  `presheafDensityEvaluationConstantComparisonIso` で同じ定値標的へ戻し、
  `presheafDensityEvaluationValueComparisonIso` は同じ実際の評価 fiber 写像の前合成を
  `presheafDensityRestrictedGlobalValueMap` へ比較する関手同型。集約 6176 jobs・監査 624 宣言、標準三公理のみ。
- **(b)**：Yoneda 像の同型と小さい κ-filtered 余極限による最小閉包を全部分 ∞ 圏にした。
  `IndInfinity`、前層への包含の充満忠実性、元の全 Yoneda の厳密な因子化と充満忠実性まで。
  `ind_exists_colimitCone` と `ind_isColimit_iff_inclusion` で、内在する小さい κ-filtered 余極限と包含による保存・検出を証明。
  閉包の最小性は頂点条件の包含の主張であり、(d) の関手の延長の普遍性ではない。
- `IsKappaFiltered` は F2N-1 の `F2/FilteredInfinity.lean` をそのまま使用。再実装しない。
- 定義の構成は任意の κ、(c)・(d) の主定理では κ の正則性を明示する。

### 残り（依存順）

1. **(a)** 元の F を、同じ小さい元の圏の Yoneda 図式の余極限として実現。HTT 5.1.5.3。24〜48時間（暫定）。
2. **(b)** 最小閉包としての構成と包含による小さい κ-filtered 余極限の保存・検出を実装済み。原典の右 fibration 定義との一致は (c)。
3. **(c)** 各 Indκ 対象の表現可能前層の κ-filtered 余極限表示と、右 fibration 定義との一致。HTT 5.3.5.4。16〜40時間（暫定）。
4. **(d)** κ-filtered 余極限を保つ延長の実際の制限関手の同値。HTT 5.3.5.10、Kerodon 9。32〜80時間（暫定）。

### 主要宣言（名前のみ）

- `presheafElementsYonedaDiagram`、`presheafElementsYonedaDiagram_vertex`
- `presheafElementsColimitCocone`、`presheafElementsColimitCocone_isColimit`
- `presheafYonedaSliceProjection`、`presheafYonedaSliceCocone`、`presheafYonedaSliceCocone_vertex`
- `presheafYonedaSliceFiberValueEquivalence`、`presheafElementsCoconeOfComparison`
- `relativeEdgewiseRightComparison_trivialKanFibration`、`twistedArrowSourceLift_projection`
- `presheafTwistedElementsEvaluation`、`presheafTwistedElementsEvaluation_projection`
- `presheafDensityJointHomotopy`、`presheafDensityCocone`、`presheafDensityCocone_vertex`
- `presheafElementsYonedaSliceComparison`、`presheafElementsYonedaSliceComparison_cocone`
- `twistedSourceElementsEvaluation_identity`、`twistedSourceElementsEvaluation_isWeakHomotopyEquivalence`
- `presheafDensityEvaluationCoconeTransformationIso`、`presheafDensityEvaluationFiberIso`
- `presheafDensityEvaluationValueComparisonIso`、`presheafDensityRestrictedGlobalValueMap`
- `presheafDensityJointRestriction_vertex`、`presheafDensityEvaluationReconstruction_isPrecompositionEquivalence`
- `IsKappaColimitClosed`、`IsIndVertex`、`isIndVertex_kappaColimitClosed`、`isIndVertex_minimal`
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

- (a) の余極限の存在だけでは、その頂点が F である密度定理を結論しない。
- 最小閉包の定義だけでは (c) の単一の κ-filtered 表示も、HTT の右 fibration 定義との一致も結論しない。
- (d) は対象の延長の存在だけでなく、元の制限写像 Fun^κ(Indκ(C),D) → Fun(C,D) 自体の同値を要する。
- 原典のモデル構造による証明は輸入せず、既存の ∞ 圏的比較と各点構成で接続する。

### 次の一手

(a)：`presheafDensityEvaluationFiberIso` の標的 `presheafDensityEvaluatedFiberMap F x` を、
`twistedSourceElementsEvaluation (smallRightUnstraighteningProjection F) x` へ比較する。
`presheafDensityEvaluationValueComparisonIso` で同じ復元射上の実際の値写像まで接続済み。
`presheafDensityRestrictedGlobalValueMap` を元の `twistedSourceElementsEvaluation` と fiber 値の比較の合成へ照合。
元の反転 fiber と小さい left unstraightening の fiber は全空間の反転同型で比較する。
`smallLeftUnstraighteningFiberValueEquivalence` と大きい比較の可換式を使い、同じ値への弱同値を得る。
その後は同じ評価復元射の前合成同値性と上の関手同型で実際の fiber 写像へ戻す。
同じ `presheafDensityCocone F` の各評価の余極限性を示し、前層の評価による検出で密度を結論する。
評価後の同じ `F2.coconeFiberMap` の弱同値性を示せば、`F2.isColimitCone_of_coconeFiberMap_weakEquivalence` が使える。
宇宙を上げる際は、小さい Kan 標的への前合成同値と `F2.ulift_pre_homotopyEquivalence` の利用を優先する。
同じ全余錐を (c) の指定表示へ使い、別の余極限の存在や各点だけの同値で密度を主張しない。
報告後は承認を待たず (a) を続行する。

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
