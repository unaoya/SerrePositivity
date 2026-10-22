# F1：fibration・straightening・Yoneda（レーン α2）

> **v2 の位置づけ（2026-10-22 10:10 変更）**：foundations.md §6 の F1。第 I 段の指定工程 F1-4 → F1-5 → F1-3b は完了。Cat∞ 値の一般底分類は第 II 段。

## 引き継ぎ（2026-10-22）

### 現在地

- 空間値 straightening は一般の小さい quasicategory 上で完了。単位・余単位・三角恒等式の明示構成は任意。
- F1-2 は完了：前層 ∞ 圏・制限・評価・定値前層、right fibration 分類、Yoneda の構成・充満忠実性。
- Cat∞ 値分類の第 I 段の区切りは全有限単体底での同じ分類主写像の同値
  `cocartesianStraighteningCoherentMap_finite_isQCatEquivalence`（06:21）。一般底の分類は未完了。
- 一般底の検証済み区切りは `dc768ab4b`。二次元標準境界の coherent 比較の同値と元の大域作用への指定同型まで保存。
- **F1-4 完了**：前層の任意の小さい極限・余極限の存在を各点で構成し、元の全評価による保存・検出を証明。
  `presheafInfinity_hasLimit`、`presheafInfinity_hasColimit`。底・形状の quasicategory 性や有限性は不要。
- 任意の小さい空間値図式の native な極限錐を元の小さい全切断で構成。
  `coherentDiagramSectionsCone_isLimit`、`hasLimit_coherentSpaceDiagram`。追加の存在条件は解消した。
- 元の錐の全 Hom 比較を、同じ三角形の相対合成と全切断の同じ恒等射の指定比較へ移して証明。
  `coneSectionsNativeComparisonIso` は全高次パラメータで元の比較射を保持する。
- `representablePresheafInfinity_isLimit`：表現可能前層は任意の小さい形状の元の極限全錐を保存。
  像の極限の存在の追加仮定も解消。HTT 5.1.3.2。
- **F1-5 完了**：`isLimitCone_iff_representablePresheafInfinity` が Cᵒᵖ 上の同じ全錐を検出。
  `isLimitCone_iff_covariantRepresentableInfinity` が二重反転を明示して元の C 上の小さい極限を特徴づける。
  `covariantRepresentableValueEquivalence` はその関手の値を元の Hom(x,y) と比較する。
- **F1-3b 完了**：元の `twistedArrowHomInfinity` が Cᵒᵖ × C 上の一つの coherent な Hom 図式。
  `homInfinityJointValueEquivalence` で同じ共同評価の値を元の標準写像空間へ比較。
  `homInfinityCovariant_eq_yonedaEvaluation`、`coyonedaInfinityMap_uncurry`、指定頂点の式も証明。
  既存の twisted arrow の left fibration 性と全体の pointed fiber 比較を集約・監査で再確認。

### 残り（依存順）

- 第 I 段の今回の指定工程に残りなし。F1-4（HTT 5.1.2.2–5.1.2.4）、F1-5（HTT 5.1.3.2）、F1-3b（Kerodon 8）を完了。
1. **第 II 段**：Cat∞ 値分類の一般底・宇宙への拡張。Kerodon 5.6。一般充満忠実性まで36〜80時間（暫定）、本質的全射性等は別途。

### 主要宣言（名前のみ）

- `leftStraighteningInfinityMap_isQCatEquivalence`、`leftStraighteningInfinityEquivalence`
- `RightFibrationInfinity`、`rightStraighteningInfinityEquivalence`、`rightUnstraighteningInfinityMap`
- `PresheafInfinity`、`presheafInfinityEvaluation`、`presheafInfinityRestriction`
- `yonedaInfinityMap`、`representablePresheafInfinity`、`representablePresheafValueEquivalence`
- `yonedaInfinityMap_isFullyFaithful`、`yonedaPresheafEvaluation_isQCatEquivalence`
- `cocartesianStraighteningCoherentMap_finite_isQCatEquivalence`
- `cocartesianTwoBoundaryCoherentHomComparison_originalIso`
- `presheafInfinity_hasColimit`、`presheafInfinity_isColimit_iff_evaluation`
- `presheafInfinity_exists_limitCone`、`presheafInfinity_hasLimit`
- `presheafInfinity_evaluation_small_isLimit`、`presheafInfinity_small_isLimit_iff_evaluation`
- `representablePresheafInfinity_isLimit`、`isLimitCone_iff_representablePresheafInfinity`
- `covariantRepresentableInfinity`、`isLimitCone_iff_covariantRepresentableInfinity`
- `covariantRepresentableValueEquivalence`、`homInfinityJointValueEquivalence`
- `homInfinityCovariant`、`homInfinityCovariant_eq_yonedaEvaluation`、`coyonedaInfinityMap`、`coyonedaInfinityMap_uncurry`
- `coherentSpaceSectionsObject`、`coherentDiagramSectionsCone`、`coherentDiagramSectionsCone_vertex`
- `coherentDiagramSectionsCone_isLimit`、`hasLimit_coherentSpaceDiagram`
- `coherentSectionsConeHomComparison_isQCatEquivalence`、`coneSectionsNativeComparisonIso`

### 依存と提供

- F0・Coherent・Stable・F1B・F2・HomotopyLimits は読み取り専用。
- F1-4・F1-5 は F1b の F2N-2（Ind）・F2N-3 へ提供。Cat∞ 値一般分類は第 I 段の利用者なし。
- 所有は F1/、F1.lean、audit_infinity_f1.lean、本計画のみ。他レーン不変。
- 新規 sorry・公理・未証明引用なし。主経路に同値性や ModelCategory の追加 instance 仮定なし。

### 未コミット

- なし。通る所有ファイルを集約・監査とともに `git commit --only` で早めに保存する。

### 既知の問題

- 有限単体の分類同値から一般底の分類同値は結論しない。標準境界は一般に nerve ではない。
- 前層は宇宙 u+1、底と小さい形状は宇宙 u。𝒮 の大きい任意形状の極限・余極限は主張しない。
- 反変前層と共変 Hom は区別する。F1-5 の共変判定は二重反転の同型と元の全錐・脚の比較で証明した。

### 再開点（第 II 段、3行）

1. `dc768ab4b`：有限二単体の coherent 境界比較の同値と、元の大域作用への `cocartesianTwoBoundaryCoherentHomComparison_originalIso` まで保存済み。
2. 次は同じ比較を任意の底の二次元セルへ移し、局所比較の自然性と指定境界値の fiber 比較を揃える。
3. その後は高次境界・有限セル・骨格降下で一般充満忠実性を閉じ、本質的全射性・一般底・宇宙へ進む。

### 次の一手

今回の承認範囲 F1-4 → F1-5 → F1-3b は完了。第 II 段へ自動で戻らない。
第 II 段を再開する場合は上の「再開点」3行から始める。
前層・表現可能関手・二変数 Hom の利用者は上の主要宣言を集約 F1 から import できる。

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

- 配置は `SerrePositivity/InfinityCategories/F1/`、namespace `SerrePositivity.InfinityCategories`。
  集約 `InfinityCategories/F1.lean` をルートに 1 行で追加する。
- fibration は `MorphismProperty.rlp` 流儀で定義し、A2d の left/right fibration と整合させる。
- Cat_∞ と 𝒮 は coherent nerve で定義する（γ1）。両者の極限・余極限は F2 まで主張しない。
- straightening は left fibration・𝒮 値の場合を先に完成させ、cocartesian・Cat_∞ 値へ拡張する。
- モデル構造（covariant/contravariant model structure）は使わない。Cisinski 流の代替は採らない。
- sorry・公理・引用は導入しない。実施記録はコミットメッセージ、宣言名と型の一覧は本文書 §3。

## 記録の所在

実施記録・現在地の詳細・型一覧は [archive/infinity-core-F1-log.md](archive/infinity-core-F1-log.md) に移した（2026-10-19）。現在地は冒頭の引き継ぎ節が正本で、工程ごとの記録はコミットメッセージに置く。
