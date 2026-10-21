# F1：fibration・straightening・Yoneda（レーン α2）

> **v2 の位置づけ（2026-10-19）**：foundations.md §6 の F1。straightening → Yoneda・前層。twisted arrow・Hom 関手は α2b と分担。

## 引き継ぎ（2026-10-22）

### 現在地

- F1a〜F1c の基盤は提供済み。F1d の Cat∞ 値 cocartesian 分類は未完了。
- `CocartesianFibrationInfinity B` の Hom は元の cocartesian な相対関手 ∞ 圏の core。
- 通常圏の nerve 上の実際の全 fibration の分類写像 `cocartesianStraighteningCoherentMap` を構成済み。
  元の全相対 Hom の作用を section へ制限し、core の混合作用・対角評価で全対象と全高次を束ねた。
  同じ写像の p での値は、F1B の cocartesian strict transport の既存の図式全体と厳密に一致する。
  各値は元の fiber と恒等射評価で同値。strict transport の同じ全相対 Hom 作用も同値と証明済み。
  core 上の同じ作用を豊穣化し、strict transport の像への coherent な比較は同値。
  全ての有限次元単体上で元の分類主写像の充満忠実性・分類同値と、元の全 Hom の core の区間作用の同値を追加仮定なしに証明済み。
  一次元の strict 変換空間は、元の二成分評価による内部 Hom の厳密な pullback と証明済み。
  薄い底上の元の輸送遷移の同値持ち上げ性と、後合成の core の Kan fibration 性も証明済み。
  一次元の元の Hom の core も、同じ二成分評価による core の厳密な pullback と証明済み。
  元の Hom 作用の成分評価を標準 Hom 同値と厳密に結び、一次元の同じ全 Hom 作用の同値性を
  実際の固定成分の全 fiber 比較へ還元し、同じ比較自体の同値性を追加仮定なしに証明した。
  両側の一成分評価の Kan 性、source の固定成分 fiber と後合成 fiber の厳密な同型も証明済み。
  分類先の実際の固定成分 fiber は、同じ第二三角形の外ホーン延長を表す厳密な pullback と証明済み。
  第一三角形への制限は Kan fibration。指定外ホーン fiber から元の fiber への同値と、元の比較の同じ外ホーン fiber への制限を構成済み。
  元の Hom の core の区間作用を構成し、底の制限・豊穣前合成の自然性と主写像への接続を証明済み。
  元の cocartesian Hom の core と分類先の両端固定の区間 Hom は、底を覆う余極限に沿う厳密な極限。
  底変換の辺の保存・反映、辺の被覆と全空間の余極限、元の Hom と分類先の単射制限の Kan 性も証明済み。
  同じ底変換比較の Hom から実際の輸送を作り、零次元の局所 Hom 比較と元の大域作用の関手同型も構成済み。
- 空間値版では、各 Kan fiber が小さい Kan 模型と同値であれば、任意の底・境界固定の相対表現と
  全パラメーターでの延長空間の可縮性を証明済み。元の次数 fiber の小ささは不要。
- **F1-1c2 の空間値版は完了**：一般の小さい quasicategory B 上の構成済みの同じ S は
  `leftStraighteningInfinityMap_isFullyFaithful` により充満忠実。既存の本質的全射性と F0 を合わせ、
  `leftStraighteningInfinityMap_isQCatEquivalence` で分類同値を閉じた。単位・余単位と三角恒等式は任意。
- **F1-2 は完了**：前層 ∞ 圏、制限・評価・定値前層、Yoneda の構成・充満忠実性を証明済み。
  元の全相対 Hom を Hom とする `RightFibrationInfinity B` と `PresheafInfinity B` の実際の分類同値
  `rightStraighteningInfinityEquivalence` を、小さい quasicategory B 上で構成した。逆の ∞ 関手も同値で、
  その F での値は既存の `smallRightUnstraighteningProjection F` と頂点の同型で一致する。
- 前層 ∞ 圏内の実際の pinched Hom に対する Map(rep(y),F) ≃ F(y) と、rep(z)(y) ≃ Map_C(y,z)
  を証明済み。宇宙・端点を正規化した、同じ Yoneda 写像の実際の Hom 作用も構成済み。
- `yonedaInfinityMap_isFullyFaithful` により、構成済みの同じ Yoneda 写像の充満忠実性を証明済み。
  空間値の essentially small Kan fiber への相対延長も閉じた。Cat∞ 値版が残り、F1 全体は未完了。

### 残り（依存順）

1. F1-1c2 の小さい quasicategory 上の空間値版は完了。Kerodon Cor 5.6.0.6、§5.6.5。
   明示的な単位・余単位と三角恒等式は任意。任意の単体集合への拡張は別件。
2. essentially small Kan fiber の空間値相対延長は完了。非 Kan の ∞ 圏的 fiber は次項に残る。
   Thm 5.6.5.12、Cor 5.6.5.15 の一般の cocartesian 版と区別する。
3. cocartesian・Cat∞ 値の分類と必要な宇宙の一般化。Thm 5.6.0.2、§5.5。80〜240時間以上。
4. F1-2：Yoneda・前層と right fibration 分類は完了。Kerodon §§8.1〜8.3。
   twisted arrow・Hom 関手と前層の極限・余極限の後続項目は、本項目と区別する。
5. 通常圏の nerve 上で Grothendieck 構成と Yoneda を回収する。§§5.6、8.3。8〜32時間。

### 主要宣言（名前のみ）

- `leftStraighteningInfinityMap`、`leftStraighteningInfinityMap_isEssentiallySurjective`
- `HasEssentiallySmallFibers`、`hasEssentiallySmallFibers_iff_transportRepresentation`
- `exists_essentiallySmall_leftTransportRepresentation_extension`
- `essentiallySmallTransportWitnessRestriction_trivialKanFibration`
- `leftStraighteningInfinityMap_isQCatEquivalence`、`leftStraighteningInfinityEquivalence`
- `RightFibrationInfinity`、`rightStraighteningInfinityEquivalence`、`rightUnstraighteningInfinityMap`
- `rightStraighteningInfinityCounitVertex`、`rightUnstraighteningInfinityVertexIso`
- `yonedaInfinityMap`、`representablePresheafInfinity`、`representablePresheafInfinity_sliceIso`
- `representableRightUnstraighteningComparison_isQCatEquivalence`
- `yonedaPresheafEvaluation_isQCatEquivalence`、`representablePresheafValueEquivalence`
- `yonedaInfinityMap_isFullyFaithful`、`yonedaInfinityMap_pinchedHomMap_isQCatEquivalence`
- `CocartesianFibrationInfinity`、`cocartesianFibrationInfinityMappingEquivalence`
- `cocartesianStraighteningCoherentMap`、`cocartesianStraighteningCoherentMap_vertex`
- `cocartesianStraighteningHomInterval_finite_isQCatEquivalence`、`cocartesianStraighteningCoherentMap_finite_isQCatEquivalence`、`cocartesianLocalHomComparison_finite_isQCatEquivalence`

### 依存と提供

- F0・Coherent・Stable・F1B・HomotopyLimits と F2 の core の充填性の一般論は読み取り専用。
- 一般道具 KanTestDetection・DiagonalAdjunction・DiagonalLocalizedEquivalence は読み取り専用。
- F1/、F1.lean、audit_infinity_f1.lean、本計画だけを所有する。他レーンは変更しない。
- 新規 sorry・公理・未証明引用なし。公開主経路に ModelCategory SSet 等の追加 instance 仮定なし。
  KanComplex と TrivialKanFibration は、Mathlib のホーン・境界に対する持ち上げ性を使う。

### 未コミット

- なし。検証済みの F1 所有ファイルを、集約・監査・本計画と同一の保存単位でコミットする。
- 他レーンの編集・ステージは保存対象外。実施記録は各コミットメッセージに置く。

### 既知の問題

- λ は局所化であり、圏同値として消去しない。実際の初頂点引き戻しの Hom 作用を証明した。
- Yoneda の充満忠実性は元の Hom 作用そのものの同値性で証明した。独立な c1 の同値だけでは
  一般の S の充満忠実性にならないため、同じ作用との厳密な比較を経由した。三角恒等式は任意。
- 一般の strict QCat 図式の Hom の quasicategory 性は仮定しない。strict transport が標的なら証明済み。
- 元の cocartesian Hom の scaffold 制限と strict transport の写像空間比較は同値。
  元の Hom の同じ区間作用と全固定成分比較は同値と証明済み。有限セル・骨格の降下、大域充満忠実性・一般の本質的全射性は残り、分類は未完了。

### 次の一手

全有限単体の同じ元の分類・全 Hom 作用の帰納は閉じた。`cocartesianStraighteningHomInterval_finite_isQCatEquivalence n` は元の全相対 Hom の core の同じ作用を使い、`cocartesianStraighteningCoherentMap_finite_isFullyFaithful` と F0・既存の本質的全射性で `cocartesianStraighteningCoherentMap_finite_isQCatEquivalence` を結論した。`cocartesianFiniteSimplexStraighteningEquivalence n` は同じ分類主写像を保つ分類同値。`cocartesianLocalHomComparison_finite_isQCatEquivalence` は任意の底の全有限次元セルの同じ局所比較。単位・余単位の明示構成は主経路へ戻さない。
`cocartesianScaffoldSourceRestrictionMap_id_trivialKanFibration`・`cocartesianScaffoldTargetRestrictionMap_id_trivialKanFibration` は、全次元で元の最初の辺と尾部への両制限自身の自明 Kan 性。小さい・大きい表示の同型と両脚の厳密な自然性により、標準 Segal 射の自明 Kan 性を元の cospan に移した。source は欠損辺を同じ三角形で分解し、元の関手の辺保存を反映する。
`cocartesianScaffoldSegalComparisonIso` は元の source 制限・同じ厳密比較と、元の分類 Hom 作用・target 制限を結ぶ。元の全 Hom 上の二射を実際の pullback 内で結び、共有頂点への指定像は両側とも同じ直接の大域自然性。尾部の局所同値を明示的な帰納仮定として最初の辺と貼り、全単体の同じ作用の同値へ戻した。
`cocartesianCellAttachment_nativeLift_isPullback`・`_interval_isPullback` は任意のセル貼付けに対する、両側の元の Hom の同じ宇宙の厳密な pullback。境界からセルへの包含だけを単射とし、既存部分への貼付け写像には単射性を要求しない。既存部分への両制限は Kan fibration で、`cocartesianCellAttachment_sourceExtensionFiberIso`・`_targetExtensionFiberIso` は指定値の延長空間を同じ局所の境界固定 fiber と同定し、セルへの射影を保つ。両延長空間の Kan 性も証明済み。`SimplexAttachmentOver` で実際の標準単体の任意の境界貼付けを底上の pushout として構成した。
次は有限セル・骨格の降下から一般の充満忠実性を結論する。元の分類作用が同じ指定値の両延長空間へ誘導する境界固定の比較を構成し、上記 fiber 同型の下で同じ局所比較を回収することを証明する。単体の境界は一般に通常圏の nerve ではないため、全有限単体の同値を境界の比較にそのまま適用しない。`CocartesianPullbackNativeCoreDescent`・`IntervalDiagramColimitDescent` の厳密な極限表示と制限の Kan 性で骨格を貼る。一般の通常圏の nerve 上の大域 Hom 同値はまだ未完了。
有限セル・骨格と一般の充満忠実性・監査は 2〜4 日（暫定）。一般の本質的全射性・一般の底と宇宙への帰着も残り、Cat∞ 値分類は未完了。既存の小さい quasicategory 上の空間値・right fibration・Yoneda の完了と混同しない。
性能上、巨大な同型は中間作用と端点を不透明な等式で揃えてから合成する。`iso_pasting_heq_of_endpoint_eq`・`IsoTriangleCommutes` とホモトピー圏の対象の等式を使い、source cospan は二脚を明示する。上限・追跡設定は増やさない。
正本は [foundations.md](foundations.md)、F0 は [infinity-core.md](infinity-core.md)。

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
