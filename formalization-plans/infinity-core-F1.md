# F1：fibration・straightening・Yoneda（レーン α2）

> **v2 の位置づけ（2026-10-19）**：foundations.md §6 の F1。straightening → Yoneda・前層。twisted arrow・Hom 関手は α2b と分担。

## 引き継ぎ（2026-10-21）

### 現在地

- F1a〜F1c の fibration・transport・coherent nerve の基盤は提供済み。F1d は未完了。
- 小さい単体 fiber について、任意の底・境界固定の相対表現の延長と表現空間の可縮性を証明済み。
  weighted nerve の共同単位、KanEnrichedComparison による全対象・全高次の比較も実現済み。
- c1 の実際の unstraightening の写像空間比較は、区間・pinched・宇宙縮小後とも同値。
  通常の圏の nerve 上の元の S は充満忠実かつ本質的全射で、F0 により分類同値を閉じた。
- 一般の底の実際の S は構成済みで本質的全射。復元射・単位成分・底変換比較も構成済み。
  ただし、その同じ S の充満忠実性は未証明。初頂点 λ に沿う実際の全相対 Hom の引き戻し作用の
  同値性と厳密に同値である。独立な c1 の比較と S の本質的全射性を直接合わせない。
- F1-2：前層 ∞ 圏、制限・評価・定値前層、底の同値による制限同値、right unstraightening を構成済み。
  right fibration 版の恒等点評価は自明 Kan fibration。後合成の自然性も証明済み。
- twisted arrow の両端射影は実際の left fibration。固定領域の inner anodyne 性から全ホーンを充填済み。
  この同じ射影の分類図式を curry して `yonedaInfinityMap` を構成し、対象前層 rep(y) も同定済み。
- coslice の両端固定の主比較は、行ごとの比較と二重単体図式の対角局所化により同値。
  元の表現可能射影と rep(y) の小さい right unstraightening の間の、底上の実際の同値を構成済み。
- 前層 ∞ 圏内の実際の pinched Hom に対する Map(rep(y),F) ≃ F(y) と、rep(z)(y) ≃ Map_C(y,z)
  を証明済み。宇宙・端点を正規化した、同じ Yoneda 写像の実際の Hom 作用も構成済み。
- 始点固定の twisted arrow 全空間への元の coslice 比較は同値。同じ恒等点は始対象であり、
  恒等点からの実際の全 Hom 輸送 `twistedArrowIdentityHomTransport` も同値。
- 先の評価で使った unstraightening 内の恒等点も始対象。その同じ点での直接評価と、
  元の `representableUnstraighteningEvaluation` の全パラメーターでの厳密な一致も証明済み。
- 同じ Yoneda 写像の充満忠実性は未証明。評価後の自己写像の同値性を別途証明する必要がある。

### 残り（依存順）

見積もりは粗い幅で、研究上の障害による上振れがある。

1. F1-1c2：一般の S の Hom 作用と復元比較の照合。Kerodon Cor 5.6.0.6、§5.6.5。24〜100時間。
   同じ関手の充満忠実性・本質的全射性で F0 を使う。明示的な単位・余単位と三角恒等式は任意。
2. essentially small な ∞ 圏的 fiber への相対延長。Thm 5.6.5.12、Cor 5.6.5.15。40〜160時間。
3. cocartesian・Cat∞ 値の分類と必要な宇宙の一般化。Thm 5.6.0.2、§5.5。80〜240時間以上。
4. F1-2：同じ Yoneda 写像の実際の Hom 作用を恒等点からの輸送と照合し、充満忠実性を閉じる。
   Kerodon §§8.1〜8.3。40〜160時間。twisted arrow・Hom 関手は α2b と分担する。
5. 通常圏の nerve 上で Grothendieck 構成と Yoneda を回収する。§§5.6、8.3。8〜32時間。

### 主要宣言（名前のみ）

- `leftStraighteningInfinityMap`、`leftStraighteningInfinityMap_isEssentiallySurjective`
- `leftStraighteningCoherentEquivalence`、`leftStraighteningInfinityReconstruction`
- `leftStraighteningInfinityMap_isQCatEquivalence_iff_relativeFunctorPullback`
- `yonedaInfinityMap`、`representablePresheafInfinity`、`representablePresheafInfinity_sliceIso`
- `representableRightUnstraighteningComparison_isQCatEquivalence`
- `yonedaPresheafEvaluation_isQCatEquivalence`、`representablePresheafValueEquivalence`
- `yonedaInfinityEvaluatedMappingSpaceMap`、`yonedaInfinityMap_isFullyFaithful_iff_evaluatedMappingSpace`
- `twistedArrowSourceIdentity_isInitialVertex`、`twistedArrowIdentityHomTransport_isQCatEquivalence`
- `representableUnstraighteningEvaluation_eq_identityEvaluation`

### 依存と提供

- F0・Coherent・Stable・F1B・HomotopyLimits の既存の一般論は読み取り専用。
- 一般道具 KanTestDetection・DiagonalAdjunction・DiagonalLocalizedEquivalence は読み取り専用。
- F1/、F1.lean、audit_infinity_f1.lean、本計画だけを所有する。他レーンは変更しない。
- 新規 sorry・公理・未証明引用なし。公開主経路に ModelCategory SSet 等の追加 instance 仮定なし。
  KanComplex と TrivialKanFibration は、Mathlib のホーン・境界に対する持ち上げ性を使う。

### 未コミット

- 値の同値・宇宙移送・同じ Yoneda Hom 作用は `3cdde3b95` に保存済み。
  F1 全体ビルド4250 jobs、公理監査9801宣言が成功（標準3公理のみ）。
- 始点固定の射影・恒等点の始対象性と輸送・同じ unstraightening 恒等点の所有3モジュール、
  集約・監査・計画が今回の保存単位。F1 全体ビルド4403 jobs、公理監査9833宣言が成功。
  標準3公理のみ。通る所有ファイルだけを早めに `git commit --only` で保存する。
- N が読む指定の2ファイルと集約は `a12f7e9f4` で保存済み。

### 既知の問題

- λ は局所化であり、圏同値として消去しない。一般の S の充満忠実性は依然未証明。
- 独立な Hom 同値だけを同じ Yoneda 写像の充満忠実性と数えない。
  比較の選択が入るため、評価後の自己写像が定義上恒等であるとは仮定しない。
- strict Kan 図式の strict な Hom が一般に Kan とは主張しない。小さい単体 fiber の条件を
  essentially small な ∞ 圏的 fiber だけへ弱める相対延長と、Cat∞ 値の分類も未証明。

### 次の一手

F1-2：TwistedArrowSourceInitial の実際の恒等点輸送の同値まで通った。
次は twistedArrowProjection C 全体の `leftStraighteningInfinityReconstruction` を、終点固定の
底の包含に沿って制限する。`smallLeftUnstraighteningMap_isPullback` と
`representablePresheafInfinity_eq_targetRestriction` により、Tw の同じ恒等点から rep(y) の
unstraightening 内の評価点を取る。既存の別々に選んだ評価点との一致を仮定しない。
その評価が c1 の `leftUnstraighteningMappingFiberHom_parametrizedIso` を通して、始点固定の
`twistedArrowIdentityHomTransport` を回収することを全パラメーターで照合する。
F1-1c2：別途、初頂点引き戻しの全相対 Hom 作用の同値性を証明し、同じ S に F0 を適用する。

全体の正本は [foundations.md](foundations.md)。F0 は [infinity-core.md](infinity-core.md) を使う。

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
