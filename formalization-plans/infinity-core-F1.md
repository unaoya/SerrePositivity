# F1：fibration・straightening・Yoneda（レーン α2）

> **v2 の位置づけ（2026-10-19）**：foundations.md §6 の F1。straightening → Yoneda・前層。twisted arrow・Hom 関手は α2b と分担。

## 引き継ぎ（2026-10-19）

### 現在地

- F1a〜F1c の fibration・transport・coherent nerve の基盤を提供済み。F1d は未完了。
- left fibrations と strict transport の像の coherent nerve の同値は構成済み。
  strict Kan 図式の復元、および有限鎖の nerve 上の coherent 図式の復元は関手同型まで証明済み。
- weighted nerve の標準単位を、底の対象で評価した `KanEnrichedComparison` と coherent な
  関手同型へ実現済み。任意の coherent な strict 図式の族へ引き戻せる。実現した辺は元の単位を回収する。
- 一図式を固定した場合は、標準単位を底全体の coherent な関手同型へ実現済み。
  単位の各成分は単射。単位に沿う strict な比較の制限は trivial Kan fibration で、
  延長空間は可縮。strict transport の像では図式全体で同値な厳密な左逆も存在する。
- 底と図式の族を同時に動かした二点図式の共同実現を構成済み。面・退化との整合性と
  比較の辺の成分公式・可逆性を証明し、curry により `kanDiagramRealization C` と
  `weightedNerveInfinityMap C ≫ leftStraighteningCoherentMap C` の大域的な関手同型を得た。
- `LeftTransportRepresentation` に分類図式・底上の比較・fiber の同値を束ね、pointed space
  への射を回収した。任意の底変換への制限は底側と全空間側の両射を厳密に保つ。
  両射の一致と表現そのものの一致の同値も証明済み。通常の nerve 上の小さい left fibration
  には、既存の直接比較から実際の表現を構成済み。
- 正次元の標準単体上で、比較の全 fiber の同値性は境界上の同値性と同値。
  可換四角形そのものの境界固定延長は未証明。
- 対象ビルド2805 jobs、公理監査4901宣言が成功。依存公理は標準3公理のみ。
  主経路にモデル構造の instance 仮定なし。実施記録はコミットメッセージ。

### 残り（依存順）

見積もりは再開後の実作業時間の粗い幅で、研究上の障害による上振れがある。

1. 任意の coherent 図式について、境界を固定した表現の延長と高次の貼り合わせを証明する。
   Kerodon Theorem 5.6.5.12、Corollary 5.6.5.15。40〜160時間。
2. unstraightening の実際の写像空間上の比較の同値性、一般の単位・余単位を完成する。
   Kerodon Corollary 5.6.0.6、§5.6.5。24〜100時間。
3. 必要な宇宙の一般化と cocartesian・Cat_∞ 値の分類へ進む。
   Kerodon Theorem 5.6.0.2、§5.5。80〜240時間以上。
4. F1h：twisted arrow、Hom 関手、前層、Yoneda の充満忠実性。
   Kerodon §§8.1〜8.3。40〜160時間。Kan 拡張は α2b の成果を使用可能。
5. F1i：通常の圏の nerve 上で Grothendieck 構成と Yoneda を回収する。
   Kerodon §§5.6、8.3 の通常圏への特殊化。8〜32時間。

### 主要宣言（名前のみ）

- `IsCartesianEdge`、`IsCocartesianEdge`、`SpaceInfinity`、`CatInfinity`
- `leftStraighteningCoherentMap`、`smallLeftUnstraighteningObject`
- `leftStrictTransportInfinityEquivalence`、`leftUnstraighteningMappingSpaceMap`
- `strictDiagramScaffoldHomEquiv`、`strictDiagramMappingPre_trivialKanFibration`
- `strictKanStraighteningUnitIso`、`finiteStraighteningUnitIso`
- `weightedNerveKanEnriched`、`weightedNerveInfinityMap`
- `weightedNerveTransportUnit`、`weightedNerveTransportUnit_isQCatEquivalence`
- `weightedNerveTransportUnit_enrichedNaturality`
- `weightedNerveTransportKanComparison`、`weightedNerveStraighteningEvaluationIso`
- `weightedNerveStraighteningFamilyEvaluationIso`、`weightedNerveStraighteningUnitIso`
- `weightedNerveJointComparisonEdge`、`weightedNerveJointComparisonIso`
- `weightedNerveStraighteningCoherentUnitIso`、`weightedNerveStraighteningCoherentFamilyUnitIso`
- `weightedNerveTransportUnit_restriction_trivialKanFibration`
- `weightedNerveTransportUnit_extensionSpace_isContractibleKan`
- `exists_weightedNerveTransportUnit_retraction`
- `LeftTransportRepresentation`、`LeftTransportRepresentation.restrict`
- `LeftTransportRepresentation.restrict_eq_iff`、`nerveLeftTransportRepresentation`
- `leftFibration_fiberEquivalence_iff_boundary`
- `coherentLeftResolutionInfinityComparisonIso`

### 依存と提供

- Core の left/right fibration、相対写像空間、同値・関手同型を読み取り専用で使用する。
  Coherent/Quasicategory の γ1 と HomotopyLimits/WeightedConstantSimplex も使用する。
- 提供界面は上記の fibration・transport、𝒮・Cat_∞、strict transport の比較。
  𝒮・Cat_∞ の極限・余極限は主張しない。F1e〜F1g は α2b/F1B の担当。
- 再開時は F1/README.md の原典照合と方針を維持し、他レーンのファイルは編集しない。

### 未コミット

- 担当する F1/、F1.lean、監査スクリプトに未コミットの実装なし。
  現在地の更新も所有ファイルだけを指定して同時にコミットする。
- 共有作業ツリーの他レーンの変更は引き継ぎ対象外であり、保存・巻き戻しを行わない。

### 既知の問題

- F1 の対象ビルド・公理監査に失敗なし。ルート全体のビルドは今回の検査対象外。
- F1B の `relativeFunctorVertex` 衝突は `relativeExtensionVertex` への改名で修正済み。
  両集約の同時ビルドと同時 import は成功。修正コミット `1132823f` は並行追加の監査29行を含む。
- F1 のソースに明示的な `ModelCategory SSet` 仮定はない。モデル構造は使わない。
  `Fibration`・`TrivialKanFibration` はホーン・境界に対する持ち上げ性として用いる。
- strict Kan 図式の strict な Hom が一般に Kan とは主張しない。
  局所 strictification は任意の内面制限と可換でも、境界を固定した構成でもない。
- 各 fiber の同値や辺での一致だけでは図式全体の同型・分類を導けない。
  同値の反映は既証明であり、残る一般の単位・充満忠実性の代わりにはならない。
- 標準単位に沿う可縮な延長は同じ通常圏上での係数図式の変更に関するもの。
  底の包含 C₀ ⊆ C に対し、指定した表現の底への射と全空間の射をともに厳密に保つ
  相対表現の延長（Theorem 5.6.5.12）は未証明。高次パラメーターの境界上でも両方を保つ必要がある。

### 次の一手

底の包含とパラメーターの境界をともに固定する表現の延長へ進む（§5.6.5）。
表現の頂点データは `LeftTransportRepresentation` として定式化済み。次はこれを
二つの関手空間の引き戻しの部分単体集合（transport witnesses）へ束ね、底の包含に沿う
制限の持ち上げ性を示す（[Lemma 5.6.8.10](https://kerodon.net/tag/02SK)）。
標準単体上での境界固定延長は、既存の局所 strictification だけからは従わない。
正次元では `leftFibration_fiberEquivalence_iff_boundary` により fiber 条件を境界から回収できるので、
底・全空間の両射を固定した可換四角形の延長を構成する。

作成日：2026-10-18。状態：着手可能。全体の正本は [foundations.md](foundations.md)。
F0 の一般論は [infinity-core.md](infinity-core.md)（レーン α）が担当し、α2 はその成果を読むだけで編集しない。

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
