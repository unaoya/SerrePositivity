# F1：fibration・straightening・Yoneda（レーン α2）

> **v2 の位置づけ（2026-10-19）**：foundations.md §6 の F1。straightening → Yoneda・前層。twisted arrow・Hom 関手は α2b と分担。

## 引き継ぎ（2026-10-19）

### 現在地

- F1a〜F1c の fibration・transport・coherent nerve の基盤を提供済み。F1d は未完了。
- left fibrations と strict transport の像の coherent nerve の同値は構成済み。
  strict Kan 図式の復元、および有限鎖の nerve 上の coherent 図式の復元は関手同型まで証明済み。
- weighted nerve の豊穣な標準単位は各成分で単射かつ同値。単位に沿う strict な比較の制限は
  trivial Kan fibration、延長空間は可縮。strict transport の像で同値な厳密な左逆も存在する。
- 底と図式の共同実現で、`kanDiagramRealization C` と
  `weightedNerveInfinityMap C ≫ leftStraighteningCoherentMap C` の大域的な関手同型を構成済み。
- 表現を `LeftTransportRepresentation` に束ねた。任意の底変換は底側と全空間側の両射を厳密に保ち、
  両射の一致は表現の一致と同値。通常の nerve 上の小さい left fibration の実際の表現も構成済み。
- 正次元の標準単体上の全 fiber の同値性は境界上で判定できる。境界固定延長は未証明。
- 可換四角形全体を関手空間の引き戻し `transportSquareSpace p` として構成。
  分類図式への射影は left fibration、固定図式上の fiber は相対関手空間と同型。
  表現を表す頂点の全部分複体 `transportWitnessSpace p` は Kan 複体。
  実際の表現との頂点全単射、任意の底変換への制限、頂点での厳密な制限の回収を証明済み。
- 単射への表現空間の制限は Kan fibration、inner anodyne なら trivial Kan fibration
  （Lemma 5.6.8.10 の空間値版）。指定表現の厳密な延長と、その延長空間の可縮性を証明済み。
  全頂点を被覆する制限は表現条件を反映する。一般の底上の表現空間の可縮性は未証明。
- left fibration に沿う inner anodyne 射の逆像は前合成同値（Lemma 5.3.6.6 の空間値版）。
  replacement のホーン逆像の pushout 分解、任意の底変換後の scaffold 比較、依存積の随伴で証明。
- `parametrizedFiberTransport` は固定端点の写像空間全体で選択独立性・パラメーター制限・係数変更を保ち、各辺で既存の transport を回収する。
  unstraightening の写像空間比較の fiber 作用と、対象評価後の普遍輸送を関手同型で結んだ。
- 実際の pointed-space 射影の普遍輸送は写像空間上で同値。豊穣合成・反転・底の同型で証明済み。
  始点同値に制限した同時端点制限、両端同値の円柱四角形の端点制限は trivial Kan fibration。
  元の区間の境界上の全空間を両端 fiber の直和と同定。指定境界表現から実際の両端同値を回収した。
  境界固定 lift 族、四角形の二条件同時 fiber、実際の境界制限の fiber を厳密な同型で結んだ。
  全頂点を被覆する制限では、表現空間の fiber と周囲の四角形の fiber は厳密に同型。
  実際の区間上の表現空間の境界制限は trivial Kan fibration（Lemma 5.6.9.1 の空間値版）。
  積上の表現空間と内部 Hom の同型は実際の底変換制限に自然。底の同型でも表現空間は厳密に同型。
  各次数で小さい全空間の点上の表現空間は可縮 Kan。非交和・単射の pushout の可縮性保存、骨格逆極限と可縮性の還元も証明済み。
- 対象ビルド3069 jobs、公理監査6158宣言が成功。依存公理は標準3公理のみ。ルート全体は検査対象外。

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
- `weightedNerveStraighteningCoherentUnitIso`、`weightedNerveStraighteningCoherentFamilyUnitIso`
- `LeftTransportRepresentation`、`LeftTransportRepresentation.restrict`
- `transportWitnessSpace`、`transportWitnessVertexEquiv`、`transportWitnessSpace_kanComplex`
- `leftFibration_pullback_innerAnodyne_isPrecompositionEquivalence`
- `transportWitnessRestriction_trivialKanFibration_of_innerAnodyne`
- `exists_leftTransportRepresentation_extension_innerAnodyne`
- `FiberTransportFamily`、`parametrizedFiberTransport`
- `leftUnstraighteningMappingFiberHom_parametrizedIso`
- `pointTransportWitnessSpace_isContractibleKan`、`transportWitnessSpace_isContractibleKan_of_skeleton`

### 依存と提供

- Core、Coherent/Quasicategory、Stable/SliceOpposite、HomotopyLimits、KST/Spectra/FibrationTower* は読み取り専用。
  F1B/FullSubcomplexMapping・SSetPullbackAdjoint・QuillenASliceOpposite を読み取り専用で使う。
- 提供界面は上記の fibration・transport、𝒮・Cat_∞、strict transport の比較。
  𝒮・Cat_∞ の極限・余極限は主張しない。F1e〜F1g は α2b/F1B の担当。
- 再開時は F1/README.md の原典照合と方針を維持し、他レーンのファイルは編集しない。

### 未コミット

- F1/、F1.lean、監査スクリプト、計画の変更は所有ファイルのみ指定して保存する。未コミット実装なし。
- 共有作業ツリーの他レーンの変更は引き継ぎ対象外であり、保存・巻き戻しを行わない。

### 既知の問題

- F1 のソースに明示的な `ModelCategory SSet` 仮定はない。モデル構造は使わない。
  `Fibration`・`TrivialKanFibration` はホーン・境界に対する持ち上げ性として用いる。
- strict Kan 図式の strict な Hom が一般に Kan とは主張しない。
  局所 strictification は任意の内面制限と可換でも、境界を固定した構成でもない。
- 各 fiber の同値や辺での一致だけでは図式全体の同型・分類を導けない。
  同値の反映は既証明であり、残る一般の単位・充満忠実性の代わりにはならない。
- 標準単位に沿う可縮な延長は同じ通常圏上での係数図式の変更に関するもの。
  底の包含 C₀ ⊆ C に対し、指定した表現の底への射と全空間の射をともに厳密に保つ
  相対表現の延長（Theorem 5.6.5.12）は未証明。高次パラメーターの境界上でも両方を保つ必要がある。
- inner anodyne 制限の fiber の可縮性は、一般の境界制限や表現空間全体の可縮性ではない。

### 次の一手

標準単体と境界の次元の帰納法を、実際のセル付加の pushout と非交和へ結ぶ。
各有限骨格での可縮性を証明し、検証済みの fibration 塔の逆極限による還元へ渡す。
小ささは各次数での条件まで検証済み。任意の essentially small な fiber への一般化は残る。
その後、一般の表現空間の可縮性と境界固定延長（Theorem 5.6.8.3、§5.6.5）へ進む。
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
