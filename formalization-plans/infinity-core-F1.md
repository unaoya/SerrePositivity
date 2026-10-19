# F1：fibration・straightening・Yoneda（レーン α2）

> **v2 の位置づけ（2026-10-19）**：foundations.md §6 の F1。straightening → Yoneda・前層。twisted arrow・Hom 関手は α2b と分担。

## 引き継ぎ（2026-10-19）

### 現在地

- F1a〜F1c の fibration・transport・coherent nerve の基盤を提供済み。F1d は未完了。
- left fibrations と strict transport の像の coherent nerve の同値、strict Kan 図式と有限鎖の nerve 上の coherent 図式の復元は関手同型まで構成済み。
- weighted nerve の豊穣な標準単位は各成分で単射かつ同値。単位に沿う strict な比較の制限は
  trivial Kan fibration、延長空間は可縮。strict transport の像で同値な厳密な左逆も存在する。
- 底と図式の共同実現で、`kanDiagramRealization C` と `weightedNerveInfinityMap C ≫ leftStraighteningCoherentMap C` の大域的な関手同型を構成済み。
- 表現を `LeftTransportRepresentation` に束ねた。任意の底変換は底側と全空間側の両射を厳密に保ち、
  両射の一致は表現の一致と同値。通常の nerve 上の小さい left fibration の実際の表現も構成済み。
- 射影の各次数の fiber が小さい場合、任意の底・パラメーターで単射に沿う境界固定延長と延長空間の可縮性を証明済み。任意の cartesian な全空間表示への厳密な延長にも適用済み。
- 可換四角形全体を関手空間の引き戻し `transportSquareSpace p` として構成。
  分類図式への射影は left fibration、固定図式上の fiber は相対関手空間と同型。
  表現を表す頂点の全部分複体 `transportWitnessSpace p` は Kan 複体。
  実際の表現との頂点全単射、任意の底変換への制限、頂点での厳密な制限の回収を証明済み。
- 単射への表現空間の制限は Kan fibration、inner anodyne なら trivial Kan fibration
  （Lemma 5.6.8.10 の空間値版）。指定表現の厳密な延長と、その延長空間の可縮性を証明済み。
  全頂点を被覆する制限は表現条件を反映する。小さい次数 fiber の一般の底上の表現空間は可縮。
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
  任意の底・小さい次数 fiber の分類図式と比較を構成。指定した単位変換の実際の射は余単位の逆であり、両者の底変換の自然性と普遍比較の実際の成分との一致を証明済み。族の制限の自然性と余単位の整合性も全高次パラメーターで証明済み。
  任意の相対射の collage は区間と底の積上の left fibration。一般の二表現の相対射の族の復元と一意性、相対関手空間全体から分類図式の変換空間への実際の比較射を構成済み。底が ∞ 圏の場合、一般の比較射の同値性を実際の前後合成との可換同型から証明済み。任意の底で、恒等射の族を恒等変換の族へ送る関手同型と、恒等変換のパラメーター制限の厳密な可換性も証明済み。全高次パラメーターで合成三角形を構成し、実際の相対豊穣合成の像を長辺と関手同型で比較した。指定三角形を保った同じ比較も証明済み。任意の inner anodyne な面で、空間値図式と pointed 比較を共同で延長し、部分パラメーター上の既存の両図式を厳密に保つ定理も証明済み。固定図式の面の lift 射影は trivial Kan fibration、各 fiber は可縮。標準表現上では元の unstraightening 比較射が明示的な逆。元の unstraightening の写像空間比較の同値性は任意の底で証明済み（区間・pinched 模型、小さい場合は宇宙縮小後とも）。
- 全 left fibrations 上で切断の頂点評価・部分図式への制限を豊穣比較から coherent な辺に実現。left anodyne な始点評価・制限は大域的な関手同型。
  底の一本の辺に沿う全対象の実際の transport の辺・prism と厳密な両端、切断の始点・終点評価による特徴づけを構成済み。
- 任意の小圏で添字付けた豊穣比較の図式を KanEnrichedDiagram として coherent に実現。任意の添字関手の制限（面・退化を含む）と厳密に可換。合成三点図式の三面は既存の比較の族と厳密に一致。既存の比較の辺そのものの合成三角形と合成等式を証明済み。全対象の transport も底の三角形の合成則・既存三辺の二単体・退化辺の単位則を証明済み。
- 全単体の共同切断評価 `transportSimplexSectionInfinity` と、単体圏の nerve から底への初頂点写像を構成済み。初頂点写像は底の射に自然で全頂点を被覆し本質的全射。
  共同切断評価の添字制限は厳密に可換。宇宙を揃えた両写像の指定辺の反転条件と、標準単体上の厳密な切断・自然比較・全次数の prism を構成済み。反転関手の全パラメーターで比較を同型へ束ね、標準単体上の IsLocalization を明示的な逆で証明済み。底の部分複体の単体圏の nerve を初単体の所属で記述した部分複体と厳密に同定。共通部分・合併・逆像と可換で、部分複体の bicartesian な分解は実際の nerve の pushout となる。反転関手の底への制限は厳密な反変図式をなし、局所化比較は全ての底・面・退化に自然。射列を作用素の列と最初の単体の依存和へ厳密に分解し、底の任意の射と可換な全単射を構成済み。任意の底の pushout は実際の単体圏の nerve の pushout へ写り、反転関手の制限は全次数の pullback をなす。底の単射は nerve でも単射で、反転関手の制限は標的が ∞ 圏なら inner fibration。反転条件は coherent な関手同型で不変。同型不変な全部分複体への可逆 path の復元は元の族を厳密に保つ。単射への制限の相対可逆 path 写像は両端とも trivial Kan fibration であり、その制限に沿う同値の引き戻しも証明済み。一般の底への局所化・降下は未証明。
- 対象ビルド3231 jobs、公理監査7202宣言が成功。依存公理は標準3公理のみ。ルート全体は検査対象外。

### 残り（依存順）

見積もりは再開後の実作業時間の粗い幅で、研究上の障害による上振れがある。

1. 次数 fiber の小ささを essentially small な ∞ 圏的 fiber のみの条件へ弱め、相対表現の延長へ一般化する。
   Kerodon Theorem 5.6.5.12、Corollary 5.6.5.15。40〜160時間。
2. 一般の left fibrations の相対射の族を一つの coherent な straightening 関手へ束ね、単位・余単位と随伴の三角恒等式を完成する。
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
- `HasSmallSimplexFibers`、`smallFiberTransportWitnessSpace_isContractibleKan`、`smallFiberTransportWitnessRestriction_trivialKanFibration`
- `exists_small_leftTransportRepresentation_extension`、`exists_small_transportWitnessFamily_lift`
- `FiberTransportFamily`、`parametrizedFiberTransport`
- `leftUnstraighteningMappingFiberHom_parametrizedIso`
- `coherentStraighteningCounit`、`coherentStraighteningUnitTransformation_eq_counit_inv`、`transportRepresentationMappingSpaceMap`、`smallFiberLeftStraighteningMappingSpaceMap`、`transportRepresentationUnstraighteningMappingEquivalence`、`kanEnrichedComparisonEdge_compStruct`、`leftFibrationNaturalTransportCompStruct`、`transportSimplexSectionInfinity`、`relativeSectionFirstVertexRestrictionIso`、`transportSimplexFirstVertexMap`、`transportSimplexInitialEdgesLifted`、`transportStandardFirstVertexSection_comp`、`ordinaryComparisonHomotopy`、`transportStandardInvertingDescentIso`、`transportStandardInvertingFamilyIso`、`transportSimplexFirstVertexMap_standard_isLocalization`、`transportSimplexSubcomplexIso`、`transportSimplexNerve_bicart_isPushout`、`transportSimplexLocalizationComparison`、`transportSimplexInvertsEdges_of_isPushout`、`transportSimplexInverting_bicart_isPullback`、`transportSimplexChainEquiv`、`transportSimplexNerve_isPushout`、`transportSimplexInverting_isPullback_of_isPushout`、`transportSimplexInvertingRestriction_innerFibration`、`FunctorIso.invertsEdges_iff`、`fullSubcomplexEquivalencePathLift_map`、`transportSimplexInvertingRestriction_relativePath_trivialKanFibration`

### 依存と提供

- Core、Coherent/Quasicategory、Stable/SliceOpposite、HomotopyLimits、KST/Spectra/FibrationTower*、F1B/FullSubcomplexMapping・SSetPullbackAdjoint・QuillenASliceOpposite・Localization・HomotopyWhiskering・RestrictedPrecomposition・FullSubcomplexFunctorFaithful は読み取り専用。
- 提供界面は上記の fibration・transport、𝒮・Cat_∞、strict transport の比較。
  𝒮・Cat_∞ の極限・余極限は主張しない。F1e〜F1g は α2b/F1B の担当。
- 再開時は F1/README.md の原典照合と方針を維持し、他レーンのファイルは編集しない。

### 未コミット

- F1/、F1.lean、監査スクリプト、計画は所有ファイルのみ指定して保存する。未コミット実装なし。他レーンの変更は保存・巻き戻しを行わない。

### 既知の問題

- F1 のソースに明示的な `ModelCategory SSet` 仮定はない。モデル構造は使わない。
  `Fibration`・`TrivialKanFibration` はホーン・境界に対する持ち上げ性として用いる。
- strict Kan 図式の strict な Hom が一般に Kan とは主張しない。
  局所 strictification は任意の内面制限と可換でも、境界を固定した構成でもない。
- 各 fiber の同値や辺での一致だけでは図式全体の同型・分類を導けない。
  同値の反映は既証明であり、残る一般の単位・充満忠実性の代わりにはならない。反転関手の単射への制限は内ホーン・相対可逆 path の持ち上げを持つが、複数の対象を同時に置換する局所化比較の立方体と transfinite な貼り合わせは別途証明する。
- 任意の単射の境界固定延長と高次パラメーターの同時持ち上げは、射影の各次数の fiber が小さい場合に証明済み。
  任意の底上の coherent 空間値図式の unstraightening にも底・パラメーターの小ささを仮定せず適用済み。
  各次数の fiber の小ささを essentially small な ∞ 圏的 fiber のみの条件へ弱める相対延長は未証明。
- 単位・余単位の成分と底変換の自然性は証明済み。一般の left fibrations 全体への coherent な straightening の組み立て・随伴の三角恒等式は未証明。

### 次の一手

相対 path の持ち上げを持つ制限の pullback 比較で、span の三対象を同時に同値で置換する立方体の比較を証明する。セル付加の局所化比較に適用し、transfinite な付加と宇宙を揃えた初頂点写像・共同切断評価の降下へ進む。
TransportSimplexLocalizationData に宇宙を揃えた両写像の反転条件を用意済み。標準単体では任意の同じ宇宙の標的 quasicategory に対する局所化普遍性を証明済み。共同切断評価の一般の底 B への降下、高次一意性、既存 transport との比較は未証明。部分複体の nerve の pushout と標準単体上の普遍性だけから一般の底の結論は導かない。一般のセル付加での厳密な pullback は証明済み。可逆比較の相対持ち上げと単射への制限に沿う同値の引き戻しは証明済み。局所化比較の立方体全体での同値性と transfinite な付加への拡張は未証明。
全対象での高次整合性・三角恒等式、essentially small な fiber への宇宙の一般化、Cat_∞ 値版は残る。
全体の正本は [foundations.md](foundations.md)。F0 は [infinity-core.md](infinity-core.md)（レーン α）の成果を読み取り専用で使う。

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
