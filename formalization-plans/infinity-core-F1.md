# F1：fibration・straightening・Yoneda（レーン α2）

> **v2 の位置づけ（2026-10-22 10:10 変更）**：foundations.md §6 の F1。第 I 段は F1-4 → F1-5 → F1-3b。Cat∞ 値の一般底分類は第 II 段。

## 引き継ぎ（2026-10-22）

### 現在地

- 空間値 straightening は一般の小さい quasicategory 上で完了。単位・余単位・三角恒等式の明示構成は任意。
- F1-2 は完了：前層 ∞ 圏・制限・評価・定値前層、right fibration 分類、Yoneda の構成・充満忠実性。
- Cat∞ 値分類の第 I 段の区切りは、全有限単体底での同じ分類主写像の同値。
  `cocartesianStraighteningCoherentMap_finite_isQCatEquivalence`（06:21）。一般底の分類は未完了。
- 一般底に向けた検証済み作業は `dc768ab4b` まで保存。二次元標準境界の coherent 比較は同値で、
  元の大域作用との指定同型まで構成した。集約ビルド 7277 jobs、公理監査 15838 宣言、標準三公理のみ。
- **F1-4 進行中**：小さい前層図式の余極限の存在・元の評価による保存・検出を証明。
  極限は各点の存在を明示した構成・保存・検出まで。形状ごとの F2 の空間値極限条件との接続も証明。
- 表現可能前層は、像の極限の存在のもとで任意の形状の元の極限全錐を保存する。
  有限性・離散性は使わない。一般の小さい空間値極限の存在は未解決。
- 一般形状の全切断を小さい Kan 対象に束ね、元の底を保つ普遍的評価を構成した。
  `coherentConstantSourceMap_isQCatEquivalence` は、定値図式からの元の全変換を
  pointed fiber から全切断への内部 Hom と比較する同値。任意の底・全高次パラメータで成立。
- `coherentSmallConstantSourceMap_isQCatEquivalence` は同じ比較を元の小さい空間の値へ正規化。
  全切断の恒等射を表す変換と比較同型を選び、`coherentDiagramSectionsCone` へ実現した。
  元の図式・全切断の頂点・全円柱の両端固定比較を保持。極限性の証明は残る。
- `coneTransformationMap_isQCatEquivalence` は native な頂点固定の全錐から、
  同じ定値始域の変換への実際の標準比較の同値性。全円柱の厳密な因子分解で証明。
  fat 錐側は `fatConeTransformationIso` で厳密に同型。任意の形状・全パラメータを保持。
- 元の錐の全 Hom 作用を同じ三角形で表し、三辺と両端固定の最小値変形を照合。
  `conePointHomNativeCompositionIso` で、元の標準比較の像を同じ二変換の実際の相対合成へ戻した。
- 実現した錐の標準変換を元の指定変換へ戻す全ホモトピーも構成。
  `coherentSectionsConeIdentityIso` はその小さい全切断への像を元の恒等射と比較する。

### 残り（依存順）

1. **F1-4**：P(C) の小さい極限・余極限を各点から構成、評価による保存・検出。
   HTT 5.1.2.2–5.1.2.4。F2・N の𝒮の界面を読み取り専用で使用。8〜24時間（暫定）。
2. **F1-4**：表現可能前層と極限の交換。HTT 5.1.3.2。4〜12時間（暫定）。
3. **F1-5**：表現可能関手による極限の特徴づけ。HTT 5.1.3.2。8〜24時間（暫定）。
4. **F1-3b**：Hom : Cᵒᵖ × C → 𝒮 の二変数関手化。Kerodon 8、HTT 5.1.3。8〜24時間（暫定）。
5. **第 II 段**：Cat∞ 値分類の一般底・宇宙への拡張。Kerodon 5.6。一般充満忠実性まで36〜80時間（暫定）、本質的全射性等は別途。

### 主要宣言（名前のみ）

- `leftStraighteningInfinityMap_isQCatEquivalence`、`leftStraighteningInfinityEquivalence`
- `HasEssentiallySmallFibers`、`exists_essentiallySmall_leftTransportRepresentation_extension`
- `RightFibrationInfinity`、`rightStraighteningInfinityEquivalence`、`rightUnstraighteningInfinityMap`
- `PresheafInfinity`、`presheafInfinityEvaluation`、`presheafInfinityRestriction`
- `yonedaInfinityMap`、`representablePresheafInfinity`、`representablePresheafValueEquivalence`
- `yonedaInfinityMap_isFullyFaithful`、`yonedaPresheafEvaluation_isQCatEquivalence`
- `cocartesianStraighteningCoherentMap_finite_isQCatEquivalence`
- `cocartesianTwoBoundaryCoherentHomComparison_isQCatEquivalence`
- `cocartesianTwoBoundaryCoherentHomComparison_originalIso`
- `presheafInfinity_hasColimit`、`presheafInfinity_isColimit_iff_evaluation`
- `presheafInfinity_hasLimit_of_evaluation`、`presheafInfinity_isLimit_iff_evaluation`
- `presheafInfinity_hasLimit_of_spaceLimitsOfShape`
- `representablePresheafInfinity_isLimit_of_hasLimit`
- `coherentSpaceSectionsObject`、`coherentSpaceSectionsEvaluation`
- `relativeFunctorExponentialIso`、`coherentConstantSourceMap_isQCatEquivalence`
- `coherentSmallConstantSourceMap_isQCatEquivalence`、`coherentSectionsIdentityRepresentation`
- `coherentDiagramSectionsCone`、`coherentDiagramSectionsCone_vertex`
- `coneTransformationMap_isQCatEquivalence`、`fatConeTransformationIso`
- `conePointHomNativeCompositionIso`

### 依存と提供

- F0・Coherent・Stable・F1B・F2・HomotopyLimits は読み取り専用。
- F1-4・F1-5 は F1b の F2N-2（Ind）・F2N-3 へ提供。Cat∞ 値一般分類は第 I 段の利用者なし。
- 所有は F1/、F1.lean、audit_infinity_f1.lean、本計画のみ。他レーン不変。
- 新規 sorry・公理・未証明引用なし。主経路に同値性や ModelCategory の追加 instance 仮定なし。

### 未コミット

- なし。通る所有ファイルを集約・監査とともに `git commit --only` で早めに保存する。

### 既知の問題

- 有限単体の分類同値から、一般底の分類同値は結論しない。標準境界は一般に nerve ではない。
- 前層は宇宙 u+1、底と小さい形状は宇宙 u。𝒮 の大きい任意形状の極限・余極限は主張しない。
- 全局所 Hom の比較と元の大域作用の比較を区別し、指定同型の共有境界像を保持する。
- F1-4 の未解決点は `∀ {B : SSet.{u}} (F : ulift B ⟶ SpaceInfinity.{u}), HasLimit F`。
  F2・N の検索では小余極限の一般存在、空・単体・積・引き戻し・塔の極限まで確認した。
  `F2.HasSpaceLimitsOfShape B` は条件の定義であり、任意 B での証明ではない。
  この条件を新しい公理や instance 仮定として主経路に置かず、native な極限錐への接続を残す。

### 再開点（第 II 段、3行）
1. `dc768ab4b`：有限二単体の coherent 境界比較の同値と、元の大域作用への `cocartesianTwoBoundaryCoherentHomComparison_originalIso` まで保存済み。
2. 次は同じ比較を任意の底の二次元セルへ移し、局所比較の自然性と指定境界値の fiber 比較を揃える。
3. その後は高次境界・有限セル・骨格降下で一般充満忠実性を閉じ、本質的全射性・一般底・宇宙へ進む。

### 次の一手

`coherentDiagramSectionsCone F` の全試験空間での Hom 比較に
`coneTransformationMap F z` と `coherentSmallConstantSourceMap F z` を合成する。
同じ錐の標準変換と定値図式の全 Hom 作用との相対合成への比較は構成済み。
実現した錐の標準変換と指定恒等射の比較は `coherentSectionsConeIdentityIso` で構成済み。
次はこの指定同型を全試験空間の Hom 作用へ移し、同じ実際の合成の同値性を示す。
錐の実現が保持する全円柱・両端固定比較を使い、元の比較射の同値性から native な極限性を結論する。
F2 の `CoconeFiberColimitCriterion`・全空間の指定単位の追跡は読み取り専用の双対設計の参考。
その後、各点存在を解消して F1-4 を閉じ、F1-5・F1-3b へ進む。

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
