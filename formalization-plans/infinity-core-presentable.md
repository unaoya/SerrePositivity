# P レーン：presentable ∞ 圏（HTT 5.4〜5.5）

> **v2 の位置づけ（2026-10-23 新設）**：foundations.md §2 の P、§6 の P。F1 の Ind_κ（F2/Ind）、N の冪等完備化と compact（F2/Idempotent、F2/Compact）、
> F1 の前層の極限・余極限、F1b の Kan 拡張と反射的局所化を読み取り専用で使う。第 I 段の到達点には不要で、第 II 段（BS-7 の animated 環、降下）の先行投資。

## 引き継ぎ（2026-10-23）

### 現在地
- 工程 (1) 進行中。κ-accessible を「正則 κ・小さい κ-filtered 余極限・小さい κ-compact 全部分生成圏」で定義。
  生成は各対象を厳密な頂点とする単一の全余錐表示。Ind との同値・比較の充満忠実性は定義に入れていない。
- 正則 κ の `IndInfinity κ A` の κ-accessibility を証明。F1 の単一 filtered 表示の同じ全余錐を Ind 内へ持ち上げ、N の Yoneda compact 性と合成。
- κ-accessible 関手は Ind の native な小さい κ-filtered 余極限保存を再利用。恒等・合成・濃度の単調性・全関手同型不変性を証明。
- 全 κ-compact 対象が生成対象の retract であることと、その逆を証明。元の生成族・対象を保持。
- 定義の小さい生成圏から κ-連続な Ind 比較を構成し、生成関手の全自然同型による回収・本質的全射性を証明。
  **元の任意の二対象間の `pinchedHomMap` の同値性・比較自身の全充満忠実性・全 ∞ 圏同値を証明。**
  `IsKappaAccessible.exists_indRepresentation` は定義の小さい compact 生成圏と κ-連続同値を回収。
  同値の順射は元の比較関手そのもの。`exists_indEquivalence` は小さい A の Indκ(A) との明示的な同値の存在。
- **同値不変性と Ind による完全な必要十分条件を証明。** 正則性を明示し、任意の指定 Ind 同値からも定義の accessibility を回収。
  `isKappaAccessible_iff_indEquivalence`・`isAccessible_iff_indEquivalence` は小さい A、Indκ(A) と標的が u+1 の規約を保持。
  全余錐の同値による保存・反映、小さい κ-filtered 余極限の存在、compact 性、同じ小さい生成圏の全表示を輸送。
  表示の頂点は同値類だけでなく指定対象そのものへ厳密に戻す。
- accessible 関手の全自然同型不変性、両側の同値による共役不変性を証明。同じ κ の保存性と存在量化版の両方。
- 元の全共変 Hom・coslice 比較を構成し、その自然性・評価式・`pinchedHomMap` との同値判定を提供。
- 関手圏の元の全比較の可逆成分条件を、両側が保存する同じ余極限・極限の頂点へ延長。
  共変 Hom の余極限・極限保存と元の余錐の反転式から、Ind の両変数の単一表示を通じて上記の全充満忠実性を得た。
- 濃度変更の十分条件 `IsCardinalChangeBound κ μ` を κ < μ と全冪の評価で定義。
  任意の指定上限を超える正則 μ の存在、小さい濃度族に共通の μ の存在を証明。
- κ-filtered poset を、μ-small な κ-filtered 部分集合の μ-filtered な族で被覆。
  族と各部分集合の nerve の filtered 性は、元の全 coherent な試験図式について成立。
  部分集合の nerve は全非退化単体を数える `IsKappaSmall μ` も満たす。圏の濃度変更自身は未証明。
- 元の任意の μ-small coherent nerve 図式を、小さい κ-filtered 部分 poset へ厳密に因子化。
  全単体での回収、包含による遷移との整合性、部分 nerve の厳密な図式と通常の SSet 余極限を証明。
  宇宙 u+1 の元の標的図式への合成も厳密に回収し、各 filtered 部分図式の native な余極限の存在へ接続。
- 部分添字とその対象の全空間を構成。値射影の各上方 comma の κ-filtered 性を証明し、
  F1B の comma 比較・Quillen A から同じ値射影の right cofinal 性を証明。
  宇宙 u+1 の元の全余錐の全空間への制限は余極限性を保存・反映する。
  全空間の同じ図式を指定 fiber へ制限すると、元の部分図式そのものを厳密に回収する。
- 部分添字射影の各左 Kan 局所添字の κ-filtered 性を証明。N の宇宙同型と F1B の局所存在定理から、
  一つの全単位変換を持つ coherent な左 Kan 拡張を構成。fiber の局所比較の right cofinal 性も証明。
  `exists_smallPartialColimitFamily` は元の全図式の各部分余極限を、延長の指定値そのものを頂点として回収する。
- 同じ部分余極限族の μ-filtered 余極限から、元の全表示の指定頂点そのものを回収。
  既存の二つの余極限を一点への Kan として比較し、指定単位の Hom 普遍性の合成で頂点同型を構成した。
  `exists_filteredPartialPresentation` は任意の小さい κ-filtered ∞ 添字を扱い、全項を元の図式の
  μ-small κ-filtered 制限の余極限として保持する。元の図式を通常の nerve に限定しない。
- 非可算正則 μ について、μ-small 形状の全単体と単体圏の全射の個数を同じ μ で評価。
  通常の SSet の μ-presentability、境界を保つ strict 因子化、積の μ-small 性と内部 Hom の μ-filtered 保存を証明。
  Type と SSet の通常の μ-small 極限と μ-filtered 余極限の交換を証明。全 coherent な Space の交換は未証明。
- weighted sections・小さい poset の Bousfield–Kan 模型の strict 連続性と、錐族の比較の弱同値保存を証明。元の全脚を保持。
- 任意の内部 Hom と weighted sections の全自然な交換同型と、元の錐の比較射との整合性を証明。
- Kan 値の strict 錐の native な極限性の比較射による iff と、小さい poset 上の strict 極限錐族の μ-filtered 保存を証明。
- F1 の実際の分類から、任意の小圏上の図式・積添字上の族・全錐族の同時 strictification を証明。元の図式への包含も保持。
- WithInitial の共同図式から元の頂点・脚・自然変換を読み戻し、既存の保存界面の段階錐との厳密な一致も証明。
- 同時 strict 化した全錐族へ元の点ごとの余極限を、指定頂点の等号を保持して輸送。各段階の極限性も保存・反映。
  同じ族の錐形状による実現と読み戻した N の strict 錐との全単体の照合、およびその余極限族の同定は未完。
- 独立集約ビルド成功（7651 jobs）、公理監査 427 宣言で標準三公理のみ。主経路の ModelCategory・追加の同値性 instance なし。

### 残り（依存順）
1. accessible ∞ 圏：濃度変更・必要な基本性質（HTT 5.4.2〜5.4.4）。定義・Ind による iff・同値不変性は完了。16〜40 時間（暫定）。
2. presentable の定義、前層 ∞ 圏・Ind_κ(C) の presentable 性（5.5.1.1、5.5.1.8）、局所小ささ。
3. presentable の小さい極限・余極限（5.5.2.4、5.5.3.13）。
4. 随伴関手定理：余極限を保つ関手は左随伴、accessible かつ極限を保つ関手は右随伴（5.5.2.9）。
5. Pr^L と Pr^R の双対性（5.5.3.4）。
6. Bousfield 局所化の存在（5.5.4.15）：N の `IsLocalObject`・`localEquivalences`・強飽和性・条件付き反射（HomotopyLimits）を再利用し、局所置換の存在を証明する。
7. P_Σ の普遍性と sifted 余極限による生成（5.5.8.14〜15）：N の `SigmaPresheafInfinity`・sifted 閉性・Yoneda の因子化を再利用する。

### 依存と提供
- 読み取り専用：`F2/Ind/`（F1）、`F2/Idempotent/`・`F2/Compact/`・`HomotopyLimits/`（N）、`F1/`、`F1B/`、`Core/`、`Stable/UniverseJoinSimplexShapes`（宇宙同型）。
- 提供先：第 II 段の BS-7（animated 環）、降下理論、K 第 II 段。

### 主要宣言
- `IsKappaAccessible`、`IsAccessible`、`IsKappaCompactGenerating`、`HasKappaFilteredGeneratorPresentation`
- `IsKappaAccessibleFunctor`、`IsAccessibleFunctor`、`indYoneda_isKappaCompactGenerating`、`indInfinity_isKappaAccessible`
- `IsKappaCompactGenerating.compact_iff_retract`、`IsKappaAccessible.exists_indComparison`
- `pinchedHomMap_equivalence_of_source_colimit`、`indComparison_isFullyFaithful`、`indComparisonEquivalence`
- `IsKappaAccessible.exists_indRepresentation`、`IsKappaAccessible.exists_indEquivalence`
- `isKappaAccessible_iff_indEquivalence`、`isAccessible_iff_indEquivalence`
- `isKappaAccessibleFunctor_iff_equivalence_conjugate`、`isAccessibleFunctor_iff_equivalence_conjugate`
- `IsCardinalChangeBound`、`exists_regular_cardinalChangeBound_family`
- `SmallFilteredPieces`、`exists_smallFilteredPiece_containing`、`smallFilteredPieces_cover`
- `smallFilteredPieces_nerve_isKappaFiltered`、`smallFilteredPiece_nerve_properties`
- `exists_smallFilteredPiece_factorization`、`nerveSubsetLift_transition`
- `SmallFilteredTotal`、`smallFilteredTotalValue_isRightCofinal`
- `smallFilteredTotal_restrict_isColimit_iff`、`smallFilteredTotalDiagram_restrict_fiber`
- `smallPiece_leftKanShape_isKappaFiltered`、`smallPiece_exists_leftKanExtension`
- `smallPieceFiberKanComparison_isRightCofinal`、`exists_smallPartialColimitFamily`
- `leftKan_colimitVertexIso`、`exists_smallPartialColimitPresentation`、`exists_filteredPartialPresentation`
- `strictConeFamilyStage_recovered`、`strictConeFamilyColimit_isLimit`
- `spaceDiagramStrictificationIso`、`spaceFamilyStrictificationIso`、`coneFamilyStrictificationIso`
- `kanCone_isLimit_iff_bousfieldKanComparison`、`coneFamilyStrictColimitCocone_pointwise`、`coneFamilyStrictColimitCocone_vertex`

### 未コミット
- なし。工程 (1) の最初の検証済み区切りを所有ファイルのみ保存。

### 既知の問題
- accessible 圏の濃度変更は未証明。κ ≤ μ だけで単調性を結論せず、必要な正則性・濃度条件を保持する。
- 既存の有限 coherent 交換界面も条件付き。これを仮定せず、P で μ-small 版の実証拠を構成する。
- 工程 (2) の「Ind の presentable 性」は任意の小さい A に対しては成立しない。適切な小余極限の条件を明示して定理化する。

### 次の一手
- 工程 (1) の濃度変更。錐形状で実現した WithInitial の段階図式を N の strictCoherentCone と全単体で照合する。
  同じ native な μ-filtered 交換を証明し、μ-small 部分余極限の μ-compact 性を N の Hom 錐族で導く。
  単に各生成対象が μ-compact であることだけでは μ-filtered 表示を与えない。元の全図式・表示の小ささを保持する。
  元の指定頂点の μ-filtered 全表示は完了。μ-compact 性と、対象に依存しない小さい生成圏は未証明。
  その後、工程 (2) の presentable の定義と前層の presentable 性へ進む。

## 規約
- 配置 `SerrePositivity/InfinityCategories/F2/Presentable/`、集約 `F2/Presentable.lean`、監査 `scripts/audit_infinity_presentable.lean`。
- foundations.md §8 の共通規約。他レーンのファイルは変更しない。`ModelCategory SSet` 等の instance 仮定を主経路に入れない。宇宙は F2/Ind の規約（Ind と標的は u+1、添字は u）に合わせる。
