# P レーン：presentable ∞ 圏（HTT 5.4〜5.5）

> **v2 の位置づけ（2026-10-23 新設）**：foundations.md §2 の P、§6 の P。F1 の Ind_κ（F2/Ind）、N の冪等完備化と compact（F2/Idempotent、F2/Compact）、
> F1 の前層の極限・余極限、F1b の Kan 拡張と反射的局所化を読み取り専用で使う。第 I 段の到達点には不要で、第 II 段（BS-7 の animated 環、降下）の先行投資。

## 引き継ぎ（2026-10-23）

### 現在地
- 工程 (1) の定義・Ind iff・関手・濃度変更の主経路を実証。κ-accessible を「正則 κ・小さい κ-filtered 余極限・小さい κ-compact 全部分生成圏」で定義。
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
- 濃度変更の十分条件 `IsCardinalChangeBound κ μ` を κ < μ と全冪の評価で定義。
  任意の指定上限を超える正則 μ の存在、小さい濃度族に共通の μ の存在を証明。
- κ-filtered poset を、μ-small な κ-filtered 部分集合の μ-filtered な族で被覆。
  族と各部分集合の nerve の filtered 性は、元の全 coherent な試験図式について成立。
  部分集合の nerve は全非退化単体を数える `IsKappaSmall μ` も満たす。
- 元の任意の μ-small coherent nerve 図式を、小さい κ-filtered 部分 poset へ厳密に因子化。
  全単体での回収、包含による遷移との整合性、部分 nerve の厳密な図式と通常の SSet 余極限を証明。
  宇宙 u+1 の元の標的図式への合成も厳密に回収し、各 filtered 部分図式の native な余極限の存在へ接続。
- 部分添字と対象の全空間の値射影の right cofinal 性を証明し、元の全余錐の制限の余極限性を保存・反映。
  部分射影への coherent な左 Kan 拡張と全単位変換を構成し、元の各部分余極限を同じ指定値そのものとして回収。
- 同じ部分余極限族の μ-filtered 余極限から、元の全表示の指定頂点そのものを回収。
  既存の二つの余極限を一点への Kan として比較し、指定単位の Hom 普遍性の合成で頂点同型を構成した。
  `exists_filteredPartialPresentation` は任意の小さい κ-filtered ∞ 添字を扱い、全項を元の図式の
  μ-small κ-filtered 制限の余極限として保持する。元の図式を通常の nerve に限定しない。
- 非可算正則 μ について、μ-small 形状の全単体と単体圏の全射の個数を同じ μ で評価。
  通常の SSet の μ-presentability、境界を保つ strict 因子化、積の μ-small 性と内部 Hom の μ-filtered 保存を証明。
  Type と SSet の通常の μ-small 極限と μ-filtered 余極限の交換を証明。Space の poset 形状の全 coherent 交換へ接続。
- Kan 値 strict 錐の native 極限性の比較射による iff と保存性を証明。F1 の分類で全錐族を同時 strict 化し、元の全脚を読み戻す。
- 同時 strict 化した全錐族の余極限と元の strictCoherentConeMap を全脚で比較。WithInitial の元の錐の比較の全自然性から同じ strict 余極限錐の native 極限性を証明。
- **小さい poset の極限と、一般の μ-filtered ∞ 添字の coherent 全錐族の指定点ごとの余極限の交換を証明。**
  cofinal μ-filtered poset への元の全余錐の制限で一般添字へ拡張。元の図式・全錐・指定余錐を量化し、交換を仮定に入れない。
- 正則濃度・κ-small 性・κ-filtered 性の宇宙移送、μ-filtered 全錐反映を証明し、小さい poset 余極限の μ-compact 閉性を証明。
- 元の小さい生成圏の μ-small poset 図式を宇宙 u の一つの符号型へ移し、共通の小さい μ-compact 余極限族を選択。
  各指定対象の厳密な全表示の全項はこの族の一項と頂点同型を持つ。Ind 内の小さい頂点族上の全部分複体は全次数で小さい。
- 小さい全部分模型と同型飽和の全同値を構成し、全表示を小さい生成圏へ移送。元の指定頂点を厳密に保持。
  `IsKappaAccessible.of_cardinalChangeBound` により圏自身の μ-accessibility を証明。任意の上限超えと小さい族の共通濃度も実証。
- 工程 (2) の `IsPresentable` を accessibility と全小余極限で定義。前層・空間の全小余極限と全小極限を提供。
  全同値による presentable 性の保存・反映と、小余極限を持つ Ind 模型による特徴づけを証明。
- 非可算正則 μ と μ-small Kan 始点の全 Hom の μ-filtered 保存を証明。終対象上の相対 Hom と N の大きい共変 Hom の全自然比較から μ-compact 性を実証。
- 任意の小さい空間族の共通 compact 濃度を証明。有限単体集合始点の全 Hom の filtered 保存と Kan 置換との全自然同型から、有限模型の Kan 置換の compact 性も実証。
- 各指定 Kan 空間を、有限部分複体の Kan 置換の filtered 全余極限として回収。全項は compact、元の指定頂点は厳密な等式。
- 有限模型を `FintypeCat.Skeleton` 値の図式で宇宙 u の共通族へ符号化し、小さい compact 全部分生成圏を構成。
  `space_isKappaAccessible_aleph0` と `space_isPresentable` を実証。一般の前層の accessibility は未証明。
- 独立集約ビルド成功（7732 jobs）、公理監査 731 宣言で標準三公理のみ。主経路の ModelCategory・追加の同値性 instance なし。

### 工程（依存順）
1. accessible ∞ 圏：定義・Ind による iff・accessible 関手・同値不変性・正則濃度変更を証明。工程 (2) へ進む。
2. 定義・同値不変性・空間の presentable 性を実証。一般の前層・条件を明示した Indκ(C) の presentable 性と局所小ささは未完。
3. presentable の小さい極限・余極限（5.5.2.4、5.5.3.13）。
4. 随伴関手定理：余極限を保つ関手は左随伴、accessible かつ極限を保つ関手は右随伴（5.5.2.9）。
5. Pr^L と Pr^R の双対性（5.5.3.4）。
6. Bousfield 局所化の存在（5.5.4.15）：N の `IsLocalObject`・`localEquivalences`・強飽和性・条件付き反射（HomotopyLimits）を再利用し、局所置換の存在を証明する。
7. P_Σ の普遍性と sifted 余極限による生成（5.5.8.14〜15）：N の `SigmaPresheafInfinity`・sifted 閉性・Yoneda の因子化を再利用する。

### 依存と提供
- 読み取り専用：`F2/Ind/`（F1）、`F2/Idempotent/`・`F2/Compact/`・`HomotopyLimits/`（N）、`F1/`、`F1B/`、`Core/`、`Stable/UniverseJoinSimplexShapes`・`UniverseHorns`（宇宙同型）。
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
- `coherentCardinalFilteredLimitExchange_poset`、`isKappaFiltered_ulift`、`isMuCompact_smallPosetColimit`
- `IsKappaAccessible.exists_muCompactPresentation`、`IsKappaCompactGenerating.exists_smallFamilyPresentation`
- `SmallPosetDiagramCode`、`exists_smallPosetColimitGeneratorIso`、`small_fullSubcomplexOnRange`
- `IsKappaAccessible.of_cardinalChangeBound`、`IsAccessible.exists_larger`、`exists_common_accessibilityCardinal`
- `IsPresentable`、`smallKanObject_isKappaCompact`、`finiteKanReplacement_isCompact`、`space_isPresentable`

### 未コミット
- なし。工程 (2) の検証済み区切りを所有ファイルのみ保存。

### 既知の問題
- 濃度変更は `IsCardinalChangeBound κ μ` と μ の正則性の下で実証。κ ≤ μ だけによる単調性は主張しない。
- 工程 (2) の「Ind の presentable 性」は任意の小さい A に対しては成立しない。適切な小余極限の条件を明示して定理化する。

### 次の一手
- 工程 (2)。F1 の `LeftFibrationInfinity` と N の相対 Hom の全共変比較を使い、一般の小さい底上の前層へ進む。
  有限な底上の単体模型の共通族・left fibration 置換・filtered 全表示・compact 性を構成して、小さい生成圏を得る。前層の accessibility は未証明。
  任意の小さい A の Indκ(A) を presentable とせず、小余極限の必要な条件を明示する。

## 規約
- 配置 `SerrePositivity/InfinityCategories/F2/Presentable/`、集約 `F2/Presentable.lean`、監査 `scripts/audit_infinity_presentable.lean`。
- foundations.md §8 の共通規約。他レーンのファイルは変更しない。`ModelCategory SSet` 等の instance 仮定を主経路に入れない。宇宙は F2/Ind の規約（Ind と標的は u+1、添字は u）に合わせる。
