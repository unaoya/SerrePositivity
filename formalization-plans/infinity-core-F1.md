# F1：straightening・Yoneda・Indκ（旧 α2）

> **v2 の位置づけ（2026-10-23 移管）**：F1-4・F1-5・F1-3b、F2N-2(a)〜(d) は完了。次は F2N-5(a)(b)（Ind の有限存在と安定性、F1b から移管）。(c) compact 生成は完了。Cat∞ 値の一般底分類は第 II 段。

## 引き継ぎ：F2N-5（2026-10-23）

### 現在地

- F2N-2 は `e128b12d4` で完了。独立集約 7245 jobs、公理監査 2974 宣言、標準三公理のみ。
  (a) 任意の前層の表現可能密度、(b) 最小全部分 κ-filtered 閉包と Yoneda 因子化、(c) 単一 κ-filtered 表示、
  (d) 元の制限射 `indKappaContinuousRestriction` 自体の全 ∞ 圏同値と、元の順射を保持する同値データまで。
- **F2N-5(a) 零対象を証明**：`indYoneda_isZero_of_zero` は ℵ₀ ≤ κ のもとで、元の零対象の同じ Yoneda 像が Indκ の零対象であること。
  `ind_hasZeroVertex_of_stable` は正則 κ と小さい安定 C に対する零対象の存在。一般有限極限交換への依存なし。
  始対象側は全表現可能値の可縮性と同型・κ-filtered native 余極限の閉性、終対象側は全評価と全部分包含で証明。
  `indVertex_evaluation_isTerminal_of_initial` は任意の Indκ 前層の元の始対象での評価が空間の終対象であること。
- 現区切り：独立集約 7659 jobs、公理監査 3075 宣言、標準三公理のみ。
- **(b) 交換入力と条件付きの有限錐保存**：`IndFiniteLimitExchangeInput.exchange` は全有限形状 K の
  `F2.CoherentFilteredLimitExchangeShape K`。一般 coherent filtered 図式・指定点ごとの native 余極限と全錐を量化する。
  この構造体の存在証拠は未提供。有限単体だけの既存結果から一般有限形状の交換を完成扱いにしない。
  `indVertex_cone_isLimit_of_exchange` は交換が成り立つ形状の元の極限全錐を、すべての Ind 前層が保存する条件付き定理。
  表現可能前層での極限保存から、全錐上の同型と κ-filtered 閉包で元の Ind 頂点まで拡張した。
  `indObject_finiteColimit_isLimit` は明示交換入力のもとで、C の指定有限余極限の反転全錐の同じ前層による像の極限性。
  `indPresheaf_finiteColimit_smallSectionRestriction_isQCatEquivalence` は同じ全余錐の反転境界に沿う、元の小さい全空間上の切断制限自身の同値。
  同じ right unstraightening の反転全空間の同型と native 全錐の宇宙持ち上げで、底を保持したまま大きい切断制限へ移した。
  `indPresheaf_finiteColimit_yonedaSliceSections_isQCatEquivalence` は、この同じ全比較で元の Yoneda slice の切断制限自身へ同値性を移す。
  `ind_finiteColimit_commaSections_isQCatEquivalence` は厳密な `indLeftKanCommaIso` の反転で、任意の元の Ind 頂点の実際の comma 上の同じ切断制限へ帰還する。
  `indCommaCoslicePullbackIso` は実際の反転 comma と元の同じ対象の coslice の厳密な底変換の同型。元の底射影も厳密に保つ。
  `leftFibrationConeRestriction_baseChange_iff` と全制限自然性で、同じ全錐の像の全係数の coslice 切断制限へ戻した。
  `indYoneda_finiteOppositeCone_isLimit` は元の指定有限余極限の反転全錐の、正規化した反転 Yoneda による像の極限性。
  全係数の `coneSectionRestriction` 判定から証明し、普遍性を仮定していない。交換入力は依然明示する。
  `uliftCoconeReverse_val` は ULift と反転の順の全射の一致。順逆の join 比較と Δ⁰ の形状自然性から証明。
  `indYoneda_finiteColimit_isColimit` は同じ指定元余錐の native な Yoneda 像の余極限性まで帰還。
  Ind の任意の有限図式の余極限存在や安定性は未証明。
- **(c) 完了**：N の `indCompact_retract_yoneda` は同じ元の compact Ind 対象の Yoneda retract 回収を証明済み。
  `compactYoneda_isQCatEquivalence` は正則 κ と冪等完備 C のもとで、元の全 compact Yoneda 自身の同値性。
  `compactGenerationEquivalence` は ULift C ≃ Indκ(C)^κ、`_hom` は同じ順射の厳密な回収。
  `indVertex_has_filteredYonedaPresentation` は任意の元の Ind 頂点そのものを頂点とする、小さい単一 κ-filtered Yoneda 表示。
  生成元の κ-compact 性は N の `Compact.indYoneda_isKappaCompact`。一般有限極限交換や安定性に依存しない。
- `diagramYoneda` は全 coherent 図式に対する同じ Yoneda の作用。`_vertex` は元の全図式の像、
  `_restrict` は形状制限との全次数の厳密な自然性、`_isFullyFaithful` は任意の形状で全写像空間の充満忠実性。
  `diagramComma` と `diagramCommaCocone` は指定元図式への大きい表示添字と、頂点を厳密に保つ標準全余錐。
  射影の right fibration 性・添字の quasicategory 性は証明済み。小ささ・κ-filtered 性・余極限性は未証明。
  `commaFamilyLift` の全射回収・往復・任意の制限自然性を証明。境界を含む元の全変換を保持する。

### 残り（依存順）

1. **(a)** 元の有限 coherent 図式の filtered 表示、有限余極限・有限極限の存在。零対象は済み。HTT 5.3.5.15。16〜40時間（暫定）。
2. **(b)** 有限図式表示と明示交換入力から安定性を証明。F1b の a7 提供後、交換入力へ実証拠を渡す。HA 1.1.3.6。24〜60時間（暫定、提供待ちを含まず）。
3. **(c) 完了**：N の元の retract 回収と合流し、正則 κ・冪等完備 C に対する同じ compact Yoneda の全同値と filtered 生成。HTT 5.3.5.11。

### 主要宣言（名前のみ）

- `IndInfinity`、`indYoneda`、`indInclusionPresheaf`、`ind_isColimit_iff_inclusion`
- `presheafDensityCocone_isColimit`、`isIndVertex_iff_singleFilteredPresentation`
- `indLeftKanExtension_preservesSmallKappaFilteredColimits`、`indKappaContinuousRestrictionEquivalence`、`indKappaContinuousRestrictionEquivalence_hom`
- `IndFiniteLimitExchangeInput`、`representablePresheafValue_isTerminal_of_initial`、`representablePresheaf_isTerminal_of_terminal`
- `indVertex_evaluation_isTerminal_of_initial`、`indYoneda_isInitial_of_initial`、`indYoneda_isTerminal_of_terminal`
- `indYoneda_isZero_of_zero`、`ind_hasZeroVertex`、`ind_hasZeroVertex_of_stable`
- `conePresheafRestriction`、`conePresheafRestriction_isPointwiseColimit`、`indVertex_cone_isLimit_of_exchange`
- `indPresheaf_finiteCone_isLimit`、`indPresheaf_finiteColimit_isLimit`、`indObject_finiteColimit_isLimit`
- `oppositeYonedaSliceProjection`、`oppositeElementsYonedaSliceComparison_projection`、`oppositeElementsYonedaSliceComparison_isPrecompositionEquivalence`
- `indPresheaf_finiteColimit_yonedaSliceSections_isQCatEquivalence`、`oppositeIndLeftKanProjection`、`ind_finiteColimit_commaSections_isQCatEquivalence`
- `indCommaCoslicePullbackIso`、`indCommaCoslicePullbackIso_projection`、`leftFibrationConeRestriction_baseChange_iff`
- `ind_finiteColimit_cosliceSections_isQCatEquivalence`、`indYoneda_finiteOppositeCone_isLimit`
- `joinUniverseReverse_hom`、`joinUniverseReverse_inv`、`uliftCoconeReverse_val`、`indYoneda_finiteColimit_isColimit`

- `compactYoneda_isQCatEquivalence`、`compactGenerationEquivalence`、`compactGenerationEquivalence_hom`
- `indVertex_has_filteredYonedaPresentation`、`diagramYoneda`、`diagramYoneda_isFullyFaithful`
- `diagramComma`、`diagramCommaCocone`、`diagramCommaCocone_vertex`、`commaFamilyLift_eta`、`commaFamilyLift_precomp`

### 依存と提供

- 所有は `InfinityCategories/F2/Ind/`、独立集約 `F2/Ind.lean`、`scripts/audit_f2_ind.lean`、本計画。
- F2 既存ファイル・集約 F2.lean、F2/Idempotent/・F2/Compact/ は読み取り専用。ルート集約を変更しない。
- F2N-1 の filtered・κ-filtered・cofinality と、既存の一般 coherent filtered 余極限の空形状交換を再利用。
- F1b の a7（一般有限極限交換）は進行中。未提供定理を instance 仮定で主経路へ隠さない。
- κ・C・小さい filtered 添字は宇宙 u、Indκ は u+1。有限形状の宇宙移送も実際の図式を保持して扱う。
- 新規 sorry・公理・引用なし。新規モジュール 100 行以内、計画 300 行・引き継ぎ 100 行以内。
- 自分のファイルのみ `git commit --only`。報告後は承認を待たず次へ。

### 未コミット

- なし。図式の充満忠実性・全 comma 族・標準全余錐まで対象ビルドと公理監査を通した区切り。

### 既知の問題

- F2N-5(a)(b) の有限余極限・有限極限・安定性は未証明。零対象だけで (a) 完了とはしない。(c) は完了。
- `IndFiniteLimitExchangeInput` の構成子は一般有限極限交換の証拠を要求する。現在は供給する定理が未提供。
- C の `IsStable` は零対象・fiber/cofiber・零角の判定による定義。有限全形状の存在への公開 API は再確認が必要。追加仮定で回避しない。

### 次の一手

`indYoneda_finiteColimit_isColimit` により、明示交換入力のもとで同じ元の有限余極限余錐を Ind Yoneda が保存することまで完了。
次は有限 coherent 図式 K → Indκ(C) 全体の、元の Yoneda による単一 filtered 表示を構成する。
`diagramYoneda` の全作用・形状自然性・充満忠実性、`diagramComma` と同じ頂点の標準余錐は済み。
次は大きい comma の次数ごとの小ささ。表示図式 a を固定した全変換を、C.op×K×(Δ[n]⋆Δ⁰) 上の Space∞ への射へ展開する。
全頂点値を a の Yoneda 像と指定 D で固定し、`coherentMap_fixedVertices_small` の符号化を利用する。小ささはまだ未証明。
その後 `smallSimplicialSet` の実同型で小さい模型を作り、`commaFamilyLift_precomp` で全境界を保って κ-filtered 性を証明する。
各頂点を別々に表示するだけではなく、元の全単体・辺・境界を保持する一つの図式表示を得る。
κ-filtered 性と元の指定図式を頂点とする全余錐の普遍性は証明すべき結論であり、入力にしない。
C の `IsStable` から有限余極限を得る公開 API は検索で未確認。`Stable/Definition` は有限存在から安定性への十分条件のみ。
不足分を所有内で証明し、その有限余極限と図式表示で元の Ind 図式の native 余極限を構成する。
有限極限と安定性では `IndFiniteLimitExchangeInput` を明示引数にし、交換の証拠を内製しない。
compact 部分は完了済み。N の元の回収・冪等完備性の宇宙不変性と全充満忠実像の retract 回収を用いた。

## F2N-2 の完了界面

- `e128b12d4`：HTT 5.1.5.3、5.3.5.4、5.3.5.10。κ の正則性と宇宙を明示し、追加の同値性 instance 仮定なし。
- 指定左 Kan 延長の同じ全相対 join 族と像について、左右の native 全余錐制限同値から一般保存性へ戻した。
- `indKappaContinuousRestriction_isFullyFaithful`・`_isEssentiallySurjective` と F0 の判定で同値を結論。

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
