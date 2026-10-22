# F1：straightening・Yoneda・Indκ（旧 α2）

> **v2 の位置づけ（2026-10-23 移管）**：F1-4・F1-5・F1-3b、F2N-2(a)〜(d) は完了。次は F2N-5（Ind の安定性と compact 生成、F1b から移管）。Cat∞ 値の一般底分類は第 II 段。

## 引き継ぎ：F2N-5（2026-10-23）

### 現在地

- F2N-2 は `e128b12d4` で完了。独立集約 7245 jobs、公理監査 2974 宣言、標準三公理のみ。
  (a) 任意の前層の表現可能密度、(b) 最小全部分 κ-filtered 閉包と Yoneda 因子化、(c) 単一 κ-filtered 表示、
  (d) 元の制限射 `indKappaContinuousRestriction` 自体の全 ∞ 圏同値と、元の順射を保持する同値データまで。
- **F2N-5(a) 零対象を証明**：`indYoneda_isZero_of_zero` は ℵ₀ ≤ κ のもとで、元の零対象の同じ Yoneda 像が Indκ の零対象であること。
  `ind_hasZeroVertex_of_stable` は正則 κ と小さい安定 C に対する零対象の存在。一般有限極限交換への依存なし。
  始対象側は全表現可能値の可縮性と同型・κ-filtered native 余極限の閉性、終対象側は全評価と全部分包含で証明。
  `indVertex_evaluation_isTerminal_of_initial` は任意の Indκ 前層の元の始対象での評価が空間の終対象であること。
- 現区切り：独立集約 7392 jobs、公理監査 3041 宣言、標準三公理のみ。
- **(b) 交換入力と条件付きの有限錐保存**：`IndFiniteLimitExchangeInput.exchange` は全有限形状 K の
  `F2.CoherentFilteredLimitExchangeShape K`。一般 coherent filtered 図式・指定点ごとの native 余極限と全錐を量化する。
  この構造体の存在証拠は未提供。有限単体だけの既存結果から一般有限形状の交換を完成扱いにしない。
  `indVertex_cone_isLimit_of_exchange` は交換が成り立つ形状の元の極限全錐を、すべての Ind 前層が保存する条件付き定理。
  `conePresheafRestriction_isPointwiseColimit` は同じ全錐上の制限族が元の前層余極限を全単体で点ごとの余極限へ送ること。
  表現可能前層での極限保存から、全錐上の同型と κ-filtered 閉包で元の Ind 頂点まで拡張した。
  `indObject_finiteColimit_isLimit` は明示交換入力のもとで、C の指定有限余極限の反転全錐の同じ前層による像の極限性。
  `indPresheaf_finiteColimit_smallSectionRestriction_isQCatEquivalence` は同じ全余錐の反転境界に沿う、元の小さい全空間上の切断制限自身の同値。
  同じ right unstraightening の反転全空間の同型と native 全錐の宇宙持ち上げで、底を保持したまま大きい切断制限へ移した。
  `oppositeElementsYonedaSliceComparison` は元の密度比較そのものの反転で、元の底射影を厳密に保つ前合成同値。
  `indPresheaf_finiteColimit_yonedaSliceSections_isQCatEquivalence` は、この同じ全比較で元の Yoneda slice の切断制限自身へ同値性を移す。
  `ind_finiteColimit_commaSections_isQCatEquivalence` は厳密な `indLeftKanCommaIso` の反転で、任意の元の Ind 頂点の実際の comma 上の同じ切断制限へ帰還する。
  `oppositeIndLeftKanCommaIso_inv_projection` はこの反転同型でも元の底射影を厳密に保持する。
  `indCommaCoslicePullbackIso` は実際の反転 comma と元の同じ対象の coslice の厳密な底変換の同型。元の底射影も厳密に保つ。
  `leftFibrationConeRestriction_baseChange_iff` と全制限自然性で、同じ全錐の像の全係数の coslice 切断制限へ戻した。
  `indYoneda_finiteOppositeCone_isLimit` は元の指定有限余極限の反転全錐の、正規化した反転 Yoneda による像の極限性。
  全係数の `coneSectionRestriction` 判定から証明し、普遍性を仮定していない。交換入力は依然明示する。
  通常形の native な Yoneda 有限余極限保存へは、ULift と反転の順の全射の一致が残る。Ind の有限余極限の存在や安定性は未証明。
- **(c) 未着手**：N の `Compact.indYoneda_isKappaCompact`、`idemToCompactInd_isQCatEquivalence_of_retracts` は利用候補。
  後者は元の compact Ind 対象の Yoneda retract 回収を入力として要求する。回収を証明済みとは扱わない。

### 残り（依存順）

1. **(a)** 元の有限 coherent 図式の filtered 表示、有限余極限・有限極限の存在。零対象は済み。HTT 5.3.5.15。16〜40時間（暫定）。
2. **(b)** 有限図式表示と明示交換入力から安定性を証明。F1b の a7 提供後、交換入力へ実証拠を渡す。HA 1.1.3.6。24〜60時間（暫定、提供待ちを含まず）。
3. **(c)** compact 対象の Yoneda retract 回収と、冪等完備 C に対する Indκ(C)^κ ≃ C。F2N-4(e)・F2N-3(d) と合流。HTT 5.3.5.11。16〜40時間（暫定）。

### 主要宣言（名前のみ）

- `IndInfinity`、`indYoneda`、`indInclusionPresheaf`、`ind_isColimit_iff_inclusion`
- `presheafDensityCocone_isColimit`、`isIndVertex_iff_singleFilteredPresentation`
- `indLeftKanExtension_preservesSmallKappaFilteredColimits`、`indKappaContinuousRestrictionEquivalence`、`indKappaContinuousRestrictionEquivalence_hom`
- `IndFiniteLimitExchangeInput`、`representablePresheafValue_isTerminal_of_initial`、`representablePresheaf_isTerminal_of_terminal`
- `indVertex_evaluation_isTerminal_of_initial`、`indYoneda_isInitial_of_initial`、`indYoneda_isTerminal_of_terminal`
- `indYoneda_isZero_of_zero`、`ind_hasZeroVertex`、`ind_hasZeroVertex_of_stable`
- `conePresheafRestriction`、`conePresheafRestriction_isPointwiseColimit`、`indVertex_cone_isLimit_of_exchange`
- `indPresheaf_finiteCone_isLimit`、`indPresheaf_finiteColimit_isLimit`、`indObject_finiteColimit_isLimit`
- `oppositeCoconeBoundary`、`indPresheaf_finiteColimit_smallSectionRestriction_isQCatEquivalence`、`leftFibrationConeRestriction_isQCatEquivalence_ulift`
- `oppositeYonedaSliceProjection`、`oppositeElementsYonedaSliceComparison_projection`、`oppositeElementsYonedaSliceComparison_isPrecompositionEquivalence`
- `indPresheaf_finiteColimit_yonedaSliceSections_isQCatEquivalence`、`oppositeIndLeftKanProjection`、`ind_finiteColimit_commaSections_isQCatEquivalence`
- `indCommaCoslicePullbackIso`、`indCommaCoslicePullbackIso_projection`、`leftFibrationConeRestriction_baseChange_iff`
- `ind_finiteColimit_cosliceSections_isQCatEquivalence`、`indYoneda_finiteOppositeCone_isLimit`、`joinReverseIso_inv_app`

### 依存と提供

- 所有は `InfinityCategories/F2/Ind/`、独立集約 `F2/Ind.lean`、`scripts/audit_f2_ind.lean`、本計画。
- F2 既存ファイル・集約 F2.lean、F2/Idempotent/・F2/Compact/ は読み取り専用。ルート集約を変更しない。
- F2N-1 の filtered・κ-filtered・cofinality と、既存の一般 coherent filtered 余極限の空形状交換を再利用。
- F1b の a7（一般有限極限交換）は進行中。未提供定理を instance 仮定で主経路へ隠さない。
- κ・C・小さい filtered 添字は宇宙 u、Indκ は u+1。有限形状の宇宙移送も実際の図式を保持して扱う。
- 新規 sorry・公理・引用なし。新規モジュール 100 行以内、計画 300 行・引き継ぎ 100 行以内。
- 自分のファイルのみ `git commit --only`。報告後は承認を待たず次へ。

### 未コミット

- なし。反転全錐の普遍性まで対象ビルドと公理監査を通し、保存する区切り。

### 既知の問題

- F2N-5 の有限余極限・有限極限・安定性・compact 比較は未証明。零対象だけで (a) 完了とはしない。
- `IndFiniteLimitExchangeInput` の構成子は一般有限極限交換の証拠を要求する。現在は供給する定理が未提供。
- C の `IsStable` は零対象・fiber/cofiber・零角の判定による定義。有限全形状の存在への公開 API は再確認が必要。追加仮定で回避しない。
- compact 側は元の全共変 Hom による定義と追加の宇宙持ち上げを持つ。Ind の native 小さい添字版と厳密に照合する。

### 次の一手

`indYoneda_finiteOppositeCone_isLimit` は元の反転全錐の正規化した反転 Yoneda 像の極限性まで証明済み。
次は `uliftCoconeReverse_val` に相当する全射の等式を証明し、通常の native な像余錐へ戻す。
必要な式は mapJoinCone(uliftOppositeIso X).hom(JoinCone.ulift(kanCoconeReverseCone c)) の全射と、
kanCoconeReverseCone(JoinCocone.ulift c) を (uliftOppositeIso K).hom で制限した全射との一致。
`joinReverseIso_inv_app` は実反転同型の逆射を明示的な切断反転同値の逆へ戻す。失敗中の試行は `/tmp/f1-ind-ulift-cocone-reverse-draft.lean` に保存し、集約外。
`augmentedReversePairUp` で切断表示の順反転と ULift の可換性まで証明済み。次数の cast・op 比較も `AugmentedUniverseReverse` に保存。
次はこれを join の全順射と `uliftJoinIso` の可換性へ束ね、同型の順射で消去して逆射の式を得る。
この式を後合成し、`isLimitCone_restrict_iff_of_isIso` と `F2.isLimitCone_reverse_postcomp_iff` で同じ元の有限余極限余錐の保存へ戻す。
交換入力の証拠は未提供のまま。頂点だけの同型で全射の式を代用しない。
続いて有限 coherent 図式 K → Indκ(C) 全体の、元の Yoneda による filtered 表示を構成する。
各頂点を別々に表示するだけではなく、元の全単体・辺・境界を保持する一つの図式表示を得る。
C の `IsStable` から有限余極限を得る公開 API を確認し、不足分を証明する。その有限余極限と表示で元の Ind 図式の native 余極限を構成する。
有限極限と安定性では `IndFiniteLimitExchangeInput` を明示引数にし、交換の証拠を内製しない。
compact 部分の回収は N の既存の全比較と retract API を再利用する。

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
