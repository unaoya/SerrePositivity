# F1：straightening・Yoneda・Indκ（旧 α2）

> **v3（2026-10-24）**：F1 と F1b は **Ind レーン**に統合。本ファイルが Ind の正本で、a7 の引き継ぎは infinity-core-F1b.md を併読。所有：F1/（Cocartesian/ は休止）、F1B/、F2/Ind・FilteredExchange・Compact・Idempotent。配置は R12・R19 で変更済み（F1 は役割別サブディレクトリ、F2 の作業中部分は F2/FilteredExchange/）。

> **v2 の位置づけ（2026-10-23 移管）**：F1-4・F1-5・F1-3b、F2N-2(a)〜(d) は完了。次は F2N-5(a)(b)（Ind の有限存在と安定性、F1b から移管）。(c) compact 生成は完了。Cat∞ 値の一般底分類は第 II 段。

## 引き継ぎ v3：Ind（2026-10-24）

- 現在地：I-1 c① [x]。8時間上限により「明示入力のまま第 I 段を進める」を確定し、I-2 a へ移行する。一般交換と安定性は未証明。交換入力の差し替え（I-2 d・旧 N-6 c）は第 I 段終了時へ送る。
- 上限：開始 2026-10-24 18:00 JST、期限 2026-10-25 02:00 JST。I-1 の追加証明はここで区切る。
- 固定三段目：a① 指定始点像の中間点同定 [x]、a② native 恒等性と最後辺比較式 [x]、a③ raw 二辺評価の Ncomp [ ]、a④ Nlong/Ncomp から元の普遍三角形の一致 [ ]、b① 全錐比較・保存・有限形状帰納と公開 [ ]、c① 期限時の明示入力継続確定 [x]。
- I-1 保存点：`coherentColimitApexZeroCompositeValue_heq_two_evaluation` は元の零面値と raw 二辺値を、元の二射の指定評価比較の合成まで無条件に同定。Nlong は `coherentColimitApexLongEvaluationComparison_heq_value_composite`。元の全係数と指定値は保持している。二射評価と合成射評価の指定値の一致・Ncomp・元の普遍三角形の一致・一般交換は未証明。
- I-1 補助界面：`pointedRightFamilyEvaluation_comp` は動く点と二射の全評価の厳密合成則。`TransportIntervalSquare.precomp` と `coherentKanRightCompositionTransport_movingIso` は同じ四角形で始点も動く合成輸送を与える。これらを指定値の合成則そのものとは扱わない。
- 依存と提供：v3 冒頭の所有範囲を正本とする。下の v2 の所有・停止記述は履歴上の引き継ぎ。I-1 の結論の P・K-B への供給は未了、I-2 e は K-B へ公開する。ModelCategory 仮定を加えない。
- I-2 a の三段目：a① 三境界固定比較の curry と宇宙移送 [x]、a② 指定始点下の相対反映と両端評価の cofinal 性 [x]、a③ 射形状の標準余錐の余極限性 [x]、a④ 有限半順序形状の帰納と単一 filtered 表示 [ ] ← 今回。
- I-2 a の界面：元の三条件固定比較と始点評価下の実 under comma の比較は保存済み。`exists_relativeCommaFamily_iso_of_functorIso` は任意の元の同型に沿う指定変換の輸送。`indArrowInterpolationOldFamily_withCornerCocone` は同じ slice 円柱を保つ終点拡張の選び直しで元の旧族が変わらないことを厳密に回収する。
- I-2 a② 完了：`nonempty_indArrowTargetUnder_cocone` は指定終点変換を含む元の試験族への実余錐。両評価の引き戻しは filtered。`diagramCommaEvaluation_interval_isRightCofinal` と `smallDiagramCommaEvaluation_interval_isRightCofinal` は、元の射図式の任意の頂点での評価そのものの cofinal 性。
- I-2 a③ 完了：`indYonedaCanonicalCocone_isColimit` は元の scalar 標準密度余錐の余極限性。`smallDiagramCommaCocone_evaluate_isColimit` で各点を回収し、`smallArrowDiagramCommaCocone_isColimit` は同じ射図式 D を頂点とする元の標準全余錐の余極限性。添字の κ-filtered 性は `smallArrowDiagramComma_isKappaFiltered`。
- I-2 a④ の入口：`posetNerve_maximal_isPushout` と `_product_isPushout` は、極大点の除去部分と下方部分を貼る元の包含の実 pushout。任意の試験族との積も保持する。`smallDiagramCommaCocone_isColimit_of_evaluation_cofinal` は各点の共終性を明示して同じ標準全余錐の普遍性を回収。`indArrow_has_singleFilteredDiagramPresentation` は射図式の単一表示を公開する。有限半順序形状の共終性と filtered 性は未証明。
- I-2 a④ の余錐形状：`terminalJoinNerveMap_isIso` と `terminalJoinNerveIso_hom` は、既存の終点付加余錐写像そのものの可逆性と順射回収。`joinInl_terminalJoinNerveIso`・`joinInr_terminalJoinNerveIso` は元の圏の包含と新しい終点を全射で保持。
- I-2 a④ の下方比較：`posetLowerTerminalFunctor_isIso` は厳密下方集合に終点を付加した圏と弱下方集合との厳密な同型。`posetLowerJoinIso` と `_inl`・`_inr` は同じ弱下方 nerve を、元の下方包含と指定点を保つ実余錐形状として表示する。
- I-2 a④ の一般補間領域：`coneTensorCornerInclusion_mono` と `coneTensorCorner_isKappaSmall` は、任意の κ-small な下方形状と試験族から元の余錐の積へ入る実領域を与える。`coneTensorCocone_inl`・`_inr` は同じ全領域と新しい二つの余錐点を回収。`coneTensorCoconeIso` は同じ比較写像自身の可逆性、`coneTensorExtend_inclusion` は元の全領域への厳密な制限回収。一般有限半順序形状の帰納は未証明。
- I-2 a④ の実拡張：`exists_indComma_coneTensor_extension` は、元の二つの全図式と共通境界を保つ、同じ scalar Ind comma 内の全余錐積への拡張。任意の κ-small な下方形状と試験族を保持し、モデル圏仮定を要しない。
- I-2 a④ の形状制限：`diagramCommaRestriction` は元の全図式 comma の形状制限。`_projection`・`_uncurry`・`_coconeMap`・`_evaluate` で元の C 全図式・全錐・指定値を回収し、`_comp`・`_id` は全射の厳密な合成則と恒等則。
- I-2 a④ の一般 slice 円柱：`coneTerminalSliceSection_projection` は元の右余錐図式 D の全切断。`exists_coneSlice_cone_lift` と `exists_coneSlice_prism_lift` は元の全底図式・下方全境界・同じ D 側面を保持する実持ち上げ。
- I-2 a④ の旧族固定：`exists_coneTensor_extension_fixing_original` は終点が終対象である元の全円柱 W と、補間領域の元の全図式を同時に固定する実再構成。`coneTerminalSliceSection_tip_isTerminal` は同じ標準 D 切断の終点の終対象性。`indConeExtendedCommaFamily_old` は元の同じ diagram comma で元の q 自身を厳密に回収する。
- I-2 a④ の全円柱の制限：`diagramCommaPrism_precomp` と `_restrict` は試験族と形状の両制限で元の全変換を保つ。補間領域の写像は単射を保ち、`coneTensorCoconeIso_inv_naturality` は同じ逆比較の全自然性。
- I-2 a④ の余錐図式：`exists_indConeEndpointRaw_extension` は同じ実終点 comma で両全族を延長。`indConeExtendedSliceData_nonempty` は旧族の全円柱と下方全余錐を保持する再構成データ。`nonempty_indConeDiagramComma_cocone_of_lower_cocone` は元の q 自身の実余錐。`smallConeDiagramComma_isKappaFiltered_of_lower` は下方 comma の κ-filtered 性から同じ余錐図式の κ-filtered 性を与える。各点評価の共終性は未証明。
- I-2 a④ の指定下方余錐：`indConeExtendedCommaCocone_lower` と `exists_indConeDiagramComma_cocone_fixing_lower` は元の同じ diagram comma の実余錐が指定 G 自身へ厳密に制限されることを保証。`diagramCommaRestriction_cone_inl_isRightCofinal` は下方 comma の κ-filtered 性のもとで元の下方制限の共終性。`diagramCommaEvaluation_cone_inl_isRightCofinal` と小さい模型版は下方の旧頂点評価の共終性を伝播する。新しい極大点の評価は未証明。
- I-2 a④ の新しい極大点の比較：`indConeEndpointSliceRelativeIso` は再構成した終点面と元の全底余錐の slice 表示を底固定で比較。`indConeEndpointEvaluation_eq_reconstructed` は再構成した実終点族と元の極大点評価の厳密な一致。`indConeEndpointEvaluationIso` は元の実終点族から元の極大点評価への指定同型。指定変換下の相対余錐と極大点評価の共終性は未証明。
- I-2 a④ の指定比較の制限：`rightAnodyneRelativeLiftIso_precomp` は同じ等号同型の充満忠実な逆像の自然性。`coneTerminalSliceRelativeIso_precomp` と `coneTerminalSliceBoundaryFunctorIso_precomp` は、頂点表示した同じ終点の全余錐と始域境界の比較を、旧族で元の指定比較へ戻す（型の等号移送までの HEq）。実極大点評価の指定同型への接続は未了。
- I-2 a④ の元の点での比較の制限：`conePointSliceBoundaryFunctorIso_precomp` は任意の元の点写像で指定比較の旧族制限を保持。元の `conePointSliceBoundaryRelativeIso` は公開名・型を保ち、同じ元の点の指定逆像で直接構成する。`conePointSliceBoundaryRelativeIso_yoneda` は従来の頂点表示の指定比較との定義的な一致。`indConeEndpointSliceFunctorIso_old_heq` は同じ初期全円柱を保持する再構成で、元の終点 slice 比較の旧族制限が変わらないことを保証する。実 comma と評価への移送は未了。
- 供給依頼：`Stable.PosetSubtypeNerve` の `posetSubtypeNerveIso`・`posetSubtypeNerveIso_hom_ι` は現在の所有 import 閉包外。下方部分と全部分複体の比較に必要なため、コピーせずコーディネータ経由の供給依頼を報告済み。順序下方部分の圏と終点余錐の厳密な比較は独立に保存済み。
- I-2 a④ の元の族への適用：`indConeSliceInterpolationData_nonempty` は元の q と指定下方余錐 G の二段持ち上げ。`indConeEndpointRaw`・`indConeLowerEndpointRaw` は同じ実終点 comma 内の両全族、`indConeEndpointRaw_boundary` はその全共有境界の厳密な一致。元の C 全図式と全 slice 円柱を保持する。
- 次の一手：I-2 a④。同じ初期全円柱を保持した再構成での旧族の slice 比較の一致を、充満忠実な射影から同じ実終点 comma の指定比較へ反映する。元の点の表示同型と評価の厳密な回収を通して、`indConeEndpointEvaluationIso` の旧族制限の一致を証明する。元の終点族に与えられた指定変換を、余錐積の実拡張と同じ比較で保持し、元の極大点評価下の実余錐を構成する。比較の存在だけで指定変換の保持や共終性を主張しない。供給後に部分型 nerve の界面で極大点 a の下方包含を実 pushout に接続し、有限半順序集合 P の nerve 上で、元の一般 κ-small 試験族を保持する点追加の相対補間を構成する。射形状の旧族不変性・指定変換の輸送・共同余錐と厳密な境界回収を拡張し、元の小さい diagram comma の κ-filtered 性と各頂点評価の cofinal 性を得る。各点密度から同じ標準全余錐の余極限性を回収し、単一 filtered 表示をまとめる。

## 参照用引き継ぎ：F2N-5（2026-10-23）

### 現在地
- 今回保存：指定始点評価図式下の始点余錐を保持する補間と、C 全図式・D・始点全余錐を固定する比較を証明。相対 cofinal 性自体は未証明。

- F2N-2 は `e128b12d4` で完了。独立集約 7245 jobs、公理監査 2974 宣言、標準三公理のみ。
  (a) 任意の前層の表現可能密度、(b) 最小全部分 κ-filtered 閉包と Yoneda 因子化、(c) 単一 κ-filtered 表示、
  (d) 元の制限射 `indKappaContinuousRestriction` 自体の全 ∞ 圏同値と、元の順射を保持する同値データまで。
- **F2N-5(a) 零対象を証明**：`indYoneda_isZero_of_zero` は ℵ₀ ≤ κ のもとで、元の零対象の同じ Yoneda 像が Indκ の零対象であること。
  `ind_hasZeroVertex_of_stable` は正則 κ と小さい安定 C に対する零対象の存在。一般有限極限交換への依存なし。
- 前区切り `93d343010`：射形状の実 comma の κ-filtered 性。今回の独立集約 7782 jobs、公理監査 3881 宣言、標準三公理のみ。
- **(b) 交換入力と条件付きの有限錐保存**：`IndFiniteLimitExchangeInput.exchange` は全有限形状 K の
  `F2.CoherentFilteredLimitExchangeShape K`。一般 coherent filtered 図式・指定点ごとの native 余極限と全錐を量化する。
  この構造体の存在証拠は未提供。有限単体だけの既存結果から一般有限形状の交換を完成扱いにしない。
  `indVertex_cone_isLimit_of_exchange` は交換が成り立つ形状の元の極限全錐を、すべての Ind 前層が保存する条件付き定理。
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
  `diagramComma_obj_small` は全次数の実単体の小ささ。固定頂点写像の符号化を Space∞ → 前層 → Ind → 全図式と伝えて証明。
  `smallDiagramCommaIso` は ULift した小さい実模型との同型、`_projection` は元の全図式への射影の厳密な一致。
  小さい射影の right fibration 性・全空間の quasicategory 性・同じ図式を頂点とする標準全余錐は証明済み。`smallArrowDiagramComma_isKappaFiltered` は射形状 Δ¹ の κ-filtered 性を証明。一般有限半順序形状の κ-filtered 性と余極限性は未証明。
  `commaFamilyLift` は全射回収・往復・制限自然性を保持。
  `nonempty_indComma_cocone` と `_coslice_cocone` は実 comma と指定図式下の κ-small 試験余錐。
  `coneCommaRestriction_isPullback` と `_trivialKanFibration` は left anodyne な形状制限の実比較。
  `indConeCommaPointRestriction_projection` は始点図式を保つ。`_trivialKanFibration` は全境界の持ち上げ。
  `nonempty_indConeComma_cocone` と `_coslice_cocone` は始対象形状の全錐 comma と指定図式下の κ-small 試験余錐。
  `diagramCommaEvaluation` と `smallDiagramCommaEvaluation` は各指定値の実 Ind comma への全評価。
  両 `_projection` は元の C の図式評価、両 `_coconeMap` は同じ標準全余錐の評価を厳密に回収。cofinal 性は未証明。
  `arrowInterpolationCorner A` は (A⊗Δ¹) と (A⋆Δ⁰) を元の始点族 A で貼った実 pushout。全円柱への比較は単射、正則 κ で κ-small。
  `indArrowPrismNativeBoundaryIso` は再構成円柱と元の円柱の比較を、C 全図式と全 D を共に固定した、元の宇宙の全図式余錐の実 fiber へ移した同型。`_NativeOriginalVertex_val` は同じ元の q の指定全余錐を厳密に回収し、`indArrowNormalizedPrism_curry_tip` は固定終点を同じ元の D へ戻す。`diagramCommaSliceProjection_isFullyFaithful` は実 slice の充填性から証明済み。`nonempty_commaFunctorIso_of_fixedCoconeBoundaryIso` で両全余錐の比較を元の comma の全族へ反映できる。`nonempty_indArrowInterpolationOldFamily_iso` は同じ補間族の制限と元の q の実 comma 内の同型。`nonempty_indArrowDiagramComma_cocone` と `smallArrowDiagramComma_isKappaFiltered` で射形状の全 κ-small 試験族の余錐と、小さい実添字の κ-filtered 性まで証明。余極限性は未証明。

### 残り（依存順）

1. **(a)** 有限半順序形状（まず射・span）の filtered 表示、有限余極限・有限極限の存在。零対象は済み。HTT 5.3.5.15。16〜40時間（暫定）。
2. **(b)** 有限半順序図式表示と明示交換入力から安定性を証明。F1b の a7 提供後、交換入力へ実証拠を渡す。HA 1.1.3.6。24〜60時間（暫定、提供待ちを含まず）。
3. **(c) 完了**：N の元の retract 回収と合流し、正則 κ・冪等完備 C に対する同じ compact Yoneda の全同値と filtered 生成。HTT 5.3.5.11。

### 主要宣言（名前のみ）

- `IndInfinity`、`indYoneda`、`indInclusionPresheaf`、`ind_isColimit_iff_inclusion`
- `presheafDensityCocone_isColimit`、`isIndVertex_iff_singleFilteredPresentation`
- `indLeftKanExtension_preservesSmallKappaFilteredColimits`、`indKappaContinuousRestrictionEquivalence`、`indKappaContinuousRestrictionEquivalence_hom`
- `indVertex_evaluation_isTerminal_of_initial`、`indYoneda_isInitial_of_initial`、`indYoneda_isTerminal_of_terminal`
- `indYoneda_isZero_of_zero`、`ind_hasZeroVertex`、`ind_hasZeroVertex_of_stable`
- `joinUniverseReverse_hom`、`joinUniverseReverse_inv`、`uliftCoconeReverse_val`、`indYoneda_finiteColimit_isColimit`

- `compactYoneda_isQCatEquivalence`、`compactGenerationEquivalence`、`compactGenerationEquivalence_hom`
- `indVertex_has_filteredYonedaPresentation`、`diagramYoneda`、`diagramYoneda_isFullyFaithful`
- `diagramComma_obj_small`、`smallDiagramComma`、`smallDiagramCommaIso_projection`、`smallDiagramCommaCocone_vertex`
- `nonempty_indComma_cocone`、`nonempty_indConeComma_cocone_of_initial`、`nonempty_indConeComma_coslice_cocone`
- `smallDiagramCommaEvaluation_coconeMap`、`arrowInterpolationCornerInclusion_mono`、`arrowInterpolationCorner_isKappaSmall`
- `IndArrowInterpolationData`、`indArrowInterpolationData_nonempty`、`indArrowInterpolationCommaFamily`、`indArrowInterpolationCommaFamily_old_projection`
- `exists_diagramComma_initialCone_family_under`、`exists_indArrowInterpolationData_with_sourceCone`、`exists_indArrowInterpolationData_under_source`
- `indArrowTerminalPrismFamily_source`、`indArrowPrismSourceFixedIso`、`indArrowPrismAllBoundaryIso`、`indArrowPrismAllBoundaryOriginalVertex_val`

### 依存と提供

- 所有は `InfinityCategories/F2/Ind/`、独立集約 `F2/Ind.lean`、`scripts/audit_f2_ind.lean`、本計画。
- F2 既存ファイル・集約 F2.lean、F2/Idempotent/・F2/Compact/ は読み取り専用。ルート集約を変更しない。
- F2N-1 の filtered・κ-filtered・cofinality と、既存の一般 coherent filtered 余極限の空形状交換を再利用。
- F1b の a7（一般有限極限交換）は進行中。未提供定理を instance 仮定で主経路へ隠さない。
- κ・C・小さい filtered 添字は宇宙 u、Indκ は u+1。有限形状の宇宙移送も実際の図式を保持して扱う。
- 新規 sorry・公理・引用なし。新規モジュール 100 行以内、計画 300 行・引き継ぎ 100 行以内。
- 自分のファイルのみ `git commit --only`。通常は報告後続行。今回はコーディネータの停止指示により保存後停止し、このチャットでは再開しない。

### 未コミット

- 所有の未コミット作業はなし（本引き継ぎと同時に保存）。新規6モジュールは全て集約・監査に接続して検証済み。共有作業木の他レーンの変更には触れない。

### 既知の問題

- F2N-5(a)(b) の有限余極限・有限極限・安定性は未証明。零対象だけで (a) 完了とはしない。(c) は完了。
- `IndFiniteLimitExchangeInput` の構成子は一般有限極限交換の証拠を要求する。現在は供給する定理が未提供。
- **経路修正**：[HTT 5.3.5.15・Warning 5.3.5.16](https://people.math.harvard.edu/~lurie/papers/HTT.pdf) は有限半順序集合の nerve を要求。任意の有限単体集合への filtered 図式表示の拡張は偽。
- 全形状で証明した充満忠実性・comma の小ささは有効。射形状の κ-filtered 性は済み。一般有限半順序形状の filtered 性と標準余錐の余極限性は残る。
- `IsStable` から有限全形状の存在への公開 API は未確認。追加仮定で回避しない。
- 旧ビルド session `20603` は現在の実行環境に存在しない。停止用ビルドは成功。ログ `/tmp/f2-ind-stop-build.log`、監査 `/tmp/f2-ind-stop-audit.log`。

### 次の一手

`indYoneda_finiteColimit_isColimit` により、明示交換入力のもとで同じ元の有限余極限余錐を Ind Yoneda が保存することまで完了。
まず有限半順序集合 P の nerve 上の図式の単一 filtered 表示を構成する（HTT 5.3.5.15）。任意の有限 K への誤った一般化を追わない。
`smallDiagramComma` の小ささ・実比較・全図式射影は済み。次は P の頂点を下から追加する補間で κ-filtered 性を証明。
局所入力 `nonempty_indComma_cocone` と `_coslice_cocone` は証明済み。κ-small 試験族・指定全境界を保つ。
上方区間の始対象への点制限は `indConeCommaPointRestriction` で実現済み。射影を厳密に保ち、全比較が自明 Kan。
`smallArrowDiagramComma_isKappaFiltered` により、射形状 Δ¹ の小さい実 comma の κ-filtered 性は追加仮定なしに完了。`nonempty_indArrowInterpolationOldFamily_iso` は補間族の制限と同じ元の q の実 comma 内の同型を回収し、実全余錐を同じ q へ輸送して結論。有限半順序全体の表示や標準余錐の余極限性は未証明。
次は両端点 k に対する `smallDiagramCommaEvaluation κ D k` の cofinal 性を証明し、既存の単一頂点表示の native 余極限から `smallDiagramCommaCocone` の余極限性を回収する。各評価の `_projection`・`_coconeMap` は元の全図式と指定余錐を厳密に保持する。指定評価対象の下での表示添字の全試験余錐を、同じ二段補間と頂点 comma の coslice の κ-filtered 性から作る。 始点側では `exists_indArrowInterpolationData_under_source` が指定下側変換の全始点余錐を選び、sourceCone を選び直さず補間する。`indArrowPrismAllBoundaryIso` は C 全図式・全 D・元の始点全余錐を同時に固定し、両端点の包含後の全円柱も厳密に回収する。再開時の最初の一工程は、この三境界固定比較を区間の curry・宇宙比較へ移し、指定下側変換に整合する全族の同型へ相対反映すること。通常の comma の関手同型の存在だけで、この整合を完成扱いにしない。一般有限 P への帰納はその後で、境界は (N(P≤a)×B)∪(N(P<a)×{∞})、B は一般 κ-small 試験形状。
HA 1.1.3.6 に沿って、元の射の filtered 表示から元の C の fiber/cofiber 全四角形の filtered 表示を構成する。
cofiber は余極限の合成、fiber は明示交換入力による前層の点ごとの引き戻し交換で示し、零角の一致から安定性へ戻す。
有限全形状の存在は一般安定性の存在定理を所有内で補い結論する。元の C の有限全存在を追加仮定にしない。
交換入力の証拠は未提供のまま、compact 部分は完了済み。引用を Lean の証明の代わりにしない。

## F2N-2 の完了界面

- `e128b12d4`：HTT 5.1.5.3、5.3.5.4、5.3.5.10。κ の正則性と宇宙を明示し、追加の同値性 instance 仮定なし。
- 指定左 Kan 延長の同じ全相対 join 族と像について、左右の native 全余錐制限同値から一般保存性へ戻した。
- `indKappaContinuousRestriction_isFullyFaithful`・`_isEssentiallySurjective` と F0 の判定で同値を結論。

## F1 の完了済み範囲と第 II 段の再開点

- 空間値 straightening・right fibration 分類・Yoneda は完了。F1-4・F1-5・F1-3b は `6f10976ea` で完了。
- 前層の小さい極限・余極限、評価による保存・検出、表現可能関手による極限の特徴づけ、二変数 Hom を提供済み。
- Cat∞ 値分類は全有限単体底の `cocartesianStraighteningCoherentMap_finite_isQCatEquivalence` で区切る。

### 再開点（第 II 段、3行）

1. 全有限単体の主写像は同値。標準二次元実境界の固定 fiber 比較に加え、任意の底への二単体の欠けた面で、比較同値・共有境界との厳密可換性・指定同型の境界像を証明。全次元の両標準境界制限の Kan 性も証明。集約7665 jobs・公理監査16331宣言（標準三公理のみ）。
2. 次は任意の二単体のホーン側の指定同型を揃え、欠けた面と貼り合わせて実境界・固定 fiber 比較へ戻し、高次境界へ進む（暫定12〜24時間）。`cocartesianTwoBoundaryLocalFaceComparison` と `cocartesianSimplexLocalBoundarySourceRestriction`・`TargetRestriction` を使う。未コミットはこの区切りの保存時に解消する。
3. 有限セル・骨格降下24〜48時間、一般充満忠実性の結論・検証4〜8時間（計40〜80時間、暫定）。本質的全射性・一般底・宇宙は続く工程。

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
