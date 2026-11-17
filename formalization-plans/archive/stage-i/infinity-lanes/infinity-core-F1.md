# F1：straightening・Yoneda・Indκ（旧 α2）

> **v3（2026-10-25 13:10 改訂）**：Ind は F2/Ind・Compact・Idempotent とその集約、audit_infinity_f2 を所有する。Ind-S (4)・(5) の F1・F1B・Core 新規葉は新設 Ind-S、I-1 a7 の F2/FilteredExchange は新設 X が担当。Ind はこれらへ新規追加・編集をしない。下記の旧所有範囲は履歴。

> **v2 の位置づけ（2026-10-23 移管）**：F1-4・F1-5・F1-3b、F2N-2(a)〜(d) は完了。次は F2N-5(a)(b)（Ind の有限存在と安定性、F1b から移管）。(c) compact 生成は完了。Cat∞ 値の一般底分類は第 II 段。

## 引き継ぎ v3：Ind（2026-10-24）

- 現在地：I-2 d′①〜d′⑤ 完了。有限 poset の strict 化、全余錐保存の形状 pushout 帰納、元の指定余錐への帰還から全有限 K の交換を結論。交換入力と Ind の有限全存在・安定性・compact 生成、旧 N-6 c の無条件化を保存して停止。X の Ncomp・元の普遍三角形の一致は別経路で未証明。
- 上限：開始 2026-10-24 18:00 JST、期限 2026-10-25 02:00 JST。I-1 の追加証明はここで区切る。
- 固定三段目：a① 指定始点像の中間点同定 [x]、a② native 恒等性と最後辺比較式 [x]、a③ raw 二辺評価の Ncomp [ ]、a④ Nlong/Ncomp から元の普遍三角形の一致 [ ]、b① 全錐比較・保存・有限形状帰納と公開 [ ]、c① 期限時の明示入力継続確定 [x]。
- I-1 保存点：`coherentColimitApexZeroCompositeValue_heq_two_evaluation` は元の零面値と raw 二辺値を、元の二射の指定評価比較の合成まで無条件に同定。Nlong は `coherentColimitApexLongEvaluationComparison_heq_value_composite`。元の全係数と指定値は保持している。二射評価と合成射評価の指定値の一致・Ncomp・元の普遍三角形の一致・一般交換は未証明。
- I-1 補助界面：`pointedRightFamilyEvaluation_comp` は動く点と二射の全評価の厳密合成則。`TransportIntervalSquare.precomp` と `coherentKanRightCompositionTransport_movingIso` は同じ四角形で始点も動く合成輸送を与える。これらを指定値の合成則そのものとは扱わない。
- 依存と提供：v3 冒頭の改訂所有範囲を正本とする。I-1 の結論は X、Ind-S (4)・(5) は新設 Ind-S が供給する。Ind は I-2 e の公開界面を K-B の K-7 d4 へ提供する。ModelCategory 仮定を加えない。
- I-2 d′ の固定三段目：d′① filtered 性の ℵ₀ 接続を確認 [x]、d′② 有限 poset の Bousfield–Kan 模型の filtered 余極限保存 [x]、d′③ strict 化を通じた有限 poset 形状の coherent 交換 [x]、d′④ cospan・単体・空形状と pushout 帰納による全有限形状への拡張 [x]、d′⑤ 交換入力の定理化、無条件の系、集約・監査 [x]。
- I-2 d′ の基底公開名：`coherentFilteredLimitExchangeShape_finite_poset`・`coherentFilteredLimitExchangeShape_cospan`・`coherentFilteredLimitExchangeShape_cospanHorn`・`coherentFilteredLimitExchangeShape_simplex`・`coherentFilteredLimitExchangeShape_empty`（名前空間 `F2.Ind`）。一般 filtered ∞ 添字と元の指定全余錐を量化し、濃度変更境界を仮定しない。
- I-2 d′ の一般交換の公開名：`F2.Ind.CoherentFiniteLimitExchange` の `coherentFilteredLimitExchangeShape_finite`・`indFiniteLimitExchangeInput`。`CoherentFilteredLimitExchangeShape K` は全有限単体集合 K と任意の filtered ∞ 添字、元の指定点ごとの全余錐を量化する。
- I-2 d′ の無条件の系：`ind_hasFiniteLimits_unconditional`・`ind_hasFiniteColimits_unconditional`、安定な C 向け `ind_hasFiniteLimits_of_isStable_unconditional`・`ind_hasFiniteColimits_of_isStable_unconditional`・`ind_isStable_unconditional`・`ind_isPullbackSquare_iff_isPushoutSquare_unconditional`・`ind_stable_with_fullyFaithful_exactYoneda_unconditional`（名前空間 `F2.Ind`）。
- K-7 d4 の無条件入口：`F2.Ind.UnconditionalStableCompactGeneration.ind_stableCompactGeneration_unconditional` と `_equivalence`。名前空間 `F2.Ind`。同じ元の生成同値・compact 像・生成表示・既存の全選択比較を保持する。正則 κ・ℵ₀ ≤ κ・安定な冪等完備 C だけを要求し、交換や C の有限全存在を追加仮定にしない。
- 旧 N-6 c の無条件化：`F2.Compact.FiniteColimitClosureUnconditional` の `isKappaCompact_finiteColimit`・`hasFiniteColimits_kappaCompactObjects`。名前空間 `F2.Compact`、添字と標的の宇宙を分け、元の指定全余錐の頂点を保持する。
- I-2 d′ の読み取り専用 import：P の `SmallWeightedSectionsContinuity`・`SmallBousfieldKanContinuity`・`WithInitialFilteredLimits`・`CoherentFilteredPosetExchange`・`PullbackExchangeShape`・`ChosenColimitParameterApex`・`PointwiseColimitPrecomposition`。Stable の既許可 `FinitePosetNerve` と、新規許可 `FunctorFiniteLimits`・`ExcisionRepresentableLimits`。重い後者は `FilteredColimitFiniteLimitPreservation` 一葉だけから直接 import。R が第 I 段終了時に FunctorFiniteLimits を Core、Space の有限存在を HomotopyLimits／Core へ付け替える。
- I-2 d′ の既存閉包内の直接 import（R 参照）：Core の `FiniteShapeInduction`・`FunctorPointwiseLimitExistence`・`PushoutCommonExtension`、F1/Joins の `CommonColimitAttachment`・`ConeSpanCoconeGlue`・`FiniteLimitGeneration`・`PointConeSpanIso`・`TerminalShapeColimit`。
- 同上：F1/Simplicial の `EmptySimplicialDomain`・`FiniteCospanNerveIso`・`FiniteHornUniverseIso`、F1B/KanExtension の `RelativeLimit`、F2/CatInfinity の `CoconeReversePostcomp`・`ConeValEquality`、HomotopyLimits の `FunctorColimitEvaluation`、Stable の `ReindexSliceOver`。
- X 所有の読み取り専用依存：`FilteredExchange.CoherentTotalColimit`・`PointwiseColimitChoiceTransport`・`SpaceLimitShapes`。既存の無条件の空間余極限・余錐一意性・空間極限の存在を使用し、X の作業中の交換結論を仮定しない。
- I-2 e′ の固定三段目：e′① D-7′ を接続し、安定な C から Ind の有限全存在・安定性を導く [x]、e′② K-B 向け compact 生成界面と既存の選択比較を接続する [x]、e′③ 集約・監査・引き継ぎを保存する [x]。
- I-2 e′ の依存：`Stable.StableFiniteLimitsColimits` を新規葉 `F2.Ind.StableSourceFiniteLimitsColimits` から読み取り専用 import。D の `hasFiniteLimits_of_isStable`・`hasFiniteColimits_of_isStable` を証明内の局所 instance に置く。Ind → Stable の逆方向 import は第 I 段終了時に R が整理する。
- I-2 e′ の公開名（名前空間 `SerrePositivity.InfinityCategories.F2.Ind`）：`ind_hasFiniteLimits_of_isStable`・`ind_hasFiniteColimits_of_isStable`・`ind_isStable_of_isStable`・`ind_isPullbackSquare_iff_isPushoutSquare_of_isStable`・`ind_stable_with_fullyFaithful_exactYoneda_of_isStable`。C の有限全存在を追加仮定にしない。
- K-7 d4 の新入口：`F2.Ind.StableSourceCompactGeneration` の `ind_stableCompactGeneration_of_isStable`。`_equivalence` は同じ元の `compactGenerationEquivalence` との厳密な一致、`_inverse_inclusion` は元の compact 包含との全関手同型。既存の compact 像・生成表示・逆同値の選択比較は変更なく使う。交換入力だけを明示のまま保持。
- I-2 e の固定三段目：e① compact 同値と元の Yoneda・包含の厳密な比較 [x]、e② 任意の Ind 対象の compact 生成表示 [x]、e③ 安定性・完全性と合わせた K-B 向け公開界面 [x]、e④ 選択比較、集約・監査、引き継ぎ [x]。
- I-2 e の公開入口：`F2.Ind.StableCompactGeneration` の `ind_stableCompactGeneration`。同じ Ind の安定性・元の Yoneda の充満忠実性と完全性・compact 像・生成同値・元の任意の頂点の filtered 生成表示を保持。安定性だけが明示交換入力と C の有限全存在に依存する。
- K-B の K-7 d4 向け公開名（名前空間 `SerrePositivity.InfinityCategories.F2.Ind`）：同値 `compactGenerationEquivalence`、順射 `compactGenerationEquivalence_hom`・`compactGenerationEquivalence_inclusion`、compact 像 `compactGenerationEquivalence_image_isKappaCompact`・`ind_isKappaCompact_iff_yoneda`、生成表示 `indVertex_has_compactGeneratorPresentation`。
- K-B 向け選択比較：`compactGenerationChoice_inclusion`・`compactGenerationInverse_inclusion`・`compactGenerationInverse_choiceIso`・`compactGenerationInverse_familyIso`、公開界面の `StableCompactGeneration.inverse_inclusion`。比較は全関手同型で、任意の入力族への前合成を保つ。K-B 自身の構造射・全入力との照合は K-B で行う。
- Ind-S への作業木引き継ぎ：未コミットの F1 葉 `FunctorCategories/RelativeFunctorDescentOver`・`Diagrams/CocartesianKanWeightedUnitData`・`Diagrams/CocartesianKanWeightedUnit` は Ind-S (5) 草稿。Data のみビルド済み、相対降下の頂点書き換えが未解決。集約・監査未接続。移管後は Ind で変更・stage しない。
- 次の一手（I-2 d′ 完了）：停止。P・K-B へ一般交換と無条件の公開名を供給する。X の直接経路の継続・整理はコーディネータが判断する。Ind-S の供給や深層モジュールは変更しない。
- I-2 c の固定三段目：c① 有限 cospan の包含による保存 [x]、c② fiber・cofiber の単一 filtered 表示 [x]、c③ bicartesian 判定 [x]、c④ Ind の安定性 [x]、c⑤ 包含の完全性と公開界面 [x]。
- I-2 c① の公開入口：`ind_cospan_inclusion_isLimit`・`ind_cospan_isLimit_iff_inclusion` は任意の元の標準 cospan 全錐の保存・反映。`ind_inclusion_isPullbackSquare_iff` は元の実四角形の引き戻し性の保存・反映。C の有限極限・正則 κ・明示交換入力を保持する。
- I-2 c②・c③ の公開入口：`ind_cospan_has_singleFilteredDiagramPresentation`・`ind_span_has_singleFilteredDiagramPresentation` は元の全図式の単一表示。`ind_exists_bicartesianLimitCone`・`ind_exists_bicartesianColimitCocone` は同じ表示から実 bicartesian 全錐・全余錐を構成。`ind_isPullbackSquare_iff_isPushoutSquare` は元の任意の実四角形自身について両普遍性の一致。
- I-2 c④ の公開入口：`F2.Ind.Stability.ind_isStable` は正則 κ・明示交換入力・安定な C と C の有限全存在から Ind の安定性を結論。`ind_stable_with_fullyFaithful_exactYoneda` は同じ元の Yoneda の充満忠実性・完全性も同時に供給。名前空間は `SerrePositivity.InfinityCategories.F2.Ind`。元の入口は変更せず、e′ の新名の系で有限全存在を IsStable C から導く。
- I-2 c⑤ の公開入口：`indYoneda_isExactFunctor` は既存 `Stable.IsExactFunctor` による元の Yoneda 包含の完全性。`indYoneda_preservesZeroVertices` と元の全 cofiber 保存を証明し、Ind の安定性を仮定しない。`indYoneda_isLimit` は任意の小さい全極限錐を追加の有限性・交換入力なしで保存する。
- I-2 c の供給許可：`Stable.ExactFunctor`・`Stable.Bicartesian` は新規 Ind 葉から読み取り専用で直接 import 可。既存の深層ファイルは変更しない。C の有限全存在の仮定除去は e′ の新規葉に接続。
- I-2 b の固定三段目：b① C の有限極限・有限余極限の全族選択と Yoneda 保存 [x]、b② Ind 関手圏での点ごとの κ-filtered 余極限の構成 [x]、b③ 有限半順序図式の有限極限と包含による保存・反映 [x]、b④ 有限半順序図式の有限余極限の普遍性 [x]、b⑤ 任意の有限単体集合形状への接続と公開界面 [x]。
- I-2 b の公開入口：`yonedaInfinityMap_isLimit` は任意の小さい極限全錐の保存。`exists_yoneda_finiteLimit_coneFamily` と `exists_indYoneda_finiteColimit_coconeFamily` は元の制限を厳密に固定した全族。余極限保存は明示交換入力を残す。`exists_indFunctor_kappaFiltered_colimit` は全関手形状で同じ filtered 余極限全余錐と包含による全評価の保存。
- I-2 b③ の接続：`ind_filteredLimitCone_isLimit` は元の Ind 全錐族の点ごとの filtered 補完に明示の形状交換を適用し、完成後の元の錐と包含像の極限性を同時に結論する。`indYonedaConeFamily_restriction` は元の下方全図式への厳密な制限回収。`ind_exists_limitCone_of_singleFilteredDiagramPresentation` は元の指定全図式の極限と包含像の極限の同時存在。`indFinitePoset_hasLimit`・`indFinitePoset_inclusion_isLimit`・`indFinitePoset_isLimit_iff_inclusion` で有限半順序図式の存在・保存・反映を公開。
- I-2 b④ の公開入口：`colimitCoconeFamily_completion_isColimit` は任意の quasicategory の全余極限族の点ごとの余極限補完。有限性・filtered 性は不要。`ind_hasColimit_of_singleFilteredDiagramPresentation` と `indFinitePoset_hasColimit` は、明示交換入力と C の有限余極限のもとで元の指定全図式の余極限存在を結論する。任意の有限単体集合形状は未完。
- I-2 b④ の供給許可：P の `CoconeFunctorUnitPrism` は新規 Ind 葉から読み取り専用で直接 import 可。R の移動対象。右端 Hom 判定は既存の所有内の円柱の随伴証明を新規の葉で一般化し、余錐形状の収縮へ適用した。既存の円柱ファイルは変更しない。
- I-2 b⑤ の供給：`HomotopyLimits.CosliceShapePushout` は新規葉から読み取り専用で使用可。一般有限生成は既存入口がなく、有限セル帰納で構成する。一般部分の新規 Core モジュールは許可済み、D の D-7′ にも公開する。
- I-2 b⑤ の準重複：`F1.Fibrations.TerminalRightFibrationRepresentation` の `rightFibration_terminal_representation_exists` は終対象を持つ right fibration の底上で厳密な slice 表示。Derived は import しない。D の `roofTerminalRepresentation_exists` との準重複は許可済みで、第 I 段終了時に R が D 側を付け替える。
- I-2 b⑤ の一般付着：`hasColimit_pushout_shape_of_pointSpan` は単射側のある任意の形状 pushout で、両部分・共通部分の余極限と三頂点 span の余極限から元の全図式の余極限を構成する。`hasColimit_coneSpan_iff` は同じ指定部分余極限を付加する前後の余極限存在の同値。この付着を用いる全有限生成と双対は下記で公開。Ind の宇宙接続は下記の全有限存在へ接続済み。
- I-2 b⑤ の一般生成：`F1.Joins.FiniteColimitSpanGeneration.hasFiniteColimits_of_initial_pushouts` と `F1.Joins.FiniteLimitGeneration.hasFiniteLimits_of_terminal_pullbacks`（名前空間はともに共通根）は、全有限単体集合形状についての生成定理。D の D-7′ 向け。新規 `Core.FiniteShapeInduction` は有限和も pushout から導き、既存の F2 の有限セル帰納を一般化する。旧ファイルは変更しない。
- I-2 b⑤ の基底供給：`HomotopyLimits.EmptyCone` は新規葉から読み取り専用で使用可、反転利用も可。R の Core 移動対象。`hasLimit_emptyDiagram_of_terminal`・`hasColimit_emptyDiagram_of_initial` は任意の空部分複体の図式を扱う。
- I-2 b⑤ の形状供給：D の excision 格子の import は避け、新規葉の `finiteSpanNerveIso`・`finiteCospanNerveIso` を使用。両辺の `_iso` と全ての面・退化の `_hom_naturality`、宇宙持ち上げの `uliftFiniteSpanNerveIso`・`uliftFiniteCospanNerveIso` を供給。準重複は許可済み、R が第 I 段終了時に D 側を付け替える。
- I-2 b⑤ の公開界面：`F2.Ind.FiniteLimitsColimits` の `ind_hasFiniteLimits`・`ind_hasFiniteColimits` は元の Ind の全有限単体集合形状について存在を結論。正則 κ・明示交換入力・C の対応する有限全存在を要求する。既存宣言はこの型を保ち、D-7′ の供給は e′ の新規葉から消費する。
- I-2 b の供給許可：`Core.LimitProjectionExistence`・`HomotopyLimits.FullSubcomplexConeLift`・`FullSubcomplexLimitReflection` を、新規 Ind 葉から読み取り専用で直接 import 可。既存の深層ファイルは変更しない。後二本は R が Core へ移動。`indFullConeLift_inclusion` と `ind_isLimit_of_inclusion` は元の全錐の厳密な持ち上げと任意の形状の極限反映。
- I-2 a の三段目：a① 三境界固定比較の curry と宇宙移送 [x]、a② 指定始点下の相対反映と両端評価の cofinal 性 [x]、a③ 射形状の標準余錐の余極限性 [x]、a④ 有限半順序形状の帰納と単一 filtered 表示 [x]。
- I-2 a の界面：元の三条件固定比較と始点評価下の実 under comma の比較は保存済み。`exists_relativeCommaFamily_iso_of_functorIso` は任意の元の同型に沿う指定変換の輸送。`indArrowInterpolationOldFamily_withCornerCocone` は同じ slice 円柱を保つ終点拡張の選び直しで元の旧族が変わらないことを厳密に回収する。
- I-2 a② 完了：`nonempty_indArrowTargetUnder_cocone` は指定終点変換を含む元の試験族への実余錐。両評価の引き戻しは filtered。`diagramCommaEvaluation_interval_isRightCofinal` と `smallDiagramCommaEvaluation_interval_isRightCofinal` は、元の射図式の任意の頂点での評価そのものの cofinal 性。
- I-2 a③ 完了：`indYonedaCanonicalCocone_isColimit` は元の scalar 標準密度余錐の余極限性。`smallDiagramCommaCocone_evaluate_isColimit` で各点を回収し、`smallArrowDiagramCommaCocone_isColimit` は同じ射図式 D を頂点とする元の標準全余錐の余極限性。添字の κ-filtered 性は `smallArrowDiagramComma_isKappaFiltered`。
- I-2 a④ の入口：`posetNerve_maximal_isPushout` と `_product_isPushout` は、極大点の除去部分と下方部分を貼る元の包含の実 pushout。任意の試験族との積も保持する。`smallDiagramCommaCocone_isColimit_of_evaluation_cofinal` は各点の共終性を明示して同じ標準全余錐の普遍性を回収。`indArrow_has_singleFilteredDiagramPresentation` は射図式の単一表示を公開する。有限半順序形状の結論は下記の公開界面へ接続済み。
- I-2 a④ の余錐形状：`terminalJoinNerveMap_isIso` と `terminalJoinNerveIso_hom` は、既存の終点付加余錐写像そのものの可逆性と順射回収。`joinInl_terminalJoinNerveIso`・`joinInr_terminalJoinNerveIso` は元の圏の包含と新しい終点を全射で保持。
- I-2 a④ の下方比較：`posetLowerTerminalFunctor_isIso` は厳密下方集合に終点を付加した圏と弱下方集合との厳密な同型。`posetLowerJoinIso` と `_inl`・`_inr` は同じ弱下方 nerve を、元の下方包含と指定点を保つ実余錐形状として表示する。
- I-2 a④ の一般補間領域：`coneTensorCornerInclusion_mono` と `coneTensorCorner_isKappaSmall` は、任意の κ-small な下方形状と試験族から元の余錐の積へ入る実領域を与える。`coneTensorCocone_inl`・`_inr` は同じ全領域と新しい二つの余錐点を回収。`coneTensorCoconeIso` は同じ比較写像自身の可逆性、`coneTensorExtend_inclusion` は元の全領域への厳密な制限回収。有限半順序帰納は下記の固定下方部分の帰納で完成。
- I-2 a④ の実拡張：`exists_indComma_coneTensor_extension` は、元の二つの全図式と共通境界を保つ、同じ scalar Ind comma 内の全余錐積への拡張。任意の κ-small な下方形状と試験族を保持し、モデル圏仮定を要しない。
- I-2 a④ の形状制限：`diagramCommaRestriction` は元の全図式 comma の形状制限。`_projection`・`_uncurry`・`_coconeMap`・`_evaluate` で元の C 全図式・全錐・指定値を回収し、`_comp`・`_id` は全射の厳密な合成則と恒等則。
- I-2 a④ の一般 slice 円柱：`coneTerminalSliceSection_projection` は元の右余錐図式 D の全切断。`exists_coneSlice_cone_lift` と `exists_coneSlice_prism_lift` は元の全底図式・下方全境界・同じ D 側面を保持する実持ち上げ。
- I-2 a④ の旧族固定：`exists_coneTensor_extension_fixing_original` は終点が終対象である元の全円柱 W と、補間領域の元の全図式を同時に固定する実再構成。`coneTerminalSliceSection_tip_isTerminal` は同じ標準 D 切断の終点の終対象性。`indConeExtendedCommaFamily_old` は元の同じ diagram comma で元の q 自身を厳密に回収する。
- I-2 a④ の全円柱の制限：`diagramCommaPrism_precomp` と `_restrict` は試験族と形状の両制限で元の全変換を保つ。補間領域の写像は単射を保ち、`coneTensorCoconeIso_inv_naturality` は同じ逆比較の全自然性。
- I-2 a④ の余錐図式：`exists_indConeEndpointRaw_extension` は同じ実終点 comma で両全族を延長。`indConeExtendedSliceData_nonempty` は旧族の全円柱と下方全余錐を保持する再構成データ。`nonempty_indConeDiagramComma_cocone_of_lower_cocone` は元の q 自身の実余錐。`smallConeDiagramComma_isKappaFiltered_of_lower` は下方 comma の κ-filtered 性から同じ余錐図式の κ-filtered 性を与える。各点評価は下方の filtered 性と各点共終性から下記で回収する。
- I-2 a④ の指定下方余錐：`indConeExtendedCommaCocone_lower` と `exists_indConeDiagramComma_cocone_fixing_lower` は元の同じ diagram comma の実余錐が指定 G 自身へ厳密に制限されることを保証。`diagramCommaRestriction_cone_inl_isRightCofinal` は下方 comma の κ-filtered 性のもとで元の下方制限の共終性。`diagramCommaEvaluation_cone_inl_isRightCofinal` と小さい模型版は下方の旧頂点評価の共終性を伝播する。新しい極大点の評価は下記で回収する。
- I-2 a④ の実評価比較：`indConeEndpointEvaluation_eq_reconstructed` は再構成した元の終点族と実評価の厳密な一致。`indConeEndpointEvaluationIso` は元の実終点族から元の極大点評価への指定同型。`indConeEndpointEvaluationIso_old_heq` は同じ初期全円柱を保つ再構成で旧族上の指定値が不変。
- I-2 a④ の指定変換保持：`coneTensorTargetInclusion` は元の試験族から補間領域への単射。`exists_indConeExtendedSliceData_relative` は同じ初期全円柱を保ち、元の両全境界と指定終点変換を同時に延長。`nonempty_relativeCommaFamily_cocone_of_comparison` は旧族上の指定比較とその逆を相殺し、元の指定変換下の実余錐へ戻す。
- I-2 a④ の極大点評価の共終性：`nonempty_indConeTargetUnder_cocone_of_lower_cocone` は元の q と指定終点変換を含む実 under comma の余錐。`indConeTargetEvaluationComma_isFiltered` と `diagramCommaEvaluation_cone_apex_isRightCofinal` は下方 comma の κ-filtered 性から元の極大点評価の共終性を与える。小さい模型版も同じ評価を保持。
- I-2 a④ の余錐表示の帰結：`diagramCommaEvaluation_cone_isRightCofinal` は下方の filtered 性と各点共終性から同じ余錐形状の全頂点評価の共終性。`indCone_has_singleFilteredDiagramPresentation` は同じ D を頂点とする単一 filtered 表示。有限半順序形状への貼り合わせと帰納は下記で完成。
- I-2 a④ の一般形状の貼り合わせ：`diagramCommaGlue_left`・`_right` と `exists_diagramComma_cocone_gluing` は、元の形状 pushout で両全族・両指定余錐を厳密に保持。`diagramComma_shape_ext` は元の両制限による全族の決定性。共通境界の図式等号移送は同じ C 全族と全円柱を保持する。
- I-2 a④ の点追加の相対性：`exists_diagramComma_cocone_cone_pushout` は局所余錐を貼る一般形状 pushout で、元の既存部分の指定余錐を固定した全余錐を構成。`smallDiagramComma_cone_pushout_isKappaFiltered` と `diagramCommaRestriction_cone_pushout_isRightCofinal` は既存部分の filtered 性から全体の filtered 性と旧評価の共終性を与える。
- I-2 a④ の帰納基底：`finitePoset_lowerSet_induction` は固定下方部分の外の極大点を除く有限濃度帰納。`indEmpty_has_singleFilteredDiagramPresentation` は空形状の元の D の単一 filtered 表示を追加仮定なしで与える。`diagramCommaRestriction_isIso` と `exists_diagramComma_cocone_lift_full_posetSubset` は元の形状同型と全点を含む順序包含で、同じ指定全余錐の厳密な持ち上げを与える。`exists_diagramComma_cocone_cone_pushout_fix_subshape` は既存部分に含まれる固定部分への厳密持ち上げを点追加へ接続。`posetSubsetPointRemovalOrderIso` と `_comp` は点除去前後の同じ固定部分と元の包含を保持。一般の下方部分の帰納結論は `exists_diagramComma_cocone_lift_poset_lowerSet`。
- I-2 a④ の共有下方部分の持ち上げ：`exists_diagramComma_cocone_pushout_fix_right` は既存部分から共有部分への厳密な指定余錐持ち上げを、右部分への指定余錐持ち上げへ移す。`diagramCommaEvaluation_cone_pushout_apex_isRightCofinal` はその明示条件と下方 comma の filtered 性から新頂点評価の共終性。下方閉部分を固定する有限半順序帰納で指定余錐持ち上げ条件を充足済み。
- 供給経路（コーディネータ許可）：`Stable.PosetSubtypeNerve` の `posetSubtypeNerveIso`・`_hom_ι` と `Stable.FinitePosetNerve.finitePosetNerve_finite` は読み取り専用で直接 import 可。Ind → Stable は第 I 段終了時に R が移動。P の `nerveOrderIso` は循環するため import 不可。新名 `orderIsoNerveIso` を F1 に置く準重複を許可済み、第 I 段終了時に R が P 版を付け替える。
- I-2 a④ の元の族への適用：`indConeSliceInterpolationData_nonempty` は元の q と指定下方余錐 G の二段持ち上げ。`indConeEndpointRaw`・`indConeLowerEndpointRaw` は同じ実終点 comma 内の両全族、`indConeEndpointRaw_boundary` はその全共有境界の厳密な一致。元の C 全図式と全 slice 円柱を保持する。
- Ind-S（P-1 d 向け供給済み）：`presheafInfinity_representableInversion_detects_locality` は P の `RepresentableInversionDetectsLocality (PresheafInfinity A)` の本体に直接適合する無条件の一方向。一般形は `representablePresheafInfinity_precompose_isQCatEquivalence_of_invertible`。Compact の `spaceUniverseDiagram_reflects_invertibleEdge_native` は保守性、`spaceUniverseDiagram_reflects_small_isColimit` は小さい quasicategory 形状の全指定余錐の余極限反映。`isLimitCone_of_conservative_image` は保存された基準極限から元の指定錐を反映。小極限反映そのものはコーディネータ指示で P 自身へ差し戻した。
- Ind-S の許可された逆方向 import：D の `FunctorIsoConstantEdges`・`PinchedSliceCompositionRealization`・`ConstantEdgeFamily` を、各依存閉包外の新規 F1 葉から読み取り専用 import。既存の閉包内 F1 モジュールは変更しない。R が第 I 段終了時に Core/PinchedHom または F1B へ移す。P の局所性述語は F1 から import しない。
- Ind-S（D-16 向け追加）：`IsLocalization.of_subset_invertedEdges` は一般の局所化で `W ⊆ W' ⊆ invertedEdges F` への移行、`IsLocalization.saturate` は反転辺全体への移行。反射・随伴を仮定しない。
- I-2 a④ 完了：`exists_diagramComma_cocone_lift_poset_lowerSet` は任意の下方閉部分の指定全余錐を厳密に持ち上げる。空部分から `smallFinitePosetDiagramComma_isKappaFiltered`、弱下方部分から `diagramCommaEvaluation_finitePoset_isRightCofinal` を導く。`smallFinitePosetDiagramCommaCocone_isColimit` と `indFinitePoset_has_singleFilteredDiagramPresentation` は元の全図式 D を厳密な頂点とする同じ標準全余錐の余極限性と単一 κ-filtered 表示を公開。一般交換・安定性・任意の有限単体集合への表示一般化は主張しない。
- Ind-S (4)（D-16 向け追加）：一般の `IsLocalization F W` の ULift 宇宙持ち上げ・可能なら降下と iff。既存の初頂点写像の専用定理を一般の場合の証明とは扱わない。`invertsEdges_ulift_iff` と `IsLocalization.of_ulift` は新規の葉だけで供給。任意の大きな標的への普遍性を要求する順方向は未証明。
- Ind-S (4) の供給許可：`Stable.UniverseVertexIso` は直接 import せず、辺・三角形・可逆性の上げ下げを `Core.UniverseEdgeTransport` に新名の準重複として置く。既存 Core ファイルは変更しない。R が第 I 段終了時に旧入口を付け替える。
- Ind-S (4) の軽い入口：`UniverseEdge.invertible_up`・`invertible_down` は quasicategory 仮定なしの実可逆辺の宇宙移送。`IsLocalization.precomposition_isFullyFaithful`・`exists_extension` は元の全前合成の充満忠実性・元の実関手同型付き延長。既存の同名でない宣言は不変、`IsLocalization.of_ulift` は同じ元の射の局所化性を元の宇宙へ降ろす。順方向は未公開。
- 深層編集禁止：R の停止窓以外で既存の深層モジュールを変更しない。必要な一般化・新宣言は新規の葉へ置く。やむを得ない深層変更は着手前にコーディネータへ申告する。Universe 4 本・Coherent 2 本・LeftStraighteningRepresentation の変更は全て復元済み。局所化の宇宙操作は `F1B.Localization.LocalizationUniverse` の新名で葉に閉じる。第 I 段終了時に R が既存 F1 の宇宙操作との準重複を整理する。
- Ind-S (5)（K-B-S 向け追加）：`archive/stage-i/kst-lanes/L3-fibration.md` の指定型に従い、元の cocartesian fibration から Kan 置換した空間値 unstraightening への全族写像を、厳密な底と全 fiber 単位の関手同型を保って構成する。I-2 b・Ind-S (4) の区切りで対応。K-B・Sp は import しない。追加の一般初頂点射の相対前合成同値は `relativeFunctorPre_isQCatEquivalence_of_firstVertexLocalization` で供給。一般入口は `IsLocalization.relativeFunctorPre_isQCatEquivalence`（新規 `F1.Diagrams.LocalizationRelativeRestriction`）。既存の `relativeFunctorOverPre_isQCatEquivalence_of_firstVertex` は標準単体間の始点保存射のみで、今回の全族の型とは異なる。
- 次の一手：I-2 c と一般初頂点相対制限は監査・保存済み、二段目完了の規約に従い区切る。再開時は Ind-S (5) の全族単位、Ind-S (4) の順方向、I-2 e の compact 生成界面。I-2 d の交換入力差し替えは第 I 段終了時。Ind-S (4) 順方向は既存入口なし、小さい内ホーン充填閉包の新規葉を許可済み。優先順位は I-2 b の後。P 向け局所性・余極限反映・保守性・一般極限反映と D 向け局所化飽和は公開済み。

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

実施記録・現在地の詳細・型一覧は [archive/infinity-core-F1-log.md](../../infinity-core-F1-log.md) に移した（2026-10-19）。現在地は冒頭の引き継ぎ節が正本で、工程ごとの記録はコミットメッセージに置く。
