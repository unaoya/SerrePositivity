# P レーン：presentable ∞ 圏（HTT 5.4〜5.5）

> **v3（2026-10-24）**：N は **P レーン**に吸収。本ファイルが P の正本。
> P-1 g（P_Σ）の引き継ぎは e-infinity-algebras.md の N 節を併読する。
> 所有：`F2/Presentable/`（P-f の `Localization/`・P-d の `Duality/`・`AccessiblePullback/`・P-s の `Supply/` を除く）、`HomotopyLimits/`。
> 集約：`SerrePositivity/InfinityCategories/F2/Presentable.lean`、`HomotopyLimits.lean`。

## 引き継ぎ（2026-10-24）

### 現在地
- P-1 a は完了。正則 κ、小さい κ-filtered 余極限、小さい κ-compact 全部分生成圏による accessibility、
  元の Ind 比較の全同値、accessible 関手、同値不変性、正則濃度変更を提供する。
- P-1 b は完了。P-1 g の7ファイルの修正・接続・集約・両公理監査を検証済み。元の左 Kan 延長の sifted 保存と制限の本質的全射性、filtered／幾何学的実現保存関手の全 ∞ 圏の普遍性を提供する。
- 任意の小さい quasicategory C 上の前層について、有限底上符号族の連続 left fibration 置換から、
  宇宙 u の小さい compact 全部分生成圏を構成した。各指定前層を厳密な頂点とする filtered 全表示を持つ。
- 通常の strict filtered 全余錐の native 性、元の left fibration への頂点回収、
  一般 coherent filtered 添字での相対 Hom 保存、有限模型の置換の compact 性を提供する。
  図式の strict 化は既存の under 切断の共同分類を再利用し、全添字の一つの関手同型で比較する。
- 一般の前層の ℵ₀-accessibility と presentable 性、構成した小さい生成圏の Ind 同値を提供する。
  その具体的な Ind 模型の全小余極限・presentable 性も、存在入力を残さず供給する。
- 一般の正則 κ の Indκ(A) は、全小余極限の存在を明示すれば presentable。
  presentable 圏を κ-compact 生成する小さい A に対しては、Ind 自身の余完備性を入力にせず回収する。
- 局所小ささは、元の各 pinched Hom と宇宙 u の Kan 空間の持ち上げとの全同値で定義した。
  固定頂点写像の小ささから二対象の小さい全部分模型を作り、Ind・accessible・presentable 圏へ供給する。
- P-1 g は g1〜g7 を完了。元の Yoneda 制限上の有限余積条件と全小余極限保存を同値にした。
- P-1 c は完了。個々の presentable 圏の全小極限・反映による小余極限構成を提供する。
  ユーザー確定により HTT 5.5.3.13 は e へ移し、c は六項目のままとする。
- P-1 d は完了。連続前層の表現可能性と随伴関手定理（5.5.2.9）を比較入力なしで提供する。

### 残り（依存順）
1. P-1 e：P の e5 fiber accessibility は公開済み。e8 は Supply まで統合済み。accessible 一般版（5.4.6.6）は P-d の到着待ち、稼働24時間により本チャットを引き継ぐ。
   e6 の全体同値（5.5.3.4）と e7 の小極限（5.5.3.13）は保留（第 II 段／R、ユーザー判断）。
2. P-1 f：Bousfield 局所化の存在（HTT 5.5.4.15）は P-f が完了（`88774c8be`、00:15 確認）。
   P は同ディレクトリを編集せず、e8 で Localization/・Duality/・Supply/・LocalObjects/・AccessiblePullback/ を集約・監査し、P-d の一般版の到着後に閉じる（Supply 修正は `10ad58008` で到着）。

### 主要宣言
- `IsKappaAccessible`、`IsAccessible`、`IsKappaCompactGenerating`、`IsKappaAccessibleFunctor`、`IsAccessibleFunctor`
- `IsKappaAccessible.exists_indEquivalence`、`isKappaAccessible_iff_indEquivalence`、`indComparison_isFullyFaithful_of_compact`（P-f 供給済み）
- `IsCardinalChangeBound`、`cardinalChangeBound_aleph0`、`isKappaCompact_iff_equivalence_universe`、`isKappaCompact_smallPosetColimit_universe`（P-9）
- `IsPresentable`、`isPresentable_iff_cocompleteIndEquivalence`、`space_isPresentable`
- `leftFibrationStrictCocone_isColimit`、`continuousLeftFibrationUnitVertexIso`、`exists_finiteLeftFibrationPresentation`
- `finiteLeftFibrationDiagram_in_family`、`leftFibrationDiagramStrictificationIso`、`finiteRelativeHom_isKappaAccessibleFunctor`
- `finiteLeftFibrationReplacement_isCompact`、`presheafCompactGeneratorCategory`、`presheafCompactGeneratorInclusion`
- `presheafCompactGeneratorInclusion_isCompactGenerating`、`presheaf_isKappaAccessible_aleph0`、`presheaf_isPresentable`
- `presheaf_exists_compactGeneratorIndEquivalence`、`indInfinity_isPresentable_iff_hasSmallColimits`
- `indInfinity_isPresentable_of_compactGenerating`、`presheafCompactGeneratorInd_isPresentable`
- `IsLocallySmall`、`indInfinity_isLocallySmall`、`IsAccessible.isLocallySmall`、`IsPresentable.isLocallySmall`
- `sigmaFiniteFamilyComparison_isIso`、`sigma_preservesFiniteCoproducts_iff_yoneda`
- `sigma_preservesSmallColimits_iff_yoneda_finiteCoproducts_sifted`、`sigmaLeftKanExtension_preservesSmallColimits_iff`
- `unitIntervalMapAt`、`unitIntervalMapAt_commaTransportIso`、`unitIntervalMapAt_unitCommaSectionTargetFiberVertex`
- `unitIntervalMapAt_commaTransportIso_unit`（P-6）、`uliftNerveCone_coherent_eq`（`HomotopyLimits/NerveConeCoherentComparison`、P-8）。
- `mapJoinCocone_isColimit_of_adjunction`、`adjunction_preservesSmallColimits`、`hasColimit_of_reflection`
- `IsPresentable.exists_reflectiveIndModel`、`IsPresentable.exists_presheafReflection`、`reflectiveIndModel_hasSmallColimits`
- `reflectiveSubcategory_hasSmallLimits`、`ind_hasSmallLimits_of_hasSmallColimits`、`IsPresentable.hasSmallLimits`
- `IsPresentable.exists_limitDetectingPresheafModel`、`IsPresentable.exists_limitCone_representables`
- `tensor_hasSmallColimits`、`pullback_hasSmallColimits`、`pullback_preservesSmallColimits_iff_components`
- `functor_isPresentable`、`piSSet_isPresentable`、`PrL`、`PrR`、`fiber_isAccessible_of_presentable`、`fiber_isAccessible_of_cocomplete_accessible`、`pullback_isPresentable_of_accessiblePullback`、`exists_presentablePullback_compactCandidate`、`isKappaCompact_smallQuasicategoryColimit_universe`、`exists_common_kappaFiltered_cofinal_index`（P-10）
- `bousfieldReflection`、`bousfieldLocalObjects_isPresentable`、`bousfield_generatedEdges_eq_invertedEdges`、`bousfieldLocalizationFunctor_isLocalization_generatedEdges`（Localization 名前空間、P-f）。`IsAccessible.exists_common_compactCardinal`、`adjunctionCovariantHomIso`
- `adjunction_hom_preservesKappaFilteredColimits_iff`、`adjunction_exists_common_hom_preservationCardinal`
- `SendsSmallColimitsToLimits`、`IsRepresentableSmallSpaceFunctor`、`presheafRepresentationIso`
- `presentableContinuous_isRepresentable`、`exists_rightAdjoint_iff_preservesSmallColimits`（d2・d4、比較入力なし）

- `IsCorepresentableSmallSpaceFunctor`、`accessible_preservesLimits_isCorepresentable`（d3、存在入力なし）。
- `IsAccessible.exists_smallCovariantHom`、`IsAccessible.exists_smallContravariantHom`
- `exists_leftAdjoint_iff_covariantHom_representable`
- `exists_rightAdjoint_of_contravariantHom_representable`（全自然な反変 Hom 表現から構成）。
- `exists_leftAdjoint_iff_accessible_preservesLimits`、`rightAdjoint_isAccessible`（d5、宇宙比較入力なし）。

### 依存と提供
- 読み取り専用：`F1/`、`F1B/`、`Core/`、`F2/Ind/`・`Compact/`・`Idempotent/`・`CatInfinity/`・`FilteredExchange/`、既存 `Stable/` の界面。
- 主な分類界面：`leftStraighteningInfinityEquivalence`、`leftStraighteningInfinityMap_evaluateIso`、
  `relativeFunctorEvaluationComparisonIso`、`underSectionClassificationIso`、`strictLeftWeightedClassificationIso`。
- 相対 Hom と既存の大きい共変 Hom は `relativeHom_covariantModelIso` で全自然比較する。
- 一般の前層の compact 生成・accessibility・presentable 性と、accessible 圏の局所小ささを提供する。
  Ind 側の a7 はこの完成範囲の新しい入力ではなく、既存の明示入力を勝手に無条件化しない。

### P-1 g の到達点
- g4：filtered 余極限と幾何学的実現のみを仮定する標的への、同じ二種類を保存する全関手 ∞ 圏の制限同値を提供する。
- g6：元の Yoneda の有限余積保存と、P_Σ 全体の有限余積・sifted 保存による全小余極限保存判定を提供する。
  指定した全余極限比較の可逆性と元の形状の全余極限保存の同値を提供する。
  元の Yoneda 制限上の有限余積条件へ縮約し、全小余極限保存判定まで提供する。
- g5：小余積と幾何学的実現からの小余極限、専用反映、
  元の前層 bar の反映による simplicial Ind 表示を提供する。
  F1 の密度・各点余極限・小余積の公開 API を利用し、他レーンへの供給依頼にはしない。

### 既知の問題
- 任意の小さい A の Indκ(A) は無条件には presentable でない。
  一般の公開定理の余完備性条件と、構成した前層生成圏の具体的な無条件の例を区別する。
- accessibility の濃度変更には `IsCardinalChangeBound κ μ` と μ の正則性を要求し、κ ≤ μ だけでは主張しない。
- d2 の局所性比較は Ind-S の `presheafInfinity_representableInversion_detects_locality` で解消済み。
  P の反映移送と小さい Hom から、d2・d4・d5 を無条件に接続した。
- 指定宇宙変更の小極限反映は P の `spaceUniverseDiagram_reflects_small_isLimit` で構成済み。
  Ind の小余極限反映と合わせ、宇宙比較の追加入力は残らない。
- e5 の濃度評価は Ind-S (7)、`d39ae1d0a` で供給済み。`SmallHullCardinal` の有界 Hull を使い、任意の μ-small 試験図式を同じ濃度の quasicategory へ厳密に因子化する。
- P-11 は P-s が供給済み。P-12 の Fun 内の全自然な end 比較・compact 性は保留（第 II 段／R、ユーザー判断）。e8 は Supply のコミット済み公開範囲を統合し、P-12 の完成を待たない。
- e8 の Supply の匿名 instance 衝突・未コミット集約は P-s の `10ad58008` で解消済み。P-12 は保留（第 II 段／R）。AccessiblePullback の一般版だけが未到着。

### 未コミット
- なし。Supply.All を含む両集約 10501 jobs、P 6372 宣言・H 12233 宣言の再帰公理監査と既存 H 監査は成功。標準三公理のみ。公開 import 閉包6811モジュールに未コミットの他レーン変更なし。AccessiblePullback の一般版だけが未到着。

### 次の一手
- e5：P の fiber 版は `fiber_isAccessible_of_presentable`（強い入口 `fiber_isAccessible_of_cocomplete_accessible`）で構成済み。共通濃度・全 compact 成分の小模型・元の各対象の小さい μ-filtered 全表示を接続し、点射の全小余極限保存を仮定しない。対象・集約ビルドと公理監査済み。公開名を報告し、e8 の準備へ移る。accessible 一般版 `pullback_isAccessible` は P-d 所有。presentable 系は P の `PresentablePullback` で一般命題を明示入力として構成し、到着時に代入する。
- e6 の全体同値と e7 の小極限は保留（第 II 段／R）。Localization.All・Duality.All・Localization.LocalObjects.All・Supply.All は接続済み。P-d の一般版到着後、P の条件付き presentable 系へ代入し AccessiblePullback.All を接続、両集約・監査で e8 を閉じる。今回は稼働24時間のため検証済みの状態を保存して停止・引き継ぎ。
- e の準備として二項積・同値持ち上げを持つ引き戻しの全小余極限と成分保存判定を提供する。
  `piSSet_isPresentable` は任意の小さい族を扱い、各射影の全小余極限保存と成分判定も構成済み。
- E2・K-B から供給依頼が来たら工程の区切りで優先する。

## P-1 b 三段目（v3）

- [x] b1. strict filtered 全余錐の left fibration ∞ 圏での余極限性。
- [x] b2. 有限底上模型による、元の指定 left fibration の小さい全表示。
- [x] b3. 一般 coherent filtered 添字での相対 Hom 保存と有限模型の compact 性。
- [x] b4. 一般の小さい底上の前層の小さい compact 生成圏と accessibility。
- [x] b5. 前層の presentable 性、条件を明示した Indκ(C) の presentable 性。
- [x] b6. 局所小ささの公開界面、集約ビルド・公理監査・引き継ぎ更新。

## P-1 g 三段目（v3）

- [x] g1. 未接続7ファイルの修正・検証と全 Hom 族の自然比較。
- [x] g2. 元の左 Kan 延長の任意小 sifted 余極限保存。
- [x] g3. Yoneda 制限の本質的全射性。
- [x] g4. 保存関手 ∞ 圏の全同値による普遍性。
- [x] g5. simplicial Ind 表示と filtered／geometric realization による生成。
  - [x] 一般補題：小余積と幾何学的実現から小余極限を構成する。
  - [x] 反映 L の構成：既存の sifted 保存と有限余積保存から P_Σ 専用反映を構成する。
  - [x] bar 表示の接続：反映を適用して simplicial Ind 表示へ接続する。
- [x] g6. Yoneda の有限余積保存と全余極限保存判定。
- [x] g7. 集約ビルド・公理監査・引き継ぎ更新。

## P-1 c 三段目（v3）

- [x] c1. 前層の反映による native な小余極限の構成と保存。
- [x] c2. 小さい compact 生成圏に沿う制限 Yoneda と前層反映。
- [x] c3. presentable 圏の小余極限を反映模型・Ind 同値へ接続。
- [x] c4. 反映された全部分圏の小極限構成。
- [x] c5. 表現可能関手による検出と、presentable 圏の全小極限の存在。
- [x] c6. 集約ビルド・両公理監査・公開界面と引き継ぎ更新。

## P-1 d 三段目（v3）

- [x] d1. 小さい対象族の共通 compact 濃度と Hom 族の保存判定。
- [x] d2. 小余極限を小極限へ送る前層の表現可能性。
- [x] d3. accessible かつ小極限保存な空間値関手の余表現可能性。
- [x] d4. 小余極限保存と右随伴の存在の同値。
- [x] d5. accessible・小極限保存と左随伴の存在の同値、右随伴の accessibility。
- [x] d6. 集約ビルド・両公理監査・公開界面と引き継ぎ更新。

## P-1 e 三段目（v3）

- [x] e1. Pr^L・Pr^R の対象・関手圏・全 ∞ 圏の定義。
- [x] e2. Fun(K,C) の小余極限と各点計算。
- [x] e3. Fun(K,C) の accessibility と presentable 性（5.5.3.6、小さい ∞ 圏 K）。
- [x] e4. 積の presentable 性。
- [ ] e5. P の fiber accessibility は公開済み。accessible 一般版（5.4.6.6）は P-d 待ち。presentable 系（5.5.3.12）は一般命題を明示入力とする `pullback_isPresentable_of_accessiblePullback` を P の新規葉で構成。
- [ ] e6. 保留（第 II 段／R）：Pr^L と Pr^R の全体同値（5.5.3.4）。`Duality/` は読み取り専用。
- [ ] e7. 保留（第 II 段／R）：Pr^L の小極限と Cat∞ での計算（5.5.3.13）。
- [x] e8. 完了（2026-10-26）：AccessiblePullback.All・Supply.All・Duality.All・Localization.All・LocalObjects.All を P 集約と全宣言監査へ接続。両集約 10625 jobs、P 7044 宣言・H 12233 宣言の再帰公理監査と既存 H 監査は成功。標準三公理のみ。
  - 引き継ぎ：一般版は `AccessiblePullback.pullback_isAccessible`（`636012a5f`）。これを `pullback_isPresentable_of_accessiblePullback` に代入した追加入力なしの presentable 引き戻しを監査内の使用例で検証済み。
  - Supply の匿名局所 instance 衝突は `10ad58008` で解消済み。ローカル import 閉包6935モジュールに未コミットの他レーン変更なし。葉は編集せず、今回の保存対象は P 集約・P 監査・本 e8 節のみ。
  - 第 II 段／R へ保留：e6-3〜e6-6、e7、P-12。上の旧引き継ぎの到着待ち記述は本 e8 完了記録で更新する。未完の統合作業・供給依頼なし。工程完了により停止。

## P-6 三段目

- [x] 局所区間比較と元の comma 点を始端とする円柱。
- [x] 終点の回収と普遍輸送との関手同型、既存比較への特殊化。
- [x] 集約ビルド・両公理監査・公開名の引き継ぎ。

## 規約

- foundations.md §8。所有だけ `set -o pipefail` のうえ `git commit --only`。新規 sorry・公理・引用なし。
- 他レーンのファイルは読むだけ。補題が自レーンの import 閉包の外にあれば、コーディネータ経由で所有レーンへ依頼する。
- モジュールの移動・改名・削除は R の停止窓で行う。記録された未追跡ファイルの再配置は再開指示に従う。
- 主経路に `ModelCategory SSet` 等の instance 仮定を入れない。docstring は 概要/方針/規約/使われ方。
- Ind・標的は u+1、添字と有限符号は u。本文300行以内、引き継ぎ100行以内。実施記録はコミットメッセージ。
- 報告後は承認を待たず続行。二段目の完了・設計変更提案・所有 import 閉包破損・稼働24時間で停止する。
