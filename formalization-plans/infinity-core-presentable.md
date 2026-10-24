# P レーン：presentable ∞ 圏（HTT 5.4〜5.5）

> **v3（2026-10-24）**：N は **P レーン**に吸収。本ファイルが P の正本。
> P-1 g（P_Σ）の引き継ぎは e-infinity-algebras.md の N 節を併読する。
> 所有：`F2/Presentable/`、`HomotopyLimits/`。N の局所化・sifted 系は R16 で前者へ移動済み。
> 集約：`SerrePositivity/InfinityCategories/F2/Presentable.lean`、`HomotopyLimits.lean`。

## 引き継ぎ（2026-10-24）

### 現在地
- P-1 a は完了。正則 κ、小さい κ-filtered 余極限、小さい κ-compact 全部分生成圏による accessibility、
  元の Ind 比較の全同値、accessible 関手、同値不変性、正則濃度変更を提供する。
- P-1 b は完了。P-1 g の7ファイルの修正・接続・集約・両公理監査を検証済み。現在は左 Kan 延長の sifted 余極限保存と普遍性を進める。
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
- P-1 g は未完了。N の検証済み範囲は e-infinity-algebras.md の N 節を正本とする。

### 残り（依存順）
1. P-1 g：元の左 Kan 延長の任意小 sifted 余極限保存、Yoneda 制限の本質的全射性・全関手 ∞ 圏の同値。
   未接続7ファイルの検証から再開。HTT 5.5.8.14〜15、30〜80時間（暫定）。
2. P-1 c：presentable の小さい極限・余極限。HTT 5.5.2.4・5.5.3.13。
3. P-1 d：随伴関手定理。余極限保存から左随伴、accessible かつ極限保存から右随伴。HTT 5.5.2.9。
4. P-1 e：Pr^L／Pr^R の双対性。HTT 5.5.3.4。
5. P-1 f：Bousfield 局所化の存在。N の局所対象・強飽和性・条件付き反射を再利用し、局所置換を実証する。
   HTT 5.5.4.15。c〜f の個別見積もりは各着手時に精査する。

### 主要宣言
- `IsKappaAccessible`、`IsAccessible`、`IsKappaCompactGenerating`、`IsKappaAccessibleFunctor`、`IsAccessibleFunctor`
- `IsKappaAccessible.exists_indEquivalence`、`isKappaAccessible_iff_indEquivalence`、`IsKappaCompactGenerating.compact_iff_retract`
- `IsCardinalChangeBound`、`coherentCardinalFilteredLimitExchange_poset`、`IsKappaAccessible.of_cardinalChangeBound`
- `IsPresentable`、`isPresentable_iff_cocompleteIndEquivalence`、`space_isPresentable`
- `leftFibrationStrictCocone_isColimit`、`continuousLeftFibrationUnitVertexIso`、`exists_finiteLeftFibrationPresentation`
- `finiteLeftFibrationDiagram_in_family`、`leftFibrationDiagramStrictificationIso`、`finiteRelativeHom_isKappaAccessibleFunctor`
- `finiteLeftFibrationReplacement_isCompact`、`presheafCompactGeneratorCategory`、`presheafCompactGeneratorInclusion`
- `presheafCompactGeneratorInclusion_isCompactGenerating`、`presheaf_isKappaAccessible_aleph0`、`presheaf_isPresentable`
- `presheaf_exists_compactGeneratorIndEquivalence`、`indInfinity_isPresentable_iff_hasSmallColimits`
- `indInfinity_isPresentable_of_compactGenerating`、`presheafCompactGeneratorInd_isPresentable`
- `IsLocallySmall`、`indInfinity_isLocallySmall`、`IsAccessible.isLocallySmall`、`IsPresentable.isLocallySmall`

### 依存と提供
- 読み取り専用：`F1/`、`F1B/`、`Core/`、`F2/Ind/`・`Compact/`・`Idempotent/`・`CatInfinity/`・`FilteredExchange/`、既存 `Stable/` の界面。
- 主な分類界面：`leftStraighteningInfinityEquivalence`、`leftStraighteningInfinityMap_evaluateIso`、
  `relativeFunctorEvaluationComparisonIso`、`underSectionClassificationIso`、`strictLeftWeightedClassificationIso`。
- 相対 Hom と既存の大きい共変 Hom は `relativeHom_covariantModelIso` で全自然比較する。
- 一般の前層の compact 生成・accessibility・presentable 性と、accessible 圏の局所小ささを提供する。
  Ind 側の a7 はこの完成範囲の新しい入力ではなく、既存の明示入力を勝手に無条件化しない。

### 未コミット
- 引き継いだ次の7本は修正・接続・検証済みで、P-1 g1 の保存対象。所在は `F2/Presentable/`。
- `PresheafDensityLeftKan.lean`、`PresheafElementsLeftKan.lean`、`PresheafUniverseArbitraryColimits.lean`、
  `SigmaHomWeightComparison.lean`、`YonedaHomWeightColimits.lean`、`YonedaWeightFamilyComparison.lean`、`YonedaWeightLeftKan.lean`。
- g2 の全 co-Yoneda による極限反映・係数制限、全 Hom 錐、sifted 保存、普遍性の作業中モジュールは、検証・集約接続後に保存する。他レーンは変更しない。

### 既知の問題
- 任意の小さい A の Indκ(A) は無条件には presentable でない。
  一般の公開定理の余完備性条件と、構成した前層生成圏の具体的な無条件の例を区別する。
- accessibility の濃度変更には `IsCardinalChangeBound κ μ` と μ の正則性を要求し、κ ≤ μ だけでは主張しない。
- 未接続7ファイルの証明本体と R13 による宣言名の変化は、P-1 g 着手時に改めて検証する。
- 最終検証ログ：`/tmp/p-v3-final-build.log`、`/tmp/p-v3-final-presentable-audit.log`、`/tmp/p-v3-final-homotopy-audit.log`。

### 次の一手
1. P-1 b の完了後は新チャットで P-1 g を再開する。e-infinity-algebras.md の N 節を併読する。
2. 新所在の `Presentable.SigmaHomWeightComparison` と `Presentable.PresheafUniverseArbitraryColimits` を対象ビルドし、
   未接続7ファイルを依存順に修正・検証する。元の指定単位と全係数の自然性を保持する。
3. 両対象の成功後にだけ集約・監査へ接続し、所有の集約ビルドと全公理監査を行う。
4. 元の左 Kan 延長の sifted 余極限保存へ進む。全 Hom 比較で元の指定余錐像の普遍性を判定する。

## P-1 b 三段目（v3）

- [x] b1. strict filtered 全余錐の left fibration ∞ 圏での余極限性。
- [x] b2. 有限底上模型による、元の指定 left fibration の小さい全表示。
- [x] b3. 一般 coherent filtered 添字での相対 Hom 保存と有限模型の compact 性。
- [x] b4. 一般の小さい底上の前層の小さい compact 生成圏と accessibility。
- [x] b5. 前層の presentable 性、条件を明示した Indκ(C) の presentable 性。
- [x] b6. 局所小ささの公開界面、集約ビルド・公理監査・引き継ぎ更新。

## P-1 g 三段目（v3）

- [x] g1. 未接続7ファイルの修正・検証と全 Hom 族の自然比較。
- [ ] g2. 元の左 Kan 延長の任意小 sifted 余極限保存。
- [ ] g3. Yoneda 制限の本質的全射性。
- [ ] g4. 保存関手 ∞ 圏の全同値による普遍性。
- [ ] g5. simplicial Ind 表示と filtered／geometric realization による生成。
- [ ] g6. Yoneda の有限余積保存と全余極限保存判定。
- [ ] g7. 集約ビルド・公理監査・引き継ぎ更新。

## 規約

- foundations.md §8。所有だけ `set -o pipefail` のうえ `git commit --only`。新規 sorry・公理・引用なし。
- 他レーンのファイルは読むだけ。補題が自レーンの import 閉包の外にあれば、コーディネータ経由で所有レーンへ依頼する。
- モジュールの移動・改名・削除は R の停止窓で行う。記録された未追跡ファイルの再配置は再開指示に従う。
- 主経路に `ModelCategory SSet` 等の instance 仮定を入れない。docstring は 概要/方針/規約/使われ方。
- Ind・標的は u+1、添字と有限符号は u。本文300行以内、引き継ぎ100行以内。実施記録はコミットメッセージ。
- 報告後は承認を待たず続行。二段目の完了・設計変更提案・所有 import 閉包破損・稼働24時間で停止する。
