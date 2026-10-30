# Asymptotic の整理計画（2026-10-30）

概要：論文の層の見直しのうち、`SerrePositivity/Asymptotic/`（87 ファイル、約 8700 行）について、ファイルの統合、未使用の宣言・死んだファイルの
削除、重複の一本化、Mathlib への置き換え、置き場所の修正をまとめる。調査（2026-10-30、読むだけ）の結果を元にした計画で、実作業はまだ行っていない。
方針：作業の決まりは [commutative-algebra-refactor-plan.md](commutative-algebra-refactor-plan.md) の §2 と同じ。
規約：Mathlib の確認は固定版（2026-10-07）と最新版（2026-10-28）の両方で行い、差はなかった。`sorry`・`axiom` はない。
使われ方：作業を再開するときの手順書。

## 1. 中身と外への影響

論文 §4–5 の漸近的な「階数の商」の道具。

- `FreeSequence R s`（階数が O(s) の自由加群の列）、その有界ホモトピー圏 `SequenceHomotopy`、小さい階数の対象による Verdier 商
  `SequenceRankQuotient`、スカラーの台を持つ部分圏、冪等完備化、環の取り替え。
- 超極限で正規化した長さ・Betti 数・Euler 標数（`normalizedLimit`）、Koszul の公式、極小分解からの下からの評価。
- もう一本の流れ：長さが有界な加群の列、その Serre 商・導来商、t 構造、一様な持ち上げ。

- **BhattScholze・CLMST は Asymptotic を import せず、名前も使わない。** 改名・移動の波及は Paper/Section4・5 と監査だけ。
- 層は綺麗：Asymptotic は Paper・BS・CLMST を import しない。
- 逆向きの import が 1 か所：`DifferentialGraded/Verdier/OrderSquare.lean` が `Asymptotic.PaperRankQuotient` を import する。その先
  （ChecksOrderSquare・U17 → ChecksU17Integration）はどこからも import されずビルドされない。DifferentialGraded の計画で扱う。

## 2. 統合（87 → 約 12 ファイル）

| 新しいファイル | 元のファイル |
| --- | --- |
| NormalizedLimit（軽い：Mathlib の解析だけ） | NormalizedLimit・NormalizedLowerBound、EulerLimit の `normalizedLimit_finsum`、LengthFamilies の最初の 3 補題 |
| FreeSequence | FreeSequence・SequenceLinear・FreeSequenceBaseChange、RankQuotient の `FreeSequence.*` |
| SequenceComplex | SequenceComplex・AssembleComplex・SequenceDerived・SequenceResolution・FreeSequenceTensor |
| RankQuotient | RankQuotient・RankQuotientBaseChange・SupportedRankQuotient・SequenceSupport・SequenceBaseChangeSupport・SupportedRankBaseChange・BaseChangeIdentity・BaseChangeComposition |
| SequenceKoszul | SequenceKoszul・SequenceKoszulSupport・SequenceKoszulBounds・KoszulTower・KoszulHomologyLimit |
| SequenceHomology | SequenceHomology・SequenceHomologyBounds・SequenceHomologyLocalization・RankHomologyShift・RankHomologyShiftNatural・CompletedHomology・CompletedHomologyLength |
| Completed | SupportedKaroubi・SupportedKaroubiTriangulated・CompletedRankEvaluation・CompletedKoszulFormula・CompletedComplexEvaluation・CompletedBaseChangeSupport |
| Euler | RankEuler・RankEulerAdditivity・RankEulerComparison・CompletedEulerAdditivity・CompletedEulerComparison・CompletedK0Comparison・EulerLimit の残り |
| Minimal | MinimalResolutionFamily・MinimalSupport・MinimalTruncationComparison・MinimalBettiEvaluation・RankMinimalLowerBound・RankVanishing |
| PaperQuotient | PaperRankQuotient・PaperRankEvaluation・PaperSupportChange・FactorizationSupport・TruncationComparison・ComplexEvaluationIndependence・PaperBaseChange・BaseChangeComparison・PaperBaseChangeEvaluation・PaperComplexBaseChange・PaperTwist・PaperTwistLowerBound・LocalBaseChangeBounds・OrdinaryTwistEvaluation・PaperMinimalLowerBound |
| LengthSequence | ModuleSequence・LengthBoundedSequence・LengthSerreQuotient・LengthQuotientValue・SmallLengthSerreQuotient・FamilyHomologyTruncation・FamilyPostnikov |
| UniformLift | SupportedDerivedImage・SupportedPureDerivedImage・SupportedUniformLift・SmallSupportedUniformLift・RankSmallHomologyCriterion・SmallRankHomologicalKernel・SupportedSequenceTStructure・SupportedRankTStructure・OrdinaryHeartResolution |

- 外へ回す：KoszulBaseChange（30 行、Koszul だけを import）→ CommutativeAlgebra/Koszul。EulerLimit の `lengthHomology_zero_outside`・
  `lambdaEuler_isBigO` → PerfectComplex/NormalizedEuler か AsymptoticLengthBounds。FamilyPostnikov・FamilyHomologyTruncation（導来圏の ℕ 族）
  → HomologicalAlgebra。`uniformlyPowTorsion` と Serre 類のインスタンス（ModuleSequence）は CommutativeAlgebra/PowTorsionCategory と同じ型の
  議論なので、そちらから点ごとに導く。
- PaperQuotient の 15 本は論文 (4.2)・ひねり・K₀ の作用など論文固有の主張。Paper/Section4 へ移す案も（Paper が import し、Paper を import しないので安全）。
  決定待ち（§8）。

## 3. 死んだファイル

- FreeSequenceGenerator・LengthDerivedQuotient・SmallLengthDerivedQuotient・PaperRankGenerators・PaperVanishing。到達できるのは
  `Paper/Section4/Foundations`（26 本の import と docstring だけの再エクスポート。importer はルートだけ）経由と、それ経由でしか届かない
  FlatRealization 経由だけ。Foundations と一緒に削除する。
- CompletedK0Comparison は唯一の定理が未使用で、PaperBaseChange への import の中継だけ。統合で消える。

## 4. Mathlib との重なり

- `isBigO_of_nonneg_le` → `Asymptotics.isBigO_of_le`（＋`Real.norm_of_nonneg`）か `IsBigO.of_bound 1`（確度高）。
- `moduleSequence_shortExact_eval` は `ShortExact.map`（確度高、インライン化）。
- `normalizedLimit` の `_add`・`_const_mul`・`_sum`・`_nonneg`・`_mono` は `Tendsto.limUnder_eq` の薄い包み。有界性の段は
  `isBigO_iff_isBoundedUnder_le_div` と `IsCompact.ultrafilter_le_nhds` で短くできる（確度中）。
- `FreeSequence.changeMatrix` は `Matrix.map` の見込み（確度中、未確認）。

## 5. 一本化

- **商の二本立て**：「Completed」（Verdier 商 → Karoubi）と「Paper」（Karoubi → Verdier 商）が同じ結果を二度示している。
  `completedRankBetti_koszul_formula`・`paperRankBetti_koszul_formula`・`paperBaseChangeBetti_koszul_formula`、`*EulerK0_changeRing` の 3 本、
  `*ChangeRingIdIso`・`*ChangeRingCompIso` は 5〜6 の水準で作られ、不変量の族（supportedRank*・completedSupported*・completedRank*・paperRank*・
  paperBaseChange*）ごとに `_nonneg`・`_iso`・`_hasFiniteSupport`・`_triangle`・`EulerK0_mk` が繰り返される。
  → CategoryTheory の `homologicalEulerK0` の形の一般 API（ホモロジー的関手 → Betti・Euler・K₀）に寄せ、各水準はその例にする。
  `maxHeartbeats 800000` の 19 か所（13 ファイル）はすべて Paper 側で、一本化で減らせる見込み。
- Small 版と通常版：LengthDerivedQuotient と SmallLengthDerivedQuotient は Serre 類と引数（U・hU・hs）以外行単位で同じ。LengthSerreQuotient と
  SmallLengthSerreQuotient、SupportedUniformLift と SmallSupportedUniformLift も並行。Serre 類（`IsSerreClass` の述語）を引数にして一度だけ書く。
- `RankHomologyShift` の点ごとの同型を `RankHomologyShiftNatural` で自然同型として作り直している。自然同型だけを残す。
- `normalizedLimit_finsum` は `normalizedLimit_sum` の包み。
- PerfectComplex との並行（形が似ているだけ、確度中）：`minimal_rank_isBigO/_isLittleO` と `resolutionFamily_rank_isBigO/_isLittleO`、
  `isBigO_of_nonneg_le` と `ennreal_isBigO_of_le_sum_nsmul`。

## 6. 未使用（全 87 ファイルを名前で走査。instance 約 40 は暗黙に使われるので除く）

`completedSupportedEuler_triangle`、`completedSupportedEulerK0_toKaroubi`、`completedSupportedBetti_nonneg/_iso`、
`completedSupportedEulerK0_changeRing`、`completedRankEuler_triangle`、`familyHomology_truncLE/_truncGE_lengthBounded`、
`changeRing_rank`（simp）・`changeRing_rank_isLittleO`、`lengthFamily_isLittleO_iff`、`lengthFamily_normalizedLimit_zero_iff`、
`lengthQuotientValue_obj`（simp）、`sequenceLength_le_of_mono/_of_epi`、`minimal_truncated_paper_supported`、`normalizedLimit_generator_pos`、
`sequenceResolutionHomologyZeroIso`・`sequenceResolutionHomology_isZero`、`paperBaseChangeBetti_nonneg`、`paperSupportedRank_eq_of_radical_eq`、
`completedSupportedEuler_image`、`supportedRankEuler_triangle`、`supportedRankEulerK0_changeRing`、`completedRankEuler_pos_of_minimal`、
`exists_model`、`sequenceRankQuotient_smallComplex_isZero`、`SequenceKaroubi`、`sequenceKoszulHomology_normalizedLimit_eq_zero`、
`supportedKaroubi_essImage`、`supportedDerivedImage_pure`、`supportedRankQuotient_retract`、`supportedRankTStructure_bounded`、
`supportedRankKaroubi_has_representative`、`supportedSequenceTStructure_evaluation_tExact`、`supportedDerivedImage_finiteAmplitude`、
`paperTruncation_K0_eq`、`exists_uniform_nat_bound`（提出しないなら）。死んだファイルの中のものは §3 で消える。
`completedSupportedEuler_hasFiniteSupport`・`completedSupportedBetti_hasFiniteSupport` は `scripts/audit_euler_betti_finite_support.lean` が使うので残す。

## 7. その他

- `hs : ∀ n, 0 < s n` がほぼ全補題に通されている。構造体（正の列）か型クラスにまとめる。LengthDerivedQuotient・LengthSerreQuotient は
  証明の引数（U・hU・hs）を圏・型の引数に持っていて扱いにくい。
- 一般的すぎる名前（`SerrePositivity.Asymptotic` 直下）：`isBigO_of_nonneg_le`、`exists_uniform_nat_bound`、`exists_model`、
  `map_coordinate_mem_ideal`、`below_rankSmall`、`paper_inclusion_isIso`、`scalar_zero_of_factorization`。
- `paper*`・`Paper*` の接頭辞は出典を表していて数学の内容を表していない。Paper/Section4 へ移すなら名前を見直す。
- `completedSupportedChangeRing` の `@[implicit_reducible]` が要るか確かめる。

### 提出候補

関手圏での完全性が評価で判定できること（`moduleSequence_exact_of_eval` の一般化）、`nonneg_add_isBigO_iff`・`nonneg_add_isLittleO_iff`、
O(s) の列の f/s は超フィルターに沿って収束する（`normalizedLimit_tendsto`）、ENNReal の `toReal` と `limUnder` の交換。

## 8. 順序と決定待ち

1. 死んだファイル 5 本と Paper/Section4/Foundations、未使用の削除（BS/CLMST の波及なし）。
2. 確度高の Mathlib への置き換え、KoszulBaseChange などの外への移動。
3. 統合（§2）。
4. 二本立ての一本化（§5、大きい）。Small 版の一本化。

決定待ち：PaperQuotient（15 本）を Paper/Section4 へ移すか、Asymptotic に残すか。二本立ての一本化をどちらの商に寄せるか
（Paper 側は論文の記述どおり、Completed 側は構成が単純）。
