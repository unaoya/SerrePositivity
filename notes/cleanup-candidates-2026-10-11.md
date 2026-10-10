# 不要になった旧形式化の候補（2026-10-11 調査）

共通の抽象化への方針転換（[section-4-plan.md](section-4-plan.md) 冒頭）のあと、旧い形式化で不要・重複になったものを調べた記録。
2026-10-11 時点の作業ツリー（並行作業の未コミット分を含む）に基づく。**まだ何も削除していない。**
候補の大半は並行作業の未コミットのファイルにあるので、そのコミット後に区分ごとに別コミットで整理し、
モジュール単位でビルドして確かめる。

## 調べ方

- 宣言名の出現回数による機械的な洗い出し（出現 1 回の宣言、ルート以外から import されないファイル）。
  docstring に名前が出る宣言は漏れるので、grep で依存を手で追った。
- 最上位の `Section5.core_of_normalization_bases` が推移的に使う定数を、ビルド済みの olean から
  Lean のメタプログラムで計算した（10/11 00:15 時点）。以下の「新経路」はこの依存集合を指す。
- 新経路の依存：`core_of_normalization_bases` → `core_of_lengthAlgebras_with_parameter_choice` →
  `core_of_lengthAlgebras` → `core_of_twistedEuler_pos`＋`firstComparison`＋
  `twistedEuler_pos_of_lengthAlgebras` → … → `lambdaChi_pos_of_parameter_tower`（`lemma_5_3`、`lemma_5_4`、
  `exists_secondComparison_pos_of_regular`）→ … → `Section4.symmetricPaperEuler_conjSum_eq`、
  `supportedRankK0_descent`。
- import の上では旧ファイルも新経路に含まれる（`AsymptoticPositivity` → … → `Positivity` → `Lemma5_2`）ので、
  判定は宣言単位で行った。

## A. 消してよいもの（旧経路の残骸）

| 場所 | 宣言 | 根拠 | 消すときの注意 |
|---|---|---|---|
| `Paper/Section5/Positivity.lean` | `core_of_inputs`、`chi_pos_of_comparisons` | 第二比較を引数で受け取る旧入口。利用 0（後者は前者からのみ） | exposition-ja.tex と section-4-plan.md の記述を直す。`chi_pos_of_firstComparison`・`core_of_twistedEuler_pos` は新経路で使用中なので残す |
| `Paper/Section4/` | `RepresentativeComparison`（3）→ `OrdinaryRankComparison`（`ordinaryRankEulerK0`(_changeRing)）→ `NormalizedRankComparison`（4）→ `CompletedRankComparison`（3） | 完備化前・Karoubi 段階の階数倍公式の旧層。`koszulPaperEulerK0_changeRing` が一般公式として置き換えた。全宣言が新経路で未使用 | `PaperK0Comparison` の import を `UniformRepresentative` に付け替え、`Foundations.lean` の import 2 本を外す |
| `Paper/Section4/KoszulInputs.lean` | 4 宣言（`ordinary_koszul_pow_finite_of_finite` など） | 上の層からのみ使用 | 上と一緒に |
| `Paper/Section4/UniformRepresentative.lean`、`Asymptotic/SupportedCompletedRepresentative.lean` | `uniform_free_representative_of_koszul` と後者の 2 宣言 | 一様代表を作る旧ルート。利用 0 | `supportedRank_isIdempotentComplete_of_koszul` は使用中なので残す |
| `PerfectComplex/NormalizedEuler.lean` | `lambdaHomology_koszulComplexOn_ne_top`、`…_ne_top_of_single`、`lambdaHomology_koszul_single_finiteFree`、`lambdaHomology_koszul_single_ring`、`lambdaHomology_shortExact_ne_top`（約 110 行）、`lambdaHomology_cone_ne_top`、`lambdaHomology_cone_le`、`lambdaHomology_ne_top_of_nullHomotopic_cone`、`lambdaLengthReal_eq_add_range`、`lambdaHomology_hasFiniteSupport` | 互いに呼び合うだけで外部利用 0。有限性は `ProjectiveBounds` に、加法性の部品は `CategoryTheory/ExactSequenceEuler` に移った | docstring 44–52 行の説明も直す。`lambdaHomology_ne_top_of_koszulComplexOn`・`…_of_retract`・`supported_homology_isPowTorsion` は使用中 |
| `PerfectComplex/KoszulLengthBounds.lean` | `lambdaHomology_koszul_single_le`、`lambdaHomology_koszul_baseChange_le_sum` | 直和因子版に置き換わった。利用 0 | |
| `Paper/Lemma3_5/Normalized.lean` | `chiLam_baseChange_koszulComplex` | `LengthAlgebra.koszulEuler_eq_length_quotient` に置き換わった。利用 0 | |
| `PerfectComplex/K0.lean` | `mk_eq_zero_of_homotopy_id_zero` | `mk_eq_zero_of_isZero` で足りる。利用 0 | |
| `IntersectionMultiplicity/ParameterQuotientTorBound.lean` | `section upper` 全体（`isPowTorsion_koszul`、`len_koszul_isZero`、`len_koszul_single_ring`、`len_koszul_single`、`len_homology_koszulComplexOn_eq_zero`）と、`len_homology_le_koszulComplexOn`、`kills_koszulComplexOn`(_self)、`Kills.smul_homology`、`isPowTorsion_homology` | `len_torAlg_eq_zero` が共通層の `lambdaHomology_projective_vanishing` を直接使うようになり、外部利用 0 | 並行作業が編集中。`Kills` 自体は残す |
| `Paper/Section2/PerfectApproximation.lean` | `perfectionRootStageQuotientEquiv`、`length_perfectionRootStage_quotient`、`…_quotient_base` | 塔の段の版 `PerfectApproximationLength.length_rootStage_*` に置き換わった | `LengthAlgebraConstruction` の docstring の記述も直す |
| `Paper/Section2/PerfectConductor.lean` | `perfectionApproximation_kernel_bound_of_conductor` | 別の 2 補題の組み合わせに置き換わった。利用 0 | |
| `Paper/Lemma3_5/ConjugateSum.lean` | ファイル全体 | 互換 import のみ（`GroupTheory/ConjugateSum`） | ルートの import 1 行と、`Paper/Lemma3_5.lean` の docstring、section-4-plan.md の表のパスを直す |
| その他の単独の未使用 | `MinimalFreeResolution.length_tor_zero`、`ControlledResolution.exists_free_resolution_length_mul_koszul`、`Section5/ApproximationGrowth.betti_growth_of_parameter_approximation`、`Section5/ApproximationHomology` の 2 宣言と `Asymptotic/MinimalTruncationComparison` の 5 宣言（Tor を極小代表で計算する別ルート） | 利用 0、または新経路が同じことを内部で行う | `ApproximationGrowth` を消すなら `AsymptoticPositivity` の import も外す |
| リポジトリ直下 `PerfectComplex/HomotopyCategory.lean` | ファイル全体 | ビルド対象外の古い複製（git 管理外） | 並行作業が置いた可能性があるので確認してから |

## B. 統合すべきもの（二重証明）

| 対象 | 内容 | 方針 |
|---|---|---|
| 共役和の比較 | 共通層の `homologicalEulerK0_conjSum_eq`・`perfectEuler_conjSum_eq` が未使用。`lemma_3_5c`、`Section4/SymmetricComparison`、`NormComparison` が `conjSum_eq` を直接呼ぶ | 適用側を共通定理経由に書き換える |
| `Section4/Theorem4_7.lean`、`NormComparison.lean` | `theorem_4_7`・`theorem_4_7_K0` は新経路で未使用で、`symmetricPaperEuler_conjSum_eq` と同じ議論の二重証明。`NormComparison` の 5 宣言は定理 4.7 からのみ使用。`PaperK0Comparison` の `ordinary/normalizedPaperEulerK0_changeRing`、`LengthHypotheses` の 3 宣言も同様 | 定理 4.7 は論文との対応として残し、`symmetricPaperEuler_conjSum_eq` の系として数行に書き直す。そのうえで `NormComparison.lean` と付随宣言を消す |
| `Section5/AsymptoticPositivity` の `paperEuler_pos_of_finiteApproximation`・`exists_paperEuler_pos_of_minimalApproximation`、`SecondComparisonLowerBound.secondComparison_minimal_lower_bound` | 新経路は未使用で、`exists_secondComparison_pos_of_approximation` の中で同じ下界を別に証明している。section-4-plan の表では入口として挙げている | 新経路をこれらの適用にする |
| `Paper/Corollary2_6.lean` と `Paper/Section2/Corollary2_6.lean` | 同名ファイルが二つ。`cor_2_6_pos` は `Section2.cor_2_6_residue_pos` を呼ぶ一行 | 一つにまとめる |
| `Paper/Lemma3_4.lemma_3_4` と `Paper/Corollary2_6.cor_2_6_tor` | どちらも `normalizedLength_tor_of_isWeaklyRegular` の `v = 1` の適用。`lemma_3_4` は `NormalizedLength.restrictToBase` を手で組み直している | `cor_2_6_tor` を `lemma_3_4` から導く。両方とも論文対応として残す |
| `HomologicalAlgebra/FiniteFreeResolution` と `CommutativeAlgebra/MinimalGenerators`＋`MinimalFreeResolution` | 有限自由被覆の核を繰り返す構成が二通り。前者の唯一の利用者は局所 Noether 環を仮定している | 極小版に統一（中優先） |
| `NormalizedEuler.lambdaHomology_ne_top_of_retract` と `KoszulLengthBounds.lambdaHomology_le_of_retract` | 前者は後者の系 | 前者を後者から導く（低優先） |
| `Lemma3_5.radical_span_eq_maximalIdeal` | 同じ証明が 2 か所にインライン | 任意 |
| `MinimalTruncationHomology.truncatedKoszulMapHomologyIso` | 未使用。利用側は `StupidTruncation.koszulMapHomologyIso` を直接呼ぶ | どちらかにそろえる |

## C. 判断が必要なもの

| 対象 | 状況 |
|---|---|
| `Section5/ApproximationEuler.lean` の 4 宣言 | 有限近似から `c_σ` を同定する別ルート。新経路は不要だが論文の式との対応がある |
| `Asymptotic/` の LengthDerivedQuotient、SmallLengthDerivedQuotient（`SmallLengthSerreQuotient` の 7 宣言を含む）、PaperRankGenerators、FreeSequenceGenerator | 論文の圏 D_S、N_S、P_S との対応。新経路には不要。import 元は `Foundations.lean` だけ |
| `Asymptotic/` の完備化前・Karoubi 段階の K₀ 評価（`RankEulerAdditivity`、`RankEulerComparison`、`CompletedK0Comparison`、`CompletedEulerAdditivity` の一部） | Section4 の旧比較層と対。P1 で `homologicalEulerK0` に統一したばかりなので、消すなら宣言単位 |
| `Section5/ApproximationBetti` の 4 宣言、`MinimalBetti.finrank_eq_length_tor`、`TorSymmetry.length_torModule_comm`・`torModuleIsoCochainLeft` | 未使用だが API の性格 |
| `CommutativeAlgebra/Multiplicity.lean` | 旧定義が消え、パラメータ系の定義だけが残る。改名候補（import 4 か所） |
| `Inputs/LengthAlgebra.lean` | `sorry` も入力もなく書き換え補題 2 つだけ。`Paper/Section2/LengthAlgebraConsequences.lean` へ移し、不要な import を削る候補 |
| `LengthAlgebra/Koszul.KoszulAcyclic` | 新しい定義だが利用 0 |
| ルートに載っていないファイル | 多数（FiniteFreeResolution、MinimalFreeResolution、Perfect* 系など）。推移的に import されるのでビルドは壊れない。ルートを全ファイルの一覧とするなら追加する |

## 残すもの

- 新経路で使用中：`lemma_5_3`、`lemma_5_4`、`length_le_tor_zero_mul`、`firstComparison`、`FirstComparison`・`NormApplication`、
  `Preparation`、`ParameterAvoidance`、`ParameterChoice`（前者を有限拡大へ移す薄い包みで重複ではない）、
  `SymmetricComparison`、`PaperK0Comparison` の `ordinaryPaperEulerK0`・`koszulPaperEulerK0_changeRing`、
  `LengthAlgebraRealization`、`SupportedDescent`。
- 論文の主張に対応する未使用の定理：`lemma_2_1`、`lemma_2_2`、`lemma_2_4_*`、`lemma_3_4`、`Statement` の 2 主張。
- 旧定義 `K0Supported`、`chiOrd`、`chiOrdHom`、`chiLam`、`chiLamHom_of_finite`、`lambdaEuler`：今も広く使用。
  降下の入力 `theorem_3_1_K0` が旧 K₀ 上で述べられ、Koszul 生成 `hom_ext_koszul` も旧側にしかない。
  計画ノートも具体的な計算と弱い有限性条件のために残すと明記。加法性の証明はすでに共通定理を通る。
- 付録の二つの実現のための API（消滅、下界、t 構造、`LengthFamilies` など）。
- §2 の未完の部品（等標数の長さ代数の `sorry` を埋めるためのもの）。

## 古い記述

- `PerfectComplex/NormalizedEuler.lean` の docstring 44–52 行（有限性の証明経路）。
- `Paper/Lemma3_5/Ordinary.lean` 後半の docstring（`K0.hom_ext_koszul` で直接比べると書いているが、実装は
  `lambdaEuler_baseChange_eq_koszulEuler_mul` 経由）。
- `Paper/Section2/Lemma2_2.lean` の「具体形（下流では使わない）」（いまは `theorem_2_5` の `hbase` が使う）。
- `notes/section-2-plan.md` の、削除済みの `exists_lengthAlgebra`・`hilbertSamuelMultiplicity` を「現在の」とする箇所。
- `PowTorsionCategory.lean`、`KoszulOrdinaryLength.lean` にモジュール docstring がない。
