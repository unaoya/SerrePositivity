# 新しい抽象化への移行後のコード整理（2026-10-11）

> 2026-10-11 の実施記録。削除数・ジョブ数・PDFページ数は当時の数値である。現在状態は [status.md](status.md)、後続の整理は [cleanup-2026-10-12.md](cleanup-2026-10-12.md) を参照。

移行完了分を `1576952`（λ-平坦性・λ-CM 性から二つの実現への接続）にコミットした後、
このノートの旧候補一覧を現在の実装と照合して整理した。
旧候補一覧は `1576952` の同ファイルに残る。

単に「核心定理から参照されない」ことだけで削除せず、現行の証明・型・import と、
付録の抽象論の公開 API としての役割を確認した。
削除した名前付き宣言は **74個**、削除した管理対象モジュールは **10個**。
Lean ソースの差分は **95行追加、1753行削除（純減1658行）**。

## 削除した経路と置換先

| 削除対象 | 現在使う経路・判断理由 |
| --- | --- |
| §4 の `RepresentativeComparison`、`OrdinaryRankComparison`、`NormalizedRankComparison`、`CompletedRankComparison` | `PaperK0Comparison.koszulPaperEulerK0_changeRing` が任意の Koszul Euler 数による全対象の基底公式を与える。通常・正規化の階数倍を別々に持ち上げる経路を削除した |
| `NormComparison` と `PaperK0Comparison` の通常・正規化専用の階数倍公式 | `theorem_4_7_K0` を `symmetricPaperEuler_conjSum_eq` の特殊例に変更。定理4.7の名前と数学的結論は残す |
| `KoszulInputs`、`LengthHypotheses` の零乗・全冪の有限性 | `LengthAlgebra.koszul_finite_of_zero_positive` と `koszulFinite_of_lengthAlgebra_values` を直接使用。抽象論は正の冪だけを要求するため、定理4.7の `0 < e` も不要になった |
| `SupportedCompletedRepresentative` と `uniform_free_representative_of_koszul` | 旧比較用に複合していた未使用の入口を削除。基底公式に必要な `supportedRank_isIdempotentComplete_of_koszul` と一般の代表・支持比較の構成は保持 |
| `PerfectComplex/NormalizedEuler` の錐・短完全列・自由項による有限性、独立した実数値加法性の補助証明（10宣言） | 有限性は `ProjectiveBounds` の有限射影版、加法性は `LengthAlgebra/ExactSequenceEuler` を経由する共通定理。ホモトピー不変性、錐加法性、直和因子への有限性の移送は現行証明から使うため保持 |
| `KoszulLengthBounds` の自由基底だけを扱う上界2個、`K0.mk_eq_zero_of_homotopy_id_zero` | 直和因子版や既存の K₀ 関係で代替でき、外部参照なし |
| `TorBound` の上下の数値的不等式、消去冪を増やす補題群（10宣言） | `ParamQuot.len_torAlg_eq_zero` は `LengthAlgebra.lambdaHomology_projective_vanishing` を使用。共通の正の消去冪と振幅を渡すので、旧 `2^h` の処理は不要 |
| `chiLam_baseChange_koszulComplex` | `LengthAlgebra.koszulEuler_eq_length_quotient` と一般の基底公式で計算する |
| `Paper/Lemma3_5/ConjugateSum` | 中身が互換 import だけだった。`GroupTheory/ConjugateSum` を直接使う |
| `core_of_inputs` と `chi_pos_of_comparisons` | 現行の核心への経路は `core_of_twistedEuler_pos` と `chi_pos_of_firstComparison`。第二比較・正値性は `core_of_lengthAlgebras` 側で導く |
| `ApproximationGrowth`、`ApproximationHomology` の Tor 代表選択2個、`MinimalTruncationComparison` の未使用5宣言、`MinimalTruncationHomology` | 生の Tor を特定次数の深い代表で計算する別経路を削除。`betti_growth_of_approximation_limits`、`exists_deeper_minimal_truncation`、現行の Koszul 計算 `minimalModelKoszulHomologyIsoAt` は保持 |
| `MinimalFreeResolution.length_tor_zero`、`exists_free_resolution_length_mul_koszul` | 外部参照のない適用だけの入口。実際に使う `MinimalGenerators.length_tor_zero` と一般の制御付き分解は保持 |
| §2 の `perfectionRootStageQuotientEquiv`・旧根の段の長さ公式2個、`perfectionApproximation_kernel_bound_of_conductor` | `PerfectApproximationLength` の塔の段での長さ公式、および分母の根と核の評価の組み合わせへ置換済み。残る §2 の存在構成・未証明入力は保持 |

定理4.7の係数環は `A → T → C` の合成で記述する。別に与えた `A → C` と塔の等式を
毎回扱う旧専用定義は削除した。通常長さと λ の Koszul Euler 数をともに
`rank_A T` と計算して共通比較へ渡す。降下と正則パラメータの引用への依存は変わらない。

管理対象外の `PerfectComplex/HomotopyCategory.lean` も、全宣言が正式な
`SerrePositivity/PerfectComplex/HomotopyCategory.lean` に存在する古い複製と確認したため削除した。
このファイルは上の74宣言・10モジュールの集計に含めない。
OS のメタデータと別途作成された文章再構成の計画ノートは変更していない。

## 残したコードと理由

- `K0Supported`、`chiOrd`、`chiOrdHom`、`chiLam`、`chiLamHom_of_finite`、`lambdaEuler`：
  現在も具体的な計算、旧 K₀ での Koszul 生成・降下、より弱い有限性条件で使用する。
  新 K₀ への比較と評価の一致は証明済みで、加法性の重複した証明は残していない。
- `RankEulerComparison`、`CompletedK0Comparison` などの一般の係数変更・完備化の比較：
  現在の `PaperBaseChange` と `koszulPaperEulerK0_changeRing` が使う。
  今回削除した論文固有の階数倍比較とは区別する。
- `LengthDerivedQuotient`、`SmallLengthDerivedQuotient`、`PaperRankGenerators`、
  `FreeSequenceGenerator`：付録の圏・関手と論文の圏の実現を支える公開 API。
- `ApproximationEuler`・`ApproximationBetti` の評価同定、正値性・下界の個別入口：
  最終の核心への一本道以外にも、論文の式や抽象論の適用に対応する独立した主張がある。
- `LengthAlgebra.KoszulAcyclic`：旧調査時には未使用だったが、現在は λ-平坦性・λ-CM 性からの
  接続で使用中。旧調査の結果だけで削除しない。
- `homologicalEulerK0_conjSum_eq`・`perfectEuler_conjSum_eq` と群論の `conjSum_eq`：
  評価の抽象度に応じた共通入口。後者を直接使う証明も群論を再証明しているわけではない。
- 論文の主張そのもの、§2の未完成の構成、既存の引用定理：今回の整理で削除しない。

## 統合と削除の区別

旧候補一覧にあった、系2.6と補題3.4の入口の統合、一般の有限自由分解と極小分解の
構成の統合、ファイル名の変更などは、単なる未使用コードの削除とは異なる。
一般性や独立した公開定理の形を変える必要があるため、今回の削除には含めていない。
現在の実装が不要であると確認できた、未処理の削除候補としては扱わない。

README・解説 TeX/PDF・現行の証明方針も置換先に合わせた。
過去の実施記録は履歴として残し、冒頭にこの整理記録への案内を加えた。

## 検証

- 全体 `lake build`：3474ジョブで成功。今回の変更による新規警告なし。
- 49宣言の `#print axioms`：46宣言は `propext`・`Classical.choice`・`Quot.sound` のみ。
  `theorem_4_7_K0`・`theorem_4_7`・`lemma_3_5` の3宣言には既存の引用に由来する
  `sorryAx` が残る。新しい `sorry`・公理は追加していない。
- ルートを import した Lean の環境を調べ、削除した74宣言が全て存在しないことを確認。
  古いビルド生成物から削除済み宣言が読み込まれていないことも確認できる。
- 全324モジュールがルートから到達可能で、欠けた import もない。
  削除したファイル経由で読み込まれていた `TorSymmetry` は、実際の使用先である
  `ApproximationBetti` から直接 import する。
- `git diff --check`：成功。解説の Lean 参照にも削除した宣言は残っていない。
- LuaLaTeX による解説PDFの再生成：50ページ。修正箇所と隣接ページ（13・14・16・17）を
  画像で確認し、はみ出し・行欠けなし。Overfull/Underfull の警告なし。
