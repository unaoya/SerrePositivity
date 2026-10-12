# 現在の形式化の状態

2026-10-12 更新。実装基準は `7c3fc2c` と、その後の抽象化・文書整理の作業ツリー。
Leanは `lean-toolchain`、Mathlibは `lake-manifest.json` の固定版を使う。
この文書を、現在の到達点・引用境界・読む順序の正本とする。
日付付きの検証数値は実施記録であり、この状態表へ過去の数値を転記しない。

## 到達点

共通の Euler 加法性・反復錐・消滅・下界・対称比較、その perfect 複体版と
ランク商版の実現、および λ-平坦性・λ-CM 性からの仮定確認は証明済み。
標準可換環論の Samuel 多項式性・次数定理・正則パラメータ・非混合性・
Koszul 重複度公式・パラメータ成分の冪の公式も証明済み。

§2 の両標数での長さ代数の構成、正規化基底と Galois 閉包の構成、§5 の比較と
正値性、完備化・剰余体拡大・加群デヴィサージュによる主定理への接続は、
以下の名前付き入力に相対的に証明済み。
`main_statement` と `core_statement` 自身に直接 `sorry` はないが、`sorryAx` に依存する。
主定理が引用なしで証明されたとは扱わない。

## 未証明入力の正本：外部引用13件、保留K理論2件

宣言名は先頭の `SerrePositivity.` を省略する。ファイル名と名前空間は別物である。

| 分類 | モジュール（`SerrePositivity/` 以下） | 宣言 | 件数 |
| --- | --- | --- | ---: |
| 外部引用 | `Inputs/SerrePositivity` | `Inputs.serrePositivity_of_field` | 1 |
| 外部引用 | `Inputs/IntersectionTheory` | `Inputs.intersectionVanishing` | 1 |
| 外部引用 | `Inputs/ResidueFieldExtension` | `Inputs.exists_complete_flat_local_extension` | 1 |
| 外部引用 | `Inputs/CohenNormalization` | `Inputs.cohen_gabber_normalization`、`Inputs.cohen_normalization_mixedCharacteristic` | 2 |
| 外部引用 | `Paper/Section2/TowerLength` | `Section2.towerLengthFun_eq_fgLength`、`Section2.towerLengthFun_add_of_exact` | 2 |
| 外部引用 | `Inputs/RobertsFrobenius` | `Inputs.frobenius_homology_length_tendsto_zero` | 1 |
| 外部引用 | `Inputs/PerfectoidTower` | `Inputs.completedTower_isIntegralPerfectoid` | 1 |
| 外部引用 | `Inputs/Perfectoidization` | `Inputs.exists_perfectoidization_of_finite` | 1 |
| 外部引用 | `Inputs/CLMST` | `Inputs.clmst_length_eq_zero_of_perfectoidIdeal_annihilates`、`Inputs.clmst_exists_perfectoidIdeal_annihilates_koszul`、`Inputs.clmst_parameter_quotient_length` | 3 |
| 保留K理論 | `Inputs/Descent` | `theorem_3_1_K0` | 1 |
| 保留K理論 | `Paper/Section4/SupportedDescent` | `Section4.supportedRankK0_descent` | 1 |

後者の保留には dg 表示・一般係数版の降下との接続が含まれる。
この二件は外部引用として数えず、証明作業を保留する。
`#print axioms` は依存する引用名を列挙しないので、`#print sorries` とソースも照合する。
引用の出典・適用範囲は各宣言の docstring、§2 の照合は [section-2.md](section-2.md) を参照。

## 抽象論から具体的な証明への道筋

| 層 | 主なモジュール／公開API | 供給するもの |
| --- | --- | --- |
| 圏論 | `CategoryTheory/EulerTheory`、`ExactSequenceEuler`、`IteratedCone` | Euler加法性、反復錐の消滅・下界、対称比較 |
| 長さ | `LengthAlgebra/SerreQuotient`、`FiniteQuotientEquivalence` | 有限な商、大きな商、その有限部分の同値 |
| perfect | `PerfectHomology`、`PerfectVanishing`、`Comparison` | 実際の関手・支持・有限性・Koszul振幅の確認 |
| ランク商 | `Asymptotic/SequenceHomologyLocalization`、`CompletedHomology`、`CompletedRankEvaluation` | 分母の可逆化、冪等完備化、シフト、有界性 |
| 基底公式 | `LengthAlgebra/KoszulFormula`、`Section4/PaperK0Comparison` | Koszul分解と一様代表から係数を計算 |
| 論文比較 | `lemma_3_5c`、`Section4.theorem_4_7_K0` | 上の一般比較へ実際の作用と保留降下を適用 |
| 正値性 | `Section5/CoreLengthPositivity`、`Core`、`Paper/Statement` | 有限近似・極小下界・第一比較から主定理へ |

一般比較は降下と Koszul 分解を明示した条件付き定理であり、未証明入力を呼ばない。
λ-平坦性から有限性を出すには有限な零次の値が必要だが、高次消滅だけには不要。
長さの `toNat`・`toReal` と `finsum` の全域定義の規約を、有限 Euler 評価とは区別する。

## 読む順序と文書の役割

1. [README](../README.md)：目的と入口。
2. [日本語解説](../exposition/ja/exposition-ja.tex)：§3共通論→§4長さ→§5・§6実現→§7適用→§8構成→§9核心。
3. [§4入力境界](section-4-plan.md)、[§2実装対応](section-2-plan.md)：仮定確認とモジュール対応。
4. [PLAN](PLAN.md)：現在の残作業と設計規約。
5. [履歴一覧](history/README.md)：過去の計画・監査・変更理由。

[λホモロジー代数](lambda-homological/lambda-homological-ja.tex) と
[λエタール](lambda-etale/lambda-etale-ja.tex) は推測を含む独立した研究ノート。
主定理の証明済み状態の根拠には使わない。

## 原本と生成物

TeX を原本とし、同じディレクトリの PDF は対応する閲覧用生成物として保持する。
TeX の変更後は `latexmk -lualatex -outdir=<一時ディレクトリ> <原本>` で生成し、
警告・相互参照・変更ページを確認して PDF を更新する。ログ・aux・ページ画像は管理しない。
原論文 `paper/paper.pdf` は出典として保持する。OSメタデータ `.DS_Store` は管理しない。
