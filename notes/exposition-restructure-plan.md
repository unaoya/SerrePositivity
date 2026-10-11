# exposition-ja.tex の再構成計画（2026-10-11 改訂）

対象は `exposition/ja/exposition-ja.tex`（1749 行、2026-10-11 07:27 時点）。編集はこのノートを書いたセッションで行う。

目的は次の二つ。

1. 付録 B「長さ付き代数とホモロジー的評価による統一」を本文に移し、本文を
   「共通の抽象論 → 長さ付き代数 → 二つの実現 → 論文への適用」の順に並べ直す。
2. Lean の参照と状況表示を、いまの形式化に合わせる。

## 前提となる形式化の状態（2026-10-11 07:27）

- 共通の抽象論、二つの実現、旧証明の移行に加えて、概念的な λ-平坦性・λ-CM 性から Koszul 条件を
  供給する接続まで実装された（`LengthAlgebra/Flat.lean`、`CohenMacaulay.lean`、`FlatRealization.lean`、
  `Paper/Section4/FlatRealization.lean`、`CommutativeAlgebra/RegularSequencePowers.lean`・`RegularSequenceLength.lean`）。
  並行作業はこれで抽象化の一区切りとしている（`section-4-plan.md` 冒頭）。
- このうち Lean の新規 6 ファイルと、exposition・`PLAN.md`・`section-4-plan.md` などの更新は未コミット
  （直前のコミットは b30f735）。全体ビルドは 3484 ジョブで成功。
- exposition の `\ld{...}` 139 件はすべて現存する宣言・モジュールを指す。ただし `core_of_inputs`、
  `chi_pos_of_comparisons` など、[cleanup-candidates-2026-10-11.md](cleanup-candidates-2026-10-11.md) で
  削除候補にした旧入口も含む。

## 現状の構成と問題

| 現在 | 内容 | 問題 |
|---|---|---|
| はじめに | 共通定理（付録 B）と二つの実現（§4、§5）という整理を宣言 | 共通定理が付録にあり、本文が付録を前方参照する |
| §1 主張と帰着 | 定理 1.1、核の場合、Lemma 5.1 | そのままでよい |
| §2 証明の方針 | CM のアイデア、基底と Galois 閉包、2 回の置き換え、ノルム比較の型 | 共通定理という骨格の説明がない |
| §3 長さ関数と λ-平坦な代数 | 長さ関数、長さ付き代数、Lemma 3.4、系、λ-CM、λ 版 Auslander–Buchsbaum | λ-AB（Lemma 5.3）は適用側の内容で、反復錐の消滅（付録 B）を前方参照する |
| §4 perfect 複体での比較 | 付録 B の要約、Koszul 上界、3.5a/b/c、Theorem 3.1、共役和の補題、消滅、下界 | 共通定理（共役和の補題）が実現の節にある。付録 B の「有限版で確認する主張」と重なる |
| §5 ランク無視の圏での比較 | 圏、Remark 4.1、Lemma 4.2、Prop 4.3、系、Prop 4.5、Lemma 4.6、Thm 4.7 | 付録 B の列の商・「ランク無視版で確認する主張」と重なる |
| §6 λ-平坦な長さ付き代数の構成 | 塔、Lemma 2.4、2.2、Thm 2.5、Cor 2.6 (3) | そのままでよい |
| §7 核の場合の証明 | 設定、Lemma 5.2、有限近似、(5.18)、Lemma 5.6、結論 | Lean 参照が旧入口のまま。`core_of_normalization_bases` までの新経路が反映されていない |
| 付録 A 引用と状況 | 引用表、状況表、変えた点、残る境界 | 状況表を新構成・新経路に合わせて作り直す |
| 付録 B 統一（738–1191 行） | 共通ホモロジー代数、評価先、長さ付き代数による実現、基底と対称比較、列の商、パラメータ商、仮定確認 2 節、実装対応（P1–P8、監査数） | 本文へ移す |
| 付録 C〜E | 先行研究、直感的説明、λ-平坦を主役にした整理 | 付録のまま |

## 新しい構成案

括弧内は移す元。ラベル名（`def:B-lenab` など）は参照を壊さないため当面そのまま使う。

- **はじめに**：節の順序の説明を新構成に合わせる。
- **§1 主張と帰着**（現 §1）：変更なし。
- **§2 証明の方針**（現 §2）：最後に「証明の骨格」を加える。共通定理 4 つ（Euler 評価、共役和比較、反復錐の消滅、
  第零次の下界）と、二つの実現、2 回の置き換えの対応表。
- **§3 共通の抽象論**（新設。付録 B の共通ホモロジー代数、現 §4 の共役和の補題）
  - 3.1 長さ付きアーベル圏、ホモロジー的関手、Euler 評価（def:B-lenab、prop:B-euler）
  - 3.2 共役和の比較（lem:conjsum）
  - 3.3 スカラーの反復錐：分裂、消滅、第零次の下界（lem:B-split、lem:B-nit、lem:B-h0）
  - 圏論だけで述べ、環・長さ代数を使わない。
- **§4 長さ付き代数**（現 §3 の前半、付録 B の評価先・長さ付き代数による実現・基底と対称比較）
  - 4.1 長さ関数と長さ付き代数（def:lengthfn、ex:ordinary、def:lengthalg）
  - 4.2 評価先：零長さの Serre 商と有限部分（lem:B-serre、def:B-alambda、prop:B-length-descends、prop:B-finite-part）
  - 4.3 Koszul 有限性と λ-平坦性（def:C-levels、lem:34、cor:allv、rem:leandiff、「有限性と消滅を分ける」）。
    概念的な定義から Koszul 条件への接続（`LengthAlgebra.Flat`）が証明済みになったことを反映する。
  - 4.4 λ-CM 代数（def:lambdacm、prop:cmflat。`LengthAlgebra.CohenMacaulay`）
  - 4.5 基底から来る類と二つの長さ付き代数のノルム比較（prop:C-base、thm:C-norm）
- **§5 第一の実現：perfect 複体**（現 §4、付録 B の lem:C-nil・prop:C-euler・有限版の仮定確認）
  - 5.1 圏と評価関手：支持とスカラーの零作用（lem:C-nil）、Koszul 上界（lem:koszulbound）、評価関手（prop:C-euler、prop:35a）
  - 5.2 比較：3.5b、Theorem 3.1、3.5c
  - 5.3 消滅と下界：lem:nit、lem:h0bound
  - 5.4 λ-平坦な代数での適用（`LengthAlgebra.FlatRealization`）
  - 付録 B の確認命題 prop:check-perfect-* は各小節の「確認した仮定」として吸収する。
- **§6 第二の実現：ランク無視の圏**（現 §5、付録 B の列の商・ランク無視版の仮定確認）
  - 6.1 圏（def:rankquot、Remark 4.1、Lemma 4.2）
  - 6.2 評価関手（Prop 4.3、局所化と冪等完備化への延長）
  - 6.3 比較（Prop 4.5、Lemma 4.6、Thm 4.7）
  - 6.4 消滅と下界（cor:nitasymp）
  - 6.5 λ-平坦な代数での適用（`Paper.Section4.FlatRealization`）
  - prop:check-rank-* を各小節に吸収する。
- **§7 パラメータ商**（現 §3 の lem:lambdaAB、付録 B のパラメータ商）：λ 版 Auslander–Buchsbaum（Lemma 5.3）を、
  反復錐の消滅（§3.3）と λ-CM 性（§4.4）の適用として述べる。
- **§8 λ-平坦な長さ付き代数の構成**（現 §6）：Lean 参照の更新だけ。
- **§9 核の場合の証明**（現 §7）：新しい経路に合わせて書き直す（下記）。
- **付録 A 引用した結果と形式化の状況**（現付録 A に付録 B の実装対応を合流）：状況表を新しい命題番号で作り直す。
  共通層のファイル対応（P1–P8）は短い表にする。ビルドのジョブ数や監査した宣言数は本文から外し、notes に任せる。
- **付録 B 先行研究、付録 C 直感的説明、付録 D λ-平坦を主役にした整理**（現 C、D、E）：位置だけ変える。

## 今の形式化に合わせる箇所

- **§9 核の場合**
  - 結論の Lean 参照を旧入口から、新しい経路 `core_of_normalization_bases` →
    `core_of_lengthAlgebras_with_parameter_choice` → `core_of_lengthAlgebras` に替える。
    状況は「正規化基底と有限群作用付き拡大を与えれば、引用を除いて証明済み」。
  - 設定の段落に、不変環から幾何ファイバーの推移性を導く議論（`isGeometricallyTransitive_of_fixed`）と、
    (5.4) のパラメータの選択（`exists_regular_parameters_in`、引用は非混合性だけ）を状況つきで入れる。
  - 有限近似（Lemma 5.4）は `lemma_5_4` を通して内部で構成されるようになったので、「有限近似を入力とした」を直す。
  - 置き換え 2 と正値性の参照を、新経路が実際に使う宣言に合わせる。
- **付録 A の引用表**：非混合性（`Inputs.Unmixedness`）を加える。Hilbert–Samuel の定理、重複度の公式、
  等標数・混標数の長さ代数の未完部分を §2 の引用として載せるか決める。
- **旧入口の参照**：cleanup で消す予定の宣言（`core_of_inputs`、`chi_pos_of_comparisons`、`NormComparison` の宣言、
  `secondComparison_minimal_lower_bound`、`paperEuler_pos_of_finiteApproximation` など）は exposition から外す。
- **最後の照合**：`\ld{...}` を全部抜き出して Lean の宣言と照合する（今回のスクリプトを再利用）。

## 作業手順（このセッションで行う）

0. **並行作業の未コミット分を先にコミットする**：Lean の新規 6 ファイル、変更 5 ファイル、exposition、
   `PLAN.md`、`section-4-plan.md`。リポジトリ直下の `PerfectComplex/HomotopyCategory.lean`（ビルド対象外の古い複製）の扱いも決める。
   以後、並行作業は exposition を編集しない前提にする。
1. **節の移動だけのコミット**：内容を変えずに、上の新構成の順に節を並べ替える。
   付録 B を §3〜§7 に分配し、§4・§5 にあった共通定理を §3 へ移す。`latexmk -lualatex` で、
   未定義参照・重複ラベルの警告がないことを確かめる。
2. **重複をまとめるコミット**：付録 B の仮定確認の 6 命題を §5・§6 の各小節に吸収し、現 §4 冒頭の付録 B の要約、
   付録 B 冒頭の導入、P1–P8 の記述を整理する。§2 に「証明の骨格」を加える。
3. **形式化に合わせるコミット**：§9 の書き直し、旧入口の参照の除去、各命題の `\lean{...}` と状況の更新、付録 A の作り直し。
4. **照合**：`\ld{...}` の全件照合、PDF のビルド、目次と相互参照の目視確認。

各段階で PDF をビルドし、未定義参照がないことを確かめてからコミットする。

## 決めてほしいこと

- **手順 0 のコミット**：並行作業の未コミット分を、このセッションでコミットしてよいか。
- **本文の順序**：抽象論（§3）を長さ付き代数（§4）より前に置く案にした。長さ付き代数を先に定義する案もある。
- **実装の記録**：P1–P8 の対応、監査数、ジョブ数を本文から外し、付録 A の短い表と notes に任せる案にした。
- **Lean の cleanup との順序**：exposition から旧入口の参照を外すのは手順 3 で行う。Lean の宣言自体の削除は exposition の後に別作業とする案にした。

## 実施状況（2026-10-11）

手順 0 は並行作業側のコミット（1576952、6fcf62d）で済んだ。手順 1〜4 をこのセッションで行った。

| コミット | 内容 |
|---|---|
| fa27f87 | 節の並べ替えのみ（新しい見出しを除き文は変えない） |
| 6a8e3f7 | 重複の統合。§3 の導入、§2 の「証明の骨格」の表。旧付録の確認命題 6 つは対応する命題に吸収し、ラベルはその命題を指す |
| ca49ad0 | Lean 参照と状況の更新（§7〜§9、付録 A の引用表・状況表・実装の構成表） |
| 70818e6、3f160c3 | 有限近似の抽象化：塔と整合する長さ、近似列の定義と存在定理を §4.5 に置き、§9 はそれを使う形に |
| 9b3bbf5 | §9 を主張と証明の列に書き直し |
| 00bcbd4 | §3〜§6 の一般の主張から論文固有の仮定を外す（Koszul 有限性・λ-平坦性・λ-CM 性を名前のついた条件にし、系で論文の状況へ） |
| 1988142 | 二つの比較定理を一つの抽象的な系（基底公式つきの共役和比較、系 B-compare-base）の適用として書く |
| e314f80 | §6 の主張の構成を §5 と揃える（Euler 有限、係数変更との両立、基底公式、比較、消滅と下界、λ-平坦な場合の系） |

計画からの変更：基底から来る類とノルム比較（命題 C-base、定理 C-norm）は §4 ではなく §5「基底から来る類と比較」に置いた。
perfect 複体の圏と命題 C-euler を前提にしているため。§4 は長さ付き代数そのものの話だけにした。

検証：各段階で `latexmk -lualatex` を通し、未定義参照・重複ラベルの警告なし（フォント情報の "undefined" 78 件は元の版と同じ）。
`\ld{...}` 166 件は、ディレクトリ名 3 件（`Asymptotic`、`Paper.Section4`、`Paper.Section5`）を除き全て現存の宣言・モジュール。

残り：付録 D（λ-平坦を主役にした整理）の「次にすること」は、λ-平坦性・λ-CM 性の接続が形式化された後の状況に合わせて見直す余地がある。
付録 B〜D の内容自体は今回変更していない。

## Lean 側の改善（2026-10-11、解説の抽象化に合わせたもの）

解説で「抽象論の適用」として書いた箇所のうち、Lean の証明がそうなっていなかったものを直した。

| 項目 | 内容 | ファイル |
|---|---|---|
| 1 | 系 B-compare-base の Lean 版 `conjSum_eq_of_base_formula`（群論）と `homologicalEulerK0_pullback_conjSum_eq_of_base_formula`（Euler 評価を準同型 `u₁`、`u₂` で引き戻した形）。`perfectEuler_conjSum_eq`、`symmetricPaperEuler_conjSum_eq` はこの適用に書き換えた（それまでは群論の `conjSum_eq` を直接呼んでいた） | `GroupTheory/ConjugateSum`、`CategoryTheory/EulerComparison`、`LengthAlgebra/Comparison`、`Paper/Section4/SymmetricComparison` |
| 2 | `lemma_3_5c` を定理 C-norm（`perfectEuler_conjSum_eq`、係数環 `A → T`、`T → T`、`T → C`）の適用に書き換えた。降下の引用 `theorem_3_1_K0` は `perfectK0_descent_of_free` で有限射影 K₀ に移し、結論は `freeToPerfectK0` で旧モデルの値に戻す。恒等係数変更の補題 `perfectBaseChangeEulerK0_id` を追加 | `Paper/Lemma3_5`、`LengthAlgebra/PerfectBaseChange` |
| 3 | 抽象層に `iteratedZeroCone_euler_eq_length_zero`（振幅 `[-n, 0]` なら Euler 評価は反復錐の第零次の長さ）を置き、`iteratedZeroCone_euler_lower_bound` をその系にした。ランク版は Betti 計算 `completedRankBetti_koszulTower_top` を一つの補題にし、`completedRankEuler_eq_koszul_zero_limit(_of_koszul)` と `completedRankEuler_koszul_lower_bound` を抽象定理の適用にした。抽象論を再証明していた `completedRankEuler_lower_bound_of_vanishing` と、不要になった `completedRankHomology_koszul_zero_iso` は削除。スカラー列は `koszulScalars`（`LengthAlgebra/PerfectVanishing`）を再利用（`koszulPowScalars`） | `CategoryTheory/IteratedCone`、`Asymptotic/RankVanishing`、`Asymptotic/RankMinimalLowerBound` |
| 5 | `Section5.lemma_5_3_of_cm`：λ-CM 性（`koszulAcyclic_of_cm`、商の有限性）と `x` の像がパラメータ系であることから `lemma_5_3` の Koszul 入力を供給する。それまで λ-CM の補題群は呼び出し元がなかった | `Paper/Section5/ParameterQuotientCM`（新規） |

項目 4（有限近似の抽象化、§4.5 の定義 approx と定理 approx-exist の Lean 版）は保留。
`Paper/Section2/TowerApproximation.lean`（約 1000 行）の `exists_tower_approximation_B` は具体的な塔 `TS A t p T = Tower A t p ⊗ T` と `μT` に対して述べられており、
抽象化には (i) 塔と整合する長さ（§4.5 の定義）を `LengthAlgebra` に置く、(ii) 近似列の条件（増大度・消滅・Tor の極限）を塔に依存しない Prop にする、
(iii) 既存の証明を「塔の各段の長さの公式」と「核の評価」を入力とする形に分ける、の三段階が要る。
Section2 は並行作業の範囲でもあるので、別の作業として計画する。

検証：全体 `lake build` 成功（3707 ジョブ、変更したファイルに警告なし）。`#print axioms`：新しい宣言と書き換えた比較定理は
`propext`・`Classical.choice`・`Quot.sound` のみ。`lemma_3_5c`、`theorem_4_7_K0`、`lemma_5_3_of_cm` の `sorryAx` は既存の引用
（`theorem_3_1_K0`、`supportedRankK0_descent`、正則パラメータ）に由来する。解説の Lean 注記（系 B-compare-base、定理 C-norm、
定理 asymp-norm、命題 35c、命題 paper-param、補題 B-h0、補題 nitasymp、補題 asymp-h0）を更新し、`\ld{...}` 228 件を確認した。
