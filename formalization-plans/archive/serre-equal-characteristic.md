# 外部引用4を主定理から外す：剰余標数零での Serre の対角線論法

> **アーカイブ（2026-10-17）**：この計画は完了したか、ほかへ吸収された。内容の要約先：解説の付録 A（「引用している結果」の対角線論法の段落）と、`IntersectionMultiplicity/Diagonal*.lean`・`EqualCharZeroPositivity.lean` の docstring。将来は削除する予定で、以下は当時の計画と実施記録のまま。


作成：2026-10-14。状態：完了（2026-10-14）。主定理は `Inputs.serrePositivity_of_field` に依存しない（§8）。
[引用4〜5の調査](intersection-inputs-4-5.md) §2 の候補を、主定理が実際に使う範囲に絞って具体化する。
5番（`Inputs.intersectionVanishing`）は引用のまま残し、この計画では外さない。

## 1. 目的と範囲

[Inputs/SerrePositivity.lean](../../SerrePositivity/Inputs/SerrePositivity.lean) の
`Inputs.serrePositivity_of_field` は、体を含む任意の正則局所環での正値性を引用している。
主定理での利用は
[CharacteristicZeroReduction](../../SerrePositivity/Paper/Section5/CharacteristicZeroReduction.lean) の
`positivity_of_residueCharZero` の 1 か所で、`ratAlgebra_of_residueCharZero` により `ℚ` を体として渡している。
つまり必要なのは **剰余標数零の正則局所環** の場合だけである。

この場合を証明し、利用先を付け替える。一般形の引用宣言は残し、docstring に
「主定理の経路では使わない」と明記する（6番と同じ扱い）。

### 簡単な近道はないか

- 剰余標数零の場合も、正値性の中身は Serre の対角線論法そのもので、これより短い既知の証明はない。
- ただし、正標数側で整備済みの帰着（完備化、代数閉剰余体、素イデアル商、次元零の境界）と、
  環自身の Koszul 重複度公式・パラメータ系の重複度の正値性はほぼそのまま再利用できる。
  新しく必要なのは「対角線の環 `T` を作り、Tor を `T` の Koszul ホモロジーに移す」部分と、
  標数零の係数体の存在である。
- 素イデアル商への帰着（`chi_pos_of_prime_quotients`）は 5番を使うが、5番は正標数・混標数の経路で
  すでに主定理の入力なので、外部入力の数は確実に 1 件減る。

## 2. 証明の流れ

`R` を剰余標数零の正則局所環、`d = dim R` とする。

1. **帰着**：完備化（`CompletionReduction` と同じ）、剰余体を代数閉に（`Section2.lemma_2_1`、`ResidueFieldReduction` と同じ）、
   素イデアル商 `D = R/P`、`E = R/Q`、`h + l = d`（`h = dim D`、`l = dim E`）へ（`chi_pos_of_prime_quotients`）。
   次元零の境界は `chi_prime_eq_one_of_dim_zero` で処理済み。以下 `h, l > 0` でもよいが、論法は境界でも通る。
2. **係数体と Cohen 構造**：完備・剰余体 `k` が標数零なので係数体 `k → R` がある。
   正則なので `R ≅ k[[X_1, …, X_d]]`（正則パラメータ系への評価が全射で、次元が等しいので同型）。
3. **対角線の環**：`S = k[[X, Y]]`（`2d` 変数）、`P_X, Q_Y ⊆ S` を `P, Q` を変数 `X`、`Y` へ写したイデアルの生成するイデアル、
   `T = S / (P_X + Q_Y)`、`δ_i = X_i − Y_i`。完備テンソル積を一般には作らず、この具体的な商環で済ませる。
4. **対角線での商**：`S/(δ) ≅ R`（`Y_i ↦ X_i`）なので `T/(δ) ≅ R/(P + Q) = D ⊗_R E`。仮定から有限長。
5. **次元**：`I = (X, Y)`、`m_X = (X)`、`m_Y = (Y)` について `I^{2n} ⊆ m_X^n + m_Y^n` で、
   `T/(m_X^n + m_Y^n) ≅ (D/m^n) ⊗_k (E/m^n)`。よって Samuel 関数は
   `ℓ_T(T/I^{2n}) ≥ ℓ(D/m^n) · ℓ(E/m^n)` で、右辺は次数 `h + l` の多項式。ゆえに `dim T ≥ h + l = d`。
   一方 `T/(δ)` が有限長なので `dim T ≤ d`。よって `δ` は `T` のパラメータ系。
6. **Tor と Koszul の比較**：`D' = S/P_X`、`E' = S/Q_Y` とおく。
   - `k[[X]] → S` は平坦なので、`R` 上の `D` の自由分解を `S` へ上げると `D'` の自由分解になる。
   - `D' ⊗_S E' = T` で、`Tor_{>0}^S(D', E') = 0`（`E'` の分解も同様に上げ、平坦な基底変換で計算）。
   - `δ` は `E'` 上で正則列（`E' ≅ E[[X]]` の上で `X_i − Y_i` は変数の取り替え）。
   - これらから `Tor_i^R(D, E) ≅ H_i(δ; T)`（`ParameterQuotientTor` の Tor 独立性の議論と同型）。
7. **結論**：`χ^R(D, E) = Σ(−1)^i ℓ H_i(δ; T) = e(δ; T) > 0`。
   `KoszulMultiplicityProof.multiplicity_eq_chiOrd_koszul` と `multiplicity_pos_of_isSystemOfParameters` による。

## 3. 段階

| 段 | 内容 | 再利用する既存 API | 新しく示すもの・見込み |
| --- | --- | --- | --- |
| S0 | 帰着の一般化：`CompletionReduction`・`ResidueFieldReduction`・`ModuleReduction` の `CharP` を外した版（「完備・代数閉剰余体の素イデアル商の核」を仮定に取る形） | `chi_baseChange_of_map_maximalIdeal`、`Section2.lemma_2_1`、`chi_pos_of_prime_quotients`、`chi_prime_eq_one_of_dim_zero` | 既存証明の複製と仮定の差し替えのみ。小 |
| S1 | 標数零の係数体：完備局所環が `ℚ` を含み剰余体が標数零なら、剰余写像の切断がある | Mathlib の超越基底、形式エタール性、完備環への持ち上げ | 完了（§6）。CG・局所代数の係数体（正標数・p-basis 版）とは独立 |
| S2 | Cohen 構造：完備正則局所環と係数体から `k[[X_1, …, X_d]] ≃ R` | `adicPowerSeriesEval_finite_of_span`、`ParameterKoszulGrowth.exists_finite_powerSeries_parameters` の組み立て、`ringHom_injective_of_finite_of_equal_dimension` | 正則パラメータ系なら評価は全射。小〜中 |
| S3 | 対角線の環 `T`、`δ`、`T/(δ) ≅ D ⊗_R E` | `MvPowerSeries` の変数の取り替え・評価 | `S/(δ) ≅ k[[X]]` の同型。中 |
| S4 | `T/(m_X^n + m_Y^n) ≅ (D/m^n) ⊗_k (E/m^n)` と長さの積、`dim T = d` | `HilbertSamuelDimension.natDegree_poly_eq_dim`、Krull の次元評価、`ParameterPowerLengthBound` の Samuel 関数の評価 | 冪級数の切断商を多項式環の商と同一視する部分が最も手間。中〜大 |
| S5 | `k[[X]] → k[[X, Y]]` の平坦性と、分解の持ち上げ | `AdicCompletion` の平坦性（`k[[X,Y]]` は `k[[X]][Y]` の `(Y)` 進完備化）、`HomologicalAlgebra/Tor` の分解による計算 | 中 |
| S6 | `Tor_i^R(D, E) ≅ H_i(δ; T)` | `ParameterQuotientTor`・`KoszulTorLength`・`TorSymmetry`・`KoszulRestriction` | Tor 独立性と `δ` の正則性から。大（最も概念的な部分） |
| S7 | `χ = e(δ; T) > 0`、核の定理、`positivity_of_residueCharZero` の付け替え | `multiplicity_eq_chiOrd_koszul`、`multiplicity_pos_of_isSystemOfParameters` | 接続。小 |

S0〜S2 は対角線と独立に進められる。S3・S4 と S5・S6 も互いに独立。

## 4. 代替と注意

- **5番を避ける余地**：対角線論法は `h + l < d` で `e(δ; T) = 0` も与えるので、等標数では 5番も示せる。
  ただし混標数の経路が 5番を使うため、主定理の入力は減らない。この計画では扱わない。
- **一般の加群で直接対角線をとる案**（[調査](intersection-inputs-4-5.md) §2 の第1案）は、
  加群版の Koszul 重複度公式が必要になるので採らない。素イデアル商なら環自身の公式で済む。
- **完備テンソル積**を一般に定義しない。`k[[X, Y]]` の具体的な商だけを使う。
- 新しい一般補題（S1、S2、S4 の冪級数の部分、S5）は `CommutativeAlgebra/`・`HomologicalAlgebra/` に置き、
  論文の型を import しない。S0・S7 は `Paper/Section5/` の新しいファイルに置く。
- 並行作業の係数体（`PBasisCoefficientField`、未コミットの `EqualCharacteristicNormalization`）は正標数用。
  標数零の S1 は別ファイルにし、既存ファイルには触れない。

## 5. 受入条件

- `positivity_of_residueCharZero` とその下流（主定理）が `Inputs.serrePositivity_of_field` に依存しない。
- 主定理の未証明入力が 1 件減る（外部引用 6 件・保留K理論 2 件）。新しい引用・`sorry` は追加しない。
- 一般形の引用は残し、docstring に「主定理の経路では使わない」と明記する。
- 全体 `lake build`、公理監査、文書の参照検査が通る。exposition 付録 A の表と README を更新する。

## 6. 実施状況と見積もりの修正（2026-10-14）

- **S1 完了**：[CharZeroCoefficientField](../../SerrePositivity/CommutativeAlgebra/CharZeroCoefficientField.lean) の
  `exists_residue_section_of_charZero`。超越基底の持ち上げで `ℚ(x) → A` を作り、
  残りの分離代数拡大は Mathlib の `Algebra.FormallyEtale.of_isSeparable` と
  `Algebra.FormallySmooth.exists_mkₐ_comp_eq_of_isAdicComplete` で持ち上げた。約 100 行。
- **S5・S6 は当初の見積もりより重い。** Mathlib にもこのリポジトリにも次がない。
  - Noether 環 `A` 上の冪級数環 `A[[Y]]` の平坦性（`k[[X]] → k[[X, Y]]`）。
  - 局所平坦性判定法。
  - `(A/P)[[Y]]` のような「無限次元の係数を持つ冪級数加群」の `k[[Y]]` 上の平坦性。
    `Tor_{>0}^S(D', E') = 0` には本質的にこれが要る（片側だけの平坦な基底変換では循環する）。
  有限自由複体の基底変換の完全性だけなら、`F ⊗_A A[[Y]] = ∏_{Y^β} F` と係数ごとに見て初等的に示せる。
  しかし `D[[Y]]` の平坦性には、`D` の完備性から `D ≅ ∏ k`（位相的基底）とする議論か、
  局所平坦性判定法のどちらかが必要で、それぞれ独立した基盤整備になる。

## 7. 改訂した設計（2026-10-14）

局所平坦性判定法を先に整備する方針に切り替えた（利用者の判断）。§2 の 5・6 を次のように具体化する。

`R` は完備正則局所環、`k → R` は係数体、`x_1, …, x_d` は極大イデアルを生成するパラメータ系。

- `S = R[[Y_1, …, Y_d]]`。`C : R → S` は定数、`Δ : S → R` は `Y_i ↦ x_i` の評価（`adicPowerSeriesEval`）。
- Cohen 同型 `c : k[[X]] ≃ R`（`X_i ↦ x_i`）と係数ごとの写像 `k[[X]] → k[[Y]] ⊆ S` から `i₂ : R → S`（`x_i ↦ Y_i`）。
  `Δ ∘ C = Δ ∘ i₂ = id`。
- `ker Δ = (δ)`、`δ_i = C(x_i) − Y_i`：`m_S = (Cx, δ)` は `2d = dim S` 個で生成されるので `δ` は正則列で `S/(δ)` は
  `d` 次元の正則局所環（整域）。全射 `S/(δ) → R` は同じ次元の整域の間なので単射。
- `D' = S/P^C = D[[Y]]`。`i₂` を通した `R` 作用で `x` は `D'` 上の正則列（変数 `Y` は係数環によらず正則列）なので、
  **局所平坦性判定法（正則列版）**で `D'` は `R` 上平坦。
- `T = D' ⊗_{R,i₂} E = S/(P^C + Q^{i₂})`。`E → T` は平坦で閉ファイバーは `D'/(Y) = D`。
  Mathlib の `Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown` から `dim T = dim E + dim D = d`（Samuel 関数は不要）。
- **Tor の比較**：`E` の自由分解を syzygy の短完全列 `0 → W_{j+1} → F_j → W_j → 0` として持ち、
  完全関手 `D' ⊗_{i₂} −` で移す。`Tor_{>0}^S(S/(δ), D'^m) = 0`（`S` は `C` で平坦、`S/(δ) ≅ R` は自由）と
  自然同型 `S/(δ) ⊗_S (D' ⊗_{i₂} W) ≅ D ⊗_R W` から、次元シフトで
  `ℓ_S Tor_n^S(S/(δ), T) = ℓ_R Tor_n^R(D, E)`（全ての `n`）。途中の項は無限長でも同型で比較するので問題ない。
- `ℓ_S Tor_n^S(S/(δ), T) = ℓ_T H_n(δ; T)`（`KoszulTorLength`）、`χ(δ; T) = e(δ; T) > 0`。

部品と状態：

| 部品 | 内容 | 状態 |
| --- | --- | --- |
| K1 | 局所平坦性判定法と正則列版 | 完了：[LocalFlatnessCriterion](../../SerrePositivity/HomologicalAlgebra/LocalFlatnessCriterion.lean) |
| K2 | 環準同型を明示した正則列版（代数構造の衝突を避ける） | 完了：[DiagonalFlat](../../SerrePositivity/IntersectionMultiplicity/DiagonalFlat.lean)：`flat_coeffQuot` |
| K3 | 任意の係数環の冪級数環で変数は正則列 | 完了：[PowerSeriesVariableRegular](../../SerrePositivity/CommutativeAlgebra/PowerSeriesVariableRegular.lean)：`isWeaklyRegular_quotient_map_C_ofFn_X`、`isWeaklyRegular_mvPowerSeries_map_C` |
| K4 | Cohen 同型 `k[[X]] ≃ R` | 完了：[EqualCharZeroPositivity](../../SerrePositivity/IntersectionMultiplicity/EqualCharZeroPositivity.lean)：`exists_mvPowerSeries_ringEquiv_of_charZero` |
| K5 | `Δ ∘ i₂ = id`（評価と係数写像の合成） | 完了：[PowerSeriesRingHomExt](../../SerrePositivity/CommutativeAlgebra/PowerSeriesRingHomExt.lean)・[DiagonalRing](../../SerrePositivity/IntersectionMultiplicity/DiagonalRing.lean)：`eval_algebraMap` |
| K6 | `ker Δ = (δ)`、`δ` は `S` の正則列 | 完了：[DiagonalRing](../../SerrePositivity/IntersectionMultiplicity/DiagonalRing.lean)：`ker_eval`、`isWeaklyRegular_diag` |
| K7 | 平坦な基底変換での Tor：`Tor^S(V, S ⊗_R D) ≅ Tor^R(V, D)` | 完了：[TorFlatBaseChangeVanishing](../../SerrePositivity/HomologicalAlgebra/TorFlatBaseChangeVanishing.lean) |
| K8 | 次元シフトによる Tor の長さの比較 | 完了：[TorDimensionShift](../../SerrePositivity/HomologicalAlgebra/TorDimensionShift.lean)・[TorTwoRingComparison](../../SerrePositivity/HomologicalAlgebra/TorTwoRingComparison.lean)：`length_torModule_tensor_eq` |
| K9 | `T ≅ D' ⊗_{i₂} E`、`T/δT ≅ D ⊗_R E` | 完了：[DiagonalTor](../../SerrePositivity/IntersectionMultiplicity/DiagonalTor.lean)：`length_torModule_eq_length_koszulHomologySelf` |
| K10 | `dim T = d`（going-down） | 完了：[DiagonalDimension](../../SerrePositivity/IntersectionMultiplicity/DiagonalDimension.lean)：`ringKrullDim_diagonalQuot` |
| K11 | 核の定理・S0 の帰着・引用の付け替え | 完了：[DiagonalPositivity](../../SerrePositivity/IntersectionMultiplicity/DiagonalPositivity.lean)：`chi_pos_of_prime`、`EqualCharZeroPositivity.chi_pos_of_residueCharZero` |

## 8. 実施結果（2026-10-14）

`Paper/Section5/CharacteristicZeroReduction.positivity_of_residueCharZero` は
`chi_pos_of_residueCharZero` を適用するだけになり、Serre の引用を使わない。
主定理の未証明入力は外部引用 6 件・保留K理論 2 件の計 8 件。
`chi_pos_of_residueCharZero` の未証明入力は `Inputs.intersectionVanishing`（デヴィサージュ）だけで、
冪級数環での核 `DiagonalRing.chi_pos_of_prime` と各部品は標準公理のみ。

計画からの変更：

- 代数閉剰余体への帰着（S0 の `lemma_2_1`）は不要だった。対角線論法は任意の係数体で動く。
- 次元 `dim T = d` は Samuel 関数ではなく、平坦な `R/Q → T` での going-down の高さ公式で示した。
- `S = R[[Y]]` には定数による既定の `R` 代数構造があるため、型の別名 `DiagonalRing` を作り、
  `R` 代数構造を変数の取り替え `i₂` にした。定数側の平坦性は局所的な代数構造で示した。
- Cohen 同型の係数体は存在量化した。`ResidueField R` のままだと冪級数環に係数ごとの `R` 作用が入り、
  代数構造が衝突する。
- 局所平坦性判定法（Matsumura 22.3 の一部）と正則列版は一般論として `HomologicalAlgebra/` に置いた。

検証：全体 `lake build` 成功（4277 ジョブ）、`scripts/audit_axioms.lean`、文書検査（失敗 0）。
