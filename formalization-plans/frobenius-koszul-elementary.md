# 外部引用6を主定理から外す：パラメータ Koszul 複体の初等的な消滅

作成：2026-10-14。状態：完了（2026-10-14）。主定理は `Inputs.frobenius_homology_length_tendsto_zero` に依存しない。
tight closure などを使う一般形の証明は [Frobenius 消滅の計画](frobenius-homology.md) に残し、この文書の範囲に含めない。

## 1. 目的

[Inputs/RobertsFrobenius.lean](../SerrePositivity/Inputs/RobertsFrobenius.lean) の
`Inputs.frobenius_homology_length_tendsto_zero` は、長さ `d` の **任意の** 有限自由複体について
高次 Frobenius ホモロジーの正規化長さの消滅を引用している。
主定理の経路で使うのは
[LengthAlgebraConstruction](../SerrePositivity/Paper/Section2/LengthAlgebraConstruction.lean) の
`perfectClosure_length_properties` の 1 か所だけで、適用先は次の形に限られる。

- `D`：完備 Noether 局所整域、標数 `p`、剰余体は完全体、`dim D = h > 0`。
- `z`：`D` のパラメータ系。
- 必要な結論（`perfectClosure_length_properties_of_higher_tendsto` の仮定 `hlim`）：
  `i > 0` について `ℓ_D H_i(z^(p^n); D) / p^(nh) → 0`。

この特殊な場合を初等的に証明し、利用先をこの証明へ付け替える。
これで一般形の引用は主定理に到達しなくなり、主定理の未証明入力が 1 件減る。
一般形の宣言そのものは引用のまま残す（[Frobenius 消滅の計画](frobenius-homology.md) の対象）。

Frobenius の性質は使わない。任意の冪 `z^q` について `ℓ_D H_i(z^q; D) = O(q^(h−1))` を示す。

## 2. 証明

`k` を `D` の剰余体とする。

1. **係数体と正規化**：`k` は完全なので、完備性から係数体 `k → D` がとれる。
   `R' = k[[Z_1, …, Z_h]]` から `Z_j ↦ z_j` で評価する写像 `F : R' → D` は有限で、
   次元が等しいので単射。`D` は整域なので、`D` は有限生成で捩れのない `R'` 加群。
2. **一様な零化元**：捩れのない有限生成加群なので、有限階数の自由部分加群 `E ⊆ D` と
   `0 ≠ c ∈ R'` で `c · (D/E) = 0` となるものがある。
   Tor の長完全列と `Tor_i(N, E) = 0`（`i ≥ 1`）から `Tor_i^{R'}(N, D) ↪ Tor_i^{R'}(N, D/E)` なので、
   任意の `R'` 加群 `N` と `i ≥ 1` について `c · Tor_i^{R'}(N, D) = 0`。
3. **有限長の中での評価**：`G_•` を `D` の `R'` 上の有限生成自由分解とし、`β_i = rank G_i` とする。
   `W = R'/(Z^q)` は有限長で、`Tor_i(W, D)` は `W ⊗ G_i ≅ W^{β_i}` の部分商 `Z/B`、しかも `cZ ⊆ B`。
   有限長の加群では `ℓ(Z/cZ) = ℓ(0 :_Z c) ≤ ℓ(0 :_{W^β} c) = ℓ(W^β/cW^β)` なので
   \[
   \ell\,\mathrm{Tor}_i^{R'}(R'/(Z^q), D)\le \beta_i\,\ell\bigl(R'/(c, Z_1^q,\dots,Z_h^q)\bigr).
   \]
4. **次元の低い商**：`R'/(c)` は次元 `h − 1` の局所環で、`(Z)^{h(q−1)+1} ⊆ (Z^q)` なので、
   Hilbert–Samuel 多項式の次数定理から `ℓ(R'/(c, Z^q)) = O(q^{h−1})`。
5. **Koszul と Tor の比較**：`Z^q` は `R'` の正則列なので Koszul 複体 `K(Z^q)` は `R'/(Z^q)` の自由分解。
   `Tor_i^{R'}(D, R'/(Z^q)) ≅ H_i(K(Z^q) ⊗ D) ≅ H_i(z^q; D)`（係数制限）。
   Tor の対称性で 3 の左辺と同じ長さになる。
6. **長さの比較**：`F` は剰余体の上で全射なので、有限長の `D` 加群の長さは `R'` 上でも同じ。
7. **結論**：`ℓ_D H_i(z^q; D) ≤ C q^{h−1}`。`q = p^n` として `p^(nh)` で割ると 0 に収束する。

## 3. 段階

| 段 | 内容 | 使う既存の API | 新しく示すもの |
| --- | --- | --- | --- |
| E1 | 有限長の加群の部分商の評価：`W` 有限長、`B ⊆ Z ⊆ W`、`cZ ⊆ B` なら `ℓ(Z/B) ≤ ℓ(W/cW)` | Mathlib の長さの加法性 | 一般補題 |
| E2 | 捩れのない有限生成加群の一様な零化元と、`c · Tor_i(N, M) = 0`（`i ≥ 1`） | `HomologicalAlgebra/TorLES` の `torModule_longExact`、自由加群の Tor の消滅 | 一般補題 |
| E3 | 有限生成自由分解による Tor の部分商表示と、`ℓ Tor_i(W, M) ≤ β_i ℓ(W/cW)` | `HomologicalAlgebra/Tor` の分解による計算、`MinimalFreeResolution` などの有限生成自由分解 | E1・E2 の組合せ |
| E4 | `ℓ(R'/(c, Z^q)) = O(q^{h−1})` | `HilbertSamuelDimension.natDegree_poly_eq_dim`、Krull の次元低下 | 冪と Frobenius 冪の包含 |
| E5 | Koszul と Tor の比較：`H_i(z^q; D) ≅ Tor_i^{R'}(D, R'/(Z^q))`、長さの一致 | `isKoszulResolution_of_isWeaklyRegular`、`RegularSequencePowers`、`TorSymmetry.torModuleIsoCochainLeft`、`KoszulRestriction.koszulModuleHomologyIso`、共通剰余体の長さの比較 | 接続 |
| E6 | 係数体と有限単射な正規化 `F : k[[Z]] → D` | `PerfectNilpotentLifting.exists_unique_ringHom_lift_of_adicComplete`、`AdicPowerSeries.adicPowerSeriesEval_finite_of_span`、`FiniteNormalizationTools.ringHom_injective_of_finite_of_equal_dimension` | 接続。並行作業の `EqualCharacteristicNormalization`（未コミット）と同じ内容になるので、そちらがコミットされていれば再利用する |
| E7 | 組み立てと付け替え：`hlim` を供給し、`perfectClosure_length_properties` を引用なしにする | `perfectClosure_length_properties_of_higher_tendsto` | 最終接続 |

E1〜E4 は互いに独立で、論文にも塔にも依存しない一般論として `CommutativeAlgebra/`・`HomologicalAlgebra/` に置く。
E5〜E7 は具体的な適用で、新しいファイルにまとめる。

## 4. 受入条件

- `perfectClosure_length_properties` とその下流（等標数の長さ代数、定理2.5、主定理）が、
  `Inputs.frobenius_homology_length_tendsto_zero` に依存しない。
- 主定理の `#print sorries` から上の宣言が消え、未証明入力が 1 件減る。新しい引用・`sorry` は追加しない。
- 一般形の引用は残し、docstring に「主定理の経路では使わない」と明記する。
- 新しい一般補題は論文の型（`Paper/`）を import しない。
- 全体 `lake build`、公理監査、文書の参照検査が通る。

## 5. 実施状況（2026-10-14、完了）

| 段 | 実装 |
| --- | --- |
| E1 | [FiniteLengthSmulSubquotient](../SerrePositivity/CommutativeAlgebra/FiniteLengthSmulSubquotient.lean)：`length_ker_eq_length_quotient_range`、`length_le_length_ker_smul_of_subquotient`、`length_le_length_quotient_smul_of_subquotient`、直積の核の長さ `length_ker_smul_pi` |
| E2 | [TorUniformAnnihilator](../SerrePositivity/HomologicalAlgebra/TorUniformAnnihilator.lean)：`torModule_smul_eq_zero`、`torModule_free_succ_eq_zero`、`exists_ne_zero_smul_torModule_eq_zero`。`M` の捩れのなさは不要 |
| E3 | [TorFiniteLengthBound](../SerrePositivity/HomologicalAlgebra/TorFiniteLengthBound.lean)：`length_torModule_le_of_smul_eq_zero`。輪体を `W ⊗ K_{-i} ≅ W^β` に入れて E1 を適用 |
| E4 | [ParameterPowerLengthBound](../SerrePositivity/CommutativeAlgebra/ParameterPowerLengthBound.lean)：`HilbertSamuel.exists_samuelFunction_le_pow`、`exists_length_quotient_generator_pow_le` |
| E5 | [KoszulTorLength](../SerrePositivity/HomologicalAlgebra/KoszulTorLength.lean)：`length_koszulHomologySelf_eq_length_torModule` |
| E6・E7 | [ParameterKoszulGrowth](../SerrePositivity/CommutativeAlgebra/ParameterKoszulGrowth.lean)：`exists_finite_powerSeries_parameters`（係数体と有限な評価）、`exists_length_koszulHomologySelf_pow_le`（`ℓ H_i(z^q; D) ≤ C q^{h-1}`）、`tendsto_length_koszulHomologySelf_frobenius_pow`。`LengthAlgebraConstruction.perfectClosure_length_properties` をこれに付け替えた |

計画からの変更：

- `D` が整域であることも、`F : k[[Z]] → D` が単射であることも使わなかった。
  一様な零化元は、有限生成加群の一般点の基底による自由部分加群の余核から得られる（E2）。
- `ℓ(R'/(c, Z^q))` の評価では、`c` が単元なら商は零なので場合分けし、
  そうでなければ `R'/(c)` で Samuel 関数の評価（E4）を使った。
- 係数体と有限な評価（E6）は、並行作業の未コミットの `EqualCharacteristicNormalization` を使わず、
  コミット済みの `exists_unique_ringHom_lift_of_adicComplete`、`adicPowerSeriesEval_finite_of_span` から
  `exists_finite_powerSeries_parameters` として組み立てた。
  `EqualCharacteristicNormalization.exists_finite_powerSeries_map_of_parameters` がコミットされたら、
  どちらかに統合する。

検証：全体 `lake build` 成功。コミット済みの版にこの変更だけを載せた作業木でも全体ビルド（4123 ジョブ）が通った。
新しい 9 宣言（E1〜E7 の主定理と `perfectClosure_length_properties`）は `propext`・`Classical.choice`・`Quot.sound` のみ。
主定理の未証明入力は外部引用 7 件・保留K理論 2 件の計 9 件になり、
`Inputs.frobenius_homology_length_tendsto_zero` は監査の一覧から消えた。文書検査は失敗 0。
