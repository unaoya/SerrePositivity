# Lemma 5.3（パラメータ商の `Tor`）の形式化

2026-10-10 作成。

## 論文の主張

§5.2 の設定：`x₁, …, x_h ∈ Q` は `R` 正則列で `D` のパラメータ系、`B = R/(x)`、`U = C/I_σ C`。
有限生成 `B` 加群 `L` について

- (a) `τ_i(L) := λ(Tor_i^B(U, L)) = λ(Tor_i^R(C, L))`、すべて有限、
- (b) `τ_i(L) = 0`（`i > l = d − h`）。

論文の証明は (a) に環の変更のスペクトル系列、(b) に導来圏での分解
`K(x; R) ⊗^L L ≃ ⊕_j L[j]^{(h choose j)}` を使う。

## (a)：証明済み（`IntersectionMultiplicity/ParameterQuotientTor.lean`、`sorry` なし）

一般の形：`R` 代数 `C`（`φ`）、`R` 正則列 `x`、`C` 上の正規化長さ `λ` で `J^a ⊆ (x)C`、
`λ(H_q(x; C)) = 0`（`q > 0`）、`λ(U) < ∞`、`R` Noether。結論 `ParamQuot.torClaim`：
すべての `i` と有限生成 `B` 加群 `L` で `λ_U(Tor_i^B(U, L)) = λ(Tor_i^R(C, L)) ≠ ⊤`。

スペクトル系列は使わず、次元シフトで示した。

- `len_torAlg_shift`（一般）：短完全列 `0 → V₁ → V₂ → V₃ → 0` で `λ(Tor_{>0}(V₂)) = 0` なら
  `λ(Tor_{i+2}(V₃)) = λ(Tor_{i+1}(V₁))`、`λ(Tor_1(V₃)) + λ(Tor_0(V₂)) = λ(Tor_0(V₁)) + λ(Tor_0(V₃))`。
- 自由加群：`Tor_i^R(C, B) ≅ H_i(x; C)`（Koszul 分解）から `B^r` へ帰納法。`B` 側は射影的なので 0。
- 0 次：`C ⊗_R L ≃ U ⊗_B L`（`C` 線形、`tensorEquiv`）を直接構成。
- `i` についての帰納法（`L` の表示 `0 → L' → B^r → L → 0`）。

## (b)：証明済み（`IntersectionMultiplicity/ParameterQuotientTorBound.lean`、`sorry` なし）

主定理 `ParamQuot.len_torAlg_eq_zero`：`x_j L = 0`、`L` の長さ `d` 以下の有限自由分解 `P`（`IsResolutionOf`、
`-d` 次より下で零）、`J` は有限生成で `J ⊆ √((x)C)`、`λ(H_q(x^v; C)) = 0`（`q, v > 0`）なら
`i + h > d` で `λ(Tor_i^R(C, L)) = 0`。論文の導来圏の分解は使わず、`K(z; P_C)`
（`P_C = C ⊗ P`、`z = φ(x)^{w 2^h}`）のホモロジーを二通りに評価した。

- 零ホモトピーの道具（`TorBound`）：`Kills a X`（ホモトピー圏で `a • 𝟙 = 0`）、写像錐ごとに冪が二乗
  （`kills_koszulComplexOn`、`kills_koszulComplexOn_self`）、ホモロジーを消す（`Kills.smul_homology`）、
  ねじれ（`isPowTorsion_homology`）。
- 下から（`len_homology_le_koszulComplexOn`）：`c_k` が `X` 上で零、`e ≥ 2^n` なら
  `λ(H^{m+n}(X)) ≤ λ(H^m(K(c^e; X)))`。写像錐の長完全列で連結射が全射（`Cone.exact₁`）。
- 上から（`len_homology_koszulComplexOn_eq_zero`）：有界有限自由複体 `Q` が `m` 次以下で零なら
  `λ(H^m(K(z; Q))) = 0`。項による帰納法（`boundedFiniteFree_induction`）、単一複体はシフト同型で
  `H_q(z; C)` へ、直積は分裂短完全列（`NormalizedEuler.lean` の有限性の議論と同じ形）。
- `x_j` の冪は `P` 上で零ホモトピック（`exists_pow_nullHomotopy_of_homology_annihilated`）、
  係数拡大で `P_C` へ（`Functor.mapHomotopy`、`baseChange_smulId`）。

仮定の形について：(a) は `J^a ⊆ (x)C`、(b) は `J` 有限生成かつ `J ⊆ √((x)C)`。論文の設定
（`J = 𝔡′C`、`I_σ` は `𝔡′` 準素）ではどちらも成り立つ。Koszul ホモロジーの評価は (b) では
すべての冪 `x^v` について要る（論文 (5.5) は Theorem 2.5 の (2.4) からすべての `v` で成り立つ）。
