# Lemma 5.4（有限近似）の形式化

2026-10-10 作成。

## 分け方

- **一般論（塔の近似）**：`Paper/Section2/TowerApproximation.lean`、汎用の評価は
  `PerfectComplex/TensorResolutionLength.lean`。§5 の対象（`C`、`ι_σ`、群）に依存しない。
- **§5 に残す部分**：`T = D′/I_σ`、`B = R/(x)`、`U = C/I_σ C` への適用、`τ_i` との同定（Lemma 5.3）、
  (5.11) の下からの評価（正値性は Theorem 2.5 由来）。

## 一般論の設定と主定理（証明済み、`sorry` なし、引用 (C1)・(C2) のみに依存）

`S = Λ ⊗_A T`、`S_j = A_j ⊗_A T`（論文の `S`、`S_j`）。`A` は Noether 局所環、`t_i ∈ m_A`、`T` は
`A` 上有限な局所環で `m_A^a T = 0`、`A → T`、`B → T` は剰余体で全射。

`exists_tower_approximation`：`J` 冪ねじれで `μ(U) < ∞` の `S` 加群 `U` と、有限自由 `B` 加群の複体の族
`G_k` について、段 `j_n ≥ n` と有限生成 `S_{j_n}` 加群 `V_n` で

- `ℓ_B(V_n) / p^{j_n h} → μ(U)`（(5.9)）
- `ℓ_B(H^m(V_n ⊗_B G_k)) / p^{j_n h} → μ(H^m(U ⊗_B G_k))`（(5.10)）

`μ` は `λ_∞` の `Λ → S` に沿った係数制限。`Tor^B` は `L_k` の有限自由分解 `G_k` で計算する
（`M ⊗_B G = M ⊗_S (S ⊗_B G)`）。

## 証明の構成

1. `TensorResolutionLength`：`μ(H^m(K ⊗ G)) ≤ rank G^m · μ(K)` と評価 (5.12)
   （`S` 線形写像の核・余核による Tor の長さの差）。
2. 段への降下：`S` の元はある段から来るので、関係式を持ち上げて `P ≅ S ⊗_{S_j} V`。
3. `S ⊗_{S_j} V ≃ Λ ⊗_{A_j} V` を直接構成し、(2.2) と剰余体の共通性で `ℓ_B(V)/p^{jh}`。
4. `S` は `S_j` 上平坦（3 の自然性と `Λ` の平坦性）。係数拡大関手のモノイダル構造で
   `(S ⊗ V) ⊗_B G ≅ S ⊗ (V ⊗_B G)`、平坦性でホモロジーと交換（Mathlib
   `preservesFiniteLimits_extendScalars_of_flat`）。
5. 近似：上限の性質 (2.3) で有限生成部分加群、さらに有限表示へ（論文の `P_ε`）。
6. `ε_n = 1/(n+1)` で一段ずつ作り、両側の評価から収束。

論文との差：誤差は「各 `(k, m)` ごとに階数 × `ε_n`」で押さえ、論文の「`i ≤ n` までの誤差を `1/n` 未満に」
という選び方は使わない（各次数で固定の階数なので `ε_n → 0` で十分）。`s_n → ∞` は `j_n ≥ n` から
（`h > 0` のとき）。

## `B` 加群の形（証明済み）

`exists_tower_approximation_B`：`M_n = V_n` を `B` 加群とみて、`M_n` は有限長、`T` を消す `B` のイデアルは
`M_n` も消し、`s_n = p^{j_n h}`（`h > 0` なら `s_n → ∞`）、`ℓ_B(M_n)/s_n → λ(U)`、
`ℓ_B(Tor_i^B(M_n, L_k))/s_n → λ(H^{-i}(U ⊗_B G_k))`。段で計算した `Tor` と通常の `Tor^B` の一致は
`TensorResolutionLength.lean` の `torModuleRestrictEquiv`（`V ⊗_S (S ⊗_B N) ≅ V ⊗_B N`、Mathlib の
`cancelBaseChange`、係数制限とホモロジーの交換）。

## §5 の形（`Paper/Section5/ParameterQuotient.lean`）

- `Section5.lemma_5_3`：証明済み。一般論に正則局所環上の長さ `d` 以下の有限自由分解を与える。
- `Section5.lemma_5_4`：主張のみ（`sorry`）。`S = Λ ⊗_A T` の `U = C/(x)C` への作用を環準同型 `θ` と
  二つの両立条件で与え、(5.9)、(5.10)（`τ_i(L) = λ(Tor_i^R(C, L))`）、(5.11)（`λ(U) ≤ τ_0(k) ℓ_B(B/I)`）を
  結論にする。証明は一般論・Lemma 5.3・`θ` による長さの一致・`Tor^B(U, L)` の二つの計算の一致から。

## 残り

- `lemma_5_4` の証明（上の接続）。
- Lemma 5.5、5.6 の主張：§4 の漸近圏（並行作業で構築中）の定義が固まってから。
