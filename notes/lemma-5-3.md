# Lemma 5.3（パラメータ商の `Tor`）の形式化

> 数学的な解説・調査記録。記載日の仮定・証明方針を保持し、現在のLean実装と未証明状態は [status.md](status.md) を正本とする。

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
`i + h > d` で `λ(Tor_i^R(C, L)) = 0`。

2026-10-11：証明を共通の反復錐定理へ移し、旧数値的不等式の反復証明を削除した。

- `x_j L = 0` から、分解 `P` 上で各 `x_j` の冪が零ホモトピックになる。
  共通の正の冪 `w` を選び、係数変更後の `P_C` へ移す。
- `c_j = φ(x_j)^w` と分解の振幅 `[-d, 0]` を
  `LengthAlgebra.lambdaHomology_projective_vanishing` に渡す。
- 環自身の正次数の Koszul 消滅と、長さの商での反復錐定理から結論を得る。
  以前の `w 2^h` という余分な冪と、上下の数値的不等式の独立した証明は不要。

仮定の形について：(a) は `J^a ⊆ (x)C`、(b) は `J` 有限生成かつ `J ⊆ √((x)C)`。論文の設定
（`J = 𝔡′C`、`I_σ` は `𝔡′` 準素）ではどちらも成り立つ。Koszul ホモロジーの評価は (b) では
すべての冪 `x^v` について要る（論文 (5.5) は Theorem 2.5 の (2.4) からすべての `v` で成り立つ）。
