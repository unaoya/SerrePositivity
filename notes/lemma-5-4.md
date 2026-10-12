# Lemma 5.4（有限近似）の形式化

> 数学的な解説・調査記録。記載日の仮定・証明方針を保持し、現在のLean実装と未証明状態は [status.md](status.md) を正本とする。

2026-10-10 作成。

現在の作業範囲（2026-10-10 方針変更）：[section-4-plan.md](section-4-plan.md) 冒頭に従い、
抽象化と二つの実現の整理を優先する。このノートの§5への具体的接続は実装済みの記録として
保存する。下の「残り」にある正規化基底・ガロア拡大の存在構成や核心定理の完成は後の課題であり、
当面の続行対象にはしない。有限近似から共通定理の比較・消滅・下界へ進む適用部分は対象に含める。

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
- `Section5.lemma_5_4`：証明済み（直接の `sorry` なし。`sorryAx` は λ_∞ の引用 (C1)・(C2) と
  「正則パラメータ系は正則列」(A1) から）。`ℓ_B(B/I) < ∞` を仮定にする
  （(5.11) で `0 · ⊤ = 0` を避けるため。論文の `I = m_B^a` では成り立つ）。
  2026-10-10 の続行で、加群族と剰余体の分解 `G`・`G₀` の入力を廃止し、
  極小自由分解を内部で構成する形に改めた。剰余体係数の全次数の Tor 極限も同じ近似列の結論に追加。`S = Λ ⊗_A T` の `U = C/(x)C` への作用を環準同型 `θ` と
  二つの両立条件で与え、(5.9)、(5.10)（`τ_i(L) = λ(Tor_i^R(C, L))`）、(5.11)（`λ(U) ≤ τ_0(k) ℓ_B(B/I)`）を
  結論にする。証明は一般論・Lemma 5.3・`θ` による長さの一致・`Tor^B(U, L)` の二つの計算の一致から。

## §5.1–5.2 の準備（証明済み）

- **幾何ファイバーの推移性**（`CommutativeAlgebra/GeometricTransitivity.lean`）：
  `isGeometricallyTransitive_of_fixed`。`T` が `A` 上有限で `T^G = A` なら `IsGeometricallyTransitive A T G`。
  ノルム `Π_g g(u)` がスカラー（`exists_prod_tensorAction_eq`）であることと、Artin 環 `T ⊗_A Ω` の
  軌道の冪等元から。論文と違い、軌道の `G` 安定性は使わず `x`、`y` を直接比べる。
- **(5.4) の `x` の選択**（`CommutativeAlgebra/ParameterAvoidance.lean`）：`exists_regular_parameters_in`。
  `x_i ∈ Q`、`R` 弱正則列、`√(P + (x)) = m_R`。素イデアル回避で随伴素イデアルと極小素イデアルを避け、
  次元の降下は Mathlib の `supportDim_quotSMulTop_succ_eq_...`。引用は非混合性
  （`Inputs/Unmixedness.lean`、`sorry`）だけ。
- **(5.6) と `θ`**（`Paper/Section5/Preparation.lean`）：`exists_pow_maximalIdeal_map_le`（局所準同型で
  `f(m_B^a) ⊆ I`）、`paramTheta : Λ ⊗_A (D′/I_σ) → C/(x)C` と両立性 `paramTheta_comp_tower`（`hθΛ`）、
  `paramTheta_comp_ψU`（`hθB`、`B → T` は `paramBT`）。

## 残り

- Lemma 5.6 の抽象部分は `Asymptotic/RankMinimalLowerBound.lean`、
  `Asymptotic/PaperMinimalLowerBound.lean` で証明済み。極小性から実際の全射を作り、
  共通の消滅定理により Euler 下界を得る。
- `Paper/Section5/ApproximationLowerBound.lean` は上記の有限近似の長さと
  `length_le_tor_zero_mul` から生成元数の正規化下界・正値性を導く。
  `Paper/Section5/AsymptoticPositivity.lean` はこれを論文側の Euler 正値性へ接続する。
- Lemma 5.5 の構成部分を実装：`HomologicalAlgebra/MinimalFreeResolution.lean`、
  `MinimalBetti.lean`、`MinimalTruncation.lean` で極小分解、全次数の Betti 階数公式、
  有限切り詰めを構成。`Asymptotic/MinimalResolutionFamily.lean` で自由複体列に組み戻す。
  `Paper/Section5/MinimalApproximation.lean` は有限近似から振幅・極小性・正の零次階数を
  同時に供給する。Noether 局所環で成立し、`B` の正則性も Tor の対称性も不要。
- `HomologicalAlgebra/TruncationBoundary.lean`、`MinimalBoundary.lean`：消去元の作用を
  切り詰めると、捨てた直前の自由項を通る射とホモトピックになる。
  `Asymptotic/MinimalSupport.lean` は `β_(l+1)=o(s)` からこの境界を商で消し、
  元の加群列の共通消去指数のままでランク商の支持を証明する。
- `Paper/Section5/SupportedApproximation.lean` は有限近似から支持・極小性・正の零次階数を
  同時に構成。`exists_paperEuler_pos_of_minimalApproximation` は、`B → S` に沿う係数変更で
  係数環側の Koszul 消滅と商の正の長さを仮定し、正の Euler 評価をもつ対象を構成する。
- `Asymptotic/MinimalTruncationComparison.lean`：高次 Betti 数が `o(s)` なら、
  切り詰めを深くしてもランク商の対象は同型。必要な次数 `i` より深い代表を実際に
  構成し、その次数の係数変更後のホモロジーを Tor と同定する。
  `HomologicalAlgebra/KoszulTruncation.lean` は Koszul 構成後の比較も供給する。
- `Paper/Section5/ApproximationHomology.lean`：有限な剰余体 Tor の極限と高次の
  零極限から、上記の代表を支持つきの商の圏内で選べる。
  これは生のホモロジーと Tor の同定。商の Betti 評価との接続は、下記の
  `MinimalBettiEvaluation` と `ApproximationBetti` で証明した。
  この二つの変数順の比較は `HomologicalAlgebra/TorSymmetry.lean` で解消した。
  `exists_supported_representative_with_tor_limit` により、有限近似の通常 Tor の
  正規化極限を、同じ支持つき対象の深い代表のホモロジーへ移せる。
  これは `B` 線形同値による通常の長さの比較で、高次の自然性は主張しない。
- `CategoryTheory/ConeLengthCancellation.lean`：上に有界な係数列に対する二項変換の単射性。
  `HomologicalAlgebra/KoszulHomologyLength.lean`：無限分解も含む零ホモトピックな
  Koszul 操作の長さの公式。`Asymptotic/KoszulHomologyLimit.lean` で正規化極限へ移す。
- `Asymptotic/MinimalBettiEvaluation.lean`：商の Betti 評価と全極小分解の
  ホモロジー・代数係数 Tor の正規化極限の一致。全分解の長さの有限性と `O(s)` も
  深い切り詰めの Koszul 評価から証明しており、追加の入力にはしていない。
- `Paper/Section5/ApproximationBetti.lean`：剰余体 Tor の有限な極限と高次の零極限、
  共通の消去冪を確認し、各次数の通常の収束値を商の Betti 評価と同定。
  極限列の有限支持と、その有限交代和による Euler 評価を証明した。
  基底環 `B` 上の通常の `Tor_i(M_n,S)` の長さにも適用でき、
  `B → S → k(S)` が全射なら `S` 上の通常の長さによる Betti・Euler 評価へも接続済み。
  `B` の正則性、有限近似の一様な射影次元、係数変更の平坦性は追加していない。
- `ApproximationEuler.lean`：任意の係数環の自己同型によるひねりが通常評価を保つこと、
  有限近似の Tor 極限と共通剰余体から通常 Euler 評価が `lambdaChi`・`c_σ` になることを証明。
  同じ近似から、支持・振幅・極小性・正の零次階数をもつ複体列とこの評価を同時に構成する。
- `ApproximationGrowth.lean`：Lemma 5.4 の剰余体 Tor 極限と Lemma 5.3 の有限性・消滅から、
  切り詰めに必要な `O(s)`・`o(s)` を導く。`B` の正則性は使わない。
- `ComplexEvaluationIndependence.lean`：同じ複体列が二つの支持をもつなら、
  各次数の評価・Euler 評価が一致する。商をとる前の一様支持や根基の一致は不要。
  `PaperComplexBaseChange.lean` で、行列の係数変更後に支持の指定を変更できる。
- `OrdinaryTwistEvaluation.lean`：商で支持される任意の複体列の通常評価は自己同型で不変。
  既存の `paperTwist` の K₀ 群作用についても成立する。
- `ApproximationSecondComparison.lean`：有限近似側から正則基底側へ、根基の包含で
  同じ複体の支持を移す。全ひねりの通常評価が同じ `lambdaChi` になることと、
  第二比較の共役和等式を共通の対称比較から導く。`twistedAlgebraMap` を用いれば `c_σ` の形になる。
- `PaperTwistLowerBound.lean` と `SecondComparisonLowerBound.lean` は
  各共役の下界と、第二比較から通常評価に戻した同じ下界を供給する。
- `LocalBaseChangeBounds.lean`：係数変更後の振幅と、局所準同型による極小性の保存を証明。
  群の自己同型が極大イデアルを保つことから、各共役のイデアル条件も一つに減らした。
- `ApproximationPositivity.lean`：同じ有限近似から対象を構成し、第二比較・全共役の正値性・
  通常 Euler 数（`lambdaChi`）の正値性を同時に導く。複体・支持・極小性・正の零次階数や
  Euler 評価の正値性を新たな入力にはしない。
  `exists_secondComparison_pos_of_primary` は、根基条件から通常 Koszul の有限性を導き、
  `LengthAlgebra/QuotientBounds.lean` により下界の商 `C / m_T C` の冪ねじれ性・有限性も確認する。
  この商に残る数値条件は `0 < λ(C / m_T C)` である。
- `LengthAlgebraRealization.lean` と `LengthAlgebraPositivity.lean`：有限局所代数・共通剰余体・
  長さ代数の消滅と商の階数公式から、局所性・支持の根基・Koszul 有限性・Euler 数の一致・
  比較先の商の正値性を確認する。支持生成元と正の消去冪も内部で選ぶ。
  正則基底と幾何的群作用からの既存の引用の適用は `RegularLengthAlgebraPositivity.lean` に分離した。
- `TowerPositivity.lean`：Lemma 5.4 の近似列を内部で作り、同じ列の剰余体と `T` に対する
  Tor 極限を使う。Lemma 5.3 で有限性と高次消滅を確認し、第二比較と正値性へ接続する。
  共通消去イデアルは Artin 環 `Z` への写像の核とし、有限余長も導く。
  `φ = ι_σ`, `T = E′` の対応で、結論は `c_σ > 0` になる。
- `ParameterLengthPositivity.lean`：本文の商 `D′/(ι(x))` を構成し、消去冪・支持・共通剰余体・
  塔からの作用の両立を確認する。(2.5) と重複度の正値性から、近似元の商の有限な正の長さも導く。
- `TwistedLengthPositivity.lean`：パラメータ系と剰余体条件を自己同型で移し、同じ長さ代数の
  (2.4)・(2.5) から全ての `c_σ > 0` を得る。長さの群不変性や長さ代数への群作用は仮定しない。
  `CoreLengthPositivity.lean` は同じ設定で第一比較まで接続する。
- `FiniteParameters.lean` と `ParameterChoice.lean`：有限単射局所拡大へパラメータ系を移し、
  次元・根基条件から `x_i ∈ Q` である正則列を選ぶ。`R/(x) → E′` の代数構造・有限性も構成する。
  `SelectedParameterPositivity.lean` はこれらの選択を正値性の内部へ移す。
- `NormalizationPositivity.lean`：`core_of_normalization_bases` が定理2.5を二回適用し、
  二つの長さ代数と必要な公式を供給する。共通剰余体から標数・完全性を移し、単射性から
  正の階数と素スペクトルの全射性、不変環条件から幾何的推移性を導く。
  `LengthAlgebra/Nontrivial.lean` により、比較先の長さ代数の非自明性も商の長さから確認する。
- 残りは核心定理の仮定から、正規化基底とそれを固定する有限群作用付き拡大を両立して選ぶこと。
  有限性・局所性・完備性・共通剰余体・生成点での分離性・不変環条件の確認が必要になる。
  基底を任意の拡大に対して独立に選ぶだけでは群作用との両立は得られない。
  `core_statement` の証明全体の完了とはしない。

2026-10-10 続行の検証：全体 `lake build` 成功（3448 jobs）。新しいひねりの評価・`c_σ` の
同定・同じ支持対象の構成は標準公理のみ。`lemma_5_4` とパラメータ商からの増大条件の具体化は
既存の引用に由来する `sorryAx` に依存する。新しい未証明入力は追加していない。

同日・第二比較の接続後の検証：全体 `lake build` 成功（3455 jobs）。支持変更、通常評価の
不変性、実際の群作用との照合、有限近似からの第二比較、共通下界を含む新しい22宣言は
標準公理のみ。`theorem_4_7_K0`・`lemma_5_4` の既存の引用依存とは分けて確認した。

同日・正値性の同時構成後の検証：全体 `lake build` 成功（3458 jobs）。係数変更後の
振幅・極小性、全共役の下界、根基条件からの通常有限性、下界の商の有限性、同じ近似からの
第二比較と正値性の構成を含む新規9宣言は、いずれも標準公理のみで `sorryAx` なし。
既存定理 `lemma_5_4`・`theorem_4_7_K0` の引用依存は残る。

同日・長さ代数と塔への接続後の検証：全体 `lake build` 成功（3463 jobs）。新規15宣言のうち、
有限局所代数の補題・長さ代数の仮定確認・その適用定理の13宣言は標準公理のみ。
正則・幾何的な版と塔からの正値性の2宣言には、既存の正則パラメータ・降下・塔の長さの
引用に由来する `sorryAx` が残る。新しい未証明入力は追加していない。

同日・本文のパラメータ商と第一比較への接続後の検証：全体 `lake build` 成功（3466 jobs）。
新規8宣言のうち、剰余体・パラメータ系の移送、商の長さの同定、最後の算術の4宣言は
標準公理のみ。具体的な正値性と第一比較への適用の4宣言は既存の引用に由来する
`sorryAx` に依存する。重複度の正値性・階数公式の引用も明示しており、
新しい未証明入力は追加していない。

同日・パラメータ選択と定理2.5からの構成後の検証：全体 `lake build` 成功（3471 jobs）。
新規8宣言のうち、有限拡大・商代数の4補題と長さからの非自明性は標準公理のみ。
パラメータ選択と二つの正値性への接続は、非混合性・定理2.5などの既存の引用に由来する
`sorryAx` に依存する。新しい未証明入力は追加していない。
