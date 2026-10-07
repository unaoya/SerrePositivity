# 形式化計画

2026-10-07 作成。対象は Theorem 1.1（`notes/INVESTIGATION.md`、`notes/MEMO.md`）。
環境は Lean `v4.35.0-rc4`、Mathlib `e6bbacd0`（2026-10-07）。Mathlib はビルド済みで、プロジェクトは数秒でビルドできる。

## 0. 到達目標とマイルストーン

| 段階 | 到達点 | 目安（粗い） |
| --- | --- | --- |
| M0 | Theorem 1.1 と帰着後の核の主張を Lean で確定する。公理の監査を CI に入れる | 1 週間 |
| M1 | Lemma 5.1（帰着）を sorry なしで証明する。入力は層 3 の束だけ | 1 か月 |
| M2 | 正規化長さの抽象化（Lemma 2.3–2.4）、Koszul 複体の定義、Theorem 2.5 の束 | 1 か月 |
| M3 | 核の骨格：Lemma 5.2–5.6 から Theorem 1.1 を sorry なしで出す。**第一マイルストーン** | 2 か月 |
| M4 | 標準事実（層 3a）を証明して束から外す。Tor API、Lemma 3.4、Lemma 5.3 | 継続 |
| M5 | §4 の圏と Theorem 4.7、Theorem 3.1 | 長期。着手は人手の検証の結果を見て判断 |

**改訂（2026-10-07）**：M2・M3 の順序は §10 の「Lemma 5.2 トラック」に置き換える。
Lemma 5.1 の帰着（M1）は後回しにし、Lemma 5.2 の証明に向けて、Theorem 2.5・Cor 2.6・
Lemma 3.4・3.5・Theorem 3.1 の主張を先に形式化する。

第一マイルストーン（M3）の判定基準：`SerrePositivity.main_theorem` が sorry なしで、`#print axioms` に出るのが Lean の標準公理（`propext`、`Classical.choice`、`Quot.sound`）と、名前つきの入力インスタンスだけであること。

## 1. 設計方針

### 1.1 仮定は Prop 値の `class` に束ね、主定理はインスタンス引数にとる

層 2・3 の入力は `axiom` をばらまかず、層ごとに Prop 値の `class` にまとめる（例：`SerrePositivity.Inputs.Serre`、`Inputs.RobertsGilletSoule`、`Inputs.NormalizedLength`、`Inputs.Descent`）。主定理はこれらを `[Inputs.Serre] [Inputs.Descent] ...` の形でとる。こうすると

- 主定理そのものは公理を使わず、`#print axioms` は標準公理だけになる。
- `SerrePositivity/Axioms.lean` に `axiom` でインスタンスを置けば、公理つきの無条件版も得られる。こちらの `#print axioms` が名前つき公理の一覧になり、CI で許容リストと照合する。
- 層 3a（下記）の束を一つずつ定理に置き換えていく作業が、インスタンス引数を減らす作業として進捗になる。

### 1.2 層の細分化

`INVESTIGATION.md` の 3 層のうち、層 3 を二つに分ける。

| 層 | 中身 | 扱い |
| --- | --- | --- |
| 1 | §5 の議論、Lemma 2.4、Lemma 3.4/3.5 の形式的部分、最終の算術 | sorry なしで証明する |
| 2 | 論文の新しい一般定理：Theorem 3.1、Lemma 3.5（Theorem 3.1 の帰結の形）、§4（Prop. 4.3、Prop. 4.5、Theorem 4.7） | 束に入れる。人手の検証を最優先 |
| 3a | 標準事実で Mathlib にないもの：Tor の長完全列と平坦基底変更、正則局所環の大域次元・整域性・CM 性、Koszul 複体の基本性質、環の取り替えスペクトル系列、極小自由分解 | 束に入れ、M4 以降で証明する。Mathlib への寄与候補 |
| 3b | 文献の深い定理：Serre、Roberts–Gillet–Soulé、Cohen–Gabber、Cohen の構造定理、Monsky、Roberts の Frobenius ホモロジー定理、CLMST、Bhatt–Scholze、Faltings/Gabber–Ramero、Stacks 03QH/0BRI/0BRJ | 束に入れる。証明はしない |

束の各フィールドには docstring で論文の番号（例：`(2.4)`、`Lemma 5.5 の証明第 1 段落`）か文献を必ず書く。論文の主張より強い形で入れざるを得ないときは、その旨を docstring に明記する。

### 1.3 Tor の規約：Mathlib の `CategoryTheory.Tor` を使い、対称性を使わない

- `Tor (ModuleCat.{u} R) i` は `X ⊗ -` の左導来関手（第 2 変数で導来）。`Tor ≅ Tor'` は Mathlib に未証明なので、証明全体で **Tor の対称性を使わない**。Lemma 5.1 の加法性は各変数で別々に示し、Lemma 5.2 の `Tor_i^R(C_D, E')` は E' の自由分解で計算する（論文もその順）。
- 任意の射影分解から計算できることは `ProjectiveResolution.isoLeftDerivedObj` にある。`i > 0` で第 2 変数が射影的なら 0 になることは `isZero_Tor_succ_of_projective`、`Tor_0 ≅ ⊗` は `Functor.leftDerivedZeroIsoSelf` にある。長完全列は Mathlib にない（層 3a）。
- 宇宙は `u` 一つに固定する。`ModuleCat.{u} R` の制約で、環も加群も `Type u` にそろえる。

### 1.4 χ の定義は `finsum` と `ENat.toNat`

`Module.length` は `ℕ∞` 値なので、`χ = ∑ᶠ i, (-1)^i * (length Tor_i).toNat` と定義する。無限長は 0 に、無限個の非零項は和 0 になる（Mathlib の `eulerChar` と同じ junk value の方針）。正則局所環上では `Tor_i = 0 (i > d)` で有限和になる（層 3a）。Tor の各項が有限長であることは台の議論（層 3a）。

### 1.5 Hilbert–Samuel 重複度は束に入れない

Theorem 2.5 の (2.5) は §5 では `0 < λ(U) < ∞`（(5.5)）としてしか使われない。(2.6) は基底パラメータについて `λ(C_D/(t^v)) = v^h rank_A D` の形で使う。したがって束には (2.5) を「任意のパラメータ系 z と v ≥ 1 で `0 < λ(C_D/(z^v)C_D) < ∞`」に弱めて入れ、Hilbert–Samuel 重複度の定義を避ける。弱めた形なので忠実性の問題はない。

## 2. Lean での主張（コンパイル確認済み）

次のファイルは `lake env lean` で通った（警告は `sorry` のみ）。M0 でそのまま `SerrePositivity/Tor.lean`、`EulerChar.lean`、`Statement.lean` に分ける。

```lean
import Mathlib

open CategoryTheory

universe u

namespace SerrePositivity

variable (R : Type u) [CommRing R]

/-- `Tor_i^R(M, N)` as a type, via Mathlib's `CategoryTheory.Tor` on `ModuleCat R`
(left derived in the second variable). -/
noncomputable abbrev TorModule (i : ℕ) (M N : Type u) [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] : Type u :=
  ((Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R M)).obj (ModuleCat.of R N)

/-- `length_R Tor_i^R(M, N)` in `ℕ∞`. -/
noncomputable def torLength (i : ℕ) (M N : Type u) [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] : ℕ∞ :=
  Module.length R (TorModule R i M N)

/-- Serre's intersection multiplicity `χ^R(M, N) = Σ_i (-1)^i length Tor_i^R(M, N)`,
as a `finsum`; infinite lengths are sent to `0` by `ENat.toNat`. -/
noncomputable def chi (M N : Type u) [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] : ℤ :=
  ∑ᶠ i : ℕ, (-1 : ℤ) ^ i * ((torLength R i M N).toNat : ℤ)

open TensorProduct in
/-- Theorem 1.1. -/
theorem main_statement [IsRegularLocalRing R]
    (M N : Type u) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Finite R N] [Nontrivial M] [Nontrivial N]
    (hfin : Module.length R (M ⊗[R] N) ≠ ⊤)
    (hdim : Module.supportDim R M + Module.supportDim R N = ringKrullDim R) :
    0 < chi R M N := by
  sorry

/-- The core case after Lemma 5.1: complete, algebraically closed residue field of
positive characteristic, prime quotients of positive dimension, `P + Q` primary to `m`. -/
theorem core_statement [IsRegularLocalRing R]
    [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    [IsAlgClosed (IsLocalRing.ResidueField R)]
    (p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField R) p]
    (P Q : Ideal R) [P.IsPrime] [Q.IsPrime]
    (hP : 0 < ringKrullDim (R ⧸ P)) (hQ : 0 < ringKrullDim (R ⧸ Q))
    (hsum : ringKrullDim (R ⧸ P) + ringKrullDim (R ⧸ Q) = ringKrullDim R)
    (hprimary : (P ⊔ Q).radical = IsLocalRing.maximalIdeal R) :
    0 < chi R (R ⧸ P) (R ⧸ Q) := by
  sorry

end SerrePositivity
```

使っている Mathlib の定義：`IsRegularLocalRing`（`IsLocalRing`・`IsNoetherianRing` を extends する）、`Module.length : ℕ∞`、`Module.supportDim`・`ringKrullDim : WithBot ℕ∞`、`IsAdicComplete`、`IsLocalRing.ResidueField`、`IsAlgClosed`、`CharP`。

## 3. ファイル構成

```
SerrePositivity.lean                 -- import の集約
SerrePositivity/
  Tor.lean                           -- TorModule, torLength, TorAlg（R 代数 C への Tor_i^R(C, -)）
  EulerChar.lean                     -- chi と基本補題（有限和、加法性は束から）
  Statement.lean                     -- Theorem 1.1 と核の主張（証明なしの命題として）
  NormalizedLength.lean              -- 正規化長さの抽象構造と λ 版 Euler 標数 lambdaChi。Lemma 2.4 は M2
  Koszul.lean                        -- Koszul 複体とそのホモロジーの長さ（M2）
  Ultralimit.lean                    -- 超フィルター極限と通常極限の関係（M3）
  Core/
    Setup.lean                       -- §5.1 のデータ CoreData、ι_σ、c_σ、Lemma 5.2 と (5.18)+(5.17) の主張
    Main.lean                        -- 最終の算術 chi_pos、入力束 Inputs.Core、core_of_inputs
  Inputs/
    Serre.lean                       -- 層 3b：等標数の正値性
    RobertsGilletSoule.lean          -- 層 3b：消滅 (5.1)
    Extension.lean                   -- 層 3b：完備化 + Lemma 2.1 の束（χ・次元・正則性を保つ平坦局所拡大）
    TorAPI.lean                      -- 層 3a：長完全列、i > d の消滅、有限長、χ(k,R) = χ(R,k) = 1
    RegularLocalRing.lean            -- 層 3a：整域、CM、大域次元
    Tower.lean                       -- 層 3b：Lemma 2.2–2.3（正規化基底、塔、λ_∞）
    LengthAlgebra.lean               -- 層 3b：Theorem 2.5、Cor 2.6 の束
    GaloisSetup.lean                 -- 層 3b + 1：§5.1 の D ⊂ D'、G_D、幾何ファイバーの推移性
    Descent.lean                     -- 層 2：Lemma 3.5 (3.11)、§4 の評価と Theorem 4.7
  Proof/
    Reduction.lean                   -- Lemma 5.1（M1）
    FirstComparison.lean             -- Lemma 5.2：CoreData.FirstComparison の証明（M3）
    ParameterQuotient.lean           -- (5.4)–(5.6)、Lemma 5.3（M3）
    Approximation.lean               -- Lemma 5.4（M3）
    Truncation.lean                  -- Lemma 5.5（M3）
    Positivity.lean                  -- Lemma 5.6：CoreData.SecondComparison の証明（M3）
    Main.lean                        -- Theorem 1.1（M3）
  Axioms.lean                        -- 束の axiom インスタンスと無条件版の主定理
  Audit.lean                         -- #print axioms（CI で許容リストと照合）
```

`Basic.lean` は削除する。

## 4. 命題の依存グラフと層の割り当て

```
Theorem 1.1 (Proof/Main.lean)
├── Lemma 5.1 帰着 (Proof/Reduction.lean) ........................................ 層 1
│   ├── Serre（等標数の正値性） ...................................................... 層 3b
│   ├── 完備化 + Lemma 2.1：χ・次元・有限長・正則性を保つ平坦局所拡大 .................. 層 3b
│   ├── Roberts–Gillet–Soulé 消滅 (5.1) ........................................... 層 3b
│   ├── χ の各変数での加法性、Tor_i = 0 (i > d)、Tor_i の有限長、χ(k,R) = χ(R,k) = 1 .. 層 3a
│   ├── 正則局所環は整域 .............................................................. 層 3a（Mathlib になし）
│   └── 素フィルトレーション、台と supportDim の単調性 .............................. Mathlib にあり
└── 核：D = R/P, E = R/Q (Proof/Main.lean)
    ├── 設定 (Inputs/Tower, LengthAlgebra, GaloisSetup)
    │   ├── Lemma 2.2 正則な正規化基底 A_D ⊂ D ..................................... 層 3b
    │   ├── Galois 閉包 D'、G_D、剰余体 k、幾何ファイバーの推移性 ....................... 層 3b + 層 1
    │   ├── 塔 Λ と λ_∞（Lemma 2.3）.................................................. 層 3b
    │   ├── Lemma 2.4 零長さの極限 .................................................... 層 1（抽象構造から証明）
    │   └── Theorem 2.5：(C_D, λ_D) と (2.4)(2.5 弱)(2.6)、Cor 2.6 .................. 層 3b
    ├── Lemma 5.2 (5.3)：|G_D| a_D a_E χ(D,E) = Σ_σ c_σ ............................ 層 1
    │   ├── Lemma 3.5 (3.11) 通常ノルム比較 .......................................... 層 2
    │   ├── Tor_i^R(C_D,E') = H_i((F ⊗_R D') ⊗_{D'} C_D)、台の有限性、ひねりの不変性 .... 層 3a
    │   └── χ(D',E') = a_D χ(D,E)：D^{a_D} → D' の余核と (5.1)、加法性 ................ 層 1
    ├── 各 σ：(5.18) |G_E| c_σ = Σ_γ b_{σ,γ}
    │   ├── x の選択 (5.4)：素イデアル回避（Mathlib `Ideal.subset_union_prime`）、R は CM .. 層 3a
    │   ├── Lemma 5.3 τ_i(L)：有限、i > l で 0 ....................................... 層 1（証明は層 3a：環の取り替えスペクトル系列、Koszul 分裂）
    │   ├── Lemma 5.4 有限近似 M_n, s_n：(5.9)(5.10)(5.11) ............................ 層 1（極限の取り出し）+ 層 3a/3b（段への降下、平坦性）
    │   ├── Lemma 5.5 台と通常評価 = c_σ ............................................. 層 1（§4 の評価 + 極小分解 (5.13) + (1+t)^l の約分）
    │   └── Theorem 4.7 漸近ノルム比較 ................................................ 層 2
    ├── Lemma 5.6 b_{σ,γ} ≥ ν_σ η_E > 0 ............................................ 層 1（多項式の議論、0 次の全射、(5.11)(5.16)）
    └── 最終の算術：|G_D| a_D a_E χ(D,E) = (1/|G_E|) Σ_σ Σ_γ b_{σ,γ} > 0 ............. 層 1
```

層 1 の各補題の中で、層 3a に預ける部分は次のとおり。これらは M3 では束のフィールドとして置き、M4 で証明する。

| 補題 | 層 1 で証明する部分 | 層 3a に預ける部分 |
| --- | --- | --- |
| 5.2 | 加法性と (5.1) から χ(D',E') = a_D χ(D,E)、ノルム比較の適用 | Tor と複体のホモロジーの同一視、Tor の台が閉点に乗ること、σ でひねっても通常の χ が変わらないこと |
| 5.3 | 結論の組み合わせ | 環の取り替えスペクトル系列による長さの一致、`K(x;R) ⊗^L L ≃ ⊕ L[j]` の分裂、`i > l` の評価 |
| 5.4 | ε と n の対角線論法、(5.11) の下からの評価 | λ の sup 性質からの有限生成近似、有限表示の段 j への降下、`Tor^B(P_ε, L) = Λ ⊗ Tor^B(P_j, L)`、(5.12) の評価 |
| 5.5 | `(1+t)^l` の約分と (5.10) からの `b_i = τ_i(E')`、`b_i` の交代和が c_σ | 切り詰めの誤差が rank o(s_n) であること、`m_B^a` の零ホモトピーから台が出ること、Koszul 分裂 |
| 5.6 | `b_i ≥ 0` かつ `(1+t)^l Σ b_i t^i` の l 次より上が 0 なら `b_i = 0 (i > 0)`、超極限の単調性、(5.17) | Koszul 先取りのスペクトル系列で総次数 > l の λ が 0、0 次ホモロジーから `(C_E/m C_E)^{β_0}` への全射、(5.16) |

## 5. §5 を書くためのインターフェース

§4 の圏や perfectoid 化は作らない。§5 が使う性質だけを structure に書き、その存在を束に入れる。

| 構造 | 論文 | 中身 | §5 で使う性質 | 層 |
| --- | --- | --- | --- | --- |
| `NormalizedLength C J` | Lemma 2.3、§3.4 冒頭 | `J` の冪で消える `C` 加群に `ℝ≥0∞` を対応させる関数 λ | `λ 0 = 0`、短完全列で加法的、同型で不変、(2.3) sup 性質、単調性 | 定義。Lemma 2.4 はここから証明 |
| `Tower A` | (2.1)、Lemma 2.3 | `A_n`、`A → A_n` は有限自由 rank `p^{nh}`、`Λ`、`λ_∞` | (2.2) 有限段の正規化、有限表示加群の段への降下、`Λ` は `A_j` 上平坦 | 3b |
| `LengthAlgebra D A` | Theorem 2.5、Cor 2.6 | `C_D`（`D` 代数かつ `Λ` 代数）、`λ_D` | (2.4) 正次数 Koszul ホモロジーの λ = 0、(2.5 弱) パラメータ商の λ は正で有限、(2.6)、Cor 2.6 | 3b |
| `GaloisSetup D` | §5.1 | `A_D ⊂ D ⊂ D'`、`G_D`、`a_D = rank_D D'` | 有限、`D'` は局所整域で剰余体 `k`、`(D')^G = A_D`、幾何ファイバーで推移的 | 3b + 1 |
| `OrdinaryNormComparison` | Lemma 3.5 | 命題 | 有限自由 `T` 複体で台が閉点のものについて (3.11)、`χ_C` の有限性 | 2 |
| `AsymptoticEvaluation` | §4、Theorem 4.7 | 台つきの列 `F = (F_n)` に `b_i^ord(F), b_i^C(F) ≥ 0` を対応させる | 有限個を除き 0、両評価の (4.2)、ひねり γ との両立、台の十分条件（Lemma 5.5 前半）、Theorem 4.7 | 2 |

補足：

- 幾何ファイバーの推移性は `∀ Ω [Field Ω] [IsAlgClosed Ω] [Algebra A Ω], ∀ x y : PrimeSpectrum (T ⊗[A] Ω), ∃ g, g • x = y` と書ける。
- `γ` によるひねり `g^*P` は `ModuleCat.restrictScalars` を複体に写したもの。
- (4.2) の右辺の超極限は `Ultrafilter.lim` で書く。有界列なら存在し、通常の極限があればそれに一致する（`Ultralimit.lean`）。
- `AsymptoticEvaluation` に「台の十分条件」を入れるのは Lemma 5.5 の証明の一部を束に移すことになる。docstring に明記し、M5 で §4 を作る段階で外す。

## 6. マイルストーン別の作業項目

### M0：主張の確定

- §2 のコードをファイルに分けて置く。`Basic.lean` を削除し、`SerrePositivity.lean` の import を更新する。
- `Inputs/Serre.lean`、`Inputs/RobertsGilletSoule.lean`、`Inputs/Extension.lean` に class の骨格を書く（証明なし）。
  - Serre：`ringChar R = ringChar (ResidueField R)`（等標数）のとき Theorem 1.1 の結論。
  - RGS：`length (M ⊗ N) ≠ ⊤` かつ `supportDim M + supportDim N < ringKrullDim R` なら `chi R M N = 0`。
  - Extension：`∃ R₁`、平坦局所 `R → R₁`、`m R₁ = m₁`、`R₁` は完備・正則・剰余体代数閉、`ringKrullDim R₁ = ringKrullDim R`、`supportDim`・有限長・`chi` を保つ。
- `Audit.lean` と CI：`lake env lean SerrePositivity/Audit.lean` の出力を `scripts/axioms.expected` と `diff` する step を `lean_action_ci.yml` に足す。マイルストーン到達時には `lake build --wfail` で sorry を禁止する。
- README の Status を更新する。

### M1：Lemma 5.1

証明の構造（Mathlib の道具つき）：

1. 剰余標数 0 なら Serre で終わる。以後 `CharP (ResidueField R) p`。
2. Extension の束で `R₁` に移る。`chi` と仮定が保たれるので `R₁` で示せばよい。
3. 主張を強めて帰納法にかける：`Claim(M)`：「有限生成 `N` で `length (M ⊗ N) ≠ ⊤` かつ `supportDim M + supportDim N ≤ d` なら `chi M N ≥ 0`、さらに `= d` なら `> 0`」。
   - `M` について `IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime`（Mathlib。零加群、`R ⧸ p`、短完全列の 3 ケース）。
   - 短完全列 `0 → M' → M → M'' → 0` では、`Module.support_of_exact`（Mathlib）で `Supp M = Supp M' ∪ Supp M''` を得て、`supportDim M = max`（要追加）、`M' ⊗ N`、`M'' ⊗ N` の有限長（台の包含と「有限生成で台 ⊆ {m} なら有限長」。要追加）、χ の第 1 変数での加法性（層 3a）。
   - `M = R ⧸ p` のときは `N` について同じ帰納法。第 2 変数の加法性（層 3a）。
   - 両方素イデアル商のとき：次元の和が `< d` なら RGS で 0、`= d` で両方正次元なら核の主張、`= d` で片方が 0 次元なら `p = m` かつもう一方が `0`（正則局所環は整域：層 3a。`ringKrullDim_quotient_succ_le_of_nonZeroDivisor` で `dim R/q < d`）で `χ(k, R) = χ(R, k) = 1`（層 3a）。
4. `P + Q` が `m` 準素であることは「`R/P ⊗ R/Q = R/(P+Q)` が有限長」から出す（Mathlib の `support_of_supportDim_eq_zero` の逆向き。要追加）。

Mathlib に足すべき小補題：`supportDim` と短完全列、`supportDim M = 0 ↔ 有限長`（有限生成・Noether 局所）、`R/(P+Q)` の有限長と `(P ⊔ Q).radical = m` の同値。

### M2：正規化長さと Koszul 複体

- `NormalizedLength C J` を定義し、Lemma 2.4 を証明する。直和は有限部分和で、直極限は `Module.DirectLimit` で扱う。
- Koszul 複体 `koszulComplex (x : Fin n → R)` を `HomologicalComplex` のモノイド構造（`Mathlib/Algebra/Homology/Monoidal.lean`）で、2 項複体 `R --x_i--> R` のテンソル積として定義する。複体のテンソル積に要る対称性・結合性のインスタンス（`TotalComplexShapeSymmetry` など）は `ComplexShape.up ℤ` にしかないので、ℤ 添字の余鎖複体として定義し、必要なら鎖複体に読み替える。ホモロジーの長さ `koszulHomologyLength` を定義する。
- `Inputs/Tower.lean`、`Inputs/LengthAlgebra.lean` の束を書く。(2.5) は §1.5 の弱い形。
- Cor 2.6 と Lemma 3.4 の主張を書く。証明は Koszul 分解と Tor の長完全列（層 3a）に依存するので M4。

### M3：核の骨格（第一マイルストーン）

済（2026-10-07）：数値レベルの骨格。`Core/Setup.lean` の `CoreData` が §5.1 のデータ
（`D'`、`G_D`、`a_D`、`C_D`、`λ_D`、`E'`、`G_E`、`a_E`）を束ね、`c_σ` を論文 (5.2) どおり
`Σ_i (-1)^i λ_D(Tor_i^R(C_D, E'))` と定義する（`R` の作用は `ι_σ`）。
Lemma 5.2 の主張 `FirstComparison`（(5.3) と長さの有限性）と、(5.18)+(5.17) の主張
`SecondComparison`（`b_{σ,γ}` は実数として抽象）から `χ^R(D,E) > 0` を出す `chi_pos` は
証明済み。入力束 `Inputs.Core` は「`core_statement` の仮定のもとで、データが存在して両主張が
成り立つ」という Prop で、`core_of_inputs` がそこから核の主張を出す。

残り：

- `Inputs/GaloisSetup.lean`、`Inputs/Descent.lean` の束を書く。
- `Ultralimit.lean`：`Ultrafilter.lim` による極限、有界列での存在、通常の極限との一致、単調性。
- Lemma 5.2–5.6 を定理として書き、§4 の表の「層 1 で証明する部分」を証明する。残りは層 3a の束に預ける。
- `Proof/Main.lean` で Theorem 1.1 を出す。`Axioms.lean` の無条件版で `#print axioms` を確認し、許容リストを確定する。

### M4：層 3a の削減

優先順：

1. Tor API：第 1 変数の長完全列（射影加群は平坦なので `M' ⊗ P → M ⊗ P → M'' ⊗ P` が各次数で短完全。`HomologicalComplex.HomologySequence` で長完全列）、第 2 変数の長完全列（馬蹄補題。Mathlib の `ProjectiveResolution` で構成）、`Tor_i` の有限長（台の包含）、`χ(k,R) = χ(R,k) = 1`。
2. 正則局所環の性質：整域、`Tor_i = 0 (i > d)`（Auslander–Buchsbaum–Serre の片方向。Mathlib には `projectiveDimension` と正則元による商のシフトがある）。
3. Lemma 3.4：Koszul 複体が `k` の分解になること（正則列）、組成列による帰納法。
4. Lemma 5.3、5.4 の降下部分、5.5 の Koszul 分裂、5.6 のスペクトル系列部分。

### M5：§4 と Theorem 3.1

Verdier 商、冪等完備化、`∏ M_{s_n}(A)` 上の dg 代数、Land–Tamme の降下はいずれも Mathlib の現状から遠い。人手の検証（`INVESTIGATION.md` の「検証の重点」）の結果を見てから、着手するかを判断する。着手する場合は Lemma 4.2 と Prop. 4.3 の圏論的部分（三角圏の局所化は Mathlib にある）から。

## 7. 公理の管理と CI

- 束の class は `SerrePositivity.Inputs` 名前空間に置き、フィールドごとに docstring で論文の番号か文献を書く。
- `Axioms.lean` 以外で `axiom` を書かない。`Inputs/` は class の定義だけ。
- `Audit.lean`：`#print axioms SerrePositivity.main_theorem`（インスタンス引数版。標準公理のみ）と `#print axioms SerrePositivity.main_theorem_unconditional`（`Axioms.lean` 版。名前つき公理のみ）。CI で許容リストと照合する。
- sorry は進行中のファイルにだけ許す。マイルストーン到達時に `lake build --wfail` を通す。
- Mathlib は `lake-manifest.json` で固定する。`update.yml` が毎日 PR を作るので、更新は PR 単位で CI を見て取り込む。

## 8. リスクと未決事項

| 項目 | 内容 | 対処 |
| --- | --- | --- |
| Tor の API が薄い | 長完全列・対称性・基底変更が Mathlib にない | §1.3 のとおり対称性を避ける。長完全列は M4 で証明。`Tor.lean` に閉じ込め、定義の差し替えに備える |
| `WithBot ℕ∞` の算術 | 次元の和や比較が煩雑 | Noether 局所環では `FiniteRingKrullDim` のインスタンスがあるので、必要箇所で `ℕ` に落とす補題を用意する |
| Koszul 複体の添字 | 複体のテンソル積の対称性・結合性は `up ℤ` にしかない | ℤ 添字で定義する。鎖複体との読み替え補題を一つ用意する |
| 束の忠実性 | 論文より強い仮定を束に入れてしまう危険 | docstring に出典を必ず書く。Lemma 5.5 の台の条件のように移した部分は一覧を `Inputs/Descent.lean` の冒頭に書く |
| Mathlib の更新 | master 追従で破壊的変更が入る | manifest で固定。更新は PR 単位 |
| §4・Theorem 3.1 | 形式化は遠い | 人手の検証を優先。M5 は着手判断を保留 |

決定済み（2026-10-07）：

1. 仮定の扱いは §1.1 の「class 束 + axiom インスタンス」方式でまず進める。
2. Koszul 複体は当面プロジェクト内に閉じる。Mathlib 寄与は考えない。
3. blueprint は今は入れない。§4 の木と docstring で代用する。

## 9. 直近の作業（M0）

1. [x] §2 のコードを `Tor.lean`、`EulerChar.lean`、`Statement.lean` に分けて置き、`Basic.lean` を削除する（2026-10-07）。
2. [ ] `Inputs/Serre.lean`、`RobertsGilletSoule.lean`、`Extension.lean` の class を書く。
3. [ ] `Audit.lean` と CI の照合 step を足す。
4. [ ] README の Status と Layout を更新する。

### 核の骨格の次の一手（M3）

1. `CoreData` に Theorem 2.5 の性質（(2.4)、(2.5 弱)、(2.6)、Cor 2.6）と正規化基底 `A_D` を足す。
   Koszul 複体（M2）が要る。
2. `FirstComparison` を Lemma 3.5 の束（`Inputs/Descent.lean`）と層 3a の Tor の同一視から証明する
   （`Proof/FirstComparison.lean`）。
3. `SecondComparison` の `b_{σ,γ}` を §4 の評価として具体化し、Lemma 5.6 の多項式の議論を証明する
   （`Proof/Positivity.lean`）。

### ファイルの書き方（M0 で決めたこと）

- Mathlib はモジュールシステム前提なので、各ファイルは `module` で始め、import は `public import` にする。
  定義を含むファイルは docstring の直後に `@[expose] public section`、定理だけのファイルは `public section` を置く。
- Mathlib の著作権ヘッダ linter は `lakefile.toml` で止めた（`weak.linter.style.header = false`）。
  LICENSE を決めてヘッダを付けるなら戻せる。
- `chi_eq_sum_range`：`Tor_i` の長さが `i > n` で `0` なら `χ` は `i ≤ n` の有限和、を `EulerChar.lean` で証明済み。

## 10. Lemma 5.2 トラック（2026-10-07 改訂）

目標：`CoreData.FirstComparison`（Lemma 5.2）を証明できる状態にする。そのために
(i) 今の主張に抜けがないかを監査し、(ii) `C_D`、`λ_D` の存在と性質を与える Theorem 2.5・Cor 2.6 を
主張として書き、(iii) 証明に使う Lemma 3.5 と、その背後の Lemma 3.4・Theorem 3.1 を主張として書く。

### 10.0 監査：`FirstComparison` に抜けはあるか

Lean の式としては完結している。`chi`、`c σ = lambdaChi lamD (iota σ) E'`、`TorAlg`、
`NormalizedLength.len` のどれも placeholder ではなく、`sorry` も含まない。

しかし `CoreData` には、データが論文の対象であるための仮定が一つもない。足りないもの：

| # | 足りない仮定 | 論文 |
| --- | --- | --- |
| 1 | 正規化基底 `A_D`：正則完備局所環、`A_D ⊆ D'` は有限かつ生成的分離、剰余体は同じ、`A_D` の正則パラメータ系 `t` | Lemma 2.2、§5.1 |
| 2 | `D'` の性質：局所整域、`D` 上有限、`G_D` は `A_D` 上で作用し `(D')^{G_D} = A_D`、幾何ファイバーで推移的、剰余体 `k` | §5.1 |
| 3 | `a_D = rank_D D'`：今は自由な自然数。`Module.finrank (R ⧸ P) D'` と等しいという仮定で縛る | §5.1 |
| 4 | `C_D`、`λ_D` の性質：(2.4)(2.5)(2.6)、Cor 2.6。今は長さ関数の公理（零、同型、加法性）だけ | Theorem 2.5 |
| 5 | `λ_D` の定義域：`m_{D'} C_D` の冪で消える加群としたが、論文は `𝔡 = m_D` の冪。`D ⊆ D'` が有限なので `m_D D'` は `m_{D'}` 準素で同じこと。docstring に書く | §2.3 |
| 6 | `E` 側も同様。Lemma 5.2 の証明で使うのは `E'` が `E` 上有限で階数 `a_E` であることだけ | §5.1 |

方針：`CoreData` は変えず、これらの仮定を `structure CoreData.IsPaperData (X) : Prop` にまとめ、
Lemma 5.2 は `theorem firstComparison (h : X.IsPaperData) : X.FirstComparison` の形で証明する。
`Inputs.Core` の存在主張も `X.IsPaperData` つきに直す。

### 10.1 T1：主張を書くのに要る定義

| 定義 | 使う場所 | 方針 | Mathlib |
| --- | --- | --- | --- |
| Koszul 複体 `koszulComplex (x : Fin n → A) : CochainComplex (ModuleCat A) ℤ`、係数つき `K(x; M)`、ホモロジー `H_i(x; M)`（homological な `i` は cochain の `-i` 次） | (2.4)、(3.9)、3.5 の証明 (3.12) | 2 項複体 `A --x_j--> A` のテンソル積（`HomologicalComplex` のモノイド構造、`up ℤ` 用）。`ModuleCat A` は全余極限をもつので `HasTensor` 系のインスタンスは通るはず。最初に小さな例で確かめる | モノイド構造あり、Koszul なし |
| パラメータ系 `IsSystemOfParameters D z` | 2.5 | `z : Fin h → D`、`h = dim D`、`(Ideal.span (range z)).radical = m_D` | なし |
| Hilbert–Samuel 重複度 `hilbertSamuelMultiplicity I M : ℝ` | (2.5) | `Filter.limUnder atTop (fun n ↦ d! * length(M/I^n M) / n^d)`、`d = dim M`。極限の存在は証明しない（junk value）。(2.5) には「右辺は正で有限」を別に入れる | なし |
| 生成的階数 `rank_A T` | (2.6)、3.4、3.5 | `Module.finrank A T`。整域上の有限ねじれなし加群では分数体上の次元に一致（`IsFractionRing.finrank_eq`） | あり |
| 閉点に台をもつ完全複体 `IsPerfectSupported A T P` | 3.5、3.1 | `P : CochainComplex (ModuleCat T) ℤ`、有界、各項は有限自由、各ホモロジーが `m_A T` の冪で消える | 複体・ホモロジーあり |
| 通常評価 `chiOrd T P = Σ_i (-1)^i length_T H_i(P)`、λ 評価 `chiLam λ P = Σ_i (-1)^i λ H_i(P ⊗_T C)` | 3.5 | `finsum`。`P ⊗_T C` は `(ModuleCat.extendScalars (algebraMap T C)).mapHomologicalComplex` | あり |
| ひねり `twist g P = g^*P` | 3.5、3.1 | `(ModuleCat.restrictScalars (MulSemiringAction.toRingHom G T g)).mapHomologicalComplex` | あり |
| 幾何ファイバーでの推移性 `IsGeometricallyTransitive A T G` | 3.1、3.5 | `∀ Ω 代数閉 A 体, ∀ x y : PrimeSpectrum (T ⊗[A] Ω), ∃ g, g • x = y` | `PrimeSpectrum` あり |
| 台つき完全複体の `K₀`：`K0Supported A J` | 3.1 (3.2) | 対象の `FreeAbelianGroup` を、ホモトピー同値と写像錐の関係 `[cone f] = [Y] - [X]` で割る。`⊗ ℚ` は `TensorProduct ℤ _ ℚ`。`G` 作用はひねりから、`K0 A → K0 T` は係数拡大から | `FreeAbelianGroup`、`CochainComplex.mappingCone` あり。K₀ はなし |

### 10.2 T2：主張の形式化

1. **Theorem 2.5 と Cor 2.6** → `Inputs/LengthAlgebra.lean`。`class Inputs.LengthAlgebra : Prop` のフィールド：
   「Lemma 2.2 の形の基底 `A ⊆ D`（正則完備局所、有限、生成的分離、同じ剰余体、`t` は `A` の正則パラメータ系かつ `D` のパラメータ系）に対し、`D` 代数 `C_D` と `λ_D : NormalizedLength C_D (m_D C_D)` が存在して、
   (2.4) 任意のパラメータ系 `z` と `v ≥ 1` で `λ H_i(z^v; C_D) = 0 (i > 0)`、
   (2.5) `λ(C_D/(z^v)C_D) = v^h e((z), D)` かつ右辺は正で有限、
   (2.6) `λ(C_D/(t^v)C_D) = v^h rank_A D`」。
   Cor 2.6 は Lemma 3.4 の特別な場合なので `theorem cor_2_6 := by sorry` として置き、3.4 から出す。
   塔 `Λ` との両立（Lemma 2.3）は Lemma 5.4 で初めて要るので今回は入れない。docstring に明記する。
2. **Lemma 3.4** → `Descent/Lemma34.lean`。設定：`(A, m_A, k)` 正則完備局所、`dim A = e > 0`、剰余標数 `p`、
   `z` は正則パラメータ系。`T` は `A` 上有限な局所整域で剰余体が同じ。`r = rank_A T`。`C` は `T` 代数で
   `λ : NormalizedLength C (m_A C)` が (3.9)：`λ H_i(z^v; C) = 0 (i > 0)`、`λ(C/(z^v)C) = v^e r` をみたす。
   結論 (3.10)：有限長 `A` 加群 `V` で `λ (TorAlg (algebraMap A C) i V) = 0 (i > 0)`、`λ (C ⊗[A] V) = r · length_A V`、すべて有限。`:= by sorry`。
   ℤ_(p) 代数という条件は、局所環で剰余標数が `p` なら自動なので書かない。
3. **Lemma 3.5** → `theorem lemma_3_5 [Inputs.Descent] ...`。追加の仮定：有限群 `G` が `A` 上 `T` に作用し幾何ファイバーで推移的。
   `P` が `IsPerfectSupported A T` なら、`chiOrd`・`chiLam` の各項は有限で、`∑ g, chiOrd T (twist g P) = ∑ g, chiLam λ (twist g P)`。`:= by sorry`。
   「`K_0^{m_A}(A)` の像と `G` 不変な有理類の上で一致する」という一般形は 3.5 自身の証明で使うだけなので、Lean の主張には入れない。
4. **Theorem 3.1** → `Inputs/Descent.lean`。`H = A`（離散・可換）の場合だけを、`K₀ ⊗ ℚ` のレベル (3.2) で書く：
   「`A` は Noether 可換 ℤ_(p) 代数で Krull 次元有限、`J ∋ p`、`T` は有限可換 `A` 代数で有限群 `G` が作用し
   `Spec T → Spec A` は全射で幾何ファイバーで推移的。このとき `K0Supported T (JT) ⊗ ℚ` の `G` 不変元は
   `K0Supported A J ⊗ ℚ` の像にある」。
   一般の連結結合的代数 `H` は Theorem 4.7 用なので M5 まで保留する。これだけが K₀ の定義を要するので、1〜3 を先にやり、4 は最後にする。

### 10.3 T3：Lemma 5.2 の証明に要る層 3a の事実

論文の証明を Lean の形に分解すると次のとおり。`[3a]` は `Inputs/TorAPI.lean` などの束に入れ、T4 以降で証明する。

| 段 | 内容 | 層 |
| --- | --- | --- |
| (a) | `E'` の有限自由 `R` 分解 `F`。`R` が正則なので有界 | 3a：正則局所環上の有限生成加群は有界な有限自由分解をもつ |
| (b) | `P := F ⊗_R D'` は `IsPerfectSupported A_D D'`。台：`H_i(P) = Tor_i^R(E', D')` は `Supp ⊆ V(P) ∩ V(Q) = {m}` で有限長 | 3a：Tor の台 |
| (c) | `chiOrd D' (twist σ P) = χ^R(D', E')`。`σ` は半線形同型。`D'` 上と `R` 上の長さは剰余体が同じなので一致 | 3a |
| (d) | `chiLam λ_D (twist σ P) = c σ`。`H_i(σ^*P ⊗_{D'} C_D) ≅ TorAlg (ι_σ) i E'` | 3a：係数拡大の結合性、導来関手を分解で計算（`isoLeftDerivedObj`） |
| (e) | Lemma 3.5 を `A = A_D`、`T = D'`、`G = G_D`、`C = C_D` に適用：`Σ_σ (c) = Σ_σ (d)` | T2 の 3 |
| (f) | `χ^R(D', E') = a_D χ^R(D, E')`：`D^{a_D} ↪ D'` の余核はねじれで `dim < h`、RGS (5.1) で `χ = 0`、第 1 変数の加法性 | 3a + RGS |
| (g) | `χ^R(D, E') = a_E χ^R(D, E)`：第 2 変数で同様 | 3a + RGS |
| (h) | 算術で (5.3) | 1 |

T3 では (a)〜(d)、(f)〜(g) を `Prop` の束にし、`firstComparison` を証明する。

### 10.4 作業順（改訂）

1. [x] T1 のうち Koszul 複体以外（2026-10-07：`Multiplicity.lean`、`Perfect.lean`、`GeometricFiber.lean`）。
2. [x] Koszul 複体（`Koszul.lean`）。モノイド構造ではなく写像錐の反復で定義した（§11.1）。
3. [x] T2 の 1〜3（`Inputs/LengthAlgebra.lean`、`Descent/Lemma34.lean`、`Descent/Lemma35.lean`）と
   `CoreData.IsPaperData`（`Core/Setup.lean`）。
4. [ ] **Lemma 3.4 の証明**（§11）。K₀ と Theorem 3.1 より先にやる。
5. [ ] T2 の 4（K₀ と Theorem 3.1）。
6. [ ] T3（Lemma 5.2 の証明の骨格）。
7. [ ] T4：3a の束を証明で置き換える。Lemma 3.5 の証明（3.1 + 3.4 + スペクトル系列）。

Lemma 5.1 の帰着（M1）はこのトラックの後に回す。

### 10.5 T1・T2 で決めたこと（2026-10-07）

- `IsRegularNormalizationBase A D t`：Lemma 2.2 の基底の性質。`IsLocalRing A`、`IsLocalRing D`、
  `Algebra A D` は型として要るので structure の引数、残り（正則、完備、整域、有限、分離、剰余体、次元、
  パラメータ）は Prop のフィールド。生成的分離は `Algebra.IsSeparable A D`。
- `LengthAlgebraData D`（`C` と `λ`）と `LengthAlgebraProps A D t C λ`（(2.4)(2.5)(2.6)）を分けた。
  Theorem 2.5 の class は `∃ Y : LengthAlgebraData D, LengthAlgebraProps A D t Y.C Y.lam`。
- `λ` の定義域のイデアルは一律に「局所整域（`D`、`T`、`D'`）の極大イデアルを `C` に延ばしたもの」。
  Lemma 3.4・3.5 の `m_A` 冪ねじれと同値（`T` は `A` 上有限で剰余体が同じ）。
- `Setup34`：Lemma 3.4 と 3.5 に共通の設定。`IsRegularLocalRing A`、`IsLocalRing T`、代数構造は引数、
  完備・標数・次元・パラメータ・`T` の性質・(3.9) はフィールド。
- `IsGaloisGroup G A B`（Mathlib）を `IsPaperData` に使う。フィールドは忠実性、`A` 上の作用、不変環 `= A`。
- `CoreData` に `A_D`、`t_D`、`A_E`、`t_E` と、`IsDomain`、`SMulCommClass` の instance を足した。

## 11. Lemma 3.4 の証明計画

数学的な整理は `notes/lemma-3-4.md`（2026-10-07、ユーザー作成）にある。そこで指摘されているとおり、
証明で実際に使う仮定は「`z` が `m_A` を生成する正則列」「`C` が `A` 代数」「`λ` の加法性と非負性」
「(3.9) の `v = 1`」だけで、完備性、剰余標数、`T` が整域であること、`T` の有限性は使わない。
そこで、最小の仮定で書いた抽象版

  `lemma_3_4_of_isRegular`：`IsRegular A (List.ofFn z) A`、`Ideal.span (range z) = m_A`、
  `λ : NormalizedLength C (m_A C)`、(3.9) の `v = 1`、`V` 有限長 ⟹ (3.10)

を先に証明し、`lemma_3_4`（`Setup34` 版）は A1（正則局所環の正則パラメータ系は正則列）と
イデアルの読み替え（`m_A C` 冪ねじれ ⟺ `m_T C` 冪ねじれ）から出す。抽象版は Cor 2.6 の 1・2 にも
そのまま使える。Cor 2.6 の 3（`λ(C_D/𝔡C_D) > 0`）は (2.5) と `D/H` の組成列による別の短い議論。

### 11.1 Koszul 複体の定義（決定）

`koszulComplex x`（`x : Fin n → R`）は `n` に関する再帰で、`K(∅) = R`（0 次に集中した cochain 複体）、
`K(x₀,…,xₙ) = Cone(xₙ • 𝟙 : K(x₀,…,xₙ₋₁) → K(x₀,…,xₙ₋₁))`。最後の元を外側の錐にとるので、
Mathlib の正則列 `RingTheory.Sequence.IsRegular M [x₀, …, xₙ]`（`xᵢ` は `M/(x₀,…,xᵢ₋₁)M` 上で正則）
と帰納法の向きが合う。写像錐は Mathlib の `CochainComplex.mappingCone`（ℤ 添字の cochain 複体）。
`H_i(x; M)` は cochain の `-i` 次のホモロジー。

### 11.2 証明の構造（論文）

`V = k` のとき：`z` の Koszul 複体は `k` の `A` 上の自由分解なので `Tor_i^A(k, C) = H_i(z; C)` で、
(3.9) の `v = 1` から主張が出る。一般の有限長 `V` は組成列の帰納法：`0 → V' → V → k → 0` の
Tor 長完全列で、正次数の項は非負性と加法性から `λ = 0`、0 次では連結射の像が `λ = 0` なので
`λ(C ⊗ V) = λ(C ⊗ V') + r`。

### 11.3 必要な部品と Mathlib の状況

| # | 部品 | Mathlib | 扱い |
| --- | --- | --- | --- |
| A1 | 正則局所環の正則パラメータ系は正則列：`Ideal.span (range z) = m` かつ `dim A = e` なら `IsRegular A (List.ofFn z) A` | なし | 層 3a。`Inputs/RegularLocalRing.lean` に `sorry` の定理として置く |
| A2 | 正則列の Koszul 複体は `H^{-i} = 0 (i > 0)`、`H^0 ≅ A/(x)` | 写像錐の三角 `mappingCone.triangleh`、`homologyFunctor` が homological、`homologySequence_exact₁/₂/₃` あり | 証明する。`n` の帰納法。錐の長完全列で `H^{-1}(Cone) = ker(xₙ : H^0 K → H^0 K) = 0`（正則性）、`H^0(Cone) = coker = A/(x)` |
| A3 | Koszul 複体を `ProjectiveResolution (A ⧸ m)` に仕立てる。ℤ 添字 cochain → ℕ 添字 chain の読み替え | `ComplexShape.Embedding.embeddingUpIntLE : Embedding (down ℕ) (up ℤ)`、`restriction`、`ProjectiveResolution` | 証明する。各項は有限自由の直和なので射影的 |
| A4 | 基底変更 `C ⊗_A K(z; A) ≅ K(ι z; C)`：写像錐と `single` が加法的関手と両立 | `homotopyCofiber.mapHomologicalComplexObjIso`、`single` の両立 | 証明する。`n` の帰納法 |
| A5 | `TorAlg (algebraMap A C) i (A ⧸ m) ≅ H_i(ι z; C)` | `ProjectiveResolution.isoLeftDerivedObj` | A3、A4 から |
| A6 | `C ⊗_A (A ⧸ m) ≅ C / mC` | `TensorProduct.quotTensorEquivQuotSMul` | ほぼそのまま |
| B1 | 有限長加群の組成列帰納法。単純加群は `k` | `IsFiniteLength.of_simple_quotient`、`isSimpleModule_iff_isCoatom`、`IsLocalRing.isMaximal_iff` | ほぼそのまま |
| B2 | Tor の長完全列（導来する変数について）：`0 → V' → V → V'' → 0` から `… → Tor_i V' → Tor_i V → Tor_i V'' → Tor_{i-1} V' → …` | なし。馬蹄補題がない。複体の短完全列のホモロジー長完全列（`HomologicalComplex.HomologySequence`）はある | 層 3a で最大の部品。まず `sorry` の補題として置き、Lemma 3.4 を完成させてから、馬蹄補題（`P'ₙ ⊕ P''ₙ` に微分を作る）で証明する |
| B3 | `Tor_i^A(V, C)` は `Ann_A V` で消える。有限長加群は `m` の冪で消える | `leftDerived` の線形性はない | 証明する。`leftDerived_map_eq` で `a • 𝟙` の持ち上げを `a • 𝟙 P` にとり、`extendScalars` が `a • f ↦ φ a • f` であることと `homologyMap` の線形性 |
| B4 | `NormalizedLength` の補題：部分加群・商で単調、完全列 `M₁ → M₂ → M₃` で `len M₂ ≤ len M₁ + len M₃`、両端が `0` なら中央も `0` | 構造の公理から | 証明する。短い |
| C | 組み立て | | B1 の帰納法の中で A5・A6（基底）と B2〜B4（帰納段） |

### 11.4 作業順と進捗（2026-10-07）

1. [x] B4（`NormalizedLength` の補題、`NormalizedLength.lean`）と B1（`FiniteLength.lean`）。
2. [x] A2（`KoszulExact.lean`：`isKoszulResolution_of_isWeaklyRegular`）。写像錐の三角と
   homological functor の長完全列を `exact_transport` で複体のホモロジーの言葉に移して使った。
   正則性を使わない `H^0(K(x)) ≃ R/(x)`（`koszulComplex_homology_zero_equiv`）も分離した。
3. [x] A3（`KoszulResolution.lean`：`koszulResolution`）、A4（`KoszulBaseChange.lean`：
   `baseChangeKoszulIso`）、A5（`TorKoszul.lean`：`torAlgKoszulEquiv`）。
   A6 は不要になった：Lemma 3.4 の 0 次の項を `Tor_0` で書いたため（§10.5 参照）。
4. [x] 抽象版 `lemma_3_4_of_isWeaklyRegular`（`Descent/Lemma34Abstract.lean`）。
   B2（`Descent/TorLES.lean` の `torAlg_longExact`）と B3（`Descent/TorTorsion.lean` の
   `torAlg_smul_eq_zero`）は `sorry`。
5. [x] B3 の証明（`Descent/TorTorsion.lean`：`torAlg_smul_eq_zero`）。`Functor.leftDerived_map_eq` で
   `a • 𝟙 V` の持ち上げを `a • 𝟙 P` にとり、係数拡大・`single`・`homologyMap` がスカラー倍と
   両立することから `φ a • 𝟙 = 0` を得る。
6. [x] B2 の証明（`Descent/TorLES.lean`：`torAlg_longExact`）。馬蹄補題ではなく写像錐による：
   `V₁`、`V₂` の射影分解を ℤ 添字に延長し（`ExtendResolution.lean`）、`f` の持ち上げの錐が `V₃` の
   分解になること（`Descent/ConeResolution.lean`）と、錐の長完全列（`ConeLES.lean`、`ConeSmul` の
   一般化）を `Tor_i ≅ H^{-i}(C ⊗ K)`（`TorCochain.lean`）で移す。長完全列の射が `Tor` の関手性の
   射と一致することは主張していない（Lemma 3.4 では完全性だけを使う）。
7. [x] A1 と「`m_T^N ≤ m_A T`」を `Inputs/RegularLocalRing.lean` に `sorry` で置き、
   `lemma_3_4`（`Setup34` 版）と `cor_2_6_tor`（Cor 2.6 の 1・2）を抽象版から出した。
   定義域のイデアルの取り替えは `NormalizedLength.restrict` と `IsPowTorsion.of_pow_le`。
   Cor 2.6 の 3（`cor_2_6_pos`）は `sorry` のまま。

`#print axioms`（2026-10-07 時点）：`lemma_3_4_of_isWeaklyRegular`（抽象版 Lemma 3.4）、
`torAlg_longExact`、`torAlg_smul_eq_zero` は標準公理のみ。`lemma_3_4`（`Setup34` 版）と
`cor_2_6_tor` が依存する `sorry` は A1（正則パラメータ系は正則列）と `m_T^N ≤ m_A T`
（`Inputs/RegularLocalRing.lean`、どちらも層 3a）だけ。Cor 2.6 の 3（`cor_2_6_pos`）は未着手。

残り：A1 と `exists_pow_maximalIdeal_le_map` の証明（Mathlib の `IsRegularLocalRing` の API は薄く、
「正則局所環は整域」「正則元で割ると正則」が要る）、`cor_2_6_pos`。

### 11.5 実装上の注意

- ホモトピー圏の `homologyFunctor` は複体の `homology` と定義上は一致しない（`rfl` が通らない）。
  `HomotopyCategory.homologyFunctorFactors` の同型で短複体ごと移す（`exact_transport`）。
- `single₀` の 0 次の項は `Z` と定義上しか一致しないので、`rw` が「motive が型正しくない」で
  失敗しやすい。`exact Category.assoc _ _ _` のように項で与える。
- 並行して走らせた Bash コマンドは作業ディレクトリを共有するので、`cd` を含むコマンドを
  並行実行すると相対パスが壊れる。ビルドは一度に一つ、読み取りは絶対パスで。
- ビルド出力を `tail` で切ると先頭の「Unknown constant」を見落とす。`head` で先頭から見る。
