# 形式化計画

2026-10-07 作成。対象は Theorem 1.1（`notes/INVESTIGATION.md`、`notes/MEMO.md`）。
環境は Lean `v4.35.0-rc4`、Mathlib `e6bbacd0`（2026-10-07）。Mathlib はビルド済みで、プロジェクトは数秒でビルドできる。

## 現在の優先順位（2026-10-10 改訂）

この節を最新方針とする。後続の旧マイルストーンや実施記録は経緯を残すために維持するが、
日程・入力の扱い・未実装項目は本節および現行コードを優先する。

1. **未証明入力を可視化する。** 入力クラスは廃止し、名前付きの `sorry` 定理を証明内で直接呼ぶ。
   `Inputs.regularResolution`、`Inputs.intersectionVanishing`、`Inputs.exists_lengthAlgebra` に移行済み。
   整域性・有限自由分解の存在は正則生成列から証明済み。正則パラメータの正則性のみを未証明入力に残す。
   Theorem 3.1 と Roberts–Gillet–Soulé は引用として残す。
   補題3.2・3.3とそのためのK理論の基礎整備は、他の部分を進めてから扱う。
2. **Lemma 3.5a の正規化長さの有限性：証明済み。**
   `koszulFunctor` の加法性・短完全列の保存・シフトとの両立を整備した。
   有限自由加群を基底で分解し、有界有限自由複体を下端への射の核による短完全列で分解する
   二つの帰納法から、係数つき Koszul ホモロジーの有限性を証明した。
   零ホモトピーからの直和因子へ有限性を戻し、`lemma_3_5a_lam_finite` の `sorry` を除去。
   中間補題にも `sorry` はない。C の Noether 性・平坦性は追加していない。
   正規化長さ側の有限性には不要な `[Module.Finite A T]` も主張から除いた。
   検証：全体 `lake build` 成功（2877 jobs）。`lemma_3_5a_lam_finite` と `lemma_3_5a`、
   今回の一般論の公理は `propext`・`Classical.choice`・`Quot.sound` のみ。
   `lemma_3_5b`・`lemma_3_5c` には保留中の入力による `sorryAx` が残る。
3. **§2 の入力境界と構成を検討する。** 正規化基底、長さ代数の存在 Theorem 2.5、
   §4・Lemma 5.4 で必要になる作用との両立を整理する。
   現在の Theorem 2.5 の結論には塔の作用との両立がまだない。系2.6の正値性は、
   Theorem 2.5 の扱いを決めるまで保留し、先行実装しない。
4. **§4 から第二比較へ進む。** [section-4-plan.md](section-4-plan.md) を現行コードに合わせて改訂した。
   §4 内の着手順は、主張の確定 S0 → 3.5a の有限性の証明の定量化 S4a → 商の t 構造と冪等完備性 S1。
   既存の Koszul 関手・有限フィルトレーション・retract を再利用して、まずランクによる一様上界を得る。
   評価の性質は個別の定理として証明し、旧案の `AsymptoticEvaluation` は作らない。
   `core_of_inputs` の第二比較は依然として引数であり、§4 だけで §5 の有限近似や正値性が完成するわけではない。
5. **核の場合と主定理を接続する。** §2 の構成、第一・第二比較から `core_statement` を示し、
   完備化・剰余体拡大・素イデアル商への帰着を整備して `main_statement` に接続する。

### Koszul Euler 標数＝階数（一般の Euler–Poincaré 公式も証明済み）

`koszulEulerChar_eq_finrank` は、一般論からの導出として実装した。
さらに `Inputs` に置いていた一般の Euler–Poincaré 公式の `sorry` も取り除いた。

- `finrank_eq_add_range_of_exact` と `resolution_alternating_finrank`：
  整域上の完全列に Mathlib の rank-nullity を使い、微分の像の階数を相殺する。
- `koszulEulerChar_eq_chi`：Koszul 分解を使って
  `χ^A(z; T) = χ^A(T, A/(z))` と同一視する。
- `chi_eq_sum_finrank_mul_length_of_resolution`：任意の可換環上の有界有限自由分解と
  有限長加群に関する Euler–Poincaré 公式。`IntersectionMultiplicity/ResolutionEvaluation.lean`
  に証明を置き、`Inputs.IntersectionTheory` から未証明の宣言を削除した。
  平坦な第1変数の高次 Tor の消滅と、自由加群とのテンソル積の長さをまず証明する。
  分解の syzygy の短完全列に沿って Tor の有限長性・高次消滅を降下帰納法で示し、
  第1変数の長完全列の Euler 加法性を足し合わせる。
  Tor の対称性・分解の交換を新たに仮定せず、Noether 性も追加しない。
- `chi_eq_finrank_mul_length_of_resolution`：上の公式と階数の交代和を組み合わせる。
  以上の一般定理はすべて `sorryAx` に依存しない。
- 正則局所環に関して残る未証明入力は、正則パラメータの正則性一つだけ。
  `Inputs/RegularParameters.lean` に名前付きの `sorry` として独立させた。
  整域性 `isDomain_of_isRegularLocalRing` と有限自由分解 `Inputs.regularResolution` は、
  極大イデアルの正則生成列を選び、以下の一般定理から導く。
  `N = A/(z)` の長さが `1` であることから `koszulEulerChar_eq_finrank` を導く。
  この最終結論には正則パラメータの正則性による `sorryAx` が残る。
  `lemma_3_5b` の他の未証明入力（Theorem 3.1 など）は引き続き保留。

仮定をまとめる入力クラスは追加していない。Theorem 3.1 の証明には今回着手しない。

検証：全体 `lake build` 成功（2877 jobs）、`git diff --check` 成功。
`#print axioms` により一般の Euler–Poincaré 公式と整域上の階数倍公式が
`propext`・`Classical.choice`・`Quot.sound` のみに依存することを確認した。
`lemma_3_5a` も引き続き `sorryAx` なし。正則局所環への適用と `lemma_3_5b` には上記入力が残る。

### 正則生成列からの整域性と有限自由分解（実装済み）

- `CommutativeAlgebra/RegularSequence.lean`：
  - Krull の共通部分定理で非零元の `x` 進位数が有限であることを示す。
  - `x` が非零因子で `R/(x)` が整域なら `R` も整域、と示す。
  - 極大イデアルを生成する正則列の長さによる帰納法で整域性を導く。
  - 短完全列の族 `0 → K(i+1) → F(i) → K(i) → 0` に対し、
    正則生成列の長さが `d` なら有限生成の `K(d)` が自由になると示す。
    正則元で割った短完全列と Mathlib の `Module.free_quotSMulTop_iff_free` を使用。
- `HomologicalAlgebra/FiniteFreeResolution.lean`：
  有限自由加群からの全射とその核を繰り返し選び、第 `d` 核で止めて分解を構成する。
  Mathlib の `ChainComplex.augment` と `ProjectiveResolution` を使用し、
  最後に次数 `[-d,0]` の cochain 分解へ移す。一般定理に `sorry` はない。
- `Inputs/RegularParameters.lean`：最小生成列の選択は `spanFinrank` から証明。
  正則性のみを名前付き未証明定理として明示的に適用する。
- 既存の `regularResolution` と整域性の主張・利用側の引数は変更していない。
  新しい仮定の束や入力クラスは作らない。§3.5 本体もこの作業では編集しない。

検証：全体 `lake build` 成功（2888 jobs）、`git diff --check` 成功。
上記一般定理を `#print axioms` で監査し、すべて
`propext`・`Classical.choice`・`Quot.sound` のみに依存することを確認した。
正則局所環への適用二つと Koszul Euler 標数＝階数には、正則パラメータの入力による
`sorryAx` が残る。`lemma_3_5a` は引き続き `sorryAx` なし。

### 完了判定

`lake build` と定理ごとの `#print axioms` を確認する。名前付きの `sorry` 定理を利用すれば、
利用先にも `sorryAx` が現れる。ただし `#print axioms` は未証明定理の名前別一覧ではないので、
証明内の引用箇所とドキュメントも併せて確認する。
通常の数学的仮定（短完全性や台の条件など）を引数にすることは維持する。
定理の仮定をまとめる専用の `structure`・`class` は禁止する。必要な仮定を個別の引数で書き、
大きな連言の別名へ置き換える方法も使わない。存在定理の結論は存在量化と明示的な連言で書く。

## 0. 到達目標とマイルストーン

| 段階 | 到達点 | 目安（粗い） |
| --- | --- | --- |
| M0 | Theorem 1.1 と帰着後の核の主張を Lean で確定する。公理の監査を CI に入れる | 1 週間 |
| M1 | Lemma 5.1（帰着）を sorry なしで証明する。入力は層 3 の束だけ | 1 か月 |
| M2 | 正規化長さの抽象化（Lemma 2.3–2.4）、Koszul 複体の定義、Theorem 2.5 の束 | 1 か月 |
| M3 | 核の骨格：Lemma 5.2–5.6 から Theorem 1.1 を sorry なしで出す。**第一マイルストーン** | 2 か月 |
| M4 | 標準事実（層 3a）を証明して束から外す。Tor API、Lemma 3.4、Lemma 5.3 | 継続 |
| M5 | §4 の圏と Theorem 4.7、Theorem 3.1 | 長期。Prop. 4.5 は一様持ち上げと有限版 3.5b の再利用で進める（下記 M5） |

**改訂（2026-10-07）**：M2・M3 の順序は §10 の「Lemma 5.2 トラック」に置き換える。
Lemma 5.1 の帰着（M1）は後回しにし、Lemma 5.2 の証明に向けて、Theorem 2.5・Cor 2.6・
Lemma 3.4・3.5・Theorem 3.1 の主張を先に形式化する。

**§4 の方針決定（2026-10-08）**：Prop. 4.5 は、一様な自由持ち上げの存在を証明して有限版 Lemma 3.5b を再利用する。4.5 を最初の到達点 M5a、4.7 と §5 向け評価までを §4 の到達点 M5b とする。列の圏の K₀ の明示的な計算は追加課題。全体の実装順と完了条件は [section-4-plan.md](section-4-plan.md)、代替証明は [section-4-devissage.md](section-4-devissage.md) に記す。

第一マイルストーン（M3）の判定基準：`SerrePositivity.main_theorem` が sorry なしで、`#print axioms` に出るのが Lean の標準公理（`propext`、`Classical.choice`、`Quot.sound`）と、名前つきの入力インスタンスだけであること。

## 1. 設計方針

### 1.1 未証明の引用は名前付きの `sorry` 定理にする

未証明の一般論を Prop 値の入力クラスで引き回さない。各数学的主張を明示的な定理として述べ、
証明を `sorry` とし、利用先ではその定理を直接適用する。これにより `sorryAx` への依存を
Lean の公理監査で確認できる。証明が完成したらその定理の本体を置き換える。
外部のコードは現時点でコピーせず、Mathlib の関連 PR の取り込みを待つ。

### 1.1a 設定用の構造体を作らない（2026-10-10）

`Setup34`、`IsRegularNormalizationBase`、`LengthAlgebraProps`、`LengthAlgebraData` は削除した。
補題3.4・系2.6・定理2.5の前提を個別に述べ、利用しない仮定を証明済みの主張から除いた。
定理2.5の存在結論は `C`、環構造、代数構造、正規化長さを直接存在量化し、四つの性質を列挙する。
過去の実施記録に現れるこれらの構造体名は旧版の記録であり、再導入しない。

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

**改訂（2026-10-10）**：この方針は取り下げた。§2 は具体的な対象の話なので、Hilbert–Samuel 重複度は
Samuel 多項式の最高次係数として定義し（`CommutativeAlgebra/HilbertSamuel.lean`）、(2.5) は論文どおり
`λ(C_D/(z^v)C_D) = v^h e((z), D)` と書く。重複度の定理（多項式性、次元定理、正値性）は可換環論の
一般論として別トラックで証明する。詳細は `notes/section-2-plan.md` §5。

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

2026-10-10 改訂。§5 は具体的な対象と個別の仮定を受け取り、証明済みの定理または名前付きの引用定理を直接使う。旧案の設定構造体・入力クラスを再導入しない。§4 では圏と評価を構成し、有限性・非負性・(4.2)・ノルム比較を個別の定理として供給する。

| 対象または定理 | 論文 | 中身 | §5 で使う性質 | 扱い |
| --- | --- | --- | --- | --- |
| `NormalizedLength C J` | Lemma 2.3、§3.4 冒頭 | 冪ねじれ加群の非負加法長さ | 加法性・同型不変性・単調性 | 数学的対象として実装済み。(2.3) の上限の性質は §2 の別の仕事 |
| 具体的な塔とその長さ | (2.1)、Lemma 2.3 | A_n、Λ、λ_∞ | 有限段での正規化、平坦性、降下、上限の性質 | `section-2-plan.md` に従って構成する |
| 長さ代数の存在定理 | Theorem 2.5、Cor 2.6 | C_D と作用・長さを存在量化 | パラメータに関する消滅・評価・正値性 | 名前付き引用。塔との両立を含む主張の更新は §2 側 |
| 環・群作用・階数 | §5.1 | A_D、D'、G_D、`Module.finrank` | 有限性、剰余体、幾何ファイバーの推移性 | 個別の対象と仮定で述べる |
| `lemma_3_5` | Lemma 3.5 | 通常のノルム比較 | (3.11)、χ_C の有限性 | 証明済みの部分と名前付き引用への依存を区別する |
| §4 の具体的な評価と各定理 | Prop. 4.3、Theorem 4.7 | b_i^ord、b_i^C、χ_ord、χ_C | 有限性、非負性、(4.2)、ひねり、共役和の一致 | M5b で構成・証明する。専用の仮定束は作らない |

補足：

- 幾何ファイバーの推移性は `∀ Ω [Field Ω] [IsAlgClosed Ω] [Algebra A Ω], ∀ x y : PrimeSpectrum (T ⊗[A] Ω), ∃ g, g • x = y` と書ける。
- `γ` によるひねり `g^*P` は `ModuleCat.restrictScalars` を複体に写したもの。
- (4.2) の右辺の超極限は Mathlib の超フィルターによる極限を使う。有界列での存在、有限和との交換、通常の極限との一致を §4 用の API として整備する（未実装）。
- 「台の十分条件」は rank-small 誤差と支持条件から示す Lemma 5.5 側の接続補題として分ける。先行実装で入力に置く場合も出典を別に明示し、評価の存在だけで証明済みとはしない。

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

詳細な計画は [section-4-plan.md](section-4-plan.md) の 2026-10-10 改訂版を基準とする。Prop. 4.5 は一様持ち上げによる代替証明を維持する。3.5a の新しい実装を再利用して S4a を先行し、仮定の束を使わない現在の規約に合わせる。

| 段階 | 成果物 | 主な依存 |
| --- | --- | --- |
| S0 | 4.3・4.5・4.6・4.7 と §5 向け評価の型、入力境界 | 論文と既存実装 |
| S1 | 商の有界 t 構造、冪等完備性 | Serre heart 条件を含む一般論。S4a の後の最初の圏論の実装単位 |
| S2 | 列の圏、ランク商、台、基底変更、ひねり、K₀ の基盤 | 通常の O・o、共通有界性、三角的 Karoubi 包絡 |
| S3 | Lemma 4.2 | S2 と Koszul による支持つき因子化 |
| S4a | ランクによる一様な長さの上界 | 既存の 3.5a の帰納法・Koszul 関手・retract。S2・S3 より先に実装できる |
| S4b | Prop. 4.3 と (4.2) | S2・S3・S4a、長さの Serre 商、超極限 |
| S5 | A 側の一様自由持ち上げ | S1・S2・S3、ランク評価つき自由分解、通常の o による特徴付け |
| S6 | Prop. 4.5。M5a 完了 | S4b・S5 と有限版 3.5b |
| S7 | Lemma 4.6、一般の連結な H による降下との接続 | S2、dg 商、生成元による表示、支持と群作用の同定、Theorem 3.1 の引用 |
| S8 | Theorem 4.7、§5 向けの各定理。M5b 完了 | S4b・S6・S7 と既存の `conjSum_eq` |

直近は S0 → S4a → S1。その後 S2 → S3 を整備し、S4b・S5 を S6 に接続する。S7 の型と両立条件は S0・S2 から設計しておき、S6 の後は追加の K₀ 計算より S7 → S8 を優先する。未コミットの共有コードを重複編集せず、先行実装は新規モジュールで進め、接続は後で行う。

M5a の完成条件は、任意の X ∈ P_A^J を実際の一様支持つき自由複体列の像として表し、構成済みの評価について Prop. 4.5 の両等式を証明すること。持ち上げ定理を入力として仮定した段階は完成に数えない。一様分解の評価は rank P(M)^i ≤ C·ℓ_A(M) と次数 [-e,0] で十分とし、二項係数の厳密な公式は必須にしない。

M5b は Lemma 4.2、Prop. 4.3 と (4.2)、Prop. 4.5、Lemma 4.6、Theorem 4.7 を接続する。既存の `Inputs/Descent.lean` は H = A の場合だけであり、4.7 には一般の連結な H に対する Theorem 3.1 の帰結が必要。現在の方針に従い、その帰結を名前付き引用として直接使う。Theorem 3.1 自体や Lemma 3.2・3.3 の証明は本トラックでは行わず、`sorryAx` への依存を明示する。

追加課題は K₀(P_A^J) ≃ G_s/g_s の明示計算、可変個数の Koszul 列による生成、および sₙ → ∞ の場合の ℓ∞/c₀ との同定。論文に必要な K₀ の構成・基底変更・群作用・降下は必須範囲に含む。

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
| §4・Theorem 3.1 | 商の t 構造・冪等完備性と dg 代数・降下に追加実装が必要 | Prop. 4.5 は M5 の最小範囲で進め、t 構造の一般論を先に検証する。K₀ の計算は追加課題 |

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

## 12. Lemma 3.5 トラック（2026-10-08）

`notes/lemma-3-5.md` の三分割に従い、主張を四つに分けて形式化した（`Descent/Lemma35.lean`、
`Descent/ConjugateSum.lean`、`K0.lean`、`Perfect.lean`）。

### 12.1 定義の変更

- 台の条件を論文 §3.1 の判定法に変えた：`IsSupported z P := ∃ v, ∀ j, z_j^v • 𝟙 P` が零ホモトピック。
  生成元 `z`（`A` の正則パラメータ系の像）で指定するので、基底変更とひねりで保たれる。
  以前の「ホモロジーが `J` の冪で消える」は基底変更と相性が悪かった。
- `K0Supported T z`：`z` に台をもつ完全 `T` 複体の自由アーベル群を、ホモトピー同値と
  写像錐の関係 `[Cone f] = [P'] - [P]` で割ったもの。`K0.mk`、`K0.lift`（関係式を保つ関数から
  準同型）を用意した。基底変更 `K₀(A) → K₀(T)` と `G` の作用はまだ定義していない
  （Theorem 3.1 を `Inputs.Descent` として置く段階で、ひねり・基底変更が台つき完全複体と
  関係式を保つ補題とともに足す）。

### 12.2 四つの主張

| 主張 | 設定 | 内容 | 状態 |
| --- | --- | --- | --- |
| `lemma_3_5a` | 節 a：`A` Noether 局所、`z` パラメータ系（`hz`）、`T` 有限、`λ H_j(z^v; C) < ∞`（`hfin`） | `χ_T`、`χ_C` が有限で `K₀` 上の準同型を定める | 通常側は証明済み、正規化長さ側は `sorry` |
| `lemma_3_5b` | 節 b：`A` 正則、`z` 正則パラメータ系（`hz'`、`hdim`）、`T` 局所で剰余体同じ（`hres`）、(3.9) の `v = 1`（`hkz`、`hq`）、`hfin` | `Q ⊗_A T` の上で `χ_T = χ_C = r · χ_A(Q)` | `sorry` |
| `lemma_3_5c` | 節 c：節 b に加えて剰余標数 `p`、`G` の作用、`Spec T → Spec A` 全射（`hsurj`）、幾何ファイバーで推移的（`htrans`） | `Σ_g χ_T(g^*P) = Σ_g χ_C(g^*P)` | 証明済み（3.5a・3.5b・`theorem_3_1_K0` から） |
| `conjSum_eq` | アーベル群の準同型 `f : K →+ K'`、有限群 `G` の `K'` への作用、`φ ψ : K' →+ ℝ`、`φ ∘ f = ψ ∘ f`、`G` 不変元は正の倍数が `f` の像 | `Σ_g φ(g • y) = Σ_g ψ(g • y)` | 証明済み |

`lemma_3_5` は 3.5a の有限性と 3.5c の組み合わせ（証明済み）。

仮定は構造体（旧 `Setup35a/b/c`）に束ねず、`Descent/Lemma35.lean` の節 a・b・c の `variable` に置き、
命題の仮定は `include` で各定理に入れる（2026-10-08）。節 b・c は Lemma 3.4 と同じく
`[IsRegularLocalRing A]` を使うので、`[IsLocalRing A]` と `λ` は共通の `variable` ではなく節ごとに置く
（同じ `Nontrivial A` が二つの経路から来る警告を避けるため）。節 b の `√(z) = m_A` は
`radical_span_eq_maximalIdeal` で `hz'` から出す。

### 12.2' 3.5c の証明と `K₀` の基盤（2026-10-08）

3.5c は `conjSum_eq` に `K' := K₀(T)`、`f := K0.map`（基底変更）、`φ ψ := ` 3.5a で得た
`χ_T`、`χ_C` の準同型を入れ、`φ ∘ f = ψ ∘ f` を 3.5b と `K0.hom_ext` で、不変元の条件を
`theorem_3_1_K0`（Theorem 3.1 の帰結、`Inputs/Descent.lean`、`sorry` つきの定理）で与えて証明した。
`G` の `K₀(T)` への作用は `g • x := (g⁻¹)^* x`（ひねりは反変なので逆元で左作用にする）。
そのために `K0.lean` に足したもの：`mk_eq_of_homotopyEquiv`、`mk_cone`、`lift`（任意のアーベル群へ）、
`hom_ext`、`IsPerfectSupported.of_iso`、台つき完全複体が基底変更・ひねりで保たれること、
`K0.map`、`K0.twistHom`、`twistOneIso`・`twistMulIso`（`restrictScalarsId'App`・
`restrictScalarsComp'App` の各項の同型）、`instDistribMulAction`。

`theorem_3_1_K0` は (3.2) の整数版：「`G` 不変な `y ∈ K₀(T)` には `n > 0`、`x ∈ K₀(A)` があって
`n • y = K0.map x`」。`⊗ ℚ` を扱わない。設定は論文より狭く、`A` は Noether 局所環で剰余標数 `p`、
`z` はパラメータ系（`√(z) = m_A ∋ p`）。

`free_baseChange`、`finite_baseChange`、`free_twist`、`finite_twist`（基底変更・環自己同型に沿った
係数制限が有限自由加群を保つ）は 2026-10-08 に証明済み（ひねりは恒等写像を `g⁻¹` 半線形同型と
みて `Module.Free.of_equiv`、`Module.Finite.of_surjective`）。

`conjSum_eq` の「全射性」は `K_ℚ → (K'_ℚ)^G` の全射の整数版（`G` 不変な `y` に `n > 0`、`x` があって
`n • y = f x`）で書いた。(3.2) からこの形が出るので、`⊗ ℚ` を扱わずに済む。

### 12.3 証明に向けて要るもの

- 3.5a：Koszul 複体の分裂 (3.12)（`z_j^v • 𝟙 P` の零ホモトピーで錐を分解）、二重複体の
  ホモロジーの長さの評価（スペクトル系列の代わりに有限フィルトレーションの長さの加法性）、
  `K₀` の関係式を `χ` が保つこと（ホモトピー不変性、錐の三角の長完全列）。
- 3.5b：論文は hyper-Tor の議論（λ 側は Lemma 3.4、通常側は `T` の有限自由 `A` 分解と交代ランク）。
  形式化では `K₀^{m_A}(A)` が `[K(z)]` で生成されることを使う方針に変えた（§12.5）。
- 3.5c：`Inputs.Descent`（Theorem 3.1 の `K₀` レベルの帰結）、`K0.map`、`G` の `K₀` への作用、
  3.5b を `K0.lift` で `K₀(A)` 上の準同型の一致に直すこと、`conjSum_eq`。
- `isPerfectSupported_twist`（ひねりが台つき完全複体を保つ）：係数制限による有限自由性の移送。


### 12.4 Lemma 3.5a の通常長さ側（2026-10-08）

通常側と正規化長さ側を独立した課題に分けた。

- `OrdinaryEuler.lean`：`T` は Noether 可換環、`w : Fin e → T`、
  `T/(w)` は Artin 環という一般設定。`IsSupported` の零ホモトピーから
  `(w) ≤ radical(Ann H^i(P))` を導き、有限生成ホモロジーの有限長性を証明。
  `chiOrd_eq_of_homotopyEquiv`、写像錐の長完全列による `chiOrd_cone`、
  `K0.lift` による `chiOrdHom` と類の上での評価式も証明した。
- `Descent/OrdinaryLength.lean`：`A` は Noether 局所環、`T` は `A` 上有限、
  `√(z) = m_A` から、`T` の Noether 性と `T/(zT)` の Artin 性を出して一般定理を適用。
  `lemma_3_5a_ord` は `C`、`λ`、`T` の局所性を要求しない。
- `Descent/Lemma35.lean`：正規化長さ側だけを `lemma_3_5a_lam`（未証明）に分離し、
  `lemma_3_5a` は両者をまとめる証明とした。

通常側の証明は Koszul 分裂、Lemma 3.4、Theorem 3.1 を使わない。
`lake build` は成功。一般設定の有限長性、`chiOrd_cone`、`chiOrdHom`、
`lemma_3_5a_ord` の `#print axioms` は `propext`、`Classical.choice`、`Quot.sound` のみ。

### 12.5 Lemma 3.5b の証明計画（2026-10-08）

**論文の議論と変更点**：論文は超 Tor スペクトル系列で `χ(Q ⊗ T)` を `H_j(Q)` の Tor に分解し、
λ 側は Lemma 3.4、通常側は `T` の有限自由 `A` 分解（交代ランク `= r`）で計算する。
Mathlib には超 Tor スペクトル系列も「正則局所環の大域次元は有限」もないので、次の方針に変える。

**方針**：`K₀^{m_A}(A)` は Koszul 複体の類 `[K(z)]` で生成される（台つき完全 `A` 複体 `Q` に
整数 `n` があって `[Q] = n · [K(z)]`）。`Q ↦ χ_T(Q ⊗ T)`、`Q ↦ χ_C(Q ⊗ T)`、`Q ↦ r · χ_A(Q)` は
どれも `K₀^{m_A}(A)` 上の準同型（3.5a を `T` と `A` に適用）なので、`K(z)` での値が `r` で
一致すれば足りる。λ 側では Lemma 3.4 を使わない（`V = k` の場合が `hkz`、`hq` そのもの）。

**主張の分割**：二つの等式は独立に示せるので分けた（`Descent/Lemma35.lean`）。

| 主張 | 内容 | 使う仮定 |
| --- | --- | --- |
| `lemma_3_5b_ord` | `χ_T(Q ⊗_A T) = r · χ_A(Q)` | `A` 正則、`hz'`、`hdim`、`T` 有限・局所、`hres` |
| `lemma_3_5b_lam` | `χ_C(Q ⊗_A T) = r · χ_A(Q)` | `A` 正則、`hz'`、`hdim`、`T` 有限、`hkz`、`hq`、`hfin` |
| `lemma_3_5b` | 二つを並べたもの（証明済み） | 両方 |

共通部分は「生成」（下の段階 1〜5）と `χ_A(K(z)) = 1` だけ。

**生成の証明（デヴィサージュ）**：`Q` の項が 0 でない最高次数を `t` とし、ホモロジーの長さの
総和と幅について帰納法。

- `H^t(Q) ≠ 0`：`H^t(Q) ↠ k` を選び、`Q → k[-t]` を Koszul 分解 `K(z)[-t] → k[-t]` に沿って
  持ち上げる（`Q` は有界な射影的複体なので K 射影的、Mathlib の `isKProjective_of_projective`、
  `DerivedCategory.Qh_map_bijective`）。写像錐の長完全列から錐のホモロジーの長さの総和は 1 減る。
  `[Q] = ±[K(z)] - [錐]`。
- `H^t(Q) = 0`：最上段の微分は分裂全射。切り詰め（`truncLE`）で一段短くする。核は有限射影的なので
  局所環上自由。切り詰めは K 射影的な複体の間の擬同型なのでホモトピー同値（`quasiIso_iff`）。
- ホモロジーが 0：非輪状で K 射影的なので可縮、`[Q] = 0`。

**段階**

| 段階 | 内容 | 使う側 |
| --- | --- | --- |
| 1 | 三角形 `X → Y → Z → X[1]` で `a` が `g` と `h` を消すなら `a² • 𝟙_Z ∼ 0`。錐と `K(z)` の台 | 共通 |
| 2 | `K(z)` は台つき完全複体。`K₀` の零複体・シフトの補題 | 共通 |
| 3 | K 射影性による持ち上げと、錐のホモロジーの長さの計算 | 共通 |
| 4 | 最上段の切り詰め（分裂、射影的なら自由、ホモトピー同値） | 共通 |
| 5 | 生成：`∀ Q, ∃ n : ℤ, K0.mk Q = n • K0.mk K(z)` | 共通 |
| 6a | `χ_A(K(z)) = 1`（A1 に依存） | 共通 |
| 6b | `χ_C(K(z) ⊗ T) = r`（`baseChangeKoszulIso`、`hkz`、`hq`、`H_0 ≅ C/(z)`） | λ 側 |
| 7a | Koszul Euler 標数 `χ(z; T) = rank_A T`（`A` 正則）。層 3a の入力として `sorry` で置く | 通常側 |
| 7b | 剰余体が同じ局所環 `T` 上の有限長加群で `length_T = length_A` | 通常側 |
| 8 | `lemma_3_5b_ord`、`lemma_3_5b_lam` の組み立て | 各側 |

7a の証明は別トラック（正則 ⇒ 有限大域次元、`K(z) ⊗ L` の二重複体、交代ランク = 生成ランク）。

### 12.6 Lemma 3.5b の証明の実装（2026-10-08）

§12.5 の方針で `Descent/Lemma35b/` に実装した。`lake build` は成功。

| ファイル | 内容 | 段階 |
| --- | --- | --- |
| `Support.lean` | 台の条件をホモトピー圏の等式 `z_j^v • 𝟙 = 0` に言い換え。三角形の補題（`a` が `g` の前と `h` の後ろで消えれば `a² • 𝟙_Z = 0`）、写像錐・シフト・ホモトピー同値での保存、`K(x)` は `x` に台をもつ | 1 |
| `K0Basic.lean` | 台つき完全複体が写像錐・シフトで保たれること、`K₀` で零複体・可縮な複体の類は `0`、`[P⟦n⟧] = (-1)^n [P]`、`K(x)` は台つき完全複体（`koszulPerfSupp`） | 2 |
| `Lift.lean` | `H^0(L) → M` から鎖写像 `L → M[0]`（`toSingleOfHomology`）、K 射影的な複体からの擬同型に沿った持ち上げ（`exists_lift_of_quasiIso`、Mathlib の `Qh_map_bijective`） | 3 |
| `ConeLength.lean` | ホモロジーの長さの総和 `homologyLengthSum`、シフト・ホモトピー同値での不変性、`f : Q → K` が `H^0` で全射なら錐の総和が 1 減る | 3 |
| `Truncate.lean` | 最上段の切り詰め：`H^0(Q) = 0` なら `τ^{≤-1}Q` とホモトピー同値（分裂全射の核は局所環上自由、K 射影的な複体の間の擬同型はホモトピー同値） | 4 |
| `Generation.lean` | **共通の入力**：`K0.exists_eq_zsmul_koszul`（`[Q] = m · [K(z)]`）、`K0.hom_ext_koszul`、`chiOrd_koszulComplex`（`χ_A(K(z)) = 1`） | 5, 6a |
| `Normalized.lean` | `chiLam_baseChange_koszulComplex`（`χ_C(K(z) ⊗ T) = λ(C/zC)`）と `lemma_3_5b_lam_of_koszul` | 6b, 8 |
| `Ordinary.lean` | `length_eq_of_residue_surjective`（剰余体が同じなら `length_A = length_T`）、`chiOrd_baseChange_koszulComplex`、`lemma_3_5b_ord_of_koszul` | 7b, 8 |

生成の定理は `[IsLocalRing A] [IsNoetherianRing A]`、`z` が `m_A` を生成すること、`IsKoszulResolution z` の
もとで述べ、正則性は使わない。`Descent/Lemma35.lean` の `lemma_3_5b_ord`、`lemma_3_5b_lam` は、
`IsKoszulResolution z` を A1 から（`isKoszulResolution_of_regular`）、`χ^A(z; T) = r` を層 3a の入力
`koszulEulerChar_eq_finrank`（`Inputs/RegularLocalRing.lean`、7a）から与えてこれらを適用する。

`#print axioms`：生成（`K0.exists_eq_zsmul_koszul`、`K0.hom_ext_koszul`）、`chiOrd_koszulComplex`、
`length_eq_of_residue_surjective`、生成元での値の計算、`lemma_3_5b_ord_of_koszul` は標準公理のみ
（`K0.lean` の四つの小補題を埋めた後）。`lemma_3_5b_lam_of_koszul` に残る `sorry` は
`lemma_3_5a_lam_finite`（3.5a の λ 側の Koszul 有限性、`Descent/NormalizedLength.lean`）だけ。
`lemma_3_5b_ord`、`lemma_3_5b_lam` にはさらに A1 と 7a の入力（`koszulEulerChar_eq_finrank`、
可換環論の古典的な定理として当面 `sorry` のまま）が加わる。

## 13. ディレクトリ構成の整理（2026-10-08）

一般論と論文の補題を分けた。

- `HomologicalAlgebra/`：ホモロジー代数の一般論（任意の可換環、またはアーベル圏）。
- `CommutativeAlgebra/`：可換環論の一般論（局所環、Koszul 複体、長さ）。
- `PerfectComplex/`：台つき完全複体・`K₀`・正規化長さ・Euler 評価（このプロジェクトの道具の一般論）。
- `Paper/`：論文の補題（`Lemma3_4`、`Lemma3_5` と `Lemma3_5/A_*`・`B_*`・`C_*`）。
- `Inputs/`、`Core/`、`Statement.lean`、`EulerChar.lean` はそのまま。

層の依存は `HomologicalAlgebra` ← `CommutativeAlgebra` ← `PerfectComplex` ← `Paper` の向きだけ。
そのために次を切り出した：`smulId` と `Cone(a • 𝟙 K)` の長完全列（`KoszulExact` から
`HomologicalAlgebra/ConeSmul`）、`baseChange` とスカラー倍の補題（`Perfect`・`KoszulBaseChange` から
`HomologicalAlgebra/BaseChange`）、三角形の補題（`Support` から `HomologicalAlgebra/TriangleSmul`）、
項の自由性（`K0Basic` から `HomologicalAlgebra/FreeTerms`）、剰余体が同じときの長さの比較
（3.5b の普通の側から `CommutativeAlgebra/LengthComparison`、定理名は `length_eq_of_common_residueField`）。

旧パスには新しいモジュールを再エクスポートするだけの互換用ファイルを置いていたが、作業中のファイルの
移行が終わったので 2026-10-09 に削除した（§14）。

| 旧パス | 新パス |
| --- | --- |
| `ConeLES.lean` | `HomologicalAlgebra/ConeLES.lean` |
| `ToChain.lean` | `HomologicalAlgebra/ToChain.lean` |
| `ResolutionOfCochain.lean` | `HomologicalAlgebra/ResolutionOfCochain.lean` |
| `ExtendResolution.lean` | `HomologicalAlgebra/ExtendResolution.lean` |
| `Tor.lean` | `HomologicalAlgebra/Tor.lean` |
| `TorCochain.lean` | `HomologicalAlgebra/TorCochain.lean` |
| `Descent/TorLES.lean` | `HomologicalAlgebra/TorLES.lean` |
| `Descent/ConeResolution.lean` | `HomologicalAlgebra/ConeResolution.lean` |
| `Descent/TorTorsion.lean` | `HomologicalAlgebra/TorTorsion.lean` |
| `Descent/Lemma35b/Lift.lean` | `HomologicalAlgebra/KProjectiveLift.lean` |
| `Descent/Lemma35b/ConeLength.lean` | `HomologicalAlgebra/ConeLength.lean` |
| `Descent/Lemma35b/Truncate.lean` | `HomologicalAlgebra/Truncate.lean` |
| `FiniteLength.lean` | `CommutativeAlgebra/FiniteLength.lean` |
| `Multiplicity.lean` | `CommutativeAlgebra/Multiplicity.lean` |
| `GeometricFiber.lean` | `CommutativeAlgebra/GeometricFiber.lean` |
| `Koszul.lean` | `CommutativeAlgebra/Koszul.lean` |
| `KoszulExact.lean` | `CommutativeAlgebra/KoszulExact.lean` |
| `KoszulResolution.lean` | `CommutativeAlgebra/KoszulResolution.lean` |
| `KoszulBaseChange.lean` | `CommutativeAlgebra/KoszulBaseChange.lean` |
| `TorKoszul.lean` | `CommutativeAlgebra/TorKoszul.lean` |
| `Perfect.lean` | `PerfectComplex/Basic.lean` |
| `NormalizedLength.lean` | `PerfectComplex/NormalizedLength.lean` |
| `K0.lean` | `PerfectComplex/K0.lean` |
| `Descent/Lemma35b/K0Basic.lean` | `PerfectComplex/K0Basic.lean` |
| `Descent/Lemma35b/Support.lean` | `PerfectComplex/Support.lean` |
| `OrdinaryEuler.lean` | `PerfectComplex/OrdinaryEuler.lean` |
| `NormalizedEuler.lean` | `PerfectComplex/NormalizedEuler.lean` |
| `Descent/Lemma35b/Generation.lean` | `PerfectComplex/KoszulGeneration.lean` |
| `Descent/Lemma34Abstract.lean` | `Paper/Lemma3_4/Abstract.lean` |
| `Descent/Lemma34.lean` | `Paper/Lemma3_4.lean` |
| `Descent/OrdinaryLength.lean` | `Paper/Lemma3_5/A_Ordinary.lean` |
| `Descent/NormalizedLength.lean` | `Paper/Lemma3_5/A_Normalized.lean` |
| `Descent/Lemma35b/Ordinary.lean` | `Paper/Lemma3_5/B_Ordinary.lean` |
| `Descent/Lemma35b/Normalized.lean` | `Paper/Lemma3_5/B_Normalized.lean` |
| `Descent/ConjugateSum.lean` | `Paper/Lemma3_5/C_ConjugateSum.lean` |
| `Descent/Lemma35.lean` | `Paper/Lemma3_5.lean` |

## 14. `PerfectComplex/` のリファクタ（2026-10-09）

§13 の再編のあと、`PerfectComplex/` の重複と層の混在を整理した。定理名・定義名は原則変えず、
移動とファイル分割だけにした。各段階で `lake build` と、`lemma_3_5`・`CoreData.firstComparison` などの
`#print axioms` が変わらないことを確認した（`sorry` の集合は不変）。

### 14.1 通常の長さは正規化長さの特別な場合

`OrdinaryEuler.lean` と `NormalizedEuler.lean` にあった、ホモトピー不変性と写像錐での加法性の
証明（`chiOrd_cone` と `lambdaEuler_cone` など約 130 行）が `Module.length` と `lam.len` の違いを除いて
同一だった。`NormalizedLength.ordinary T : NormalizedLength T ⊥`（`ℕ∞` を `ℝ≥0∞` に埋め込んだ
`Module.length`）を定義し、`IsPowTorsion ⊥ M` がどの `M` でも成り立つこと（`IsPowTorsion.bot`）を使って、
通常の長さ側の定理を `lambdaEuler` 側の系として導く（`chiOrd_eq_lambdaEuler_ordinary`）。
依存の向きは `NormalizedEuler ← OrdinaryEuler` に反転した。

### 14.2 層の規律に合わせた移動

`HomologicalAlgebra ← CommutativeAlgebra ← PerfectComplex ← Paper` の向きに合わせて次を移した。

| 移したもの | 移動先 |
| --- | --- |
| `IsPowTorsion` とその補題、`IsPowTorsion.of_pow_le` | `CommutativeAlgebra/PowTorsion.lean`（新規） |
| `lambdaChi`（`Tor` による Euler 標数） | `PerfectComplex/NormalizedEuler.lean`（`NormalizedLength.lean` は `Tor` を import しなくなった） |
| `isArtinianRing_quotient_of_le_radical`、`isFiniteLength_of_le_radical_annihilator`、`isArtinianRing_quotient_span_of_eq`、`isSimpleModule_quotient_span_of_eq`、`exists_surjective_quotient_span` | `CommutativeAlgebra/FiniteLength.lean` |
| `homology_moduleFinite` | `HomologicalAlgebra/FreeTerms.lean` |
| `koszulComplex_isZero_X_of_lt`、`koszulComplex_free_finite_X` | `CommutativeAlgebra/KoszulExact.lean` |
| `koszulH0Iso`、`koszulAugmentation`、`quasiIso_koszulAugmentation`、`koszulComplex_d_zero_one` | `CommutativeAlgebra/KoszulResolution.lean` |
| `baseChange_bounded` | `HomologicalAlgebra/BaseChange.lean` |
| `IsSupported.le_radical_annihilator`、`isSupported_baseChange`、`isSupported_twist` | `PerfectComplex/Support.lean` |
| `supported_homology_isPowTorsion`、`chiLam_homology_isPowTorsion`、`chiLam_eq_of_homotopyEquiv`、`chiLam_cone_of_finite`、`chiLamHom_of_finite`（`Paper/Lemma3_5/A_Normalized.lean` にあった一般論） | `PerfectComplex/NormalizedEuler.lean` |

### 14.3 `PerfectComplex/` の構成（依存順）

| ファイル | 内容 |
| --- | --- |
| `NormalizedLength.lean` | 正規化長さの構造体と基本補題、`restrict`、`ordinary` |
| `Basic.lean` | `IsSupported`、`IsPerfectSupported`、`PerfSupp`、`chiOrd`、`chiLam`、`twist` |
| `Support.lean` | `IsSupported` の閉包性（ホモトピー同値・シフト・錐・基底変更・ひねり・Koszul）、ホモロジーの零化 |
| `Closure.lean` | `IsPerfectSupported` の閉包性（同型・錐・シフト・零複体・基底変更・ひねり）、`koszulPerfSupp` |
| `K0.lean` | `K0Supported` の定義、`mk`・`lift`・`hom_ext`、零複体・シフトの関係式 |
| `K0Functor.lean` | `K0.map`、`K0.twistHom`、`G` の作用 |
| `NormalizedEuler.lean` | `lambdaEuler`・`lambdaChi`、錐での加法性、`ordinary` との関係、台つき複体への `chiLamHom_of_finite` |
| `OrdinaryEuler.lean` | 台つき完全複体のホモロジーの有限長性、`chiOrdHom` |
| `KoszulGeneration.lean` | `K₀^{m}(A)` が `[K(z)]` で生成されること |

`K0Basic.lean` は `Closure.lean` と `K0.lean` に分けて廃止した。

### 14.4 `Paper/Lemma3_5` のインターフェース

`∃ χ, ∀ P, χ (K0.mk P) = …` の形で準同型を返していた `lemma_3_5a_ord`・`lemma_3_5a_lam`・
`ordinary_euler_of_artinian_quotient` を廃止し、準同型そのものを定義した。

- 通常の長さ側：`length_homology_ne_top_of_radical`（有限性）、`chiOrdHom_of_radical`（準同型）と
  `chiOrdHom_of_radical_mk`（`Paper/Lemma3_5/A_Ordinary.lean`）。
- 正規化長さ側：`lemma_3_5a_lam_finite`（有限性、唯一の `sorry`、`A_Normalized.lean`）、
  `chiLamHom_of_finite`（準同型）と `chiLamHom_of_finite_mk`（`PerfectComplex/NormalizedEuler.lean`）。

`lemma_3_5a` は論文の形にこれらを並べたもので残した。3.5b・3.5c は準同型を直接使う。

## 15. `HomologicalAlgebra/` のリファクタ（2026-10-09）

§14 と同じ方針（名前は原則変えない、移動とファイル分割だけ、各段階で `lake build` と `#print axioms` を確認）。

### 15.1 重複の解消

- `ConeSmul.lean` にあった `Cone(a • 𝟙 K)` の長完全列（`ConeSmul.cone/δ/S₁₂₃/exact₁₂₃`、約 85 行）は、
  `ConeLES.lean` の一般の射の長完全列 `Cone.*` に `φ = smulId a K` を代入したものと定義まで一致していたので
  削除し、`KoszulExact.lean` では `Cone.exact₃ (smulId a K)` のように使う。`ConeSmul.lean` の残り
  （ホモトピー圏のホモロジー関手との同一視 `e`、短複体の移送補題）は `ConeLES.lean` に吸収し、
  `ConeSmul.H₀`・`ConeSmul.e`・`ConeSmul.e_naturality` は `Cone.H₀`・`Cone.e`・`Cone.e_naturality` に改名した。
- `isZero_homology_of_isZero_X'`（`ModuleCat` 限定）は一般の `isZero_homology_of_isZero_X` に、
  `homologyMap_smul'`（任意の complex shape）は `homologyMap_smul` に統一した（プライムなしが残る）。

### 15.2 新しい `Basic.lean` と依存の正常化

- `HomologicalAlgebra/Basic.lean`（新規）：`isZero_homology_of_isZero_X`、`isZero_of_isZero_X`、
  `projective_of_free`、`smulId`、`homologyMap_smul`、`single_map_smul`。
- `ModuleCat.extendScalars` の加法性のインスタンスと `baseChange_isZero_X_of_pos` は `BaseChange.lean` に置き、
  `Tor.lean` が `BaseChange.lean` を import する向きにした（以前は逆で、インスタンスのためだけに
  `BaseChange` が `Tor` を import していた）。

### 15.3 層の規律に合わせた移動

| 旧 | 新 |
| --- | --- |
| `HomologicalAlgebra/ConeLength.lean` | `CommutativeAlgebra/HomologyLength.lean`（`homologyLengthSum`、`Module.length` を使う） |
| `HomologicalAlgebra/Truncate.lean` | `CommutativeAlgebra/Truncate.lean`（局所環を要求する。`free_finite_ker_of_surjective` もここ） |

どちらも利用者は `PerfectComplex/KoszulGeneration.lean` だけ。

### 15.4 ファイルの統合

`ToChain.lean`・`ResolutionOfCochain.lean`・`ExtendResolution.lean` を `HomologicalAlgebra/Resolution.lean`
に統合した（ℤ 添字 cochain 複体と `ProjectiveResolution` の行き来、という一つの話）。

### 15.5 `HomologicalAlgebra/` の構成（依存順）

| ファイル | 内容 |
| --- | --- |
| `Basic.lean` | 複体についての基本補題、`smulId` |
| `ConeLES.lean` | 写像錐の長完全列 `Cone.exact₁₂₃`、ホモトピー圏のホモロジー関手との同一視 |
| `TriangleSmul.lean` | 完全三角形で `a² • 𝟙 = 0`、`homotopyQuot` |
| `FreeTerms.lean` | 項の有限自由性、`homology_moduleFinite` |
| `Resolution.lean` | `toChain`、`IsResolutionOf`、`extRes`、`extLift` |
| `BaseChange.lean` | `baseChange`、係数拡大とスカラー倍 |
| `Tor.lean` | `TorModule`、`torLength`、`TorAlg` |
| `TorCochain.lean` | `torIsoCochain` |
| `ConeResolution.lean` | 持ち上げの錐は余核の分解 |
| `TorLES.lean` | Tor の長完全列 |
| `TorTorsion.lean` | Tor の消去イデアル |
| `KProjectiveLift.lean` | `toSingleOfHomology`、`exists_lift_of_quasiIso` |

`torAlg_longExact` の `∃ α β δ, …` の形は残した。利用者（Lemma 3.4 の抽象形）は長完全列の存在だけを使い、
射の具体形には依存しないため、梱包を解く利点がない。

## 16. `CommutativeAlgebra/` のリファクタ（2026-10-09）

§14・§15 と同じ方針。`CommutativeAlgebra/` の内部には重複がほとんどなく、主な作業は
`Inputs/`・`IntersectionMultiplicity/` に散っていた一般論の引き上げだった。

### 16.1 Koszul 複体の定義ファイルへの集約

`koszulComplex_zero/succ`、`koszulComplex_isZero_X_of_pos/lt`、`koszulComplex_free_finite_X`、
`koszulComplex_isZero_homology_of_pos`（KoszulExact から）と `koszulComplex_projective_X`
（KoszulResolution から。`projective_of_free (koszulComplex_free_finite_X x i).1` の 1 行に簡略化）を
`Koszul.lean` に集めた。KoszulExact は完全性だけ、KoszulResolution は分解だけになった。
`koszulEulerChar` は定義であって入力ではないので、`Inputs/RegularLocalRing.lean` から `Koszul.lean` へ移した。
どこからも使われていない `koszulComplexCoeff`・`koszulHomology` は削除した
（係数つき Koszul ホモロジーは `koszulHomologySelf (φ ∘ z)` で書く）。

### 16.2 `sorry` の入力の置き換え

`Inputs/RegularLocalRing.lean` の `exists_pow_maximalIdeal_le_map`（`sorry`）と同じ主張が、Lemma 5.2 の
作業で `IntersectionMultiplicity/LocalAlgebra.lean` に `maximalIdeal_pow_le_map_of_finite` として
証明されていた。後者を `CommutativeAlgebra/LocalAlgebra.lean`（新規）に移し、前者を削除して
`Paper/Lemma3_4.lean` と `Inputs/LengthAlgebra.lean` の利用箇所を置き換えた。`sorry` は 8 → 7。

### 16.3 `IntersectionMultiplicity/` からの引き上げ

| 移したもの | 移動先 |
| --- | --- |
| `quotient_action_annihilator`、`annihilator_le_quotient`、`residueFieldEquiv_of_surjective`、`maximalIdeal_pow_le_map_of_finite` | `CommutativeAlgebra/LocalAlgebra.lean` |
| `finiteLength_of_restrictScalars`、`length_eq_of_semilinear_bijective`、`length_restrictScalars_equiv` | `CommutativeAlgebra/LengthComparison.lean` |
| `chiOrd_restrictScalars_equiv`、`chiOrd_twist` | `PerfectComplex/OrdinaryEuler.lean` |

`IntersectionMultiplicity/LocalAlgebra.lean`・`LengthComparison.lean`・`TwistEvaluation.lean` は廃止。
`length_restrictScalars_eq_of_residue_surjective` は `length_restrictScalars_eq` の薄い包み（有限長の仮定が未使用）
だったので削除し、その結果 `chiOrd_baseChange_resolution` から `λ(T ⊗ M) < ∞` の仮定が不要になった。
`IntersectionMultiplicity/` に残るのは Lemma 5.2 固有の `FiniteExtension`・`OrdinaryEvaluation`・
`ResolutionEvaluation` の 3 ファイル。

### 16.4 `CommutativeAlgebra/` の構成

| ファイル | 内容 |
| --- | --- |
| `PowTorsion.lean` | イデアルの冪で消える加群 |
| `FiniteLength.lean` | 有限長（Noether 環上、局所環上、`m` を生成する列） |
| `LocalAlgebra.lean` | 局所環上の有限代数（零化イデアル、剰余体の同型、`m_T^n ≤ m_R T`） |
| `LengthComparison.lean` | 剰余体が同じときの長さ、係数制限・半線形同型と長さ |
| `Multiplicity.lean` | パラメータ系、Hilbert–Samuel 重複度 |
| `GeometricFiber.lean` | 幾何ファイバーでの推移性 |
| `Koszul.lean` | Koszul 複体の定義、項の性質、`koszulEulerChar` |
| `KoszulExact.lean` | 正則列の Koszul 複体の完全性 |
| `KoszulResolution.lean` | Koszul 複体を射影分解に、添加写像 |
| `KoszulBaseChange.lean` | 基底変更との両立 |
| `TorKoszul.lean` | `Tor` と Koszul ホモロジー |
| `HomologyLength.lean` | ホモロジーの長さの総和（デヴィサージュ） |
| `Truncate.lean` | 最上段の切り詰め |

## 17. `Support/` の解体（2026-10-10）

`Support/` の 3 ファイルは、一般定理（ホモロジーの台から零ホモトピーへ）と Lemma 5.2 固有の 1 定理の同居だった。
中身を層に合わせて移し、ディレクトリを廃止した。定理名は変えていない（消えたのは `SupportBridge.quot` だけ）。

| 旧 | 新 |
| --- | --- |
| `Support/NullHomotopy.lean` の `clear_degree`、`exists_pow_nullHomotopy_of_homology_annihilated` | `HomologicalAlgebra/NullHomotopy.lean`（`SupportBridge.quot` は `homotopyQuot` に統一） |
| `Support/PerfectComplex.lean` の `HasHomologySupport` と補題、`Support/NullHomotopy.lean` の `isSupported_of_homologySupport`・`isSupported_iff_homologySupport`・`isPerfectSupported_of_homologySupport` | `PerfectComplex/HomologySupport.lean` |
| `Support/Resolution.lean` と `IntersectionMultiplicity/OrdinaryEvaluation.lean` | `IntersectionMultiplicity/BaseChangeResolution.lean`（分解の基底変更についての 2 定理） |

「`J` が有限生成で `J ≤ √(Ann M)` なら `J` の冪が `M` を消す」という共通部分は
`IsPowTorsion.of_le_radical_annihilator`（`CommutativeAlgebra/PowTorsion.lean`）にし、
`homology_pow_torsion_of_support` と `supported_homology_isPowTorsion` の両方がそれを使う。

`IntersectionMultiplicity/` に残るのは `FiniteExtension`・`BaseChangeResolution`・`ResolutionEvaluation` の 3 ファイル。

## 18. 説明コメント（docstring）の書き直し（2026-10-10）

全 46 ファイルのモジュール docstring と宣言 docstring を、次の方針で書き直した（コードは変えていない）。
ディレクトリごとに 1 コミット（`HomologicalAlgebra/`、`CommutativeAlgebra/`、`PerfectComplex/`、`Inputs/`、
`IntersectionMultiplicity/`、`Paper/` ×2）。

### 18.1 モジュール docstring

見出しつきで 10〜30 行。

- **概要**：このファイルが何を定義・証明するか、論文のどこに当たるか。
- **背景 / 定義 / 方針 / 証明**：なぜこの形で定義するか、証明の筋道（使う Mathlib の定理、このプロジェクトの
  どの補題に帰着するか）。
- **規約と注意**：添字の向き（cochain の `-i` 次が `H_i`）、junk value（無限長は `0`、`finsum` の規約）、
  ひねりの反変性（`g • [P] = [twist g⁻¹ P]`）、`Tor` は第 2 変数を分解する、など。
- **使われ方**：どのファイル・どの補題から使われるか。残る `sorry` への依存があれば明記する。

### 18.2 宣言 docstring

- 最初の文で主張を日本語で述べる（記号は補助。`λ`、`χ_T`、`K₀^{m}(A)` などは初出で説明する）。
- 仮定の意味（なぜ要るか、何に使うか）を書く。
- 自明でない証明には 1〜3 文で筋道を書く（長完全列のどこを見るか、帰納法の構造、など）。
- 関連する補題・論文の式番号・使われる場所を書く。
- 定義と構造体は「なぜこの形か」を書き、構造体の場には 1〜2 文ずつ付ける。
- 目安：補題 2〜5 文、定義・構造体 3〜8 文。

### 18.3 注意

docstring の変更だけなので定理名・証明は変わらず、`#print axioms` の結果も変わらない。
各ディレクトリの書き換え後に `lake build` で確認した。

## 19. §2 トラック（2026-10-10）

計画と実施記録は `notes/section-2-plan.md`。要点：

- 塔 `Λ`、正規化長さ `λ_∞`、Hilbert–Samuel 重複度を具体的に定義した（`Paper/Section2/Tower.lean`、
  `TowerLength.lean`、`CommutativeAlgebra/HilbertSamuel.lean`）。
- Theorem 2.5（`Section2.theorem_2_5`、`sorry`）は塔の作用との両立を含み、`λ_D` は `λ_∞` の係数制限
  （`towerLengthOn`）として定義する。旧 `Inputs.exists_lengthAlgebra` と極限の式による
  `hilbertSamuelMultiplicity` は削除した。
- Lemma 2.4（`Paper/Section2/Lemma2_4.lean`）と Corollary 2.6 (3)（`cor_2_6_pos`、
  `Section2.cor_2_6_residue_pos`）を証明した。後者は `HilbertSamuel.multiplicity_pos`（`sorry`）に依存。
- 残る `sorry`：引用（Lemma 2.1、2.2、Theorem 2.5、`λ_∞` の加法性・`λ = λ*`・有限段の公式・降下）、
  塔の段の標準事実 8 つ、重複度の定理 3 つ。
