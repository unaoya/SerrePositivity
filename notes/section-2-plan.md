# §2 の形式化計画（Lemma 2.1–2.4、Theorem 2.5、Corollary 2.6）

2026-10-10 作成、同日改訂。対象は論文 §2（p.4–9）。主張の確認と引用元の照合は `section-2.md`。

方針（2026-10-10 の決定）：

- §2 は具体的な対象の話なので、**数学的な定義があるものはその定義で書く**。塔 `Λ`、
  正規化長さ `λ_∞`、Hilbert–Samuel 重複度 `e(I, M)` を抽象化・存在量化で済ませない。
- **Hilbert–Samuel 重複度は定義した上で、必要な性質を主張として書く**（§5）。証明は可換環論の
  一般論として後回しにし、当面 `sorry`（2026-10-10 の決定）。正規化は論文の `e(I, D)` に合わせる。
- 塔 `Λ` と `λ_∞` は一般論に出さず、`Paper/Section2/` に置く（論文固有の対象。§5 の Lemma 5.4 も
  ここから使う）。
- 引用されている深い定理（Cohen–Gabber、Cohen の構造定理、Faltings の正規化長さの加法性、
  Monsky、Roberts、CLMST、Bhatt–Scholze）は `sorry` のままにする。

## 0. 作業の規則（他の作業と重ならないために）

作業ツリーには別の作業の未コミットの変更が多数ある（`git status` で `M` のファイル）。

- **新しいファイルだけを作る。** 既存ファイルは §2 の作業中は編集しない。とくに
  `Inputs/LengthAlgebra.lean`（現在の Theorem 2.5 `Inputs.exists_lengthAlgebra`）、
  `Paper/Corollary2_6.lean`、`PerfectComplex/NormalizedLength.lean`、
  `CommutativeAlgebra/Multiplicity.lean`（現在の junk value つきの `hilbertSamuelMultiplicity`）、
  ルートの `SerrePositivity.lean` は触らない。
- **ビルドはモジュール単位**（`lake build SerrePositivity.CommutativeAlgebra.HilbertSamuel.Function` など）。
  ルートの import には最後の接続段階まで足さない。
- **接続は最後に一度だけ**（§7 段階 D）。別の作業がコミットされてから行う。
- 既存の名前と衝突しない名前を使う。

## 1. 論文 §2 の構造と、形式化での扱い

| 主張 | 内容 | 深い定理 | 扱い |
| --- | --- | --- | --- |
| Lemma 2.1 | 剰余体を代数閉包に延ばす平坦局所拡大 `B → B'`。長さ・次元・正則性・Tor の長さを保つ | Cohen の構造定理 | 主張のみ（`sorry`）。Lemma 5.1（帰着、M1）でしか使わない。優先度最低 |
| Lemma 2.2 | 正規化基底 `A ⊆ D`。`A ≅ k[[t₁..t_h]]`（標数 `p`）または `W(k)[[t₂..t_h]]`（混標数、`t₁ = p`） | Cohen–Gabber、Cohen の構造定理 | 主張のみ（`sorry`）。**`A` の具体形も結論に入れる**（`MvPowerSeries`、`WittVector`） |
| 塔 (2.1) | `A_n = A[t^{1/p^n}]`、`Λ = ⋃ A_n` | — | **具体的に定義**（§2） |
| Lemma 2.3 (a) | `A_n` は完備正則局所、剰余体 `k`、`A_a → A_b` は有限自由でランク `p^{(b−a)h}` | 標準事実 | 主張（`sorry`、層 3a）。定義が具体的なので後で証明できる |
| Lemma 2.3 (b) | `λ_∞`：有限段の公式 (2.2)、下限、上限 (2.3)、加法性 | Faltings / Gabber–Ramero / CLMST | **`λ_∞` を定義**（§3）。加法性と「有限生成加群で `λ = λ*`」は引用（`sorry`） |
| Lemma 2.4 | 長さ 0 の加群の和・直和・有向余極限は長さ 0。増大列の合併で `λ = sup`。`λ(V_a) → 0` なら余極限は長さ 0 | — | **証明**（層 1）。上限の性質と加法性だけから出る |
| Theorem 2.5 | `C_D`：`Λ` と両立する作用をもつ `D` 代数、`λ_D = λ_∞` の制限、(2.4)、(2.5)、(2.6) | Monsky、Roberts、CLMST、Bhatt–Scholze | 主張を書き直す（`sorry`）。塔の作用との両立を入れる。(2.5) は定義した `e` で書く |
| Cor 2.6 (1)(2) | `λ_D Tor_i^A(V, C_D) = 0 (i>0)`、`λ_D(V ⊗ C_D) = r · ℓ(V)` | — | 証明済み（`cor_2_6_tor`、別の作業のファイル）。接続のみ |
| Cor 2.6 (3) | `λ_D(C_D/𝔡C_D) > 0` | — | **証明**（層 1）。`0 < e(H, D)`（§5 で証明）と組成列 |

## 2. 塔の定義（`Paper/Section2/Tower.lean`、新規）

- 段：`TowerStage A t p n := MvPolynomial (Fin h) A ⧸ (X_i^{p^n} − t_i)`。
  `t₁ = p` の混標数でもこの形で正しい（`p` は `A` の元として扱う）。
- 遷移写像 `TowerStage a →ₐ[A] TowerStage b`（`a ≤ b`）：`X_i ↦ X_i^{p^{b−a}}`。
- `Tower A t p := Ring.DirectLimit (TowerStage A t p)`（Mathlib `Algebra/Colimit/Ring.lean`）。
  `Algebra A (Tower)`、`Algebra (TowerStage n) (Tower)`、`IsScalarTower`。

理由：

- 論文は「基底と `p` 冪根を固定して `Λ` を作る」ので `Λ` は `(A, t, p)` から決まる対象。
  抽象的な「性質をみたす `Λ`」で Theorem 2.5 を述べると偽になる（`Λ = A`、`λ_∞ = length_A` が
  反例。証明は Frobenius と `A^{1/q} ≅ A` の同一視、混標数では perfectoid 塔の具体形を使う）。
- 具体的に定義すれば Lemma 2.3 (a) の事実（単項式基底、`A_n/(X) = A/(t) = k`、有限 ⇒ 完備）は
  後で標準的な議論で証明できる。

Lemma 2.3 (a) として同じファイルに置く事実（`sorry`、標準事実）：各段は `A` 上有限自由で
ランク `p^{nh}`、`a ≤ b` で `TowerStage b` は `TowerStage a` 上有限自由でランク `p^{(b−a)h}`、
各段は Noether 局所環で剰余体は `k`、正則、完備。`Tower` は各段の上で平坦（自由加群の有向極限。
Mathlib に直極限の平坦性があるか要確認）。

## 3. 正規化長さ `λ_∞` の定義（`Paper/Section2/TowerLength.lean`、新規）

CLMST Definition 2.2.1（= Faltings）の三段階をそのまま定義にする。`Λ = Tower A t p`、
`s n = p^{nh}`。

- 有限表示の段階 `λ**`：`m_A` 冪ねじれで有限表示な `Λ` 加群 `M` について、段 `n` と有限長
  `A_n` 加群 `V` で `M ≃ Λ ⊗[A_n] V` となるもの全体にわたる `length_{A_n}(V) / s n` の下限
  （`⨅` で定義。該当がなければ `⊤`）。
- 有限生成の段階 `λ*`：有限生成 `N` について、有限表示な全射 `P ↠ N` にわたる `λ**(P)` の下限。
- 一般 `λ_∞(M) := ⨆ (N : Submodule Λ M) (_ : N.FG), λ*(N)`。

性質の扱い：

- 上限 (2.3)：定義から（`λ_∞(M) = ⨆ λ*(N)` の形）。ただし「有限生成 `N` で `λ_∞(N) = λ*(N)`」は
  CLMST Prop. 2.2.3 の本体（Gabber–Ramero 14.5.74）で、**引用（`sorry`）**。
- (2.2) 有限段の公式：「`V` を変えても値が同じ」は平坦性と自由ランクの計算で、Lemma 2.3 (a) から
  出る（後で証明できる）。当面は `sorry` の主張として置く。
- 加法性（`NormalizedLength` の instance）：Faltings Appendix 2 / Gabber–Ramero 14.5.75。
  **引用（`sorry`）**。
- 非負性・零加群で `0`・同型不変：定義から証明する。

これで `λ_∞ : NormalizedLength (Tower) (m_A Tower)` を具体的な `len` で作れる。Lemma 2.4 と
Theorem 2.5 はこの `λ_∞` について述べる。

## 4. 正規化長さの一般論の追加（`PerfectComplex/`、新規ファイル）

既存の `NormalizedLength.lean` は触らず、新しいファイルに足す。

### 4.1 `PerfectComplex/NormalizedLengthComap.lean`：係数制限

環準同型 `f : Λ →+* C` と `lam : NormalizedLength Λ J` から、`C` 加群を `Λ` 加群とみて測る
`lam.comap f J' h : NormalizedLength C J'`。`h : J.map f ≤ J'`。

- `len M := lam.len (M を Module.compHom で Λ 加群とみたもの)`。値は変わらない（`rfl`）。
- 同型不変性：`C` 線形同型は `Λ` 線形同型。加法性：完全列は関数の性質なので同じ。

Theorem 2.5 の「`λ_D = λ_∞` の係数制限」の定義に使う。適用は `J = m_A Λ`、`J' = m_D C`、
`h` は `m_A C ≤ m_D C`（`IsScalarTower A D C` と `m_A → m_D`）。

### 4.2 `PerfectComplex/SupProperty.lean`：上限の性質と Lemma 2.4 の一般形

- `NormalizedLength.HasSup lam : Prop`：`J` 冪ねじれの `M` で
  `lam.len M = ⨆ (N : Submodule) (_ : N.FG), lam.len N`。
- そこから（`J` 冪ねじれの加群について）：`len_iSup_eq_zero`（部分加群の族で各 `len = 0` なら
  和も `0`）、`len_directSum_eq_zero`、`len_iSup_of_directed`（有向な族で `len (⨆ V_i) = ⨆ len V_i`）、
  `len_directLimit_eq_zero_of_tendsto`（`Module.DirectLimit` で `len V_a → 0` なら余極限の
  `len = 0`、遷移写像の単射性は不要）。

### 4.3 `PerfectComplex/QuotientLength.lean`：パラメータ商と剰余商の比較

局所環 `D`、`D` 代数 `C`、`lam : NormalizedLength C (m_D C)`、有限長 `D` 加群 `N` で
`lam.len (C ⊗[D] N) ≤ length_D(N) · lam.len (C ⊗[D] k)`。組成列（`IsFiniteLength` の帰納法）と
テンソルの右完全性（`TensorProduct.rTensor_exact`）、`C ⊗[D] (D/H) ≃ C/HC`
（`TensorProduct.quotientTensorEquiv`）。Cor 2.6 (3) の中身。

## 5. Hilbert–Samuel 重複度：定義と主張（`CommutativeAlgebra/HilbertSamuel.lean`、新規。証明は後回し）

### 5.1 現状と問題

`CommutativeAlgebra/Multiplicity.lean` の `hilbertSamuelMultiplicity I M` は
`Filter.limUnder` の式で、極限の存在・正値性・通常の重複度との一致のどれも証明していない
（極限が存在しなければ既定値になる junk value）。`PLAN.md` §1.5 は「重複度を導入せず (2.5) を
`0 < λ < ∞` に弱める」としていた。どちらも採らず、**定義して証明する**。

### 5.2 定義（標準の定義：Samuel 関数の多項式の最高次係数）

- Samuel 関数 `hsFunction I M n := Module.length D (M ⧸ I^n • M)`（`ℕ∞` 値）。
  `D` Noether、`M` 有限生成、`I` が `M` の台で `m` 準素なら有限（`D/I^n` は Artin）。
- **Hilbert–Samuel の定理**：多項式 `P ∈ ℚ[X]` で `deg P ≤ s`（`s` は `I` の生成元の個数）、
  十分大きい `n` で `hsFunction I M n = P(n)` となるものが一意に存在する。
  `hilbertSamuelPoly I M : ℚ[X]` をこの `P` と定義する（存在定理の `choose`）。
- `hilbertSamuelMultiplicity I M : ℚ := d! · (hilbertSamuelPoly I M).coeff d`、`d = dim M`
  （`Module.supportDim` を自然数に落としたもの。Serre の正規化：`deg P < d` なら `0`）。
  論文の `e((z), D)` は `M = D`、`I = (z)`、`d = h = dim D`。

### 5.3 証明すべき定理

| 定理 | 内容 | Mathlib にある材料 | 規模の目安 |
| --- | --- | --- | --- |
| HS1 有限性 | `I` が `m` 準素、`M` 有限生成なら `hsFunction I M n < ⊤` | `D/I^n` Artin（既存の `isFiniteLength_of_le_radical_annihilator` 相当） | 小 |
| HS2 上界 | `hsFunction I M n ≤ ℓ(M/IM) · C(n+s−1, s)` | 単項式の数え上げ | 小〜中 |
| HS3 Hilbert の定理 | `gr_I(M) = ⊕ I^n M / I^{n+1} M` は `(D/I)[X₁..X_s]` 上有限生成な次数つき加群で、Poincaré 級数 `Σ ℓ(gr_n) X^n` は `p(X)/(1−X)^s`（`p` 多項式）。帰納法：`X_s` 倍の核と余核は変数が一つ少ない環の上の有限生成次数つき加群 | `Polynomial.hilbertPoly`（`p/(1−X)^d` の係数が最終的に多項式、一意性）、`MvPolynomial` の Noether 性、`reesAlgebra` の Noether 性 | **大**。次数つき加群（斉次成分、斉次部分加群、核・余核の次数つき構造、有限生成なら斉次生成元で生成）の基盤が Mathlib にほぼない |
| HS4 Samuel 関数の多項式性 | HS3 から `n ↦ ℓ(M/I^n M)` は `deg ≤ s` の多項式（`Σ_{k<n}` は `1/(1−X)` 倍） | `hilbertPoly`、`invOneSubPow` | 中 |
| HS5 次元の不等式 | `deg (hilbertSamuelPoly I D) ≥ dim D`。素イデアル鎖に沿った帰納法：整域 `D/p₀`、`x ∈ p₁ \ p₀`、Artin–Rees から `χ(D/(p₀,x), n) ≤ χ(D/p₀, n) − χ(D/p₀, n−c)`、`dim D/(p₀, x) ≥ dim D − 1` | Artin–Rees（`Ideal.exists_pow_inf_eq_pow_smul`）、Krull の単項イデアル定理、`ringKrullDim_le_ringKrullDim_quotSMulTop_succ` | **中〜大** |
| HS6 正値性 | パラメータ系 `z`（`s = h = dim D`）で `0 < e((z), D)`。HS4 の `deg ≤ h` と HS5 の `deg ≥ h` から `deg = h`、最高次係数は正 | — | 小（HS4・HS5 の帰結） |
| HS7 整数性（任意） | `e((z), D) ∈ ℕ` | 整数値多項式 | 小〜中 |

Theorem 2.5 の証明（別途判断、段階 E）でさらに要るもの：冪の規則 `e((z^v)) = v^h e((z))`、
ランク公式 `e((t), D) = rank_A D · e((t), A)`、`e((t), A) = 1`（正則パラメータ）、Koszul Euler 標数と
重複度（Stacks 0AZZ）。これらは §2 の主張と Cor 2.6 には不要。

### 5.4 規模の見積もりと位置づけ（証明を後回しにする理由）

- Atiyah–Macdonald 第 11 章（Hilbert 関数、Samuel 関数、次元定理の `dim ≤ d` の向き）に相当する。
  Mathlib にないのは HS3〜HS5 で、とくに HS3 の次数つき加群の基盤が大きい。
- 目安は 2000〜4000 行。現在のプロジェクト全体が約 9500 行なので、独立した小プロジェクトになる。
  Mathlib への寄与候補でもある（`HilbertPoly.lean` の TODO「有限生成次数つき加群の Hilbert
  多項式」がこれ）。
- §2 の主張（Theorem 2.5 の (2.5)）は定義 `hilbertSamuelMultiplicity` だけあれば書ける。
  Cor 2.6 (3) の `sorry` なしの証明には HS6 が要る。

### 5.5 §2 の中での使われ方

- (2.5)：`λ_D(C/(z^v)C) = ENNReal.ofReal ((v : ℝ)^h * e((z), D))`（`e : ℚ` を `ℝ` に埋め込む）。
  「正で有限」は HS6 から出るので Theorem 2.5 の結論には入れない。
- Cor 2.6 (3)：`H = (t)` で `0 < e(H, D) = λ(C/HC) ≤ length(D/H) · λ(C/𝔡C)`（§4.3 と HS6）。
- (5.5)（§5）：`0 < λ(U) = e(I_σ, D') < ∞`。HS6 から。

## 6. Theorem 2.5 の新しい主張（`Paper/Section2/Theorem2_5.lean`、新規、`sorry`）

```
theorem exists_towerLengthAlgebra
    (A D : Type u) [CommRing A] [IsRegularLocalRing A] [IsAdicComplete (maximalIdeal A) A]
    [CommRing D] [IsLocalRing D] [IsNoetherianRing D] [IsDomain D]
    [IsAdicComplete (maximalIdeal D) D] [Algebra A D] [Module.Finite A D] [Algebra.IsSeparable A D]
    (hinj : Function.Injective (algebraMap A D))
    (hres : Function.Surjective ((residue D).comp (algebraMap A D)))
    {h : ℕ} (t : Fin h → A) (hdimA : ringKrullDim A = h) (hdimD : ringKrullDim D = h) (hpos : 0 < h)
    (ht : Ideal.span (Set.range t) = maximalIdeal A) (hsop : IsSystemOfParameters D (algebraMap A D ∘ t))
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField D) p] [PerfectField (ResidueField D)] :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra D C) (_ : Algebra (Tower A t p) C)
      (_ : IsScalarTower A D C) (_ : IsScalarTower A (Tower A t p) C),
      let lam := (towerLength A t p).comap (algebraMap (Tower A t p) C) (m_D C) (…m_A C ≤ m_D C…)
      -- (2.4)
      (∀ (z : Fin h → D), IsSystemOfParameters D z → ∀ v, 0 < v → ∀ i, 0 < i →
        lam.len (koszulHomologySelf (fun j ↦ algebraMap D C (z j ^ v)) i) = 0) ∧
      -- (2.5)
      (∀ (z : Fin h → D), IsSystemOfParameters D z → ∀ v, 0 < v →
        lam.len (C ⧸ Ideal.span (Set.range fun j ↦ algebraMap D C (z j ^ v))) =
          ENNReal.ofReal ((v : ℝ) ^ h * hilbertSamuelMultiplicity (Ideal.span (Set.range z)) D)) ∧
      -- (2.6)
      (∀ v, 0 < v →
        lam.len (C ⧸ Ideal.span (Set.range fun j ↦ algebraMap D C (algebraMap A D (t j) ^ v))) =
          ((v ^ h * Module.finrank A D : ℕ) : ℝ≥0∞))
```

- `λ_∞` は §3 で定義した `towerLength A t p` そのもの（仮定ではなく定義）。
- **塔の作用との両立**は `[Algebra (Tower) C]`、`[IsScalarTower A (Tower) C]`、
  `[IsScalarTower A D C]`。`C` は可換なので `Λ` と `D` の作用は自動的に可換。
  `λ_D` を `λ_∞` の係数制限（`comap`）で**定義**するので、「`λ_D = λ_∞`」と
  「Lemma 2.3 の有限段・下限・上限の性質は塔の加群の上で使える」は定義から従う。
  Lemma 5.4 が使うのはこの形（`S = Λ ⊗_A (D'/I_σ)` 加群の上で `λ_∞` を使う）。
- 既存の `Inputs.exists_lengthAlgebra` との差：`Tower` の作用、`λ_D` の定義、(2.5) の `e` が
  定義されたもの、正値性の結論が不要になること。接続段階で置き換える。

## 7. 作業の順序と完了条件

### 段階 A：正規化長さの一般論（層 1、`sorry` なし）

1. `PerfectComplex/NormalizedLengthComap.lean`（§4.1）。
2. `PerfectComplex/SupProperty.lean`（§4.2）。Lemma 2.4 の一般形。
3. `PerfectComplex/QuotientLength.lean`（§4.3）。

### 段階 H：Hilbert–Samuel 重複度（§5）

4. `CommutativeAlgebra/HilbertSamuel.lean`：Samuel 関数、多項式性 `IsSamuelPoly`、
   `HilbertSamuel.poly`、`HilbertSamuel.multiplicity` の定義と、HS1〜HS6 の主張（`sorry`）。
   証明は後回し（可換環論の一般論として別トラック）。

### 段階 B：塔・`λ_∞`・主張

8. `Paper/Section2/Tower.lean`（§2）：定義と instance、Lemma 2.3 (a) の主張（`sorry`）。
9. `Paper/Section2/TowerLength.lean`：`λ_∞` の定義（§3）と、定義から出る性質の証明。加法性・
   有限生成加群での一致・有限段の公式・降下は引用（`sorry`）。`NormalizedLength` の instance。
10. `Paper/Section2/Lemma2_2.lean`：Lemma 2.2（具体形つき）を `sorry` で。
11. `Paper/Section2/Theorem2_5.lean`：Theorem 2.5（§6）を `sorry` で。段階 H の定義に依存。
12. `Paper/Section2/Lemma2_1.lean`：Lemma 2.1 を `sorry` で（優先度最低）。

### 段階 C：論文の補題（`Paper/Section2/`）

14. `Paper/Section2/Lemma2_4.lean`：段階 A の一般形を `λ_∞` に適用した論文の形。
15. `Paper/Section2/Corollary2_6.lean`：(3) を §4.3 と HS6 と Theorem 2.5 の (2.5) から証明
    （新しい名前）。(1)(2) は既存の `cor_2_6_tor` を接続段階で指す。

### 段階 D：接続（別の作業のコミット後）

16. `Inputs/LengthAlgebra.lean` の `exists_lengthAlgebra` を `exists_towerLengthAlgebra` に、
    `CommutativeAlgebra/Multiplicity.lean` の `hilbertSamuelMultiplicity` を段階 H の定義に
    置き換え、`Paper/Corollary2_6.lean` の `cor_2_6_pos` を段階 C で埋める。利用側（`Lemma5_2`、
    `Section5/*`）の引数は、正値性の仮定 `hmult` が不要になる以外は変えない。
17. ルートの import、README、`PLAN.md`（§1.5 の方針の変更、§2 トラックの記録）。
18. 全体ビルドと `#print axioms`。

### 段階 E（別途判断）：Theorem 2.5 の証明

標数 `p` の証明は [21] §3.2 の議論（トレースの分母 (2.7)、Hilbert–Kunz 極限 (2.8)、Roberts、
Koszul Euler 標数、Lemma 2.4）を、Monsky・Roberts・Stacks 0AZZ を `sorry` にして形式化する
もので、`C_D = D_perf` の構成から始める大きな作業。混標数は CLMST の結果がほぼ Theorem 2.5
そのものなので、入力として置く以外にない。段階 A〜D が終わってから判断する。

## 8. 決定（2026-10-10）

- 段階 H は定義と主張のみ（`sorry`）。証明は可換環論の一般論として後回し。
- 正規化は論文の `e(I, D)`（`M = D`、`d = dim D`）に合わせる。一般の `M` でも `d = dim M`。
- Lemma 2.2 の結論に `A` の具体形を入れる。
- 塔・`λ_∞` は `Paper/Section2/` に置く。引用する結果は `sorry` でよい。

## 9. 要確認（実装時）

- Mathlib の `Ring.DirectLimit` の API（`of`、`exists_of`、`Algebra` instance）。
- `Module.FinitePresentation` の正確な名前と場所。
- 直極限の平坦性の有無。なければ Lemma 2.3 (a) の平坦性は `sorry`。
- `TensorProduct.quotientTensorEquiv` の形と `C ⊗[D] (D ⧸ H) ≃ C ⧸ H C` への変換。
- `IsPowTorsion` の現在の場所（`CommutativeAlgebra/PowTorsion.lean` の可能性）。
- 次数つき加群の表現：`DirectSum` と `MvPolynomial` の作用を自前で組むか、Mathlib の
  `GradedModule`（`Algebra/DirectSum/...`）が使えるか。HS3 の最初に決める。

## 10. 実施記録（2026-10-10）

段階 A・H（定義と主張）・B・C を実装した。新しいファイルだけを作り、既存ファイルは触っていない。
ルートの `SerrePositivity.lean` にもまだ足していない（段階 D）。各モジュールは単体でビルドでき、
全体の `lake build` も通る。

| ファイル | 内容 | `sorry` |
| --- | --- | --- |
| `PerfectComplex/NormalizedLengthComap.lean` | 係数制限 `NormalizedLength.comap`、`IsPowTorsion.comap` | なし |
| `PerfectComplex/SupProperty.lean` | `HasSup`、有限和の評価、和・直和・有向族・直極限の長さ `0`（Lemma 2.4 の一般形） | なし |
| `PerfectComplex/QuotientLength.lean` | `λ(C ⊗ N) ≤ ℓ(N) · λ(C ⊗ k)`、`λ(C/HC) ≤ ℓ(D/H) · λ(C/𝔡C)`、正値性の移送 | なし |
| `CommutativeAlgebra/HilbertSamuel.lean` | Samuel 関数、`IsSamuelPoly`（一意性は証明）、`poly`、`multiplicity` の定義。有限性は証明済み。Hilbert–Samuel の定理・次元定理・正値性の主張 | 3（可換環論の一般論、別トラック） |
| `Paper/Section2/Tower.lean` | `TowerStage`、`towerMap`、`Tower`、代数構造と `IsScalarTower`、`towerMaxIdeal`、`stageRank`。Lemma 2.3 (a) の主張。整性と有限生成性は証明済み | 8（標準事実） |
| `Paper/Section2/TowerLength.lean` | `λ_∞` の三段階の定義、同型不変性・零加群で `0`（証明）、`towerLength : NormalizedLength`、`towerLength_hasSup`。引用：有限生成加群で `λ = λ*`、(2.2)、降下、加法性 | 4（引用） |
| `Paper/Section2/Lemma2_4.lean` | Lemma 2.4 の四つの主張を `λ_∞` に適用 | なし（`hasSup` 経由で引用に依存） |
| `Paper/Section2/Lemma2_2.lean` | Lemma 2.2（具体形つき） | 1（Cohen–Gabber、Cohen） |
| `Paper/Section2/Lemma2_1.lean` | Lemma 2.1（長さ・正則性・`Tor` の長さの保存） | 1（Cohen の構造定理） |
| `Paper/Section2/Theorem2_5.lean` | `m_A C ≤ 𝔡 C`、`towerLengthOn`（`λ_D` の定義）、Theorem 2.5 | 1（Monsky、Roberts、CLMST、Bhatt–Scholze） |
| `Paper/Section2/Corollary2_6.lean` | Cor 2.6 (3) `cor_2_6_residue_pos`（(2.5) と `multiplicity_pos` から） | なし（`multiplicity_pos` に依存） |

`#print axioms`：一般論（`comap`、`SupProperty` の四定理、`QuotientLength`）、`IsSamuelPoly.unique`、
`Tower`、`towerLengthFun_congr`・`_eq_zero_of_subsingleton` は標準公理のみ。`towerLength`、
`towerLength_hasSup`、Lemma 2.4、`towerLengthOn`、`cor_2_6_residue_pos` は引用の `sorry` に依存する
（それぞれ加法性、`λ = λ*`、`multiplicity_pos`）。

段階 D（接続、2026-10-10）：別の作業のコミット後に、`Inputs.exists_lengthAlgebra` を削除して
`theorem_2_5` を正とし、`CommutativeAlgebra/Multiplicity.lean` の極限の式による
`hilbertSamuelMultiplicity` を削除し、`Paper/Corollary2_6.lean` の `cor_2_6_pos` を
`Section2.cor_2_6_residue_pos` による証明に置き換えた（仮定は (2.5) だけ）。ルートの import、
README、`PLAN.md` §1.5・§19 を更新した。利用側（Lemma 5.2、§5）は (2.6) の形の `hquot` を
引数にとるので変更なし。

残り：段階 H の証明（重複度の定理）、塔の段の標準事実、段階 E。

### 10.1 標準的事実のうち証明したもの（2026-10-10）

- `HilbertSamuel.samuelFunction_ne_top`：`D/I` が Artin（`√I = m_D`）で `M/I^n M` が `I^n` で消える
  有限生成加群なので有限長（既存の `isFiniteLength_of_le_radical_annihilator`）。
- `Section2.isIntegral_towerStage`、`towerStage_finite`：`A_n` は `X_i` の像で生成され、各 `X_i` は
  `X_i^{p^n} = t_i` から整（`IsIntegral.of_pow`）。有限型かつ整なので有限生成
  （`Algebra.IsIntegral.finite`）。`[Fact p.Prime]` を仮定に加えた（`p = 0` では偽）。

残りの標準的事実が簡単でない理由：

- 自由性・ランク（`towerStage_free`、`finrank_towerStage`、`towerMap_free_finrank`）：単項式基底
  `X^e`（`0 ≤ e_i < p^n`）が基底であることは、多変数の割り算（Gröbner 基底的な議論）か、
  `AdjoinRoot.powerBasis` を変数ごとに反復する同型 `A[X₁..X_h]/(…) ≅ (((A[X₁]/(…))[X₂]/(…))…)` が要る。
- 局所性・剰余体（`isLocalRing_towerStage`、`residue_surjective_towerStage`）：有限な局所環上の代数で、
  ファイバー `A_n/m_A A_n = k[X]/(X_i^{p^n})` が局所であることから出るが、Mathlib にその判定法はない。
- 正則性・完備性：局所性に依存し、さらに「有限加群は完備」「極大イデアルが `h` 個で生成」が要る。
- `flat_tower`：段の自由性（上）と、自由加群の有向極限が平坦であること（Mathlib に未確認）。
