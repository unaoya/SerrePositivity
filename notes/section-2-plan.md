# §2 の形式化計画（Lemma 2.1–2.4、Theorem 2.5、Corollary 2.6）

2026-10-10 作成、同日改訂。対象は論文 §2（p.4–9）。主張の確認と引用元の照合は `section-2.md`。

現在の優先順位（2026-10-10 方針変更）：[PLAN.md](PLAN.md) と
[section-4-plan.md](section-4-plan.md) 冒頭に従い、抽象化と二つの実現に集中する。
§2の具体的な長さ代数の構成と未証明部分の解消は後の課題として保存し、当面は続行しない。
抽象理論への適用では、必要な長さの性質を個別の入力として明示する。

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

残り：段階 H の証明（重複度の定理）、塔の段の標準事実のうち完備性・正則性、段階 E。

### 10.1 標準的事実のうち証明したもの（2026-10-10）

- `HilbertSamuel.samuelFunction_ne_top`：`D/I` が Artin（`√I = m_D`）で `M/I^n M` が `I^n` で消える
  有限生成加群なので有限長（既存の `isFiniteLength_of_le_radical_annihilator`）。
- `Section2.isIntegral_towerStage`、`towerStage_finite`：`A_n` は `X_i` の像で生成され、各 `X_i` は
  `X_i^{p^n} = t_i` から整（`IsIntegral.of_pow`）。有限型かつ整なので有限生成
  （`Algebra.IsIntegral.finite`）。`[Fact p.Prime]` を仮定に加えた（`p = 0` では偽）。

### 10.2 塔の段の標準事実と引用の明確化（2026-10-10、第二回）

**単項式基底の一般論（`Paper/Section2/MonomialBasis.lean`、新規、`sorry` なし）**：可換環 `R`、
`s : Fin h → R`、`q > 0` について `R[X₁..X_h]/(X_i^q − s_i)` は `X^e`（`0 ≤ e_i < q`）を基底とする
自由加群（`relBasis`）、ランク `q^h`（`finrank_quotient_relIdeal`、`R` が非自明のとき）。証明は
「割り算」写像 `ψ : R[X] → R^{(Fin h → Fin q)}`（`X^d ↦ (∏ s_i^{⌊d_i/q⌋}) e_{d mod q}`）が関係式を消して
商に降り、単項式の写像 `Φ` の逆になることによる。`Tower.lean` の `towerRel` はこの `relIdeal` で
`q = p^n` としたものに定義し直した。

**段の性質（`Paper/Section2/TowerStage.lean`、新規）**：Lemma 2.3 (a) の主張を `Tower.lean` から移し、
次を証明した（`[Fact p.Prime]`）。

- `towerStage_free`、`towerStage_finite`、`finrank_towerStage`（`= p^{nh}`）、基底 `towerStageBasis`。
- `towerMap_free_finrank`：`A_b` は `A_a` 上有限自由でランク `p^{(b−a)h}`。`A_b ≅ A_a[Y]/(Y_i^{p^{b−a}} − x_i)`
  （`relStageEquiv`、`Y_i ↦ X_i`、逆は `X_i ↦ Y_i`、`A_a` の作用は `towerMap`）を作って一般論を使う。
  基底は `towerMapBasis`。
- `isLocalRing_towerStage`、`maximalIdeal_towerStage`、`residue_surjective_towerStage`（`t_i ∈ m_A` を仮定）：
  `A_n → k`（`X_i ↦ 0`、`a ↦ ā`）の核 `M` が極大で、任意の極大イデアル `M'` は整拡大なので `m_A` の上にあり
  （`Ideal.isMaximal_comap_of_isIntegral_of_isMaximal`）、`X_i^{p^n} = t_i ∈ M'` と素性から `X_i ∈ M'`、
  よって `M ⊆ M'`、極大性から `M = M'`（`IsLocalRing.of_unique_max_ideal`）。剰余体は定数項から。
- `flat_tower`：`Λ` は `A_n` 上平坦。等式的判定法（`Module.Flat.of_forall_exists_factorization`）で、
  `A_n^l → Λ` の生成元の像が入る段 `m` と関係式が消える段 `m' ≥ m`（`Ring.DirectLimit.of.zero_exact`、
  `DirectedSystem` の instance を `Tower.lean` に追加）をとり、`A_n^l → A_{m'} ≅ A_n^k → Λ` と分解する。
  `Tower` の定義は `towerMapRingHom`（環準同型の族）で書き直した（`zero_exact` の形に合わせるため）。

残り（`sorry`）：`isAdicComplete_towerStage`（完備な Noether 局所環上の有限加群の完備性と、`m_{A_n}` 進と
`m_A A_n` 進の位相の一致が要る）、`isRegularLocalRing_towerStage`（整拡大での次元の保存
`dim A_n = dim A` が Mathlib にない。あれば `IsRegularLocalRing.of_spanFinrank_maximalIdeal_le` と
`m_{A_n} = (X)` から出る）。どちらも Theorem 2.5 の証明（段階 E）まで使わない。

**引用の明確化（`TowerLength.lean`）**：Lemma 2.3 (b) の四つの `sorry` を次のように分けた。

| 名前 | 主張 | 位置づけ | 出典 |
| --- | --- | --- | --- |
| (C1) `towerLengthFun_eq_fgLength` | 有限生成・`m_A` 冪ねじれで `λ_∞ = λ*` | 引用 | CLMST Prop. 2.2.3。本体は Gabber–Ramero *Foundations for almost ring theory* Lemma 14.5.74（Shimomoto Lemma 2.2）：有限生成加群の有限生成部分加群で `λ*` が単調 |
| (C2) `towerLengthFun_add_of_exact` | 短完全列での加法性 | 引用 | CLMST Prop. 2.2.6(a)。証明は Faltings *Almost étale extensions* (Astérisque 279, 2002) Appendix 2 に委ねられている。Gabber–Ramero Thm 14.5.75、Shimomoto Prop. 2.8 も同じ |
| (S1) `fgLength_tensor` | 有限長 `A_n` 加群 `V` で `λ*(Λ ⊗_{A_n} V) = ℓ(V)/p^{nh}` | 標準事実（後で証明） | 段の自由ランクと平坦性、有限表示加群で `λ* = λ**` |
| (S2) `exists_descent` | `m_A` 冪ねじれで有限表示な加群はある段から来る | 標準事実（後で証明） | 有限個の生成元と関係式はある段に入る |

(2.2) `towerLengthFun_tensor` は (C1) と (S1) から証明した（`isPowTorsion_tower_tensor` を経由。
`QuotientLength.lean` の `isPowTorsion_tensorProduct` を任意のイデアルに一般化した
`isPowTorsion_tensorProduct_of_isTorsionBySet` を使う）。

残りの標準的事実が簡単でない理由：

- 自由性・ランク（`towerStage_free`、`finrank_towerStage`、`towerMap_free_finrank`）：単項式基底
  `X^e`（`0 ≤ e_i < p^n`）が基底であることは、多変数の割り算（Gröbner 基底的な議論）か、
  `AdjoinRoot.powerBasis` を変数ごとに反復する同型 `A[X₁..X_h]/(…) ≅ (((A[X₁]/(…))[X₂]/(…))…)` が要る。
- 局所性・剰余体（`isLocalRing_towerStage`、`residue_surjective_towerStage`）：有限な局所環上の代数で、
  ファイバー `A_n/m_A A_n = k[X]/(X_i^{p^n})` が局所であることから出るが、Mathlib にその判定法はない。
- 正則性・完備性：局所性に依存し、さらに「有限加群は完備」「極大イデアルが `h` 個で生成」が要る。
- `flat_tower`：段の自由性（上）と、自由加群の有向極限が平坦であること（Mathlib に未確認）。

### 10.3 標準事実 (S1)・(S2) の証明（2026-10-10、第三回）

新しいファイル `Paper/Section2/TowerDescent.lean`（`sorry` なし）と一般論
`CommutativeAlgebra/PresentationBaseChange.lean`（`sorry` なし）。`TowerLength.lean` からは (S1)・(S2)・
(2.2) の主張を移し、引用 (C1)・(C2) だけを残した。

**一般論（`PresentationBaseChange.lean`）**：`R` 代数 `S` と関係式 `r : κ → (ι → R)` について
`S ⊗_R (R^ι / span r) ≃ S^ι / span (ρ ∘ r)`（`S` 線形、`baseChangeQuotEquiv`、`ρ = piAlgebraMap` は各成分に
`algebraMap`）。Mathlib の `tensorQuotientEquiv` は `R` 線形にしか述べられていないので直接作った
（順方向は `liftBaseChange`、逆方向は `e_i ↦ 1 ⊗ [e_i]`）。

**段への降下の道具**（`Tower.lean` と `TowerDescent.lean`）：

- `exists_towerOf_family`：`Λ` の有限個の元は共通の段から来る。
- `exists_towerMap_eq_zero`：段の有限個の元が `Λ` で `0` ならある段で `0`（`Ring.DirectLimit.of.zero_exact`）。
- `stageToTower m`（各成分に `towerOf m`）、`stageToStage m m'`（各成分に `towerMap m m'`）と
  その計算規則。
- `exists_stage_mem_span`：段の元の有限族の像が `Λ` で `span` に入るならある段で `span` に入る
  （係数を段に持ち上げ、差が `Λ` で `0` になることから先の段で `0`）。
- `exists_stage_surjective`：段 `N` で表示された二つの加群の `Λ` への係数拡大の間の `Λ` 線形な全射は、
  ある段 `N' ≥ N` の `A_{N'}` 線形な全射に降りる（生成元の像、関係式、全射性の証人を段に持ち上げ、
  `exists_stage_mem_span` で降ろす）。

**(S2) `exists_descent`**（`[IsNoetherianRing A] [Fact p.Prime]` を追加）：`M ≃ Λ^l / span k`
（`Module.FinitePresentation.exists_fin`）、`k` の成分を段 `m` に持ち上げ、ねじれ `(m_A Λ)^e M = 0` から
`x_σ e_i ∈ span k`（`x` は `m_A^e` の生成元、`A` の Noether 性）、`exists_stage_mem_span` で段 `N` に降ろす。
`V := A_N^l / span (c の像)` は `(m_A A_N)^e` で消え、`A` 上有限（`towerStage_finite`）で `m_A^e` で消えるので
`A` 上有限長、`isNoetherian_of_tower`・`isArtinian_of_tower` で `A_N` 上有限長。
`Λ ⊗_{A_N} V ≃ Λ^l / span k ≃ M` は `baseChangeQuotEquiv`。

**(S1) `fgLength_tensor`**（`ht : ∀ i, t i ∈ m_A` を追加。`[IsNoetherianRing A] [Fact p.Prime]`）：

- `length_tensor_towerMap`：`ℓ_{A_N}(A_N ⊗_{A_n} V) = p^{(N−n)h} ℓ_{A_n}(V)`。`A_N ≅ A_n^{p^{(N−n)h}}`
  （`towerMapBasis`）で `A_N ⊗ V ≅ V^{p^{(N−n)h}}`（`finsuppScalarLeft`、`Module.length_finsupp`）、
  `A_n` 上の長さと `A_N` 上の長さは剰余体が同じなので一致（`length_eq_of_common_residueField`、
  `residue_surjective_towerMap`）。
- `length_div_le_of_surjective`：有限長 `V`（段 `n`）、`W`（段 `m`）と `Λ` 線形な全射
  `Λ ⊗_{A_m} W ↠ Λ ⊗_{A_n} V` があれば `ℓ(V)/p^{nh} ≤ ℓ(W)/p^{mh}`。共通の段 `N = n ⊔ m` に上げ
  （`cancelBaseChange`）、`A_N ⊗ V`・`A_N ⊗ W` を有限表示し、全射を段 `N'` に降ろし
  （`exists_stage_surjective`）、`Module.length_le_of_surjective` と `length_tensor_towerMap` で
  `p^{(N'−n)h} ℓ(V) ≤ p^{(N'−m)h} ℓ(W)`、両辺を `p^{N'h}` で割る（`div_stageRank_eq`）。
- `fgLength_tensor`：`≤` は定義（`P := Λ ⊗ V`、`f := id`、降下 `(n, V)`）、`≥` は
  `length_div_le_of_surjective`。

(2.2) `towerLengthFun_tensor` は (C1) と (S1) から（`sorryAx` は (C1) 経由のみ）。
`#print axioms`：`exists_descent`、`fgLength_tensor`、`exists_stage_surjective`、`length_tensor_towerMap`、
`baseChangeQuotEquiv` は標準公理のみ。

残る `sorry`（§2）：引用 (C1)・(C2)、Lemma 2.1、2.2、Theorem 2.5、段の完備性・正則性、重複度の定理 3 つ。


### 10.4 定理2.5の標数別分割と共通の導出（2026-10-10）

- `TowerStage` の完備性・正則性は、有限代数の完備性と整拡大の次元比較に接続済み。
- `TowerLengthOn.lean` に、長さを `D` に沿って扱うための係数制限を移した。
- `LengthAlgebraConstruction.lean` に等標数・混標数それぞれの未完了の存在主張を置いた。
  これらは単なる引用定理ではない。等標数では perfection、トレース、核の誤差評価、
  Monsky・Roberts の結果との接続が残る。混標数では CLMST の結果と塔の完備化の比較が残る。
- `Theorem2_5` は補題2.2の具体的な基底の選択肢を明示的な引数 `hbase` に受け取る。
  混標数では Witt 冪級数環の表示に加えて `t₀ = p` を明示する。
- `IsSystemOfParameters.pow` は証明済み。正の冪を取っても生成イデアルの根基が変わらない。
- `MultiplicityFormulas.lean` に二つの標準的な未証明主張を明示した：
  成分ごとの冪の重複度公式、剰余体が一致する有限局所拡大での
  Hilbert–Samuel 重複度と係数制限した Koszul Euler 特性の一致。
  基底が正則な場合の階数公式は、後者と既存の `koszulEulerChar_eq_finrank` から導出した。
- `LengthAlgebraConsequences.lean` では、一乗のパラメータ商の値から全ての正の冪での
  (2.5) を導き、階数公式を用いて (2.6) を導出した。
- `theorem_2_5` の直接の `sorry` はなくなったが、定理全体は未完成。
  標数別の構成二つ、重複度の一般公式二つに直接 `sorry` があり、既存の
  長さの可加性、Hilbert–Samuel 理論、正則パラメータの正則性の未証明入力にも依存する。
  `sorry` の個数の減少や、等標数でのトレースの議論の完了を意味しない。

次の実装は、等標数で Mathlib の `PerfectClosure` に塔の作用を構成すること。
その後、トレースの共通分母、商への写像の核の評価、正規化後の誤差の消滅へ進む。
Monsky・Roberts の定理そのものの引用と、この接続の未実装部分は引き続き区別する。

### 10.5 等標数の具体的な代数と塔の作用（2026-10-10）

`PerfectTower.lean` に、任意の標数 `p` の完全環 `C` への `A` 代数準同型
`Tower A t p →ₐ[A] C` を構成した。このファイルには `sorry` はない。

- `perfectRoot`：反復 Frobenius の逆による `tᵢ` の `pⁿ` 乗根。
- `perfectRoot_pow`、`perfectRoot_compatible`：根の関係式と遷移写像との両立。
- `towerStageToPerfect`：商環の普遍性による各段からの写像。
- `towerToPerfect`：Mathlib の `Ring.DirectLimit.lift` による塔からの写像。
- `towerStageToPerfect_unique`、`towerToPerfect_unique`：完全環での根の一意性に基づく一意性。

`lengthAlgebra_equalCharacteristic` は `C = PerfectClosure D p` を実際に選び、
`D`・`A`・塔の作用と二つのスカラー塔の両立を証明する形に変更した。
`Theorem2_5` の等標数分岐もこれに接続済み。
残る `perfectClosure_length_properties_pending` は具体的な perfection 上の
Koszul ホモロジーの長さの消滅とパラメータ商の重複度公式である。
この未証明主張は純粋な引用ではなく、トレース・誤差評価・文献定理との接続を含む。
混標数側と重複度の一般公式の未証明入力は今回変更していない。

### 10.6 Perfection の近似と分母による核の評価（2026-10-10）

この段階では新しい `sorry` は追加していない。

- `PerfectApproximation.lean` で `D^{1/pⁿ}` と係数環 `R` が生成する部分代数を
  `Algebra.adjoin` で定義した。逆 Frobenius による根と Mathlib の `PerfectClosure.mk`
  が一致すること、部分代数の増大性、全ての元を覆うことを証明した。
  `R = Λ` とすれば論文の `B_q` の像に当たるが、テンソル積表示との同定はまだ未実装。
- `ConductorQuotient.lean`：単射な環拡大 `B → C` と `gC ⊆ B` から、
  `B/I → C/IC` の核が `g` で消えることを証明した。Noether 性は不要。
- `NormalizedLength.lean`：`λ(M) < ∞` のとき自己準同型の核と余核の長さが等しいこと、
  `ker(f) ⊆ ker(g)` なら `λ ker(f) ≤ λ coker(g)` となることを証明した。
- `QuotientLength.lean`：上記を組み合わせ、係数環に制限した正規化長さについて
  商写像の核を分母倍写像の余核で評価した。
- `perfectionApproximation_kernel_bound`：この評価を近似部分代数に適用した。
  共通分母と商の長さの有限性は明示的な仮定であり、まだ構成していない。

定理2.5の等標数側の未証明主張は依然として残る。次に必要なのは、
(1) 近似部分代数と有限段からのテンソル積の同定・正規化長さの計算、
(2) トレース双対基底からの共通分母の存在、
(3) 分母倍写像の余核と `D/(H^[q],g)` の比較および成長評価、
(4) Monsky・Roberts の定理と極限への接続である。
今回証明した核の評価自体は、これらの未証明主張に依存しない。

### 10.7 商による核の評価と根の段の通常の長さ（2026-10-10）

新しい `sorry` は追加せず、次を証明した。

- `quotientSmulCokerEquiv`：`B/I` 上の `g` 倍写像の余核と `B/(I,g)` の
  係数環 `R` 上の線形同型。これにより `len_ker_quotientToExtension_le` と
  `perfectionApproximation_kernel_bound` の右辺を、余核から通常の商の長さへ変更した。
- `perfectionRootHom_injective`：被約環で根の写像が単射。Mathlib の被約環の
  Frobenius の単射性を使用する。
- `perfectionRootStage` と `perfectionRootStageEquiv`：`D_perf` 内の `D^{1/pⁿ}` と
  元の環 `D` の環同型。
- `perfectionRootStageBaseMap`：根の段への通常の包含。perfection まで合成すれば
  `PerfectClosure.of` と一致する。この包含と根を取る環同型は区別した。
- `perfectionRootStageQuotientEquiv`：`D/(H^[q],g)` と
  `D^{1/q}/(H D^{1/q},g^{1/q})` の環同型。
- `length_perfectionRootStage_quotient`：上の二つの商の、それぞれの係数環上での
  通常の長さの一致。Mathlib の商環同型と全射に沿った長さの不変性を組み合わせた。
  `length_perfectionRootStage_quotient_base` は分母を加えない `g = 0` の場合。

ここで `H^[q]` は新しい独自定義を作らず、`H.map (iterateFrobenius D p n)` とした。
今回の結果は `q⁻ʰ length_D(D/(H^[q],g))` の通常の長さの部分を準備するもの。
`B_q = Λ ⊗_{A^{1/q}} D^{1/q}` との同定と有限段の正規化長さへの接続は依然として残る。
トレースによる分母の存在、成長評価、極限への接続もまだ未完了である。

### 10.8 有限段からのテンソル積と近似部分代数の接続（2026-10-10）

`PerfectBaseChange.lean` を追加し、以下を `sorry` なしで証明した。

- `towerStageToRootStage`：各段 `A_n → D^{1/pⁿ}`。係数は通常の包含で送り、変数は
  対応するパラメータの根に送る。定義関係式を満たすことも証明した。
- `towerStageToRootStage_coe`：perfection への包含と合成すると、既存の
  `towerStageToPerfect` に一致する。
- `perfectBaseChangeMap`：`Λ ⊗_{A_n} D^{1/pⁿ} → D_perf` の `Λ` 代数準同型。
  `perfectBaseChangeMap_tmul` は単純テンソルについての計算規則。
- `perfectBaseChangeMap_range`：写像の像は `perfectionApproximation` に等しい。
- `perfectBaseChangeSurjection`：値域を近似部分代数へ制限した全射。

一般論 `tensorProduct_range_eq_adjoin` は `PresentationBaseChange.lean` に置いた。
これは係数拡大の積写像の像を、右因子の像が生成する部分代数と同定する。
仮定をまとめる独自の構造体・クラスは追加していない。根の段・塔の作用については
既存の Mathlib の `Algebra` と `IsScalarTower` を具体的に構成し、ファイル内で登録した。

**未完了の境界**：全射は環同型ではない。単射性のための、一般点での分離拡大と
純非分離拡大の線形無関連性、および平坦性・ねじれなし性からの降下がまだ必要。
正規化長さの有限段公式にこのテンソル積を同定する作業、共通分母、成長評価、
極限への接続も引き続き残る。今回新しい `sorry` は追加していない。

### 10.9 単射性の体論と平坦な降下、および塔への部分適用（2026-10-10）

`CommutativeAlgebra/SeparableBaseChange.lean` で以下を証明した。

- 分離拡大と純非分離拡大の共通の体への積写像は単射。
  Mathlib の純非分離拡大後の線形独立性を、基底の係数拡大に適用した。
- 各元のある `p` 冪が底体に入る環の分数体は純非分離。
  分子と分母の冪をそろえる直接の証明。
- 底環の局所化が体で、左因子が平坦であり、両因子がそれぞれ純非分離拡大と
  分離拡大に単射で入る場合の、環のテンソル積の積写像の単射性。
  Mathlib の平坦性によるテンソル積の単射性と局所化による底環変更を利用した。

`PerfectTower.lean` では、有限段の元の `pⁿ` 乗が基底環から来ること、
塔の各元のある `p` 冪が基底環から来ることを証明した。
また、被約な各段から完全環への単射性と、その塔全体への拡張を証明した。
これらと上の一般論は `sorryAx` に依存しない。

`PerfectBaseChange.lean` では、正則パラメータの設定で塔から perfection への
単射性を導出し、塔の分数体の純非分離性も証明した。
前者の各段の整域性は既存の `isDomain_of_isRegularLocalRing` を用いるため、
既存の正則パラメータの入力定理の `sorry` に依存する。新しい `sorry` はない。
仮定をまとめる独自の構造体・クラスも追加していない。

**未完了の境界**：`perfectBaseChangeMap` 自体の単射性はまだ未証明。
`Frac(D^{1/q}) / Frac(A_n)` の分離性を Lemma 2.2 の生成的分離性から導く部分と、
共通の分数体の中の代数構造・包含を整合させ、上の一般定理を適用する部分が残る。
有限段の長さ公式、トレースの共通分母、成長評価、極限への接続も引き続き必要。

### 10.10 近似環のテンソル積表示の完成と生成的分離性の修正（2026-10-10）

`perfectBaseChangeMap_injective` と `perfectBaseChangeEquiv` を証明した。
後者は補題2.2と同じ剰余体の一致・完全性の仮定から
`Λ ⊗_{A_n} D^{1/pⁿ} ≃ₐ[Λ] perfectionApproximation D p Λ n` を与える。
前節で残していた単射性は、今回で解決した。新しい `sorry` はない。

証明の流れ：

1. `TowerStage.lean` の極大イデアルの生成元の議論を
   `span_stageX_eq_maximalIdeal` として取り出し、既存の正則性の証明でも再利用。
2. `PerfectTower.lean` で `towerStageFrobenius` を構成。
   係数を `pⁿ` 乗、根を元のパラメータに送る。
   剰余体の完全性と Mathlib の完備性による全射性判定で全射性を証明。
   被約性による単射性と合わせて `towerStageFrobeniusEquiv : A_n ≃+* A` を得た。
3. 根の段の同型 `D ≃+* D^{1/pⁿ}` との可換性を証明。
   分数体での分離性を環同型に沿って移す一般論から
   `rootStage_fractionRing_isSeparable` を導いた。
4. 整域の perfection が整域であることを、その分数体の perfection への単射で証明。
   これによりすべての因子を `Frac(D_perf)` に埋め込み、前回の平坦性・局所化の
   一般定理を適用した。既存の全射性と合わせて近似環との同型を構成。

**ステートメントの修正**：従来の `Algebra.IsSeparable A D` は環上の条件として強すぎた。
Mathlib の多項式の `Separable` は導関数との Bezout 関係を要求するため、
分岐を許す生成的分離性と同一視できない。
`Lemma2_2.lean`、`Theorem2_5.lean`、`LengthAlgebraConstruction.lean` を
`∀ d : D, ((minpoly A d).map (algebraMap A (FractionRing A))).Separable`
という明示的な仮定に統一し、呼び出し側も修正した。
正規な整域上の整拡大で、この条件が分数体の分離性と同値であることも
一般定理 `separable_minpoly_iff_fractionRing` として証明した。
仮定をまとめる独自の構造体・クラスは導入していない。

**依存と残り**：Frobenius 写像の構成・全射性、分数体の分離性の一般論、
perfection の整域性に `sorry` はない。論文の設定での同型は、各段の被約性を得る
既存の正則パラメータの正則性の未証明入力に依存する。
定理2.5の長さの性質の証明はまだ完成していない。
次はこの同型を有限段の正規化長さの公式につなぎ、トレースによる共通分母の存在、
成長評価、Monsky・Roberts の結果と極限への接続を進める。

### 10.11 近似環の商の正規化長さと元の環の長さの接続（2026-10-10）

`PerfectApproximationLength.lean` で有限段の長さ公式を近似環の商へ接続した。

- `PresentationBaseChange.lean`：Mathlib のテンソル積と商の交換同型から、
  `R ⊗_S T ≃ₐ[R] B` の下で `R ⊗_S (T/I) ≃ₐ[R] B/IB` を構成。
- `TowerDescent.lean`：有限長性から極大イデアルの冪による零化を導き、
  `towerLengthFun_tensor_of_finiteLength` により利用側の冪ねじれ条件を省く。
- `FiniteLength.lean`：係数環と代数の環同型が構造写像と可換なら、対応する商の長さが
  等しいことを半線形全単射による一般論から証明。
- `PerfectApproximationLength.lean`：Frobenius 同型と剰余体の一致から、
  `A_n` 上の根の段の商の長さを `D` 上の商の長さに戻す。
  近似環のテンソル積表示に適用すると、有限長な `D/J` に対し、
  根の同型で移した商の正規化長さは `ℓ_D(D/J)/p^(nh)` になる。
  特に `J = H^[q] + (g)` として、論文の
  `λ(B_q/(HB_q + g^(1/q)B_q)) = ℓ_D(D/(H^[q]+(g)))/q^h` を得る。

仮定は明示的に保ち、新しい `sorry` や入力クラスは追加しない。
商・テンソル積の交換と同型による長さの比較の一般論は `sorryAx` に依存しない。
論文の公式は既存の (C1) と、有限段の被約性のための正則パラメータの入力に依存する。

**残り**：トレースによる共通分母の存在、誤差項の成長評価、
Monsky・Roberts の結果および極限との接続。混標数の引用入力も残る。
`perfectClosure_length_properties_pending` は引き続き未証明であり、
有限段の公式が完成しても定理2.5全体の完成ではない。

### 10.12 トレース双対基底による共通分母の一般論（2026-10-10）

`CommutativeAlgebra/TraceConductor.lean` を追加し、次を証明した。

- 正規整域 `R` の分数体 `K` の有限分離拡大 `L` と基底 `b` に対して、
  全ての `g • b.traceDual i` が `R` 上整なら、任意の整元 `x` の `g • x` は
  `b` の `R` 線形包に入る。
  Mathlib の `traceDual_repr_apply`、`Algebra.isIntegral_trace`、
  `IsIntegrallyClosed.algebraMap_eq_of_integral` を組み合わせた。
- Mathlib の `Algebra.IsAlgebraic.exists_integral_multiples` を使って、
  双対基底の有限個の整倍数の分母を一つにそろえる。
- より小さい整域 `A` 上 `L` が代数的な場合、分母を `A` 内で選べる。
  論文の `g ∈ A` を保つための形であり、分母を `Λ` 内にしか取れないという問題を避ける。
- 基底を含む部分代数 `B` と、全ての元が `R` 上整な部分代数 `C` に対して、
  `∃ g : A, g ≠ 0 ∧ gC ⊆ B` を導いた。

論文では `gβ_i ∈ D` とするが、トレースの整性に必要なのは `gβ_i` の整性だけである。
今回の一般論はその十分な条件を使う。仮定は個々に明示し、入力クラスや `sorry` は追加しない。

`PerfectApproximation.lean` には `isIntegral_perfection_of_isIntegral` を追加。
整拡大 `R → D` と両立する作用の下で、`D_perf` の各元が `R` 上整であることを
`pⁿ` 乗からの整性の下降で証明した。

**未完了の境界**：論文の具体的な `g D_perf ⊆ B₁` はまだ導出していない。
`Λ` の正規性、`Frac(D_perf)` と係数拡大した有限分離拡大の同定、
`B₁` に入る体上の基底の構成・対応を整える必要がある。
その後で根を取って `g^(1/q) D_perf ⊆ B_q` を得る。
共通分母の一般論が証明済みであることと、その具体的な適用の完成とは区別する。
成長評価・極限・混標数の未証明部分は引き続き残る。

### 10.13 塔の完全性と共通分母の根への移行（2026-10-10）

`PerfectConductor.lean` で、初段の共通分母を各段へ移す部分を証明した。

- `perfectionApproximation_root_mem`：完全な係数環 `R` では、`B₁` の元の
  `pⁿ` 乗根は `B_q` に入る。部分代数の生成に関する帰納法で、係数の根には
  `R` の完全性、`D` の元の根には既存の `perfectionRootHom` を用いる。
- `perfectionApproximation_conductor_root`：`gC ⊆ B₁` を `c^q` に適用して
  逆 Frobenius を取ることで `g^(1/q)C ⊆ B_q` を導く。
- `perfectionApproximation_kernel_bound_of_conductor`：既存の核の長さ評価に接続し、
  各段の分母条件を初段の一つの条件から導く形にした。
- `towerEquivPerfection`：既存の有限段 Frobenius の全射性から、
  `Tower A t p ≃+* PerfectClosure A p` を構成。
  単射性には各段の被約性を使い、これは既存の正則パラメータの入力に依存する。
- `perfectRing_tower`：この同型から塔の完全性を導出。
- `tower_perfectionApproximation_conductor_root`：剰余体の一致から基底の完全剰余体を得て、
  塔の完全性を証明して使う。完全性を新しい仮定にはせず、論文の塔で各段の包含を得る。

新しい `sorry` や独自の入力クラスは追加していない。
一般形の根への移行は `sorryAx` 非依存。
塔の同型・完全性と具体的適用は既存の正則パラメータ入力に依存する。

**残り**：最初の `gC ⊆ B₁` の存在は引き続き未証明。
塔の正規性と、perfection の分数体における有限分離拡大・基底の対応が必要。
Mathlib の正則局所環・多変数形式冪級数環・直極限のファイルを確認した範囲では、
この塔の正規性に直接適用できる定理は見つかっていない。
今回得た塔と perfection の同型も、以降の正規性・分数体の議論に再利用できる。
成長評価・極限・混標数の未証明部分は変わらない。

### 10.14 正規整域の perfection の正規性（2026-10-10）

有限段の係数への降下の代わりに、整性の推移性と純非分離性による証明を実装した。

- `CommutativeAlgebra/PerfectNormality.lean`：正規整域 `A` の整拡大 `S` が完全であり、
  分数体拡大 `Frac(S)/Frac(A)` が純非分離なら `S` は正規。
  `Frac(S)` の `S` 上整な元 `x` は `A` 上も整である。
  純非分離性から `x^(p^n)` を `Frac(A)` に戻すと、正規性により `A` の元になる。
  `S` の完全性からその根を取り、体上の Frobenius の単射性で `x` 自身を `S` に戻す。
  Noether 性は不要。
- `perfectClosure_fractionRing_isPurelyInseparable`：perfection の分数体の純非分離性を
  再利用可能な定理として証明。
- `perfectClosure_isIntegrallyClosed`：上記と前回の perfection の整性を合わせ、
  正規整域の perfection が正規であることを証明。
- `isIntegrallyClosed_tower_of_base`：前回の `Tower ≃+* PerfectClosure A p` を使い、
  `A` が正規なら塔も正規であることを導出。

新しい `sorry` や独自の入力クラスはない。一般論・perfection の正規性は `sorryAx` 非依存。
塔への移行だけは既存の同型を通じて正則パラメータ入力に依存する。

**正確な残り**：`isIntegrallyClosed_tower_of_base` は標準の `[IsIntegrallyClosed A]` を
明示的に要求する。定理2.5本体の仮定にこれを追加したわけではなく、
論文の基底環（体上の多変数形式冪級数環）の正規性を現行の仮定から導く部分は未実装。
体の係数拡大における基底の対応と合わせて、最初の `gC ⊆ B₁` の導出がなお必要。
成長評価・極限・混標数の未証明部分も残る。

### 10.15 完全な係数体への拡大とトレース基底の接続（2026-10-10）

`SeparableBaseChange.lean` で既存の単射性を拡張した。
`L/K` が有限分離、`E/K` が純非分離、`E` が完全体、共通の体 `Ω` が `L` 上純非分離なら、
積写像 `E ⊗_K L → Ω` は全単射である。

単射性は既存の線形無関連性の証明を使う。テンソル積は `E` 上有限次元の整域なので体であり、
完全体の代数拡大なので完全体である。`x ∈ Ω` のある `pⁿ` 乗は `L` から来るので、
そのテンソル積内で根を取り、`Ω` の Frobenius の単射性から `x` が像に入ることを示した。

- `tensorProduct_bijective_of_perfect_of_purelyInseparable` とその代数同型版。
- `basisOfPerfectBaseChange`：`L/K` の基底を `Ω/E` の基底に移す。
  各ベクトルが元の基底の自然な像であることも計算補題で証明。
- `finrank_perfectBaseChange`：`[Ω:E] = [L:K]`。
- `TraceConductor.exists_smul_subalgebra_le_of_perfectBaseChange`：この基底を
  既存のトレース分母定理に渡す。拡大後の基底を別に仮定せず、元の基底の像が
  `B` に入るという条件から、`A` 内の非零分母 `g` と `gC ⊆ B` を構成する。

全て一般の体・整域・部分代数についての定理で、新しい `sorry` や入力クラスはない。

**未完了の境界**：論文の具体的な `A, D, Λ, D_perf` にこの一般論を適用する部分はまだ残る。
`A` の正規性を現行の仮定から導くこと、`Frac(D)` の有限基底を `D` 内から選ぶこと、
具体的な分数体の代数構造と完全性・純非分離性を整合させることが必要。
初段の `g D_perf ⊆ B₁` の無条件の導出はまだ完成していない。
成長評価・極限・混標数の未証明部分も残る。

### 10.16 元の環内からの分数体基底の選択（2026-10-10）

`SeparableBaseChange.lean` で次を証明した。

- `span_range_fractionRing_eq_top`：代数的な整域拡大 `A → D` では、
  `D` の像が `Frac(D)` を `Frac(A)` 上張る。
  Mathlib の `IsFractionRing.ideal_span_singleton_map_subset` を単位イデアルに適用。
  同定理が分母を底環側に移す議論を既に含むため、独自の分母計算は重複して実装しない。
- `finiteDimensional_fractionRing_of_finite`：`D` が有限 `A` 加群なら、分数体拡大は有限次元。
  `Frac(A) ⊗_A D → Frac(D)` の像が全体を張ることから全射性を示し、
  有限加群の商として有限次元性を得る。
- `exists_basis_fractionRing_mem_range`：張る集合から基底を選ぶ Mathlib の
  `Module.Basis.ofSpan` を使い、分数体の基底を `D` の像の中から選ぶ。

`TraceConductor.exists_smul_subalgebra_le_of_fractionRing` で、これらを前回の
完全な係数拡大とトレースの議論へ接続した。
利用側は有限分数体拡大や具体的な基底を別に仮定する必要がなく、
`Module.Finite A D` と `D` の像が `B` に含まれることから、それらを証明内で導く。
その他の正規性・純非分離性・完全性・整性等の前提は明示的に残る。
新しい `sorry` や独自の入力クラスは追加していない。

**残り**：論文の `A` の正規性を現行の仮定から導くことと、
具体的な `A, D, Λ, D_perf` の分数体に代数構造・両立条件・完全性等を与えて
上の分母定理を適用すること。基底の存在・選択そのものは今回で解決した。
初段の共通分母の具体的な導出、成長評価・極限・混標数の未証明部分はなお残る。


### 10.17 具体的な塔への共通分母定理の適用（2026-10-10）

- `PerfectNormality.perfectRing_fractionRing`：完全整域の分数体の完全性を証明。
  分子と分母の根を取る証明で、Noether 性は不要。`sorryAx` 非依存。
- `exists_tower_perfection_conductor_of_normal_base`：基底環の正規性を明示的に
  仮定した上で、非零の `g : A` と `g C ⊆ B₁` を構成。
  `Frac(A), Frac(D), Frac(Λ), Frac(C)` の両立する代数構造を与え、
  分離性・純非分離性・完全性・整性を既存の定理から導いた。
  トレースの一般定理を分数体内の部分代数に適用し、分数体への単射から環へ戻す。
- `exists_tower_perfection_conductor_roots_of_normal_base`：同じ `g` について
  全ての `n` で `g^(1/p^n) C ⊆ B_(p^n)` を導出。
  既存の `perfectionApproximation_kernel_bound` へこの包含を渡せる。

新しい `sorry` や入力を束ねる独自の構造・クラスは追加していない。
塔の定理は従来どおり正則パラメータの引用入力に依存する。

**残りの境界**：共通分母の具体的な適用は今回で完了したが、標準の
`[IsIntegrallyClosed A]` を前提とする。これを論文の元の仮定から導くことは未実装。
`perfectClosure_length_properties_pending` の仮定は変更しておらず、その `sorry` も残る。
成長評価・極限への接続・混標数の場合も引き続き未完了。

検証：`lake build` 全体が成功（3062 jobs）。`git diff --check` も成功。
`#print axioms` で分数体の完全性とトレースの一般定理は `sorryAx` 非依存、
塔の二つの存在定理は既存の正則パラメータ入力を通じた `sorryAx` 依存を確認した。


### 10.18 誤差商の成長評価と零への収束（2026-10-10）

`CommutativeAlgebra/QuotientPowerLength.lean` で、Noether 性や正則列を仮定しない
通常の長さの評価を証明した。値域は `ℕ∞` とする。

- `length_quotient_sup_span_mul_le`：`ℓ(R/(I,xy)) ≤ ℓ(R/(I,x)) + ℓ(R/(I,y))`。
  `y` 倍と自然な商写像の右完全列、および Mathlib の長さの加法性・単調性を使う。
- `length_quotient_sup_span_pow_le`：一つの生成元の `q` 乗で長さは高々 `q` 倍。
- `length_quotient_sup_span_powers_le`：`r` 個の生成元の `q` 乗では高々 `q^r` 倍。
- `length_quotient_frobenius_sup_le`：`z_i ∈ H` なら
  `ℓ(R/(H^[q]+I)) ≤ q^r ℓ(R/(I,z))`。
- `isFiniteLength_quotient_frobenius_sup`：右辺の基礎となる商が有限長なら、
  各 Frobenius 段の商の有限長性もこの上界から従う。

`PerfectApproximationLength.lean` で上記を実際の近似環の商に接続した。
`z : Fin r → D`、`z_i ∈ H`、`D/(g,z)` が有限長という明示的な仮定のもとで、
`λ(B_q/(HB_q+g^(1/q))) ≤ q^r ℓ(D/(g,z))/q^h`。
特に `r+1=h` なら定数倍の `1/q` に抑えられ、正規化長さは零へ収束する。
各段の有限長性を別に要求する必要はない。

**未完了の境界**：`g ≠ 0` と次元の条件から、この `h-1` 個の元を `H` 内に
選べることはまだ証明していない。今回の収束定理は選んだ元と有限長性を明示的に要求する。
また核の長さの収束、余極限との比較、Monsky・Roberts の引用との接続も残る。
基底環の正規性と混標数の場合も従来どおり未完了。
新しい `sorry` や仮定を束ねる独自の構造・クラスは追加していない。

検証：全体の `lake build` が成功（3089 jobs）、`git diff --check` も成功。
`#print axioms` により、新しい一般の長さ評価・有限長性は `sorryAx` 非依存。
近似環の上界と収束定理には、既存の有限段の長さ公式を通じた `sorryAx` 依存が残る。


### 10.19 商写像の核の消滅と核・像の長さの等式（2026-10-10）

前回の誤差商の収束を、実際の商写像の核へ接続した。

- `radical_map_iterateFrobenius`：Frobenius 冪イデアルは根基を保つ。
- `isFiniteLength_quotient_map_iterateFrobenius`：Noether 環で `D/H` が有限長なら
  `D/H^[q]` も有限長。既存の根基による Artin 性の比較を使い、追加の未証明入力は不要。
- `isPowTorsion_quotient_of_baseChange` と近似環への適用：有限段の有限長性から
  塔上の商の冪ねじれを導く。
- `length_rootStage_base_quotient` と有限長性の系：通常の包含で作る根の段の商を
  `D/H^[q]` と長さのレベルで同定する。
- `towerLengthFun_perfectionApproximation_kernel_le`：上記と有限段の長さ公式により、
  核の評価に必要な冪ねじれ・長さの有限性を証明内で用意する。
- `towerLengthFun_perfectionApproximation_kernel_tendsto_zero`：`D/H` の有限長性、
  初段の共通分母 `gC ⊆ B₁`、および前回の `h-1` 個の元 `z ∈ H` と `D/(g,z)` の
  有限長性から、`λ ker(B_q/HB_q → C/HC) → 0` を証明。
  各段の分母条件は初段から導き、各段の有限長性・冪ねじれも追加仮定にしていない。
- `rootStageToApproximation_map_extension`：拡大イデアルはどの段からでも `HC` になり、
  商写像の行き先が段によらないことを確認。
- `towerLengthFun_perfectionApproximation_kernel_add_range`：各段で
  `λ ker(f_q) + λ im(f_q) = ℓ_D(D/H^[q])/q^h` を証明。
  Hilbert–Kunz 極限と結び付けるための加法性の等式である。

**残り**：`h-1` 個の元の選択、基底環の正規性、像の増大・被覆と余極限での
長さの比較、Monsky・Roberts の結果との接続は未完了。
今回の核の消滅は共通分母と元の組を明示的に与える定理であり、定理2.5全体の完成ではない。
新しい `sorry` や仮定を束ねる独自の構造・クラスは追加していない。

検証：全体の `lake build` 成功（3089 jobs）、`git diff --check` 成功。
`#print axioms` により、根基・有限長性・一般の係数拡大後の冪ねじれ・拡大イデアルの同定は
`sorryAx` 非依存。核の収束と核・像の等式には既存の長さ公式等を通じた依存が残る。


### 10.20 像の増大・被覆と Frobenius 商の極限の比較（2026-10-10）

- `perfectionQuotientImage`：固定した商 `C/J` の中で、近似部分代数 `B_q` から来る
  元の部分加群を定義。仮定の束ではなく、比較する数学的な像である。
  `perfectionQuotientImage_monotone` と `iSup_perfectionQuotientImage` で増大性と被覆を証明。
- `isPowTorsion_quotient_extension`：`R → B → C` において `B/I` が `R` の
  イデアルの冪で消えるなら、`C/IC` も同じ冪で消える。平坦性・有限性は不要。
- `towerLengthFun_quotient_eq_iSup_image` と `towerLengthFun_quotientImage_tendsto`：
  既存の長さの上限性を用い、像の長さの上限と極限が商全体の長さになることを証明。
  無限大の長さも扱う。
- `isPowTorsion_perfection_quotient`：`D/H` が有限長なら、初段の商を使って
  `C/HC` の塔上の冪ねじれを導く。
  したがって具体的な像の収束定理に冪ねじれを追加仮定する必要はない。
- `towerLengthFun_perfectionApproximation_range_eq_image`：前回までの段ごとの
  商写像の像と、固定した商の中の像の長さを同定する。
  この同定自体に正則性・完備性・剰余体の条件は不要。
- `normalized_frobenius_length_tendsto_perfection_quotient`：共通分母 `gC ⊆ B₁` と
  `z : Fin (h-1) → H`、`D/(g,z)` の有限長性を与えると、
  `ℓ_D(D/H^[q])/q^h → λ(C/HC)`。前回の核の零への収束、今回の像の収束、
  各段の加法性を合わせて証明した。

**未完了の境界**：この比較定理では共通分母と元の組を明示的に要求する。
論文の仮定からそれらを用意するには、なお基底環の正規性と元の選択の次元論が必要。
また文献からの Hilbert–Kunz 極限の値の同定はまだ接続していない。
正次数の Koszul ホモロジーの長さの消滅、混標数の場合も未完了。
定理2.5本体の仮定と `sorry` は維持しており、新たな `sorry` は追加していない。

検証：全体の `lake build` 成功（3089 jobs）、`git diff --check` 成功。
公理監査で、冪ねじれの環拡大・像の増大と被覆・段の像との長さの同定は
`sorryAx` 非依存。最終比較定理には既存の長さ公式等を通じた `sorryAx` 依存が残る。
