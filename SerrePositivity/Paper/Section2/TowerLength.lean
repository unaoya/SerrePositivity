module

public import SerrePositivity.LengthAlgebra.RootTowerLength.Basic
public import SerrePositivity.LengthAlgebra.RootTowerLength.Additivity
public import SerrePositivity.LengthAlgebra.Normalized

/-! # 証明した塔の正規化長さの互換入口

三つの数値関数と、その零・同型不変性は
`LengthAlgebra/RootTowerLength/Defs.lean` に抽出した。
有限生成一致 C1 と加法性 C2 は、Noether 局所環・素数・座標の極大イデアル所属を仮定して
有限段の長さと近似から証明した。共通層の証明済み `NormalizedLength` を
`towerLength` として再公開し、上限の性質もそこから供給する。

有限段の λ* の公式と有限表示降下は `TowerDescent.lean` で証明済み。
λ∞ の有限段公式は証明済み C1 を使う。
-/

@[expose] public section

universe u

open IsLocalRing TensorProduct
open scoped ENNReal

namespace SerrePositivity
namespace Section2

variable (A : Type u) [CommRing A] {h : ℕ} (t : Fin h → A) (p : ℕ)

/-! ## Lemma 2.3 (b)：証明した性質と標準事実

**証明済みの有限生成一致と加法性**

- (C1) `towerLengthFun_eq_fgLength`：有限生成で `m_A` 冪ねじれの加群で `λ_∞ = λ*`。
  CLMST（Cai–Lee–Ma–Schwede–Tucker, arXiv:2209.04046v4）Proposition 2.2.3 の主張
  「`λ_∞` は well defined で、有限生成加群では `λ_∞^*` と一致する」。その証明は
  Gabber–Ramero, *Foundations for almost ring theory*, Lemma 14.5.74（または Shimomoto, Lemma 2.2）
  に関連する。ここでは標準基底より弱い Noether 局所環の条件で証明した。
  内容は「有限生成 `N` の有限生成部分加群 `N'` について `λ*(N') ≤ λ*(N)`」
  （`λ*` の単調性）で、これが (2.3) の上限が `λ*` 自身に戻ることを保証する。
- (C2) `towerLengthFun_add_of_exact`：`m_A` 冪ねじれ加群の短完全列での加法性。
  CLMST Proposition 2.2.6(a) に対応する性質を、有限段の長さ・有限表示な被覆・
  有限生成部分による近似で証明した。文献の加法性の引用には依存しない。

**証明済みの標準事実（`Paper/Section2/TowerDescent.lean`）**

- (S1) `fgLength_tensor`：有限長 `A_n` 加群 `V` で `λ*(Λ ⊗_{A_n} V) = ℓ_{A_n}(V) / p^{nh}`。
- (S2) `exists_descent`：`m_A` 冪ねじれで有限表示な `Λ` 加群は、ある段の有限長 `A_n` 加群から
  `Λ ⊗_{A_n} V` として得られる。

(2.2) `towerLengthFun_tensor` は (C1) と (S1) から導く（同じファイル）。 -/

variable [IsLocalRing A]

set_option linter.unusedVariables false in
/-- (C1) **有限生成加群で `λ_∞ = λ*`**。有限段の長さで証明済み。
CLMST Prop. 2.2.3 の有限生成一致を、Noether 局所環の条件で導く。
冪ねじれの引数は既存利用との互換性のため残す。新しい数値関数の証明には不要。 -/
theorem towerLengthFun_eq_fgLength [IsNoetherianRing A] [Fact p.Prime]
    (ht : ∀ i, t i ∈ maximalIdeal A)
    (N : Type u) [AddCommGroup N] [Module (Tower A t p) N]
    [Module.Finite (Tower A t p) N] (hN : IsPowTorsion (towerMaxIdeal A t p) N) :
    towerLengthFun A t p N = fgLength A t p N := by
  clear hN
  exact towerLengthFun_eq_fgLength_of_noetherian A t p ht N

/-- (C2) **加法性**。有限段の長さと近似から証明済み。
`m_A Λ` 冪ねじれ加群の短完全列 `0 → M₁ → M₂ → M₃ → 0` で `λ_∞(M₂) = λ_∞(M₁) + λ_∞(M₃)`。 -/
theorem towerLengthFun_add_of_exact [IsNoetherianRing A] [Fact p.Prime]
    (ht : ∀ i, t i ∈ maximalIdeal A) (M₁ M₂ M₃ : Type u) [AddCommGroup M₁]
    [Module (Tower A t p) M₁] [AddCommGroup M₂] [Module (Tower A t p) M₂] [AddCommGroup M₃]
    [Module (Tower A t p) M₃] (f : M₁ →ₗ[Tower A t p] M₂) (g : M₂ →ₗ[Tower A t p] M₃)
    (hf : Function.Injective f) (hg : Function.Surjective g) (hfg : Function.Exact f g)
    (hM₂ : IsPowTorsion (towerMaxIdeal A t p) M₂) :
    towerLengthFun A t p M₂ = towerLengthFun A t p M₁ + towerLengthFun A t p M₃ := by
  exact towerLengthFun_add_of_exact_of_noetherian A t p ht f g hf hg hfg hM₂

/-! ## 正規化長さの構造 -/

/-- **`λ_∞`**：塔 `Λ` の、`m_A Λ` 冪ねじれ加群の上の正規化長さ。値は `towerLengthFun`、加法性は
共通層で証明済み。 -/
noncomputable def towerLength [IsNoetherianRing A] [Fact p.Prime]
    (ht : ∀ i, t i ∈ maximalIdeal A) :
    NormalizedLength (Tower A t p) (towerMaxIdeal A t p) :=
  RootTowerLength.normalizedLength A t p ht

@[simp] lemma towerLength_len [IsNoetherianRing A] [Fact p.Prime]
    (ht : ∀ i, t i ∈ maximalIdeal A)
    (M : Type u) [AddCommGroup M] [Module (Tower A t p) M] :
    (towerLength A t p ht).len M = towerLengthFun A t p M := rfl

/-- **上限の性質 (2.3)**：`λ_∞(M) = sup{λ_∞(N) : N ⊆ M 有限生成}`。定義（`λ*` の上限）と、
有限生成加群で `λ_∞ = λ*` であること（`towerLengthFun_eq_fgLength`）から。 -/
theorem towerLength_hasSup [IsNoetherianRing A] [Fact p.Prime]
    (ht : ∀ i, t i ∈ maximalIdeal A) : (towerLength A t p ht).HasSup :=
  RootTowerLength.normalizedLength_hasSup A t p ht

end Section2

end SerrePositivity
