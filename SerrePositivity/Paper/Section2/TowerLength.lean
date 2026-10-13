module

public import SerrePositivity.LengthAlgebra.RootTowerLength.Defs
public import SerrePositivity.LengthAlgebra.RootTowerLength.FiniteGeneration
public import SerrePositivity.PerfectComplex.QuotientLength
public import SerrePositivity.PerfectComplex.SupProperty

/-! # 塔の正規化長さの引用と構造

三つの数値関数と、その零・同型不変性は
`LengthAlgebra/RootTowerLength/Defs.lean` に抽出した。
有限生成一致 C1 は、Noether 局所環・素数・座標の極大イデアル所属を仮定して
有限段の長さから証明する。C2（加法性）は既存の引用を保持し、
`NormalizedLength` を組み立てる。上限の性質には証明済み C1 を使う。
C2 の原典の標準基底と現在の署名の一般性の差は、CLMST 移行時に別途監査する。

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

/-! ## Lemma 2.3 (b)：引用する性質と標準事実

**有限生成一致の証明と、加法性の引用**

- (C1) `towerLengthFun_eq_fgLength`：有限生成で `m_A` 冪ねじれの加群で `λ_∞ = λ*`。
  CLMST（Cai–Lee–Ma–Schwede–Tucker, arXiv:2209.04046v4）Proposition 2.2.3 の主張
  「`λ_∞` は well defined で、有限生成加群では `λ_∞^*` と一致する」。その証明は
  Gabber–Ramero, *Foundations for almost ring theory*, Lemma 14.5.74（または Shimomoto, Lemma 2.2）
  に関連する。ここでは標準基底より弱い Noether 局所環の条件で証明した。
  内容は「有限生成 `N` の有限生成部分加群 `N'` について `λ*(N') ≤ λ*(N)`」
  （`λ*` の単調性）で、これが (2.3) の上限が `λ*` 自身に戻ることを保証する。
- (C2) `towerLengthFun_add_of_exact`：`m_A` 冪ねじれ加群の短完全列での加法性。
  CLMST Proposition 2.2.6(a)。証明は Faltings, *Almost étale extensions*, Astérisque 279 (2002),
  Appendix 2 の補題（Gabber–Ramero Theorem 14.5.75、Shimomoto Prop. 2.8 も同じ主張）。

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

/-- (C2) **加法性**。引用：CLMST Prop. 2.2.6(a)、Faltings Appendix 2、Gabber–Ramero Thm 14.5.75。
`m_A Λ` 冪ねじれ加群の短完全列 `0 → M₁ → M₂ → M₃ → 0` で `λ_∞(M₂) = λ_∞(M₁) + λ_∞(M₃)`。 -/
theorem towerLengthFun_add_of_exact (M₁ M₂ M₃ : Type u) [AddCommGroup M₁]
    [Module (Tower A t p) M₁] [AddCommGroup M₂] [Module (Tower A t p) M₂] [AddCommGroup M₃]
    [Module (Tower A t p) M₃] (f : M₁ →ₗ[Tower A t p] M₂) (g : M₂ →ₗ[Tower A t p] M₃)
    (hf : Function.Injective f) (hg : Function.Surjective g) (hfg : Function.Exact f g)
    (hM₂ : IsPowTorsion (towerMaxIdeal A t p) M₂) :
    towerLengthFun A t p M₂ = towerLengthFun A t p M₁ + towerLengthFun A t p M₃ := by
  sorry

/-! ## 正規化長さの構造 -/

/-- **`λ_∞`**：塔 `Λ` の、`m_A Λ` 冪ねじれ加群の上の正規化長さ。値は `towerLengthFun`、加法性は
`towerLengthFun_add_of_exact`（引用）。 -/
noncomputable def towerLength : NormalizedLength (Tower A t p) (towerMaxIdeal A t p) where
  len M _ _ := towerLengthFun A t p M
  len_eq_zero_of_subsingleton M _ _ _ := towerLengthFun_eq_zero_of_subsingleton M
  len_congr _ _ _ _ _ _ e := towerLengthFun_congr e
  len_add_of_exact M₁ M₂ M₃ _ _ _ _ _ _ f g hf hg hfg hM₂ :=
    towerLengthFun_add_of_exact A t p M₁ M₂ M₃ f g hf hg hfg hM₂

@[simp] lemma towerLength_len (M : Type u) [AddCommGroup M] [Module (Tower A t p) M] :
    (towerLength A t p).len M = towerLengthFun A t p M := rfl

/-- **上限の性質 (2.3)**：`λ_∞(M) = sup{λ_∞(N) : N ⊆ M 有限生成}`。定義（`λ*` の上限）と、
有限生成加群で `λ_∞ = λ*` であること（`towerLengthFun_eq_fgLength`）から。 -/
theorem towerLength_hasSup [IsNoetherianRing A] [Fact p.Prime]
    (ht : ∀ i, t i ∈ maximalIdeal A) : (towerLength A t p).HasSup := by
  intro M _ _ hM
  rw [towerLength_len, towerLengthFun]
  refine le_antisymm (iSup₂_le fun N hN ↦ le_iSup₂_of_le N hN (le_of_eq ?_))
    (iSup₂_le fun N hN ↦ le_iSup₂_of_le N hN (le_of_eq ?_))
  · have : Module.Finite (Tower A t p) N := Module.Finite.iff_fg.mpr hN
    rw [towerLength_len, towerLengthFun_eq_fgLength A t p ht N (hM.submodule N)]
  · have : Module.Finite (Tower A t p) N := Module.Finite.iff_fg.mpr hN
    rw [towerLength_len, towerLengthFun_eq_fgLength A t p ht N (hM.submodule N)]

end Section2

end SerrePositivity
