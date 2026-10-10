module

public import SerrePositivity.Paper.Section2.Tower
public import SerrePositivity.PerfectComplex.SupProperty
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.FiniteLength

/-!
# 塔の正規化長さ `λ_∞`（論文 Lemma 2.3 (b)）

## 概要

塔 `Λ = Tower A t p` の加群の正規化長さ `λ_∞` を、CLMST Definition 2.2.1（Faltings の正規化長さ）
の三段階どおりに定義する。`s(n) = p^{nh}`。

1. 有限表示の段階 `λ**`（`presentedLength`）：段 `n` と有限長 `A_n` 加群 `V` で
   `M ≃ Λ ⊗_{A_n} V` となるもの全体にわたる `ℓ_{A_n}(V) / s(n)` の下限。
2. 有限生成の段階 `λ*`（`fgLength`）：有限表示な全射 `P ↠ N` にわたる `λ**(P)` の下限。
3. 一般（`towerLengthFun`）：`λ_∞(M) = sup{λ*(N) : N ⊆ M 有限生成}`（論文 (2.3)）。

定義から出る性質（零加群で `0`、同型不変）はここで証明し、Lemma 2.3 (b) の本体

- 有限生成加群で `λ_∞ = λ*`（CLMST Prop. 2.2.3、Gabber–Ramero Lemma 14.5.74）、
- (2.2) 有限段の公式 `λ_∞(Λ ⊗_{A_n} V) = ℓ_{A_n}(V) / p^{nh}`、
- `m_A` 冪ねじれで有限表示な加群の段への降下、
- `m_A` 冪ねじれ加群の短完全列での加法性（Faltings [9, Appendix 2]、Gabber–Ramero 14.5.75）

は引用（`sorry`）とする。これで `towerLength : NormalizedLength Λ (m_A Λ)` ができ、上限の性質
`towerLength_hasSup` が従う。Lemma 2.4 と Theorem 2.5 はこの `λ_∞` について述べる。

## 論文との差

- 論文（CLMST）は `λ**` を「ある降下 `M ≅ V_n ⊗ Λ` の値」として定め、降下の取り方によらないことを
  示す。ここでは下限で定義するので、よらないことは「有限段の公式」の主張に含まれる。
- 混標数の完備化 `A_∞` は扱わない（論文 Lemma 2.3 の最後の主張で非完備の塔に制限してよい）。
-/

@[expose] public section

universe u

open IsLocalRing TensorProduct
open scoped ENNReal

namespace SerrePositivity

namespace Section2

variable (A : Type u) [CommRing A] {h : ℕ} (t : Fin h → A) (p : ℕ)

/-- 1. 有限表示の段階 `λ**`：段 `n` と有限長 `A_n` 加群 `V` で `M ≃ Λ ⊗_{A_n} V` となるもの全体に
わたる `ℓ_{A_n}(V) / p^{nh}` の下限。該当がなければ `⊤`。 -/
noncomputable def presentedLength (M : Type u) [AddCommGroup M] [Module (Tower A t p) M] :
    ℝ≥0∞ :=
  ⨅ (n : ℕ) (V : Type u) (_ : AddCommGroup V) (_ : Module (TowerStage A t p n) V)
    (_ : IsFiniteLength (TowerStage A t p n) V)
    (_ : Nonempty (M ≃ₗ[Tower A t p] Tower A t p ⊗[TowerStage A t p n] V)),
    (Module.length (TowerStage A t p n) V : ℝ≥0∞) / (stageRank h p n : ℝ≥0∞)

/-- 2. 有限生成の段階 `λ*`：有限表示な全射 `P ↠ N` にわたる `λ**(P)` の下限。 -/
noncomputable def fgLength (N : Type u) [AddCommGroup N] [Module (Tower A t p) N] : ℝ≥0∞ :=
  ⨅ (P : Type u) (_ : AddCommGroup P) (_ : Module (Tower A t p) P)
    (_ : Module.FinitePresentation (Tower A t p) P) (f : P →ₗ[Tower A t p] N)
    (_ : Function.Surjective f), presentedLength A t p P

/-- 3. 一般の加群：`λ_∞(M) = sup{λ*(N) : N ⊆ M 有限生成}`（論文 (2.3)）。 -/
noncomputable def towerLengthFun (M : Type u) [AddCommGroup M] [Module (Tower A t p) M] :
    ℝ≥0∞ :=
  ⨆ (N : Submodule (Tower A t p) M) (_ : N.FG), fgLength A t p N

variable {A t p}

/-! ## 定義から出る性質 -/

/-- `λ**` は線形同型で単調（したがって不変）。 -/
lemma presentedLength_le_of_equiv {M M' : Type u} [AddCommGroup M] [Module (Tower A t p) M]
    [AddCommGroup M'] [Module (Tower A t p) M'] (e : M ≃ₗ[Tower A t p] M') :
    presentedLength A t p M ≤ presentedLength A t p M' := by
  refine le_iInf fun n ↦ le_iInf fun V ↦ le_iInf fun i₁ ↦ le_iInf fun i₂ ↦ le_iInf fun hV ↦
    le_iInf fun ⟨e'⟩ ↦ ?_
  exact iInf_le_of_le n (iInf_le_of_le V (iInf_le_of_le i₁ (iInf_le_of_le i₂ (iInf_le_of_le hV
    (iInf_le_of_le ⟨e.trans e'⟩ le_rfl)))))

lemma presentedLength_congr {M M' : Type u} [AddCommGroup M] [Module (Tower A t p) M]
    [AddCommGroup M'] [Module (Tower A t p) M'] (e : M ≃ₗ[Tower A t p] M') :
    presentedLength A t p M = presentedLength A t p M' :=
  le_antisymm (presentedLength_le_of_equiv e) (presentedLength_le_of_equiv e.symm)

/-- `λ*` は線形同型で単調。 -/
lemma fgLength_le_of_equiv {N N' : Type u} [AddCommGroup N] [Module (Tower A t p) N]
    [AddCommGroup N'] [Module (Tower A t p) N'] (e : N ≃ₗ[Tower A t p] N') :
    fgLength A t p N ≤ fgLength A t p N' := by
  refine le_iInf fun P ↦ le_iInf fun i₁ ↦ le_iInf fun i₂ ↦ le_iInf fun hP ↦ le_iInf fun f ↦
    le_iInf fun hf ↦ ?_
  exact iInf_le_of_le P (iInf_le_of_le i₁ (iInf_le_of_le i₂ (iInf_le_of_le hP
    (iInf_le_of_le (e.symm.toLinearMap.comp f) (iInf_le_of_le (e.symm.surjective.comp hf)
      le_rfl)))))

lemma fgLength_congr {N N' : Type u} [AddCommGroup N] [Module (Tower A t p) N]
    [AddCommGroup N'] [Module (Tower A t p) N'] (e : N ≃ₗ[Tower A t p] N') :
    fgLength A t p N = fgLength A t p N' :=
  le_antisymm (fgLength_le_of_equiv e) (fgLength_le_of_equiv e.symm)

/-- `λ_∞` は線形同型で単調。 -/
lemma towerLengthFun_le_of_equiv {M M' : Type u} [AddCommGroup M] [Module (Tower A t p) M]
    [AddCommGroup M'] [Module (Tower A t p) M'] (e : M ≃ₗ[Tower A t p] M') :
    towerLengthFun A t p M ≤ towerLengthFun A t p M' := by
  refine iSup₂_le fun N hN ↦ le_iSup₂_of_le (N.map (e : M →ₗ[Tower A t p] M')) (hN.map _) ?_
  exact le_of_eq (fgLength_congr (Submodule.equivMapOfInjective _ e.injective N))

lemma towerLengthFun_congr {M M' : Type u} [AddCommGroup M] [Module (Tower A t p) M]
    [AddCommGroup M'] [Module (Tower A t p) M'] (e : M ≃ₗ[Tower A t p] M') :
    towerLengthFun A t p M = towerLengthFun A t p M' :=
  le_antisymm (towerLengthFun_le_of_equiv e) (towerLengthFun_le_of_equiv e.symm)

/-- 一方が零加群なら、テンソル積も零加群。 -/
lemma subsingleton_tensorProduct_of_right {R M N : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] [Subsingleton N] :
    Subsingleton (M ⊗[R] N) := by
  refine ⟨fun x y ↦ ?_⟩
  have h0 : ∀ z : M ⊗[R] N, z = 0 := fun z ↦
    TensorProduct.inductionOn z (fun c m ↦ by rw [Subsingleton.elim m 0, TensorProduct.tmul_zero])
      (fun x y hx hy ↦ by rw [hx, hy, add_zero])
  rw [h0 x, h0 y]

/-- 零加群の `λ**` は `0`：段 `0`、`V = 0` で `ℓ(V)/1 = 0`。 -/
lemma presentedLength_eq_zero_of_subsingleton (M : Type u) [AddCommGroup M]
    [Module (Tower A t p) M] [Subsingleton M] : presentedLength A t p M = 0 := by
  refine le_antisymm ?_ zero_le
  let V : Type u := (⊥ : Submodule (TowerStage A t p 0) (TowerStage A t p 0))
  have : Subsingleton (Tower A t p ⊗[TowerStage A t p 0] V) :=
    subsingleton_tensorProduct_of_right
  refine iInf_le_of_le 0 (iInf_le_of_le V (iInf_le_of_le _ (iInf_le_of_le _
    (iInf_le_of_le IsFiniteLength.of_subsingleton
      (iInf_le_of_le ⟨LinearEquiv.ofSubsingleton _ _⟩ (le_of_eq ?_))))))
  rw [Module.length_eq_zero (M := V)]
  simp

/-- 零加群の `λ*` は `0`。 -/
lemma fgLength_eq_zero_of_subsingleton (N : Type u) [AddCommGroup N] [Module (Tower A t p) N]
    [Subsingleton N] : fgLength A t p N = 0 := by
  refine le_antisymm ?_ zero_le
  refine iInf_le_of_le N (iInf_le_of_le _ (iInf_le_of_le _ (iInf_le_of_le inferInstance
    (iInf_le_of_le LinearMap.id (iInf_le_of_le Function.surjective_id (le_of_eq ?_))))))
  exact presentedLength_eq_zero_of_subsingleton N

/-- 零加群の `λ_∞` は `0`。 -/
lemma towerLengthFun_eq_zero_of_subsingleton (M : Type u) [AddCommGroup M]
    [Module (Tower A t p) M] [Subsingleton M] : towerLengthFun A t p M = 0 := by
  refine le_antisymm (iSup₂_le fun N _ ↦ le_of_eq ?_) zero_le
  exact fgLength_eq_zero_of_subsingleton N

/-! ## Lemma 2.3 (b)：引用する性質（`sorry`） -/

variable (A t p) [IsLocalRing A]

/-- **有限生成加群で `λ_∞ = λ*`**（CLMST Prop. 2.2.3 の本体、Gabber–Ramero Lemma 14.5.74）。
`m_A` 冪ねじれで有限生成な `N` について `sup{λ*(N') : N' ⊆ N 有限生成} = λ*(N)`。 -/
theorem towerLengthFun_eq_fgLength (N : Type u) [AddCommGroup N] [Module (Tower A t p) N]
    [Module.Finite (Tower A t p) N] (hN : IsPowTorsion (towerMaxIdeal A t p) N) :
    towerLengthFun A t p N = fgLength A t p N := by
  sorry

/-- **(2.2) 有限段の公式**：有限長 `A_n` 加群 `V` について `λ_∞(Λ ⊗_{A_n} V) = ℓ_{A_n}(V) / p^{nh}`。
段を上げても値が変わらないこと（`Λ` の平坦性と遷移写像の自由ランク）を含む。 -/
theorem towerLengthFun_tensor (n : ℕ) (V : Type u) [AddCommGroup V]
    [Module (TowerStage A t p n) V] (hV : IsFiniteLength (TowerStage A t p n) V) :
    towerLengthFun A t p (Tower A t p ⊗[TowerStage A t p n] V) =
      (Module.length (TowerStage A t p n) V : ℝ≥0∞) / (stageRank h p n : ℝ≥0∞) := by
  sorry

/-- **降下**：`m_A` 冪ねじれで有限表示な `Λ` 加群は、ある段 `n` の有限長 `A_n` 加群 `V` から
`Λ ⊗_{A_n} V` として得られる（有限個の生成元と関係式はどれかの段に入る）。 -/
theorem exists_descent (M : Type u) [AddCommGroup M] [Module (Tower A t p) M]
    [Module.FinitePresentation (Tower A t p) M] (hM : IsPowTorsion (towerMaxIdeal A t p) M) :
    ∃ (n : ℕ) (V : Type u) (_ : AddCommGroup V) (_ : Module (TowerStage A t p n) V),
      IsFiniteLength (TowerStage A t p n) V ∧
        Nonempty (M ≃ₗ[Tower A t p] Tower A t p ⊗[TowerStage A t p n] V) := by
  sorry

/-- **加法性**（Faltings [9, Appendix 2]、Gabber–Ramero Thm 14.5.75、CLMST Prop. 2.2.6(a)）：
`m_A` 冪ねじれ加群の短完全列 `0 → M₁ → M₂ → M₃ → 0` で `λ_∞(M₂) = λ_∞(M₁) + λ_∞(M₃)`。 -/
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
theorem towerLength_hasSup : (towerLength A t p).HasSup := by
  intro M _ _ hM
  rw [towerLength_len, towerLengthFun]
  refine le_antisymm (iSup₂_le fun N hN ↦ le_iSup₂_of_le N hN (le_of_eq ?_))
    (iSup₂_le fun N hN ↦ le_iSup₂_of_le N hN (le_of_eq ?_))
  · have : Module.Finite (Tower A t p) N := Module.Finite.iff_fg.mpr hN
    rw [towerLength_len, towerLengthFun_eq_fgLength A t p N (hM.submodule N)]
  · have : Module.Finite (Tower A t p) N := Module.Finite.iff_fg.mpr hN
    rw [towerLength_len, towerLengthFun_eq_fgLength A t p N (hM.submodule N)]

end Section2

end SerrePositivity
