module

public import SerrePositivity.CommutativeAlgebra.Length.Euler
public import SerrePositivity.HomologicalAlgebra.TorFiniteLength
public import SerrePositivity.IntersectionMultiplicity.Basic
public import SerrePositivity.HomologicalAlgebra.Resolution.FiniteFree
public import SerrePositivity.IntersectionMultiplicity.Vanishing
public import SerrePositivity.CommutativeAlgebra.SupportDimension
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.Data.ENat.BigOperators
public import SerrePositivity.CommutativeAlgebra.Length.CommonResidueField

/-! # 交点重複度の加法性・デヴィサージュ・有限拡大

## 概要

交点重複度の左右の加法性（高次 Tor の消滅のもと長完全列の交代和から）、素因子による帰納法で正値性を素イデアル商へ帰着すること（デヴィサージュ）、素イデアル商を有限代数に取り替えたときの階数倍の公式 `chi_finite_extensions`（論文 Lemma 5.2 の最初の段階）を与える。

## 方針

第 2 変数は左導来関手の長完全列、第 1 変数は固定した第 2 変数の射影分解と平坦性から長完全列を作る。低次元の側は交点消滅定理 `intersectionVanishing_of_adams` で零になる。

## 規約

完備化や剰余体の変更は行わない。

## 使われ方

Paper の §5（Lemma 5.2）、`IntersectionMultiplicity/EqualCharZero/Positivity`。
-/

@[expose] public noncomputable section

universe u

section AdditivityPart

open CategoryTheory Limits MonoidalCategory TensorProduct

namespace SerrePositivity

variable {R : Type u} [CommRing R]

section noetherian

variable [IsNoetherianRing R]

/-- Noether 環上で、関係する Tor が高次で消えるときの交点重複度の第2変数に関する加法性。
中央のテンソル積の有限長性から両端の有限長性を台で判定し、Tor の長完全列の交代和を取る。 -/
theorem chi_add_right_of_eventually
    (M N₁ N₂ N₃ : Type u) [AddCommGroup M] [Module R M]
    [AddCommGroup N₁] [Module R N₁] [AddCommGroup N₂] [Module R N₂]
    [AddCommGroup N₃] [Module R N₃] [Module.Finite R M] [Module.Finite R N₁]
    [Module.Finite R N₂] [Module.Finite R N₃]
    (f : N₁ →ₗ[R] N₂) (g : N₂ →ₗ[R] N₃)
    (hf : Function.Injective f) (hg : Function.Surjective g) (he : Function.Exact f g)
    (h : Module.length R (M ⊗[R] N₂) ≠ ⊤)
    (z₁ : ∃ n, ∀ i, n < i → Subsingleton (TorModule R i M N₁))
    (z₂ : ∃ n, ∀ i, n < i → Subsingleton (TorModule R i M N₂))
    (z₃ : ∃ n, ∀ i, n < i → Subsingleton (TorModule R i M N₃)) :
    chi R M N₂ = chi R M N₁ + chi R M N₃ := by
  have h₂ := Module.length_ne_top_iff.mp h
  have h₁ : IsFiniteLength R (M ⊗[R] N₁) :=
    isFiniteLength_of_support_subset _ _ h₂ (by
      simp only [support_tensorProduct, Module.support_of_exact he hf hg]
      exact fun p hp => ⟨hp.1, Or.inl hp.2⟩)
  have h₃ : IsFiniteLength R (M ⊗[R] N₃) :=
    isFiniteLength_of_support_subset _ _ h₂ (by
      simp only [support_tensorProduct, Module.support_of_exact he hf hg]
      exact fun p hp => ⟨hp.1, Or.inr hp.2⟩)
  obtain ⟨α, β, δ, hab, hbd, hda, hb⟩ := torModule_longExact M f g hf hg he
  exact lengthEuler_finsum_longExact
    (fun i => ModuleCat.of R (TorModule R i M N₁))
    (fun i => ModuleCat.of R (TorModule R i M N₂))
    (fun i => ModuleCat.of R (TorModule R i M N₃))
    α β δ hab hbd hda hb
    (isFiniteLength_torModule M N₁ h₁) (isFiniteLength_torModule M N₂ h₂)
    (isFiniteLength_torModule M N₃ h₃) z₁ z₂ z₃

/-- Noether 環上で、関係する Tor が高次で消えるときの交点重複度の第1変数に関する加法性。
固定した第2変数の分解から作った長完全列に、長さの交代和の一般定理を適用する。 -/
theorem chi_add_left_of_eventually
    (M₁ M₂ M₃ N : Type u) [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂] [AddCommGroup M₃] [Module R M₃]
    [AddCommGroup N] [Module R N] [Module.Finite R M₁] [Module.Finite R M₂]
    [Module.Finite R M₃] [Module.Finite R N]
    (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃)
    (hf : Function.Injective f) (hg : Function.Surjective g) (he : Function.Exact f g)
    (h : Module.length R (M₂ ⊗[R] N) ≠ ⊤)
    (z₁ : ∃ n, ∀ i, n < i → Subsingleton (TorModule R i M₁ N))
    (z₂ : ∃ n, ∀ i, n < i → Subsingleton (TorModule R i M₂ N))
    (z₃ : ∃ n, ∀ i, n < i → Subsingleton (TorModule R i M₃ N)) :
    chi R M₂ N = chi R M₁ N + chi R M₃ N := by
  have h₂ := Module.length_ne_top_iff.mp h
  have h₁ : IsFiniteLength R (M₁ ⊗[R] N) :=
    isFiniteLength_of_support_subset _ _ h₂ (by
      simp only [support_tensorProduct, Module.support_of_exact he hf hg]
      exact fun p hp => ⟨Or.inl hp.1, hp.2⟩)
  have h₃ : IsFiniteLength R (M₃ ⊗[R] N) :=
    isFiniteLength_of_support_subset _ _ h₂ (by
      simp only [support_tensorProduct, Module.support_of_exact he hf hg]
      exact fun p hp => ⟨Or.inr hp.1, hp.2⟩)
  obtain ⟨α, β, δ, hab, hbd, hda, hb⟩ := torModule_longExact_left N f g hf hg he
  exact lengthEuler_finsum_longExact
    (fun i => ModuleCat.of R (TorModule R i M₁ N))
    (fun i => ModuleCat.of R (TorModule R i M₂ N))
    (fun i => ModuleCat.of R (TorModule R i M₃ N))
    α β δ hab hbd hda hb
    (isFiniteLength_torModule M₁ N h₁) (isFiniteLength_torModule M₂ N h₂)
    (isFiniteLength_torModule M₃ N h₃) z₁ z₂ z₃

end noetherian

section regular

variable [IsRegularLocalRing R]
/-- 有限生成な第2変数の有界有限自由分解から、高次 Tor の消滅を得る。
分解の存在だけを `regularResolution` から受け取り、消滅自体は一般の左導来関手の定理による。
第1変数には有限生成性を要求しない。 -/
theorem torModule_eventually_subsingleton (M N : Type u) [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module.Finite R N] :
    ∃ n, ∀ i, n < i → Subsingleton (TorModule R i M N) := by
  obtain ⟨F, ⟨hF⟩, ⟨a, b, hb⟩, _, _⟩ := regularResolution R N
  obtain ⟨n, hn⟩ := isZero_leftDerived_eventually_of_resolution
    (tensorLeft (ModuleCat.of R M)) hF a (fun i hi => hb i (Or.inl hi))
  exact ⟨n, fun i hi => ModuleCat.subsingleton_of_isZero (hn i hi)⟩

/-- 正則局所環上の交点重複度は第2変数の短完全列について加法的である。
中央のテンソル積は有限長とし、有界有限自由分解の存在から高次消滅を供給する。 -/
theorem chi_add_right
    (M N₁ N₂ N₃ : Type u) [AddCommGroup M] [Module R M]
    [AddCommGroup N₁] [Module R N₁] [AddCommGroup N₂] [Module R N₂]
    [AddCommGroup N₃] [Module R N₃] [Module.Finite R M] [Module.Finite R N₁]
    [Module.Finite R N₂] [Module.Finite R N₃]
    (f : N₁ →ₗ[R] N₂) (g : N₂ →ₗ[R] N₃)
    (hf : Function.Injective f) (hg : Function.Surjective g) (he : Function.Exact f g)
    (h : Module.length R (M ⊗[R] N₂) ≠ ⊤) :
    chi R M N₂ = chi R M N₁ + chi R M N₃ :=
  chi_add_right_of_eventually M N₁ N₂ N₃ f g hf hg he h
    (torModule_eventually_subsingleton M N₁) (torModule_eventually_subsingleton M N₂)
    (torModule_eventually_subsingleton M N₃)

/-- 正則局所環上の交点重複度は第1変数の短完全列について加法的である。
中央のテンソル積は有限長とし、有界有限自由分解の存在から高次消滅を供給する。 -/
theorem chi_add_left
    (M₁ M₂ M₃ N : Type u) [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂] [AddCommGroup M₃] [Module R M₃]
    [AddCommGroup N] [Module R N] [Module.Finite R M₁] [Module.Finite R M₂]
    [Module.Finite R M₃] [Module.Finite R N]
    (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃)
    (hf : Function.Injective f) (hg : Function.Surjective g) (he : Function.Exact f g)
    (h : Module.length R (M₂ ⊗[R] N) ≠ ⊤) :
    chi R M₂ N = chi R M₁ N + chi R M₃ N :=
  chi_add_left_of_eventually M₁ M₂ M₃ N f g hf hg he h
    (torModule_eventually_subsingleton M₁ N) (torModule_eventually_subsingleton M₂ N)
    (torModule_eventually_subsingleton M₃ N)

end regular

end SerrePositivity

end AdditivityPart

section DevissagePart

namespace SerrePositivity

open TensorProduct

variable {R : Type u} [CommRing R] [IsRegularLocalRing R]

/-- 第1変数の素イデアル商に対する正値性から、任意の有限生成第1変数へ移す。 -/
theorem chi_pos_of_prime_left
    (M N : Type u) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Finite R N]
    (hprime : ∀ (P : Ideal R) [P.IsPrime],
      Module.length R ((R ⧸ P) ⊗[R] N) ≠ ⊤ →
      ringKrullDim (R ⧸ P) + Module.supportDim R N = ringKrullDim R →
      0 < chi R (R ⧸ P) N)
    (hfin : Module.length R (M ⊗[R] N) ≠ ⊤)
    (hdim : Module.supportDim R M + Module.supportDim R N = ringKrullDim R) :
    0 < chi R M N := by
  have hforall : ∀ (L : Type u) [AddCommGroup L] [Module R L] [Module.Finite R L],
      Module.length R (L ⊗[R] N) ≠ ⊤ →
      Module.supportDim R L + Module.supportDim R N = ringKrullDim R → 0 < chi R L N := by
    intro L _ _ hL
    induction hL using IsNoetherianRing.induction_on_isQuotientEquivQuotientPrime R with
    | subsingleton L =>
        intro _ hd
        have hb : ringKrullDim R = ⊥ := by
          simpa only [Module.supportDim_eq_bot_of_subsingleton, WithBot.bot_add] using hd.symm
        exact (ringKrullDim_ne_bot (R := R) hb).elim
    | quotient L P e =>
        intro hf hd
        rw [chi_congr e (LinearEquiv.refl R N)]
        apply hprime P.asIdeal
        · rwa [← (TensorProduct.congr e (LinearEquiv.refl R N)).length_eq]
        · rwa [Module.supportDim_eq_of_equiv e, Module.supportDim_quotient_eq_ringKrullDim] at hd
    | exact L₁ L₂ L₃ f g hf hg he ih₁ ih₃ =>
        intro hlength hd
        have h₁ : Module.length R (L₁ ⊗[R] N) ≠ ⊤ := Module.length_ne_top_iff.mpr
          (isFiniteLength_of_support_subset _ _ (Module.length_ne_top_iff.mp hlength) (by
            simp only [support_tensorProduct, Module.support_of_exact he hf hg]
            exact fun p hp ↦ ⟨Or.inl hp.1, hp.2⟩))
        have h₃ : Module.length R (L₃ ⊗[R] N) ≠ ⊤ := Module.length_ne_top_iff.mpr
          (isFiniteLength_of_support_subset _ _ (Module.length_ne_top_iff.mp hlength) (by
            simp only [support_tensorProduct, Module.support_of_exact he hf hg]
            exact fun p hp ↦ ⟨Or.inr hp.1, hp.2⟩))
        have hd₁ : Module.supportDim R L₁ + Module.supportDim R N ≤ ringKrullDim R :=
          (add_le_add (Module.supportDim_le_of_injective f hf) le_rfl).trans hd.le
        have hd₃ : Module.supportDim R L₃ + Module.supportDim R N ≤ ringKrullDim R :=
          (add_le_add (Module.supportDim_le_of_surjective g hg) le_rfl).trans hd.le
        have hn₁ : 0 ≤ chi R L₁ N := by
          rcases hd₁.eq_or_lt with hd₁ | hd₁
          · exact (ih₁ h₁ hd₁).le
          · rw [intersectionVanishing_of_adams R L₁ N h₁ hd₁]
        have hn₃ : 0 ≤ chi R L₃ N := by
          rcases hd₃.eq_or_lt with hd₃ | hd₃
          · exact (ih₃ h₃ hd₃).le
          · rw [intersectionVanishing_of_adams R L₃ N h₃ hd₃]
        rw [chi_add_left L₁ L₂ L₃ N f g hf hg he hlength]
        rw [supportDim_eq_max_of_exact f g hf hg he] at hd
        rcases le_total (Module.supportDim R L₁) (Module.supportDim R L₃) with hle | hle
        · rw [max_eq_right hle] at hd
          exact add_pos_of_nonneg_of_pos hn₁ (ih₃ h₃ hd)
        · rw [max_eq_left hle] at hd
          exact add_pos_of_pos_of_nonneg (ih₁ h₁ hd) hn₃
  exact hforall M hfin hdim

/-- 両変数が素イデアル商である場合の正値性から、任意の有限生成加群の正値性へ移す。 -/
theorem chi_pos_of_prime_quotients
    (hprime : ∀ (P Q : Ideal R) [P.IsPrime] [Q.IsPrime],
      Module.length R ((R ⧸ P) ⊗[R] (R ⧸ Q)) ≠ ⊤ →
      ringKrullDim (R ⧸ P) + ringKrullDim (R ⧸ Q) = ringKrullDim R →
      0 < chi R (R ⧸ P) (R ⧸ Q))
    (M N : Type u) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Finite R N]
    (hfin : Module.length R (M ⊗[R] N) ≠ ⊤)
    (hdim : Module.supportDim R M + Module.supportDim R N = ringKrullDim R) :
    0 < chi R M N := by
  refine chi_pos_of_prime_left M N (fun P _ hf hd ↦ ?_) hfin hdim
  rw [chi_comm]
  refine chi_pos_of_prime_left N (R ⧸ P) (fun Q _ hq hqd ↦ ?_) ?_ ?_
  · exact hprime Q P hq (by simpa only [Module.supportDim_quotient_eq_ringKrullDim] using hqd)
  · rwa [← (TensorProduct.comm R (R ⧸ P) N).length_eq]
  · simpa only [Module.supportDim_quotient_eq_ringKrullDim, add_comm] using hd

end SerrePositivity

end DevissagePart

section FiniteExtensionPart

open scoped TensorProduct

namespace SerrePositivity

variable {R : Type u} [CommRing R]
variable {D D' E E' : Type u}
  [AddCommGroup D] [Module R D] [AddCommGroup D'] [Module R D']
  [AddCommGroup E] [Module R E] [AddCommGroup E'] [Module R E']

/-- 第 1 変数の階数因子を取り出す算術：`f : D^a → D'` について、加法性 `χ(D', E) = χ(D^a, E) + χ(coker f, E)`、
直和の評価 `χ(D^a, E) = a χ(D, E)`、余核の消滅 `χ(coker f, E) = 0` を等式として受け取り、
`χ(D', E) = a χ(D, E)` を得る。三つの等式を代入するだけで、`f` の単射性や消滅定理自体は扱わない。 -/
theorem chi_rank_factor_left_of_additivity_and_vanishing (a : ℕ)
    (f : (Fin a → D) →ₗ[R] D')
    (hadd : chi R D' E = chi R (Fin a → D) E + chi R (D' ⧸ LinearMap.range f) E)
    (hfree : chi R (Fin a → D) E = (a : ℤ) * chi R D E)
    (hvanish : chi R (D' ⧸ LinearMap.range f) E = 0) :
    chi R D' E = (a : ℤ) * chi R D E := by
  rw [hadd, hfree, hvanish, add_zero]

/-- 第 2 変数の階数因子を取り出す算術（`chi_rank_factor_left_of_additivity_and_vanishing` の第 2 変数版）。
第 1 変数とは独立に計算し、`Tor` の対称性は使わない。 -/
theorem chi_rank_factor_right_of_additivity_and_vanishing (a : ℕ)
    (f : (Fin a → E) →ₗ[R] E')
    (hadd : chi R D E' = chi R D (Fin a → E) + chi R D (E' ⧸ LinearMap.range f))
    (hfree : chi R D (Fin a → E) = (a : ℤ) * chi R D E)
    (hvanish : chi R D (E' ⧸ LinearMap.range f) = 0) :
    chi R D E' = (a : ℤ) * chi R D E := by
  rw [hadd, hfree, hvanish, add_zero]

/-- 二つの変数の階数比較を合成する：`χ(D', E') = a_D χ(D, E')` と `χ(D, E') = a_E χ(D, E)` から
`χ(D', E') = a_D a_E χ(D, E)`。 -/
theorem chi_rank_factors (aD aE : ℕ)
    (hD : chi R D' E' = (aD : ℤ) * chi R D E')
    (hE : chi R D E' = (aE : ℤ) * chi R D E) :
    chi R D' E' = (aD : ℤ) * aE * chi R D E := by
  rw [hD, hE, mul_assoc]

/-- `WithBot ℕ∞` 値の次元について、`x < a` なら `x + b < a + b`（`a`、`b` は自然数）。零加群の次元 `⊥` も
含めて成り立つ。`dim coker + dim U < dim R` を作るのに使う。 -/
lemma dimension_add_nat_lt {x : WithBot ℕ∞} {a b : ℕ}
    (hx : x < (a : WithBot ℕ∞)) : x + (b : WithBot ℕ∞) < ((a + b : ℕ) : WithBot ℕ∞) := by
  cases x with
  | bot => simp
  | coe x =>
    have h : x < (a : ℕ∞) := by exact_mod_cast hx
    have h' := (ENat.add_lt_add_iff_right (ENat.natCast_ne_top b)).mpr h
    exact_mod_cast h'

/-- `WithBot ℕ∞` 値の次元について、`x + 1 ≤ n`（`n` は自然数）なら `x < n`。零加群の次元 `⊥` も含めて
成り立つ。`exists_genericBasis` の評価 `dim coker + 1 ≤ dim R/P` を狭義不等式に直すのに使う。 -/
lemma dimension_lt_of_add_one_le_nat {x : WithBot ℕ∞} {n : ℕ}
    (hx : x + 1 ≤ (n : WithBot ℕ∞)) : x < n := by
  cases x with
  | bot => simp
  | coe x =>
    have hx' : x + 1 ≤ (n : ℕ∞) := by exact_mod_cast hx
    have hfin : x ≠ ⊤ := by intro h; simp [h] at hx'
    lift x to ℕ using hfin
    exact_mod_cast (show x < n by exact_mod_cast hx')

section additivity

variable [IsRegularLocalRing R]

/-- 第 1 変数の有限直和の公式 `χ(M^n, N) = n · χ(M, N)`（`M ⊗ N` が有限長のとき）。`n` についての帰納法で、
分裂短完全列 `0 → M^n → M^{n+1} → M → 0`（先頭成分への射影）に加法性 `add_left` を使う。各段階で
要るテンソル積の有限長性は、`M^{n+1} ⊗ N ≅ (M ⊗ N)^{n+1}` から。 -/
theorem chi_pi_left_of_additivity
    (M N : Type u) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Finite R N]
    (h : Module.length R (M ⊗[R] N) ≠ ⊤) :
    ∀ n : ℕ, chi R (Fin n → M) N = (n : ℤ) * chi R M N := by
  intro n
  induction n with
  | zero =>
    have he : Function.Exact (LinearMap.id : (Fin 0 → M) →ₗ[R] (Fin 0 → M))
        (LinearMap.id : (Fin 0 → M) →ₗ[R] (Fin 0 → M)) := by
      intro x
      exact ⟨fun _ ↦ ⟨x, rfl⟩, fun _ ↦ Subsingleton.elim _ _⟩
    have hh := chi_add_left (Fin 0 → M) (Fin 0 → M) (Fin 0 → M) N
      LinearMap.id LinearMap.id Function.injective_id Function.surjective_id he
      (by simp [Module.length_eq_zero])
    simpa using (show chi R (Fin 0 → M) N = 0 by omega)
  | succ n ih =>
    let f : (Fin n → M) →ₗ[R] (Fin (n + 1) → M) :=
      LinearMap.pi (fun j ↦ Fin.cases 0 (fun k ↦ LinearMap.proj k) j)
    let g : (Fin (n + 1) → M) →ₗ[R] M := LinearMap.proj 0
    have hf : Function.Injective f := by
      intro x y h
      funext k
      exact congrFun h k.succ
    have hg : Function.Surjective g := fun x ↦ ⟨fun _ ↦ x, rfl⟩
    have he : Function.Exact f g := by
      intro x
      constructor
      · intro hx
        refine ⟨fun k ↦ x k.succ, ?_⟩
        funext j
        refine Fin.cases ?_ (fun k ↦ ?_) j
        · exact hx.symm
        · rfl
      · rintro ⟨y, rfl⟩
        rfl
    have hfin : Module.length R ((Fin (n + 1) → M) ⊗[R] N) ≠ ⊤ := by
      rw [(TensorProduct.piLeft R N (fun _ : Fin (n + 1) ↦ M)).length_eq,
        Module.length_pi_of_fintype]
      exact ENat.sum_ne_top.mpr (fun _ _ ↦ h)
    rw [chi_add_left _ _ _ _ f g hf hg he hfin, ih]
    push_cast
    ring

/-- 第 2 変数の有限直和の公式 `χ(M, N^n) = n · χ(M, N)`（`chi_pi_left_of_additivity` の第 2 変数版、
`add_right` を使う）。第 1 変数の公式や `Tor` の対称性には依存しない。 -/
theorem chi_pi_right_of_additivity
    (M N : Type u) [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [Module.Finite R M] [Module.Finite R N]
    (h : Module.length R (M ⊗[R] N) ≠ ⊤) :
    ∀ n : ℕ, chi R M (Fin n → N) = (n : ℤ) * chi R M N := by
  intro n
  induction n with
  | zero =>
    have he : Function.Exact (LinearMap.id : (Fin 0 → N) →ₗ[R] (Fin 0 → N))
        (LinearMap.id : (Fin 0 → N) →ₗ[R] (Fin 0 → N)) := by
      intro x
      exact ⟨fun _ ↦ ⟨x, rfl⟩, fun _ ↦ Subsingleton.elim _ _⟩
    have hh := chi_add_right M (Fin 0 → N) (Fin 0 → N) (Fin 0 → N)
      LinearMap.id LinearMap.id Function.injective_id Function.surjective_id he
      (by simp [Module.length_eq_zero])
    simpa using (show chi R M (Fin 0 → N) = 0 by omega)
  | succ n ih =>
    let f : (Fin n → N) →ₗ[R] (Fin (n + 1) → N) :=
      LinearMap.pi (fun j ↦ Fin.cases 0 (fun k ↦ LinearMap.proj k) j)
    let g : (Fin (n + 1) → N) →ₗ[R] N := LinearMap.proj 0
    have hf : Function.Injective f := by
      intro x y h
      funext k
      exact congrFun h k.succ
    have hg : Function.Surjective g := fun x ↦ ⟨fun _ ↦ x, rfl⟩
    have he : Function.Exact f g := by
      intro x
      constructor
      · intro hx
        refine ⟨fun k ↦ x k.succ, ?_⟩
        funext j
        refine Fin.cases ?_ (fun k ↦ ?_) j
        · exact hx.symm
        · rfl
      · rintro ⟨y, rfl⟩
        rfl
    have hfin : Module.length R (M ⊗[R] (Fin (n + 1) → N)) ≠ ⊤ := by
      rw [(TensorProduct.piRight R R M (fun _ : Fin (n + 1) ↦ N)).length_eq,
        Module.length_pi_of_fintype]
      exact ENat.sum_ne_top.mpr (fun _ _ ↦ h)
    rw [chi_add_right _ _ _ _ f g hf hg he hfin, ih]
    push_cast
    ring

end additivity

section extension

variable [IsRegularLocalRing R]

/-- **有限拡大による階数倍**：正則局所環 `R` の素イデアル `P`、`Q` で `√(P + Q) = m_R`、
`dim R/P + dim R/Q = dim R` なるものと、有限代数 `T/(R/P)`、`U/(R/Q)`（`U` の階数は正）について
`χ^R(T, U) = rank_{R/P} T · rank_{R/Q} U · χ^R(R/P, R/Q)`。

証明：`exists_genericBasis` で `(R/P)^a ↪ T`、`(R/Q)^b ↪ U` をとる。余核の台の次元はそれぞれ
`dim R/P`、`dim R/Q` より真に小さいので、`U` の次元（`supportDim_of_quotient_rank_pos` で `dim R/Q`）
あるいは `R/P` の次元と足すと `dim R` 未満になり、消滅定理 `intersectionVanishing` で
余核の寄与が消える。各テンソル積の有限長性は `length_tensorProduct_ne_top_of_annihilator` から。
第 1 変数、第 2 変数の順に `chi_rank_factor_*` を適用し、`chi_rank_factors` で合成する。 -/
theorem chi_finite_extensions
    (P Q : Ideal R) [P.IsPrime] [Q.IsPrime]
    (T U : Type u) [CommRing T] [Algebra R T] [Algebra (R ⧸ P) T]
    [IsScalarTower R (R ⧸ P) T] [Module.Finite R T] [Module.Finite (R ⧸ P) T]
    [CommRing U] [Algebra R U] [Algebra (R ⧸ Q) U]
    [IsScalarTower R (R ⧸ Q) U] [Module.Finite R U] [Module.Finite (R ⧸ Q) U]
    (hU : 0 < Module.finrank (R ⧸ Q) U)
    (hprimary : (P ⊔ Q).radical = IsLocalRing.maximalIdeal R)
    (h l : ℕ) (hP : ringKrullDim (R ⧸ P) = h) (hQ : ringKrullDim (R ⧸ Q) = l)
    (hsum : ((h + l : ℕ) : WithBot ℕ∞) = ringKrullDim R) :
    chi R T U = (Module.finrank (R ⧸ P) T : ℤ) * Module.finrank (R ⧸ Q) U *
      chi R (R ⧸ P) (R ⧸ Q) := by
  have annT := quotient_action_annihilator P T
  have annU := quotient_action_annihilator Q U
  have annD := quotient_action_annihilator P (R ⧸ P)
  have annE := quotient_action_annihilator Q (R ⧸ Q)
  have finTU := length_tensorProduct_ne_top_of_annihilator P Q T U annT annU hprimary
  have finDU := length_tensorProduct_ne_top_of_annihilator P Q (R ⧸ P) U annD annU hprimary
  have finDE := length_tensorProduct_ne_top_of_annihilator P Q (R ⧸ P) (R ⧸ Q) annD annE hprimary
  obtain ⟨f, hf, hC⟩ := exists_genericBasis P T
  obtain ⟨g, hg, hK⟩ := exists_genericBasis Q U
  have hC : Module.supportDim R (T ⧸ LinearMap.range f) < (h : WithBot ℕ∞) := by
    rw [hP] at hC
    exact dimension_lt_of_add_one_le_nat hC
  have hK : Module.supportDim R (U ⧸ LinearMap.range g) < (l : WithBot ℕ∞) := by
    rw [hQ] at hK
    exact dimension_lt_of_add_one_le_nat hK
  have finCU := length_tensorProduct_ne_top_of_annihilator P Q (T ⧸ LinearMap.range f) U
    (annT.trans ((Submodule.mkQ _).annihilator_le_of_surjective (Submodule.mkQ_surjective _))) annU hprimary
  have finDK := length_tensorProduct_ne_top_of_annihilator P Q (R ⧸ P) (U ⧸ LinearMap.range g)
    annD (annU.trans ((Submodule.mkQ _).annihilator_le_of_surjective (Submodule.mkQ_surjective _))) hprimary
  have dimU : Module.supportDim R U = (l : WithBot ℕ∞) := by
    rw [supportDim_of_quotient_rank_pos Q U hU, hQ]
  have dimD : Module.supportDim R (R ⧸ P) = (h : WithBot ℕ∞) := by
    rw [Module.supportDim_quotient_eq_ringKrullDim, hP]
  have vanishC : chi R (T ⧸ LinearMap.range f) U = 0 :=
    intersectionVanishing_of_adams R _ _ finCU (by
      rw [dimU, ← hsum]
      exact dimension_add_nat_lt hC)
  have vanishK : chi R (R ⧸ P) (U ⧸ LinearMap.range g) = 0 :=
    intersectionVanishing_of_adams R _ _ finDK (by
      rw [dimD, add_comm, ← hsum, Nat.add_comm h l]
      exact dimension_add_nat_lt hK)
  have left := chi_rank_factor_left_of_additivity_and_vanishing
    (Module.finrank (R ⧸ P) T) f
    (chi_add_left _ _ _ _ f (LinearMap.range f).mkQ hf
      (Submodule.mkQ_surjective _) (LinearMap.exact_map_mkQ_range f) finTU)
    (chi_pi_left_of_additivity _ _ finDU _) vanishC
  have right := chi_rank_factor_right_of_additivity_and_vanishing
    (Module.finrank (R ⧸ Q) U) g
    (chi_add_right _ _ _ _ g (LinearMap.range g).mkQ hg
      (Submodule.mkQ_surjective _) (LinearMap.exact_map_mkQ_range g) finDU)
    (chi_pi_right_of_additivity (R ⧸ P) (R ⧸ Q) finDE _) vanishK
  exact chi_rank_factors _ _ left right

end extension

end SerrePositivity

end FiniteExtensionPart
