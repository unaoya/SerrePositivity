module

public import SerrePositivity.IntersectionMultiplicity.Additivity
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.Data.ENat.BigOperators
public import SerrePositivity.IntersectionMultiplicity.AdamsVanishingAll
public import SerrePositivity.CommutativeAlgebra.Length.CommonResidueField
public import SerrePositivity.CommutativeAlgebra.SupportDimension

/-!
# 有限拡大による交点重複度の階数倍

## 概要

論文 Lemma 5.2 の証明の最初の段階：素イデアル商 `R/P`、`R/Q` を、その上の有限代数 `T`、`U` に
取り替えたときの交点重複度の変化を記述する。結論は

  `χ^R(T, U) = rank_{R/P} T · rank_{R/Q} U · χ^R(R/P, R/Q)`

（`chi_finite_extensions`）。§5 では `T = D`（`R/P` の正規化の有限拡大）、`U = E` にとる。

## 方針

`T` は整域 `R/P` 上の有限生成加群なので、一般点（分数体）での基底をとると自由部分加群
`(R/P)^a ↪ T`（`a = rank_{R/P} T`）があり、余核 `T/(R/P)^a` はねじれ加群なので台の次元が `dim R/P`
より真に小さい（`CommutativeAlgebra/LocalAlgebra.lean` の `exists_genericBasis`）。短完全列
`0 → (R/P)^a → T → coker → 0` に `χ` の加法性を使うと `χ(T, U) = a · χ(R/P, U) + χ(coker, U)`、そして
`dim coker + dim U < dim R` なので Roberts–Gillet–Soulé の消滅定理により `χ(coker, U) = 0`。
第 2 変数も同様に処理する。

## 内容

- 前半：加法性・直和の評価・余核の消滅を等式として受け取る算術的な整理
  （`chi_rank_factor_left/right_of_additivity_and_vanishing`、`chi_rank_factors`）と、`WithBot ℕ∞` 値の
  次元についての不等式の補題。
- 有限直和の公式 `χ(M^n, N) = n · χ(M, N)` を加法性から帰納法で示す（`chi_pi_left/right_of_additivity`）。
- `chi_finite_extensions`：以上を組み合わせる。加法性は正則局所環上の有限自由分解の存在、消滅は台つき巡回 Adams 作用素による
  `intersectionVanishing_of_adams`（証明済み）を使う。Lemma 3.5、Galois 作用、正規化長さとは独立の議論。
-/

public section

universe u

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
