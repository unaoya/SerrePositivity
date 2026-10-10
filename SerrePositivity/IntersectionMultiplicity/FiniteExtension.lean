module

public import SerrePositivity.IntersectionMultiplicity.Basic
public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.Data.ENat.BigOperators
public import SerrePositivity.Inputs.IntersectionTheory
public import SerrePositivity.CommutativeAlgebra.LocalAlgebra

/-!
# 有限拡大による交点重複度の階数倍

有限代数に置き換えたときの交点重複度を、もとの交点重複度と一般点での階数で表す。
前半の三つの補題は、加法性・直和の評価・余核の消滅を等式として受け取る算術的な整理である。
有限直和の公式は加法性から証明する。後半の `chi_finite_extensions` は、正則局所環上の一般的な入力クラスを使って
それらの等式を用意し、各変数の階数を順に取り出す。

数学的な要点は、一般点で基底となる自由部分加群の余核が低次元になることと、
その余核の交点重複度が Roberts–Gillet–Soulé の定理で消えることである。
補題3.5、Galois 作用、正規化長さとは独立した議論である。
-/

public section

universe u

open scoped TensorProduct

namespace SerrePositivity

variable {R : Type u} [CommRing R]
variable {D D' E E' : Type u}
  [AddCommGroup D] [Module R D] [AddCommGroup D'] [Module R D']
  [AddCommGroup E] [Module R E] [AddCommGroup E'] [Module R E']

/-- 第1変数の階数因子を取り出す形式的な計算。
加法性の等式、自由加群の直和の評価、余核に対する消滅を受け取り、`χ(D′, E) = a χ(D, E)` を得る。
この補題自体は、与えた写像の単射性や消滅定理を証明するものではない。 -/
theorem chi_rank_factor_left_of_additivity_and_vanishing (a : ℕ)
    (f : (Fin a → D) →ₗ[R] D')
    (hadd : chi R D' E = chi R (Fin a → D) E + chi R (D' ⧸ LinearMap.range f) E)
    (hfree : chi R (Fin a → D) E = (a : ℤ) * chi R D E)
    (hvanish : chi R (D' ⧸ LinearMap.range f) E = 0) :
    chi R D' E = (a : ℤ) * chi R D E := by
  rw [hadd, hfree, hvanish, add_zero]

/-- 第2変数について、加法性・直和の評価・余核の消滅から階数因子を取り出す。
第1変数と独立に計算し、Tor の対称性は用いない。 -/
theorem chi_rank_factor_right_of_additivity_and_vanishing (a : ℕ)
    (f : (Fin a → E) →ₗ[R] E')
    (hadd : chi R D E' = chi R D (Fin a → E) + chi R D (E' ⧸ LinearMap.range f))
    (hfree : chi R D (Fin a → E) = (a : ℤ) * chi R D E)
    (hvanish : chi R D (E' ⧸ LinearMap.range f) = 0) :
    chi R D E' = (a : ℤ) * chi R D E := by
  rw [hadd, hfree, hvanish, add_zero]

/-- 二つの変数で得た階数比較を合成し、`χ(D′, E′) = a_D a_E χ(D, E)` を得る。 -/
theorem chi_rank_factors (aD aE : ℕ)
    (hD : chi R D' E' = (aD : ℤ) * chi R D E')
    (hE : chi R D E' = (aE : ℤ) * chi R D E) :
    chi R D' E' = (aD : ℤ) * aE * chi R D E := by
  rw [hD, hE, mul_assoc]

/-- 拡張自然数値の次元に有限な自然数を加えても、有限な上界に対する狭義不等式は保たれる。
零加群に対応する値 `⊥` も含めて扱う。 -/
lemma dimension_add_nat_lt {x : WithBot ℕ∞} {a b : ℕ}
    (hx : x < (a : WithBot ℕ∞)) : x + (b : WithBot ℕ∞) < ((a + b : ℕ) : WithBot ℕ∞) := by
  cases x with
  | bot => simp
  | coe x =>
    have h : x < (a : ℕ∞) := by exact_mod_cast hx
    have h' := (ENat.add_lt_add_iff_right (ENat.natCast_ne_top b)).mpr h
    exact_mod_cast h'

section additivity

variable [Inputs.IntersectionAdditivity R]

/-- 第1変数の有限直和の評価は短完全列の加法性から従う。
各段階でテンソル積の有限長性を有限直和との同型で確認し、
先頭成分と残りの成分に分ける分裂短完全列に加法性を適用する。 -/
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
    have hh := Inputs.IntersectionAdditivity.add_left (Fin 0 → M) (Fin 0 → M) (Fin 0 → M) N
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
    rw [Inputs.IntersectionAdditivity.add_left _ _ _ _ f g hf hg he hfin, ih]
    push_cast
    ring

/-- 第2変数の有限直和の評価を、その変数の加法性から導く。
第1変数の公式や Tor の対称性には依存しない。 -/
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
    have hh := Inputs.IntersectionAdditivity.add_right M (Fin 0 → N) (Fin 0 → N) (Fin 0 → N)
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
    rw [Inputs.IntersectionAdditivity.add_right _ _ _ _ f g hf hg he hfin, ih]
    push_cast
    ring

end additivity

section extension

variable [IsRegularLocalRing R] [Inputs.IntersectionAdditivity R]
  [Inputs.GenericBasis R] [Inputs.IntersectionVanishing R]

/-- 有限代数 `T/(R/P)` と `U/(R/Q)` の交点重複度は、それぞれの階数の積を因子にもつ。
`√(P + Q) = m_R` と次元の和の条件のもとで、一般点の基底から自由加群の単射を取り、
低次元の余核の寄与を消滅定理で除く。加法性・台の一般論・消滅定理は入力クラスに依存する。
Galois 拡大や正規化長さは用いない。 -/
theorem chi_finite_extensions
    (P Q : Ideal R) [P.IsPrime] [Q.IsPrime]
    (T U : Type u) [CommRing T] [Algebra R T] [Algebra (R ⧸ P) T]
    [IsScalarTower R (R ⧸ P) T] [Module.Finite R T] [Module.Finite (R ⧸ P) T]
    [CommRing U] [Algebra R U] [Algebra (R ⧸ Q) U]
    [IsScalarTower R (R ⧸ Q) U] [Module.Finite R U] [Module.Finite (R ⧸ Q) U]
    (hT : 0 < Module.finrank (R ⧸ P) T) (hU : 0 < Module.finrank (R ⧸ Q) U)
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
  obtain ⟨f, hf, hC⟩ := Inputs.GenericBasis.generic_basis P T hT
  obtain ⟨g, hg, hK⟩ := Inputs.GenericBasis.generic_basis Q U hU
  have finCU := length_tensorProduct_ne_top_of_annihilator P Q (T ⧸ LinearMap.range f) U
    (annT.trans (annihilator_le_quotient T _)) annU hprimary
  have finDK := length_tensorProduct_ne_top_of_annihilator P Q (R ⧸ P) (U ⧸ LinearMap.range g)
    annD (annU.trans (annihilator_le_quotient U _)) hprimary
  have dimU : Module.supportDim R U = (l : WithBot ℕ∞) := by
    rw [supportDim_of_quotient_rank_pos Q U hU, hQ]
  have dimD : Module.supportDim R (R ⧸ P) = (h : WithBot ℕ∞) := by
    rw [Module.supportDim_quotient_eq_ringKrullDim, hP]
  have vanishC : chi R (T ⧸ LinearMap.range f) U = 0 :=
    Inputs.IntersectionVanishing.vanish _ _ finCU (by
      rw [dimU, ← hsum]
      exact dimension_add_nat_lt (hP ▸ hC))
  have vanishK : chi R (R ⧸ P) (U ⧸ LinearMap.range g) = 0 :=
    Inputs.IntersectionVanishing.vanish _ _ finDK (by
      rw [dimD, add_comm, ← hsum, Nat.add_comm h l]
      exact dimension_add_nat_lt (hQ ▸ hK))
  have left := chi_rank_factor_left_of_additivity_and_vanishing
    (Module.finrank (R ⧸ P) T) f
    (Inputs.IntersectionAdditivity.add_left _ _ _ _ f (LinearMap.range f).mkQ hf
      (Submodule.mkQ_surjective _) (LinearMap.exact_map_mkQ_range f) finTU)
    (chi_pi_left_of_additivity _ _ finDU _) vanishC
  have right := chi_rank_factor_right_of_additivity_and_vanishing
    (Module.finrank (R ⧸ Q) U) g
    (Inputs.IntersectionAdditivity.add_right _ _ _ _ g (LinearMap.range g).mkQ hg
      (Submodule.mkQ_surjective _) (LinearMap.exact_map_mkQ_range g) finDU)
    (chi_pi_right_of_additivity (R ⧸ P) (R ⧸ Q) finDE _) vanishK
  exact chi_rank_factors _ _ left right

end extension

end SerrePositivity
