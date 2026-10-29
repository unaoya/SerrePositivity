module

public import SerrePositivity.CommutativeAlgebra.Adic.Complete
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # adic 前完備性による有限生成判定

概要：イデアル `I` について `R` が `I` 進前完備なら
- 生成元の像が `M / I M` を生成すれば、`M` の分離商は同じ生成元で生成される（完備版の中山の補題）。
  特に `M` が `I` 進分離で `M / I M` が有限なら `M` は有限。代数の有限性も同様。
- 次数のずれを許す `I` 進近似（`M_n` の元を `I^{n - c}` 倍の誤差で近似できる）から、実際の包含と有限生成性を得る。
方針：生成元の持ち上げで `R^n → M` を作り、Mathlib の `AdicCompletion.surjective_of_mkQ_comp_surjective` で全射性を移す。
規約：Noether 性は仮定しない。
使われ方：完備化の有限性（`Adic/Completion/Basic`）、冪級数の評価の有限性、Rees 加群の近似（`ReesCoefficientApproximation`）。
Mathlib への提出候補。
-/

@[expose] public noncomputable section

universe u v w

namespace SerrePositivity

section AdicFiniteGeneration

open Submodule

variable {R : Type*} [CommRing R] (I : Ideal R)
variable {M : Type*} [AddCommGroup M] [Module R M]
variable [IsPrecomplete I R] [IsHausdorff I M]

/-- 商を生成する有限列を持ち上げると、同じ列が元の加群を生成する。
有限自由な始域の前完備性と終域の分離性から、商での全射を反映する。 -/
theorem surjective_linearCombination_of_quotient {ι : Type*} [Fintype ι]
    (x : ι → M)
    (hx : Function.Surjective
      ((I • (⊤ : Submodule R M)).mkQ.comp (Fintype.linearCombination R x))) :
    Function.Surjective (Fintype.linearCombination R x) := by
  let := isPrecomplete_pi (M := R) I ι
  exact surjective_of_mkQ_comp_surjective hx

/-- 有限生成な商の生成元を持ち上げ、有限自由加群からの全射を構成する。
商の有限生成性はまず基底環上で述べ、係数制限と構成の議論を分ける。 -/
theorem exists_surjective_pi_of_finite_quotient
    [Module.Finite R (M ⧸ I • (⊤ : Submodule R M))] :
    ∃ (n : ℕ) (f : (Fin n → R) →ₗ[R] M), Function.Surjective f := by
  classical
  let J : Submodule R M := I • ⊤
  obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin' R (M ⧸ J)
  let b := Pi.basisFun R (Fin n)
  choose x hx using fun i : Fin n ↦ J.mkQ_surjective (g (b i))
  let f : (Fin n → R) →ₗ[R] M := b.constr ℕ x
  have hfg : J.mkQ.comp f = g := by
    apply b.ext
    intro i
    change J.mkQ (f (b i)) = g (b i)
    rw [Module.Basis.constr_basis]
    exact hx i
  let := isPrecomplete_pi (M := R) I (Fin n)
  refine ⟨n, f, surjective_of_mkQ_comp_surjective (I := I) (f := f) ?_⟩
  change Function.Surjective (J.mkQ.comp f)
  rw [hfg]
  exact hg

/-- 前完備な環上の分離加群は、イデアル商が有限生成なら有限生成。
商の自然な R/I 作用から基底環の作用へ制限し、明示的な全射を適用する。 -/
theorem finite_of_quotient_of_isPrecomplete
    [Module.Finite (R ⧸ I) (M ⧸ I • (⊤ : Submodule R M))] : Module.Finite R M := by
  let : Module.Finite R (M ⧸ I • (⊤ : Submodule R M)) :=
    Module.Finite.trans (R ⧸ I) _
  obtain ⟨n, f, hf⟩ := exists_surjective_pi_of_finite_quotient (M := M) I
  exact Module.Finite.of_surjective f hf

omit [IsHausdorff I M] in
/-- 完備基底のイデアルの像で割った有限な閉ファイバーから、代数の有限性を得る。
商の係数制限とイデアル倍の同定を明示し、終域のNoether性や有限性を前提にしない。 -/
theorem finite_algebra_of_finite_quotient_map
    (S : Type*) [CommRing S] [Algebra R S] (J : Ideal S)
    [IsHausdorff J S] (hJ : I.map (algebraMap R S) = J)
    [Module.Finite R (S ⧸ J)] : Module.Finite R S := by
  let : IsHausdorff I S := (IsHausdorff.map_algebraMap_iff (I := I) (S := S) (M := S)).mp
    (by rw [hJ]; infer_instance)
  let e : (S ⧸ I • (⊤ : Submodule R S)) ≃ₗ[R] S ⧸ J :=
    (Submodule.quotEquivOfEq _ _ (by rw [Ideal.smul_top_eq_map, hJ])).trans
      (Submodule.Quotient.restrictScalarsEquiv R J)
  let : Module.Finite R (S ⧸ I • (⊤ : Submodule R S)) :=
    Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective
  obtain ⟨n, f, hf⟩ := exists_surjective_pi_of_finite_quotient (M := S) I
  exact Module.Finite.of_surjective f hf

end AdicFiniteGeneration

section AdicApproximationLifting

variable {R P M : Type*} [CommRing R]
variable [AddCommGroup P] [Module R P] [AddCommGroup M] [Module R M]

/-- 初期形式の生成から得られる一様な次数付き近似を、元の部分加群の生成へ持ち上げる。
cは生成元の次数の上界。次数nでの係数はI^(n-c)に入ることを要求する。 -/
theorem submodule_le_range_of_shifted_adic_approximation
    (I : Ideal R) [IsPrecomplete I P] [IsHausdorff I M]
    (f : P →ₗ[R] M) (N : Submodule R M) (hf : f.range ≤ N) (c : ℕ)
    (happrox : ∀ n x, x ∈ N → x ∈ I ^ n • (⊤ : Submodule R M) →
      ∃ p : P, p ∈ I ^ (n - c) • (⊤ : Submodule R P) ∧
        x - f p ∈ I ^ (n + 1) • (⊤ : Submodule R M)) : N ≤ f.range := by
  classical
  intro x hx
  let A (n : ℕ) := {p : P // x - f p ∈ N ∧ x - f p ∈ I ^ n • (⊤ : Submodule R M)}
  let step (n : ℕ) (p : A n) : A (n + 1) := by
    let H := happrox n (x - f p.val) p.property.1 p.property.2
    let q := Classical.choose H
    have hq := Classical.choose_spec H
    refine ⟨p.val + q, ?_, ?_⟩
    · rw [map_add, sub_add_eq_sub_sub]
      exact N.sub_mem p.property.1 (hf (LinearMap.mem_range_self f q))
    · simpa only [map_add, sub_add_eq_sub_sub] using hq.2
  let u : ∀ n, A n := fun n ↦ Nat.rec
    (show A 0 from ⟨0, by simpa using hx, by simp⟩) step n
  have hu_step (n : ℕ) : (u (n + 1)).val - (u n).val ∈
      I ^ (n - c) • (⊤ : Submodule R P) := by
    change (step n (u n)).val - (u n).val ∈ _
    change (u n).val + Classical.choose
      (happrox n (x - f (u n).val) (u n).property.1 (u n).property.2) - (u n).val ∈ _
    simpa only [add_sub_cancel_left] using (Classical.choose_spec
      (happrox n (x - f (u n).val) (u n).property.1 (u n).property.2)).1
  let v (n : ℕ) := (u (n + c)).val
  have hv_step (n : ℕ) : v (n + 1) - v n ∈ I ^ n • (⊤ : Submodule R P) := by
    have hidx : n + c + 1 = n + 1 + c := by omega
    exact Eq.mp (congrArg (fun t : ℕ ↦ (u t).val - (u (n + c)).val ∈
      I ^ n • (⊤ : Submodule R P)) hidx)
      (by simpa only [Nat.add_sub_cancel] using hu_step (n + c))
  have hv : ∀ m n, m ≤ n → v m ≡ v n [SMOD (I ^ m • (⊤ : Submodule R P))] := by
    intro m n hmn
    induction n, hmn using Nat.le_induction with
    | base => exact SModEq.refl _
    | succ n hmn ih =>
      apply ih.trans
      exact (SModEq.sub_mem.mpr (hv_step n)).symm.mono
        (Submodule.smul_mono_left (Ideal.pow_le_pow_right hmn))
  obtain ⟨L, hL⟩ := IsPrecomplete.prec' (I := I) v (fun {m n} h ↦ hv m n h)
  refine ⟨L, ?_⟩
  apply (IsHausdorff.eq_iff_smodEq (I := I)).mpr
  intro n
  have herr : x ≡ f (v n) [SMOD (I ^ n • (⊤ : Submodule R M))] :=
    (SModEq.sub_mem.mpr (u (n + c)).property.2).mono
      (Submodule.smul_mono_left (Ideal.pow_le_pow_right (Nat.le_add_right n c)))
  exact ((smodEq_map_pow I f (hL n)).symm.trans herr.symm)

/-- 前完備な環上の有限な係数加群で上の近似を供給すれば、部分加群は有限生成。
部分加群自体の閉性・前完備性・有限性を仮定しない。 -/
theorem fg_of_shifted_adic_approximation
    (I : Ideal R) [IsPrecomplete I R] [IsHausdorff I M] [Module.Finite R P]
    (f : P →ₗ[R] M) (N : Submodule R M) (hf : f.range ≤ N) (c : ℕ)
    (happrox : ∀ n x, x ∈ N → x ∈ I ^ n • (⊤ : Submodule R M) →
      ∃ p : P, p ∈ I ^ (n - c) • (⊤ : Submodule R P) ∧
        x - f p ∈ I ^ (n + 1) • (⊤ : Submodule R M)) : N.FG := by
  let : IsPrecomplete I P := isPrecomplete_finite I P
  have hN : N = f.range := le_antisymm
    (submodule_le_range_of_shifted_adic_approximation I f N hf c happrox) hf
  rw [hN]
  simpa only [Submodule.map_top] using (Module.Finite.fg_top (R := R) (M := P)).map f

end AdicApproximationLifting

end SerrePositivity
