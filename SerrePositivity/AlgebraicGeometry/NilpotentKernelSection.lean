module

public meta import SerrePositivity.Util.DeprecatedAlias
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.RingTheory.Ideal.Operations

/-!
概要：KST §5、Stacks 05CG の核をイデアル倍へ縮小する自己準同型による右逆。
方針：自己準同型の冪が核上でイデアルの冪に値を持つことを帰納し、商へ降ろす。
規約：冪零性は具体的な指数で与え、基礎環の Noether 性を課さない。
使われ方：冪零剰余の射影性を元の加群の射影性へ持ち上げる。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.AlgebraicGeometry

/--
概要：イデアル倍に値を持つ自己準同型の n 乗は、そのイデアルの n 乗倍に値を持つ。
方針：イデアル倍の生成元に対する線形性で帰納する。
規約：KST §5、Stacks 05CG、加群は任意。
使われ方：冪零イデアルの場合に自己準同型の冪を零とする。
-/
theorem endomorphism_pow_mem_ideal_pow
    {R K : Type u} [CommRing R] [AddCommGroup K] [Module R K]
    (I : Ideal R) (e : Module.End R K)
    (he : ∀ x, e x ∈ I • (⊤ : Submodule R K)) (n : ℕ) (x : K) :
    (e ^ n) x ∈ I ^ n • (⊤ : Submodule R K) := by
  induction n with
  | zero => simp
  | succ n hn =>
      have hmap (y : K) (hy : y ∈ I ^ n • (⊤ : Submodule R K)) :
          e y ∈ I ^ n • (I • (⊤ : Submodule R K)) := by
        refine Submodule.smul_induction_on hy ?_ ?_
        · intro r hr z hz
          rw [map_smul]
          exact Submodule.smul_mem_smul hr (he z)
        · intro z w hz hw
          simpa using (I ^ n • (I • (⊤ : Submodule R K))).add_mem hz hw
      rw [pow_succ' e n]
      change e ((e ^ n) x) ∈ I ^ (n + 1) • (⊤ : Submodule R K)
      simpa only [pow_succ, mul_smul] using hmap ((e ^ n) x) hn

/--
概要：全射を保ち核を冪零イデアル倍へ縮小する自己準同型から、全射の右逆を構成する。
方針：核上の自己準同型の冪を零とし、その冪を全射の核の商から終域へ移す。
規約：KST §5、Stacks 05CG、冪零指数には正値を別に要求しない。
使われ方：剰余の右逆の持ち上げから射影性を得る。
-/
theorem exists_section_of_nilpotent_kernel_endomorphism
    {R F M : Type u} [CommRing R] [AddCommGroup F] [Module R F]
    [AddCommGroup M] [Module R M] (π : F →ₗ[R] M) (hπ : Function.Surjective π)
    (I : Ideal R) (n : ℕ) (hn : I ^ n = 0) (e : Module.End R F)
    (he : π.comp e = π)
    (hK : ∀ x : LinearMap.ker π,
      e x.val ∈ (I • (⊤ : Submodule R (LinearMap.ker π))).map (LinearMap.ker π).subtype) :
    ∃ s : M →ₗ[R] F, π.comp s = LinearMap.id := by
  let K := LinearMap.ker π
  have heK (x : K) : e x.val ∈ K := by
    change π (e x.val) = 0
    have hx := congrArg (fun f => f x.val) he
    exact hx.trans x.property
  let eK : Module.End R K := (e.comp K.subtype).codRestrict K heK
  have heKI (x : K) : eK x ∈ I • (⊤ : Submodule R K) := by
    obtain ⟨y, hy, hye⟩ := hK x
    have hye' : y = eK x := Subtype.ext hye
    rwa [hye'] at hy
  have hpowK (k : ℕ) (x : K) : ((eK ^ k) x).val = (e ^ k) x.val := by
    induction k with
    | zero => rfl
    | succ k hk =>
        simp only [pow_succ', Module.End.mul_apply]
        change e ((eK ^ k) x).val = e ((e ^ k) x.val)
        rw [hk]
  have hkill : K ≤ LinearMap.ker (e ^ n) := by
    intro x hx
    have hz := endomorphism_pow_mem_ideal_pow I eK heKI n (⟨x, hx⟩ : K)
    rw [hn, zero_smul] at hz
    have hz' : (eK ^ n) (⟨x, hx⟩ : K) = 0 := hz
    have := congrArg Subtype.val hz'
    change (e ^ n) x = 0
    simpa only [hpowK, Submodule.coe_zero] using this
  have hπpow (k : ℕ) : π.comp (e ^ k) = π := by
    induction k with
    | zero => ext x; rfl
    | succ k hk =>
        rw [pow_succ', Module.End.mul_eq_comp, ← LinearMap.comp_assoc, he, hk]
  let q := π.quotKerEquivOfSurjective hπ
  let s := (K.liftQ (e ^ n) hkill).comp q.symm.toLinearMap
  refine ⟨s, ?_⟩
  apply LinearMap.ext
  intro m
  obtain ⟨x, rfl⟩ := hπ m
  change π (K.liftQ (e ^ n) hkill (q.symm (π x))) = π x
  have hq : q.symm (π x) = K.mkQ x := by
    apply q.injective
    simp [q]
  rw [hq]
  change π ((e ^ n) x) = π x
  exact congrArg (fun f => f x) (hπpow n)

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
