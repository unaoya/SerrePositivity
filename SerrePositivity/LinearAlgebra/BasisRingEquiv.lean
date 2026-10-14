module

public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.Algebra.Algebra.Basic

/-! # 係数体と拡大体の同型に沿う基底の移送

係数写像との両立を明示し、Mathlib の `Basis.map` と `Basis.mapCoeffs` を組み合わせる。
-/

@[expose] public section
namespace SerrePositivity

variable {F K F' K' ι : Type*} [Field F] [Field K] [Field F'] [Field K']
  [Algebra F K] [Algebra F' K']

/-- 両立する二つの体同型は、同じ添字を持つ基底を移す。 -/
theorem exists_basis_of_ringEquiv (B : Module.Basis ι F K)
    (eF : F ≃+* F') (eK : K ≃+* K')
    (h : ∀ c, eK (algebraMap F K c) = algebraMap F' K' (eF c)) :
    ∃ B' : Module.Basis ι F' K', ∀ i, B' i = eK (B i) := by
  let : Algebra F K' := (eK.toRingHom.comp (algebraMap F K)).toAlgebra
  let e : K ≃ₗ[F] K' :=
    { eK.toAddEquiv with
      map_smul' := by
        intro c x
        simp only [Algebra.smul_def, RingHom.id_apply]
        change eK (algebraMap F K c * x) = eK (algebraMap F K c) * eK x
        exact eK.map_mul _ _ }
  have hc : ∀ (c : F) (x : K'), eF c • x = c • x := by
    intro c x
    simp only [Algebra.smul_def]
    change algebraMap F' K' (eF c) * x = eK (algebraMap F K c) * x
    rw [h]
  exact ⟨(B.map e).mapCoeffs eF hc, fun i ↦ by simp [e]⟩

end SerrePositivity
