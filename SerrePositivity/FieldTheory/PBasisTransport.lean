module

public import SerrePositivity.FieldTheory.PBasis
public import SerrePositivity.LinearAlgebra.BasisRingEquiv

/-! # 体同型に沿う p-basis の移送

Frobenius と体同型の可換性により、係数の p 乗部分体も同時に移す。
-/

@[expose] public section
namespace SerrePositivity

variable {k l : Type*} [Field k] [Field l] {p : ℕ} [Fact p.Prime]
  [CharP k p] [CharP l p]

/-- 体同型が誘導する p 乗部分体の同型。 -/
noncomputable def pPowerSubfieldEquiv (e : k ≃+* l) :
    pPowerSubfield k p ≃+* pPowerSubfield l p :=
  (pPowerEquiv k p).symm.trans (e.trans (pPowerEquiv l p))

@[simp] theorem pPowerSubfieldEquiv_apply_coe (e : k ≃+* l)
    (c : pPowerSubfield k p) : (pPowerSubfieldEquiv e c : l) = e (c : k) := by
  change (e ((pPowerEquiv k p).symm c)) ^ p = e (c : k)
  rw [← map_pow]
  congr 1
  exact congrArg Subtype.val ((pPowerEquiv k p).apply_symm_apply c)

/-- p-basis の独立性と生成性は、ともに体同型で保たれる。 -/
theorem IsPBasis.ringEquiv {ι : Type*} {b : ι → k} (hb : IsPBasis k p b)
    (e : k ≃+* l) : IsPBasis l p (e ∘ b) := by
  let B := basisOfRingEquiv hb.basis (pPowerSubfieldEquiv e) e
    (fun c ↦ (pPowerSubfieldEquiv_apply_coe e c).symm)
  have he : ∀ d : PExponent p ι, B d = pMonomial (e ∘ b) d := by
    intro d
    rw [show B d = e (hb.basis d) from basisOfRingEquiv_apply _ _ _ _ d, hb.basis_apply]
    simp only [pMonomial, map_finsuppProd, map_pow, Function.comp_apply]
  have hfun : (B : PExponent p ι → l) = pMonomial (e ∘ b) := funext he
  exact ⟨hfun ▸ B.linearIndependent, hfun ▸ B.span_eq⟩

end SerrePositivity
