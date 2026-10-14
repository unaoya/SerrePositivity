module
public import SerrePositivity.CommutativeAlgebra.AdicRecurrence

/-! # The scalar becomes invertible on the kernel and cokernel of its recurrence

For D(x)ₙ = xₙ - a xₙ₊₁, sequence shift is an inverse to multiplication by a
on both ker D and coker D. No completeness, regularity or finiteness is assumed.
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
namespace SerrePositivity
variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]

/-- Shift a sequence one position to the left. -/
def adicSequenceShift : (ℕ → M) →ₗ[R] (ℕ → M) where
  toFun x n := x (n + 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Shift preserves the kernel of the scalar recurrence. -/
def adicRecurrenceKernelShift (a : R) :
    (adicRecurrenceMap (M := M) a).ker →ₗ[R] (adicRecurrenceMap (M := M) a).ker where
  toFun x := ⟨adicSequenceShift (R := R) x.val, by
    apply LinearMap.mem_ker.mpr
    funext n
    exact congrFun (LinearMap.mem_ker.mp x.property) (n + 1)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Multiplication by a is invertible on the kernel, with inverse sequence shift. -/
def adicRecurrenceKernelScalarEquiv (a : R) :
    (adicRecurrenceMap (M := M) a).ker ≃ₗ[R] (adicRecurrenceMap (M := M) a).ker where
  toFun x := a • x
  invFun := adicRecurrenceKernelShift a
  left_inv x := by
    apply Subtype.ext
    funext n
    exact (sub_eq_zero.mp (congrFun (LinearMap.mem_ker.mp x.property) n)).symm
  right_inv x := by
    apply Subtype.ext
    funext n
    exact (sub_eq_zero.mp (congrFun (LinearMap.mem_ker.mp x.property) n)).symm
  map_add' _ _ := smul_add _ _ _
  map_smul' _ _ := smul_comm _ _ _

/-- Shift descends to the cokernel since it commutes with the recurrence. -/
def adicRecurrenceCokernelShift (a : R) :
    ((ℕ → M) ⧸ (adicRecurrenceMap (M := M) a).range) →ₗ[R]
      ((ℕ → M) ⧸ (adicRecurrenceMap (M := M) a).range) :=
  Submodule.mapQ _ _ (adicSequenceShift (R := R)) (by
    rintro x ⟨y, rfl⟩
    exact ⟨adicSequenceShift (R := R) y, rfl⟩)

/-- Modulo the recurrence, scalar multiplication after shift is the identity. -/
lemma adicRecurrenceCokernel_smul_shift (a : R)
    (x : (ℕ → M) ⧸ (adicRecurrenceMap (M := M) a).range) :
    a • adicRecurrenceCokernelShift (M := M) a x = x := by
  induction x using Submodule.Quotient.induction_on with
  | _ x =>
    change Submodule.Quotient.mk (a • adicSequenceShift (R := R) x) = Submodule.Quotient.mk x
    apply (Submodule.Quotient.eq _).mpr
    refine ⟨-x, ?_⟩
    funext n
    simp only [adicRecurrenceMap, LinearMap.coe_mk, AddHom.coe_mk, Pi.neg_apply,
      Pi.sub_apply, Pi.smul_apply, adicSequenceShift, smul_neg]
    abel

/-- Multiplication by a is also invertible on the cokernel; lim¹ need not vanish. -/
def adicRecurrenceCokernelScalarEquiv (a : R) :
    ((ℕ → M) ⧸ (adicRecurrenceMap (M := M) a).range) ≃ₗ[R]
      ((ℕ → M) ⧸ (adicRecurrenceMap (M := M) a).range) where
  toFun x := a • x
  invFun := adicRecurrenceCokernelShift (M := M) a
  left_inv x := by
    rw [map_smul]
    exact adicRecurrenceCokernel_smul_shift (M := M) a x
  right_inv := adicRecurrenceCokernel_smul_shift (M := M) a
  map_add' _ _ := smul_add _ _ _
  map_smul' _ _ := smul_comm _ _ _

end SerrePositivity
