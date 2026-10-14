module

public import SerrePositivity.CommutativeAlgebra.FrobeniusKernelLift
public import SerrePositivity.FieldTheory.FrobeniusPowerSubfield
public import SerrePositivity.CommutativeAlgebra.NilpotentFrobenius

/-! # p^n 乗部分体の係数写像

核を消すFrobenius冪から係数写像を実構成し、剰余写像と指定元の冪への両立を証明する。
-/

@[expose] public section
namespace SerrePositivity

variable {A : Type*} [CommRing A]
variable (p : ℕ) [Fact p.Prime] [CharP A p]

variable {k : Type*} [Field k] [CharP k p]

/-- p^n 乗部分体からの実際の係数写像。任意の剰余体に適用できる。 -/
noncomputable def frobeniusCoefficientLift (f : A →+* k) (hf : Function.Surjective f)
    (n : ℕ) (hkill : ∀ x : A, f x = 0 → x ^ p ^ n = 0) :
    frobeniusPowerSubfield k p n →+* A :=
  (liftFrobeniusOfSurjective p f hf n hkill).comp
    (frobeniusPowerEquiv k p n).symm.toRingHom

/-- 係数写像は剰余体への包含写像を実際に持ち上げる。 -/
theorem map_frobeniusCoefficientLift (f : A →+* k) (hf : Function.Surjective f)
    (n : ℕ) (hkill : ∀ x : A, f x = 0 → x ^ p ^ n = 0)
    (c : frobeniusPowerSubfield k p n) :
    f (frobeniusCoefficientLift p f hf n hkill c) = c := by
  change f (liftFrobeniusOfSurjective p f hf n hkill ((frobeniusPowerEquiv k p n).symm c)) = c
  rw [map_liftFrobeniusOfSurjective]
  exact congrArg Subtype.val ((frobeniusPowerEquiv k p n).apply_symm_apply c)

/-- 剰余体の元の任意の持ち上げについて、その p^n 乗は係数写像の値と一致する。 -/
theorem frobeniusCoefficientLift_pow (f : A →+* k) (hf : Function.Surjective f)
    (n : ℕ) (hkill : ∀ x : A, f x = 0 → x ^ p ^ n = 0) (x : A) :
    frobeniusCoefficientLift p f hf n hkill (frobeniusPowerEquiv k p n (f x)) = x ^ p ^ n := by
  change liftFrobeniusOfSurjective p f hf n hkill
    ((frobeniusPowerEquiv k p n).symm (frobeniusPowerEquiv k p n (f x))) = _
  rw [RingEquiv.symm_apply_apply, liftFrobeniusOfSurjective_apply_map]

/-- 冪零核を持つ全射について、高い p 冪の係数部分体からの持ち上げを実構成する。 -/
theorem exists_frobeniusCoefficientLift_of_nilpotent_kernel
    (f : A →+* k) (hf : Function.Surjective f) (hker : IsNilpotent (RingHom.ker f)) :
    ∃ n : ℕ, ∃ c : frobeniusPowerSubfield k p n →+* A,
      f.comp c = (frobeniusPowerSubfield k p n).subtype ∧
        ∀ x : A, c (frobeniusPowerEquiv k p n (f x)) = x ^ p ^ n := by
  obtain ⟨n, hn⟩ := exists_pow_exp_eq_zero_of_nilpotent_ideal p (RingHom.ker f) hker
  let hkill := fun x hx ↦ hn x hx
  refine ⟨n, frobeniusCoefficientLift p f hf n hkill, ?_, ?_⟩
  · ext x
    exact map_frobeniusCoefficientLift p f hf n hkill x
  · exact frobeniusCoefficientLift_pow p f hf n hkill

end SerrePositivity
