module
public import SerrePositivity.DifferentialGraded.Complexes.Cells
public import SerrePositivity.DifferentialGraded.Complexes.Shift
/-!
概要：実 cycle を複体同型と整数 shift に沿って線形に輸送する。
方針：同型の各次数成分と、shift 微分の可逆な符号を用いる。
規約：cycle の元を保持し、shift 後の次数は n+s とする。
使われ方：c′ のシフト自由閉射の元の Hom 係数を cycle として回収する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (R : Type u) [CommRing R]

def complexCycleMap {P Q : Complex R} (f : P ⟶ Q) (n : ℤ) :
    complexCycles R P n →ₗ[R] complexCycles R Q n where
  toFun z := ⟨f.f n z.val, by
    have h := congrArg (fun φ => φ z.val) (f.comm n (n + 1))
    change Q.d n (n + 1) (f.f n z.val) = f.f (n + 1) (P.d n (n + 1) z.val) at h
    rw [z.property, map_zero] at h
    exact h⟩
  map_add' z w := Subtype.ext (map_add _ _ _)
  map_smul' r z := Subtype.ext (map_smul _ _ _)

def complexCycleIso {P Q : Complex R} (e : P ≅ Q) (n : ℤ) :
    complexCycles R P n ≃ₗ[R] complexCycles R Q n where
  toFun := complexCycleMap R e.hom n
  invFun := complexCycleMap R e.inv n
  left_inv z := by
    apply Subtype.ext
    exact congrArg (fun φ => φ.f n z.val) e.hom_inv_id
  right_inv z := by
    apply Subtype.ext
    exact congrArg (fun φ => φ.f n z.val) e.inv_hom_id
  map_add' := (complexCycleMap R e.hom n).map_add
  map_smul' := (complexCycleMap R e.hom n).map_smul

def complexShiftCycleIso (K : Complex R) (s n : ℤ) :
    complexCycles R (K⟦s⟧) n ≃ₗ[R] complexCycles R K (n + s) where
  toFun z := ⟨z.val, by
    have h : s.negOnePow • K.d (n + s) (n + 1 + s) z.val = 0 := z.property
    rw [show n + 1 + s = n + s + 1 by omega] at h
    exact (smul_eq_zero_iff_eq s.negOnePow).mp h⟩
  invFun z := ⟨z.val, by
    change s.negOnePow • K.d (n + s) (n + 1 + s) z.val = 0
    rw [show n + 1 + s = n + s + 1 by omega, z.property, smul_zero]⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end SerrePositivity.DifferentialGraded
