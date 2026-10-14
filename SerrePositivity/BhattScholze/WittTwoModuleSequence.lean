module

public import SerrePositivity.BhattScholze.DeltaSectionNaturality
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleClosure

/-! # W₂の第0成分の核とFrobeniusでねじれた作用

著者版Lemma 2.18の短完全列の具体的な加群部分。
核を第1座標の加法群と同定し、基底作用がφによる作用になることを証明する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A B : Type u} [CommRing A] [CommRing B]

/-- 第0座標が零であるW₂元を第1座標から構成する加法射。 -/
def wittTwoZeroFirst : B →+ WittTwo p B where
  toFun x := TruncatedWittVector.mk p (fun i ↦ if i = 0 then 0 else x)
  map_zero' := by ext i; fin_cases i <;> simp
  map_add' x y := by
    apply TruncatedWittVector.ext
    intro i
    fin_cases i
    · change 0 =
        ((TruncatedWittVector.mk p (fun i : Fin 2 ↦ if i = 0 then 0 else x)).out +
          (TruncatedWittVector.mk p (fun i : Fin 2 ↦ if i = 0 then 0 else y)).out).coeff 0
      rw [WittVector.add_coeff_zero]
      simp [TruncatedWittVector.out]
    · change x + y =
        ((TruncatedWittVector.mk p (fun i : Fin 2 ↦ if i = 0 then 0 else x)).out +
          (TruncatedWittVector.mk p (fun i : Fin 2 ↦ if i = 0 then 0 else y)).out).coeff 1
      rw [witt_add_coeff_one]
      simp [TruncatedWittVector.out]

/-- 零第0座標の構成の座標公式。 -/
@[simp] theorem wittTwoZeroFirst_coeff (x : B) (i : Fin 2) :
    (wittTwoZeroFirst (p := p) x).coeff i = if i = 0 then 0 else x := rfl

/-- δ切断を通じたW₂への具体的な基底射。 -/
def wittTwoBaseMap (D : DeltaStructure p A) (f : A →+* B) : A →+* WittTwo p B :=
  (wittTwoMap f).comp D.sectionHom

section ModuleSequence
variable (D : DeltaStructure p A) (f : A →+* B)

/-- 第0座標射は、δ切断を通じた基底作用について線形。 -/
def wittTwoProjectionLinear :
    letI := f.toAlgebra
    letI := (wittTwoBaseMap D f).toAlgebra
    WittTwo p B →ₗ[A] B := by
  letI := f.toAlgebra
  letI := (wittTwoBaseMap D f).toAlgebra
  exact {
    toAddHom := (wittTwoProjection p B).toAddMonoidHom
    map_smul' := fun r x ↦ by
      change wittTwoProjection p B (wittTwoBaseMap D f r * x) = f r * wittTwoProjection p B x
      rw [map_mul]
      congr 1
      simp only [wittTwoProjection_apply, wittTwoBaseMap, RingHom.comp_apply, wittTwoMap_coeff]
      rw [D.coeff_zero]
  }

/-- 第0座標射の核と第1座標の加法群の具体的同型。 -/
def wittTwoKernelEquiv :
    letI := f.toAlgebra
    letI := (wittTwoBaseMap D f).toAlgebra
    (wittTwoProjectionLinear D f).ker ≃+ B := by
  letI := f.toAlgebra
  letI := (wittTwoBaseMap D f).toAlgebra
  exact {
    toFun x := x.val.coeff 1
    invFun b := ⟨wittTwoZeroFirst b, by simp [LinearMap.mem_ker, wittTwoProjectionLinear]⟩
    left_inv x := by
      apply Subtype.ext
      apply TruncatedWittVector.ext
      intro i
      fin_cases i
      · have h : x.val.coeff 0 = 0 := x.property
        simpa using h.symm
      · rfl
    right_inv b := rfl
    map_add' := fun x y ↦ by
      change (x.val.out + y.val.out).coeff 1 = x.val.coeff 1 + y.val.coeff 1
      rw [witt_add_coeff_one]
      have hx : x.val.coeff 0 = 0 := x.property
      have hy : y.val.coeff 0 = 0 := y.property
      simp [TruncatedWittVector.out, hx, hy]
  }

/-- 核への基底作用は、φを経由した第1座標への作用に一致する。 -/
theorem wittTwoKernelEquiv_smul (r : A) :
    letI := f.toAlgebra
    letI := (wittTwoBaseMap D f).toAlgebra
    ∀ x : (wittTwoProjectionLinear D f).ker,
      wittTwoKernelEquiv D f (r • x) = f (D.frobeniusLift r) * wittTwoKernelEquiv D f x := by
  let := f.toAlgebra
  let := (wittTwoBaseMap D f).toAlgebra
  intro x
  simp only [wittTwoKernelEquiv, AddEquiv.coe_mk]
  change ((wittTwoBaseMap D f r).out * x.val.out).coeff 1 =
    f (D.frobeniusLift r) * x.val.coeff 1
  rw [witt_mul_coeff_one]
  change (wittTwoBaseMap D f r).coeff 0 ^ p * x.val.coeff 1 +
    (wittTwoBaseMap D f r).coeff 1 * x.val.coeff 0 ^ p +
    (p : B) * (wittTwoBaseMap D f r).coeff 1 * x.val.coeff 1 =
      f (D.frobeniusLift r) * x.val.coeff 1
  have hx : x.val.coeff 0 = 0 := x.property
  simp only [wittTwoBaseMap, RingHom.comp_apply,
    wittTwoMap_coeff, D.coeff_zero, hx, zero_pow (Fact.out : p.Prime).ne_zero,
    mul_zero, add_zero, DeltaStructure.delta, D.frobeniusLift_apply,
    map_add, map_mul, map_pow, map_natCast]
  ring

end ModuleSequence
end SerrePositivity.BhattScholze
