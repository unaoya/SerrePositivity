module

public import SerrePositivity.AlgebraicGeometry.ReesFiltrationModule
public import SerrePositivity.AlgebraicGeometry.Blowup

/-!
概要：一般のフィルトレーションの Rees 加群に自然数次数の内部直和を与える。
方針：各次数を単項式の像と同定し、既存の直和との同値を移す。
規約：Rees 環の次数には既存の reesGrade を使う。
使われ方：有限斉次生成元の次数の上界と、形式関数の評価の構成。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.AlgebraicGeometry

open scoped DirectSum

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
variable {I : Ideal R} (F : I.Filtration M)

/-- Rees 加群の一つの次数の斉次部分加群。 -/
def reesFiltrationGrade (n : ℕ) : Submodule R F.submodule :=
  LinearMap.range (reesFiltrationSingle F n)

/-- Rees 加群の係数を一つの次数の単項式へ戻す射影。 -/
def reesFiltrationProjection (n : ℕ) : F.submodule →ₗ[R] F.submodule :=
  (reesFiltrationSingle F n).comp (reesFiltrationCoeff F n)

/-- 同じ次数の単項式の係数は元の元に戻る。 -/
@[simp]
theorem reesFiltrationCoeff_single (n : ℕ) (m : F.N n) :
    reesFiltrationCoeff F n (reesFiltrationSingle F n m) = m := by
  apply Subtype.ext
  change (reesFiltrationSingle F n m).val.coeff n = m.val
  simp only [reesFiltrationSingle_coeff, ite_true]

/-- 各次数の斉次部分加群は Rees 加群の内部直和を与える。 -/
theorem isInternal_reesFiltrationGrade : DirectSum.IsInternal (reesFiltrationGrade F) := by
  classical
  have hi (n : ℕ) : Function.Injective (reesFiltrationSingle F n) := by
    intro x y h
    have hc := congrArg (reesFiltrationCoeff F n) h
    simpa only [reesFiltrationCoeff_single] using hc
  let e (n : ℕ) : F.N n ≃ₗ[R] reesFiltrationGrade F n :=
    LinearEquiv.ofInjective (reesFiltrationSingle F n) (hi n)
  let E := DirectSum.congrLinearEquiv e
  have hcomp : (DirectSum.coeLinearMap (reesFiltrationGrade F)).comp E.toLinearMap =
      reesFiltrationAssemble F := by
    apply DirectSum.linearMap_ext
    intro n
    apply LinearMap.ext
    intro x
    change DirectSum.coeLinearMap (reesFiltrationGrade F) (E (DirectSum.lof R ℕ _ n x)) = _
    simp only [E, DirectSum.coe_congrLinearEquiv, DirectSum.lmap_lof,
      DirectSum.coeLinearMap_lof]
    change ((LinearEquiv.ofInjective (reesFiltrationSingle F n) (hi n) x) : F.submodule) =
      reesFiltrationAssemble F (DirectSum.of (fun n ↦ F.N n) n x)
    rw [reesFiltrationAssemble_of]
    exact LinearEquiv.ofInjective_apply _ _
  have heq : DirectSum.coeLinearMap (reesFiltrationGrade F) =
      (reesFiltrationAssemble F).comp E.symm.toLinearMap := by
    apply LinearMap.ext
    intro z
    have hz := DFunLike.congr_fun hcomp (E.symm z)
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] using hz
  change Function.Bijective (DirectSum.coeLinearMap (reesFiltrationGrade F))
  rw [heq]
  exact (reesFiltrationDirectSumLinearEquiv F).bijective.comp E.symm.bijective

/-- Rees 加群の自然数次数の分解。 -/
@[instance_reducible]
def reesFiltrationGradeDecomposition : DirectSum.Decomposition (reesFiltrationGrade F) :=
  (isInternal_reesFiltrationGrade F).chooseDecomposition

/-- Rees 環の斉次作用は、加群の自然数次数を加える。 -/
theorem reesFiltrationGradeSMul :
    SetLike.GradedSMul (reesGrade I) (reesFiltrationGrade F) := by
  refine ⟨?_⟩
  intro i j r m hr hm
  change r • m ∈ reesFiltrationGrade F (i + j)
  obtain ⟨x, hx⟩ := hm
  rw [← hx]
  have he : r = reesMonomial I i ⟨r.val.coeff i, r.property i⟩ :=
    Subtype.ext ((mem_reesGrade_iff I i r).mp hr)
  rw [he]
  refine ⟨⟨r.val.coeff i • x.val,
    F.pow_smul_le i j (Submodule.smul_mem_smul (r.property i) x.property)⟩, ?_⟩
  exact (reesFiltration_monomial_smul_single F i j (r.val.coeff i) (r.property i) x).symm

end SerrePositivity.AlgebraicGeometry
