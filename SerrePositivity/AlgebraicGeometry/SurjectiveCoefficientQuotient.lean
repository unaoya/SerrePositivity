module

public import Mathlib.LinearAlgebra.Quotient.Defs
public import Mathlib.Algebra.Module.Submodule.RestrictScalars
public import Mathlib.Algebra.Algebra.Tower

/-!
概要：全射な係数変更の下で、同じ部分加群の商に大きい係数環の作用を入れる。
方針：係数の代表を取って部分加群の閉性を示し、商加群の既存の作用を使う。
規約：元の商の型と小さい環の作用を保つ。
使われ方：R/J を固定した I 進閉厚化の係数表示と遷移。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
variable {P Q M : Type*} [CommRing P] [CommRing Q] [Algebra P Q]
variable [AddCommGroup M] [Module P M] [Module Q M] [IsScalarTower P Q M]
variable (h : Function.Surjective (algebraMap P Q)) (V : Submodule P M)

/-- 全射な係数変更では、小さい環の部分加群は大きい環でも閉じている。 -/
def surjectiveCoefficientSubmodule : Submodule Q M where
  toAddSubmonoid := V.toAddSubmonoid
  smul_mem' := by
    intro q x hx
    obtain ⟨p, rfl⟩ := h q
    rw [algebraMap_smul Q]
    exact V.smul_mem p hx

/-- 係数変更後の部分加群の制限は元の部分加群に一致する。 -/
theorem surjectiveCoefficientSubmodule_restrictScalars :
    (surjectiveCoefficientSubmodule h V).restrictScalars P = V := rfl

/-- 元の商の型を保った、変更後の係数環上の加群構造。 -/
@[instance_reducible]
def surjectiveCoefficientQuotientModule : Module Q (M ⧸ V) :=
  inferInstanceAs (Module Q (M ⧸ surjectiveCoefficientSubmodule h V))

/-- 変更後の係数作用は、元の商の作用と両立する。 -/
theorem surjectiveCoefficientQuotient_scalarTower :
    letI := surjectiveCoefficientQuotientModule h V
    IsScalarTower P Q (M ⧸ V) := by
  letI := surjectiveCoefficientQuotientModule h V
  exact inferInstanceAs (IsScalarTower P Q (M ⧸ surjectiveCoefficientSubmodule h V))

/-- 商への射影は変更後の係数環上でも線形。 -/
def surjectiveCoefficientQuotientProjection :
    letI := surjectiveCoefficientQuotientModule h V
    M →ₗ[Q] M ⧸ V := by
  letI := surjectiveCoefficientQuotientModule h V
  exact (surjectiveCoefficientSubmodule h V).mkQ

/-- 係数変更後の射影も、代表を同じ剰余類へ送る。 -/
theorem surjectiveCoefficientQuotientProjection_apply (x : M) :
    surjectiveCoefficientQuotientProjection h V x = V.mkQ x := rfl

end SerrePositivity.AlgebraicGeometry
