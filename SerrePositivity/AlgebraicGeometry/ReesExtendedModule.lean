module

public import SerrePositivity.AlgebraicGeometry.ReesFiltrationModule
public import SerrePositivity.AlgebraicGeometry.ReesExtendedFiltration
public import SerrePositivity.AlgebraicGeometry.ReesMap

/-!
概要：拡大イデアルの Rees 加群に、基底環上の線形写像を係数ごとに作用させる。
方針：係数の有限台写像を使い、基底の Rees 環の作用との可換性を畳み込みで示す。
規約：係数環上の線形性は要求せず、基底環上の線形性だけを使う。
使われ方：Proj 次数の射影を Rees 加群上に持ち上げる。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.AlgebraicGeometry

variable {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
variable [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]
variable (I : Ideal R)

/-- 拡大イデアルの Rees 加群に、基底の Rees 環を作用させる。 -/
@[instance_reducible]
def reesExtendedModule :
    Module (reesAlgebra I)
      ((I.map (algebraMap R S)).stableFiltration (⊤ : Submodule S M)).submodule :=
  Module.compHom _ (reesMap I (I.map (algebraMap R S)) (algebraMap R S) le_rfl)

/-- 係数ごとに基底環上の線形写像を適用する。 -/
def reesExtendedPolynomialMap (f : M →ₗ[R] N) :
    PolynomialModule S M →ₗ[R] PolynomialModule S N :=
  (PolynomialModule.coeffLinearEquiv S R).symm.toLinearMap.comp
    ((Finsupp.mapRange.linearMap f).comp
      (PolynomialModule.coeffLinearEquiv S R).toLinearMap)

/-- 係数写像の値。 -/
@[simp]
theorem reesExtendedPolynomialMap_coeff (f : M →ₗ[R] N)
    (p : PolynomialModule S M) (n : ℕ) :
    (reesExtendedPolynomialMap f p).coeff n = f (p.coeff n) := rfl

/-- 基底の Rees 環の作用は、基底環上の係数の畳み込みで計算できる。 -/
theorem reesExtendedModule_smul_coeff
    (b : reesAlgebra I)
    (p : ((I.map (algebraMap R S)).stableFiltration (⊤ : Submodule S M)).submodule)
    (n : ℕ) :
    letI := reesExtendedModule (S := S) (M := M) I
    (b • p).val.coeff n =
      ∑ a ∈ Finset.antidiagonal n, b.val.coeff a.1 • p.val.coeff a.2 := by
  letI := reesExtendedModule (S := S) (M := M) I
  change (((reesMap I (I.map (algebraMap R S)) (algebraMap R S) le_rfl b).val) •
    p.val).coeff n = _
  rw [PolynomialModule.smul_apply]
  simp only [reesMap_val, Polynomial.coeff_map, algebraMap_smul]

/-- 基底環上の線形写像は、拡大イデアルの Rees 加群の基底 Rees 線形写像を与える。 -/
def reesExtendedMap (f : M →ₗ[R] N) :
    letI := reesExtendedModule (S := S) (M := M) I
    letI := reesExtendedModule (S := S) (M := N) I
    ((I.map (algebraMap R S)).stableFiltration (⊤ : Submodule S M)).submodule →ₗ[reesAlgebra I]
      ((I.map (algebraMap R S)).stableFiltration (⊤ : Submodule S N)).submodule := by
  letI := reesExtendedModule (S := S) (M := M) I
  letI := reesExtendedModule (S := S) (M := N) I
  exact
    { toFun := fun p ↦ ⟨reesExtendedPolynomialMap f p.val, fun n ↦
        reesExtendedAdic_map_mem I f n _ (p.property n)⟩
      map_add' := fun p q ↦ Subtype.ext ((reesExtendedPolynomialMap f).map_add p.val q.val)
      map_smul' := by
        intro b p
        apply Subtype.ext
        apply PolynomialModule.coeff_injective
        ext n
        rw [reesExtendedPolynomialMap_coeff, reesExtendedModule_smul_coeff,
          reesExtendedModule_smul_coeff, map_sum]
        apply Finset.sum_congr rfl
        intro a ha
        exact f.map_smul _ _ }

/-- 拡大 Rees 加群上の写像は、各係数で元の写像を適用する。 -/
@[simp]
theorem reesExtendedMap_coeff (f : M →ₗ[R] N)
    (p : ((I.map (algebraMap R S)).stableFiltration (⊤ : Submodule S M)).submodule)
    (n : ℕ) :
    (reesExtendedMap (S := S) I f p).val.coeff n = f (p.val.coeff n) := rfl

end SerrePositivity.AlgebraicGeometry
