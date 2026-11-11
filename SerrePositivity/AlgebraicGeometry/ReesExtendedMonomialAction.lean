module

public import SerrePositivity.AlgebraicGeometry.ReesExtendedModule

/-!
概要：拡大イデアルの Rees 加群に対する、基底 Rees 環の単項式の作用を計算する。
方針：係数環の写像と単項式の両立性から、既存の単項式作用の公式へ帰着する。
規約：元の基底環の係数は、拡大先の環を経由して作用する。
使われ方：Rees の Čech 比較において、移した作用と実際の斉次作用を照合する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry

variable {R S : Type*} [CommRing R] [CommRing S]
variable (I : Ideal R) (J : Ideal S) (f : R →+* S) (hf : I.map f ≤ J)

/-- Rees 代数の係数写像は、任意の次数の斉次単項式を保つ。 -/
theorem reesMap_monomial (i : ℕ) (a : R) (ha : a ∈ I ^ i) :
    reesMap I J f hf ⟨Polynomial.monomial i a, reesAlgebra.monomial_mem.mpr ha⟩ =
      ⟨Polynomial.monomial i (f a), reesAlgebra.monomial_mem.mpr
        (map_pow_center_le I J f hf i (Ideal.mem_map_of_mem f ha))⟩ := by
  apply Subtype.ext
  exact Polynomial.map_monomial f

section Module
variable {M : Type*} [Algebra R S]
variable [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

/-- 拡大 Rees 加群の次数 j の単項式に、基底 Rees 環の次数 i の単項式を掛ける。
結果の Rees 次数は i+j となる。 -/
theorem reesExtendedModule_monomial_smul_single
    (i j : ℕ) (a : R) (ha : a ∈ I ^ i)
    (m : ((I.map (algebraMap R S)).stableFiltration (⊤ : Submodule S M)).N j) :
    letI := reesExtendedModule (S := S) (M := M) I
    (⟨Polynomial.monomial i a, reesAlgebra.monomial_mem.mpr ha⟩ : reesAlgebra I) •
        reesFiltrationSingle
          ((I.map (algebraMap R S)).stableFiltration (⊤ : Submodule S M)) j m =
      reesFiltrationSingle
        ((I.map (algebraMap R S)).stableFiltration (⊤ : Submodule S M)) (i + j)
        ⟨(algebraMap R S a) • m.val,
          ((I.map (algebraMap R S)).stableFiltration (⊤ : Submodule S M)).pow_smul_le i j
            (Submodule.smul_mem_smul
              (by rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ ha) m.property)⟩ := by
  letI := reesExtendedModule (S := S) (M := M) I
  change (reesMap I (I.map (algebraMap R S)) (algebraMap R S) le_rfl
    ⟨Polynomial.monomial i a, reesAlgebra.monomial_mem.mpr ha⟩) •
      reesFiltrationSingle
        ((I.map (algebraMap R S)).stableFiltration (⊤ : Submodule S M)) j m = _
  rw [reesMap_monomial I (I.map (algebraMap R S)) (algebraMap R S) le_rfl i a ha]
  exact reesFiltration_monomial_smul_single
    ((I.map (algebraMap R S)).stableFiltration (⊤ : Submodule S M)) i j
    (algebraMap R S a) (by rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ ha) m

end Module
end SerrePositivity.AlgebraicGeometry
