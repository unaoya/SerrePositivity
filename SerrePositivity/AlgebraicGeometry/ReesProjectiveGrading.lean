module

public import SerrePositivity.AlgebraicGeometry.ReesExtendedModule
public import SerrePositivity.CommutativeAlgebra.HilbertSamuel.Graded.Subquotient

/-!
概要：拡大イデアルの Rees 加群に、元の加群の Proj 次数の分解を入れる。
方針：元の次数への射影を係数ごとに持ち上げ、有限個の係数の台をまとめる。
規約：この次数は Rees の変数の次数とは別であり、基底 Rees 環は次数零で作用する。
使われ方：基底 Rees 環上の射影 Čech 有限性の入力。
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.AlgebraicGeometry

universe u

variable {R S M : Type u} [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
variable (I : Ideal R) (G : ℕ → Submodule R M) [DirectSum.Decomposition G]

local instance : Module (reesAlgebra I)
    ((I.map (algebraMap R S)).stableFiltration (⊤ : Submodule S M)).submodule :=
  reesExtendedModule (S := S) (M := M) I

/-- 元の Proj 次数への射影を、拡大イデアルの Rees 加群へ持ち上げる。 -/
def reesProjectiveProjection (d : ℕ) :
    ((I.map (algebraMap R S)).stableFiltration (⊤ : Submodule S M)).submodule →ₗ[reesAlgebra I]
      ((I.map (algebraMap R S)).stableFiltration (⊤ : Submodule S M)).submodule :=
  reesExtendedMap (S := S) I (SerrePositivity.HilbertSerre.gradeProjection G d)

/-- 持ち上げた射影の像としての Proj 次数成分。 -/
def reesProjectiveGrade (d : ℕ) :
    Submodule (reesAlgebra I)
      ((I.map (algebraMap R S)).stableFiltration (⊤ : Submodule S M)).submodule :=
  LinearMap.range (reesProjectiveProjection (S := S) I G d)

/-- Proj 次数の射影は、各 Rees 係数の Proj 次数への射影。 -/
@[simp]
theorem reesProjectiveProjection_coeff (d : ℕ)
    (p : ((I.map (algebraMap R S)).stableFiltration (⊤ : Submodule S M)).submodule) (n : ℕ) :
    (reesProjectiveProjection (S := S) I G d p).val.coeff n =
      (DirectSum.decompose G (p.val.coeff n) d : M) := rfl

/-- Proj 次数の所属は、全ての Rees 係数の所属で判定する。 -/
theorem mem_reesProjectiveGrade_iff (d : ℕ)
    (p : ((I.map (algebraMap R S)).stableFiltration (⊤ : Submodule S M)).submodule) :
    p ∈ reesProjectiveGrade (S := S) I G d ↔ ∀ n, p.val.coeff n ∈ G d := by
  constructor
  · rintro ⟨x, rfl⟩ n
    exact (DirectSum.decompose G (x.val.coeff n) d).property
  · intro hp
    refine ⟨p, ?_⟩
    apply Subtype.ext
    apply PolynomialModule.coeff_injective
    ext n
    rw [reesProjectiveProjection_coeff]
    exact DirectSum.decompose_of_mem_same G (hp n)

set_option maxHeartbeats 800000 in
/-- 二つ目の、Proj 次数による内部直和。 -/
theorem isInternal_reesProjectiveGrade :
    DirectSum.IsInternal (reesProjectiveGrade (S := S) I G) := by
  classical
  let V := ((I.map (algebraMap R S)).stableFiltration (⊤ : Submodule S M)).submodule
  let D : ℕ → Submodule (reesAlgebra I) V := reesProjectiveGrade (S := S) I G
  let p : ℕ → V →ₗ[reesAlgebra I] V := reesProjectiveProjection (S := S) I G
  change DirectSum.IsInternal D
  refine @SerrePositivity.HilbertSerre.isInternal_of_projections
    (reesAlgebra I) inferInstance V inferInstance (reesExtendedModule (S := S) (M := M) I)
    D p ?_ ?_ ?_
  · intro d p
    apply Subtype.ext
    apply PolynomialModule.coeff_injective
    ext n
    rw [reesProjectiveProjection_coeff]
    exact DirectSum.decompose_of_mem_same G
      ((mem_reesProjectiveGrade_iff (S := S) I G d p).mp p.property n)
  · intro d k hkd p
    apply Subtype.ext
    apply PolynomialModule.coeff_injective
    ext n
    rw [reesProjectiveProjection_coeff]
    exact DirectSum.decompose_of_mem_ne G
      ((mem_reesProjectiveGrade_iff (S := S) I G k p).mp p.property n) hkd
  · apply top_unique
    intro p _
    let t := p.val.coeff.support.biUnion (fun n ↦ (DirectSum.decompose G (p.val.coeff n)).support)
    have hp : ∑ d ∈ t, reesProjectiveProjection (S := S) I G d p = p := by
      apply Subtype.ext
      apply PolynomialModule.coeff_injective
      ext n
      simp only [Submodule.coe_sum, PolynomialModule.coeff_sum, Finsupp.finsetSum_apply,
        reesProjectiveProjection_coeff]
      by_cases hn : n ∈ p.val.coeff.support
      · have hs : (DirectSum.decompose G (p.val.coeff n)).support ⊆ t := by
          intro d hd
          exact Finset.mem_biUnion.mpr ⟨n, hn, hd⟩
        calc
          _ = ∑ d ∈ (DirectSum.decompose G (p.val.coeff n)).support,
              (DirectSum.decompose G (p.val.coeff n) d : M) := by
            symm
            apply Finset.sum_subset hs
            intro d hd hdn
            rw [DFinsupp.notMem_support_iff.mp hdn, Submodule.coe_zero]
          _ = _ := DirectSum.sum_support_decompose G (p.val.coeff n)
      · have hz : p.val.coeff n = 0 := Finsupp.notMem_support_iff.mp hn
        simp [hz]
    rw [← hp]
    apply Submodule.sum_mem
    intro d hd
    exact (le_iSup (reesProjectiveGrade (S := S) I G) d) ⟨p, rfl⟩

/-- Rees 加群の Proj 次数分解。 -/
@[instance_reducible]
def reesProjectiveGradeDecomposition :
    DirectSum.Decomposition (reesProjectiveGrade (S := S) I G) :=
  (isInternal_reesProjectiveGrade (S := S) I G).chooseDecomposition

end SerrePositivity.AlgebraicGeometry
