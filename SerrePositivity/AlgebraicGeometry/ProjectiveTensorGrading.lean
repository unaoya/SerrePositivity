module

public import SerrePositivity.AlgebraicGeometry.ProjectiveTensorPolynomialModule
public import SerrePositivity.AlgebraicGeometry.ProjectiveNatGrading

/-!
概要：基底変更した多項式加群の次数成分を、元の次数成分のテンソル像で定める。
方針：純テンソルと単項式で次数を計算し、加法で一般の場合へ広げる。
規約：次数付き作用には平坦性を仮定せず、次数成分の像だけを使う。
使われ方：B[X] 加群の実際の標準開図式と、テンソル係数の図式との比較の入口。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct
variable {R B M ι : Type*} [CommRing R] [CommRing B] [Algebra R B]
variable [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
variable [IsScalarTower R (MvPolynomial ι R) M]

local instance projectiveTensorGradingCoefficientModule {V : Type*}
    [AddCommGroup V] [Module R V] : Module B (V ⊗[R] B) :=
  tensorRightCoefficientModule
local instance projectiveTensorGradingPolynomialModule :
    Module (MvPolynomial ι B) (M ⊗[R] B) := projectiveTensorPolynomialModule
local instance projectiveTensorGradingCoefficientTower :
    IsScalarTower B (MvPolynomial ι B) (M ⊗[R] B) :=
  projectiveTensorPolynomial_coefficient_scalarTower

/-- 基底変更した次数成分は、元の次数成分のテンソル積の像。 -/
def projectiveTensorPiece (G : ℕ → Submodule R M) (j : ℕ) :
    Submodule B (M ⊗[R] B) :=
  LinearMap.range (tensorRightCoefficientMap (B := B) (G j).subtype)

/-- 元の次数成分の純テンソルは、基底変更後の同じ次数成分に入る。 -/
theorem projectiveTensorPiece_tmul_mem (G : ℕ → Submodule R M) (j : ℕ)
    (m : M) (hm : m ∈ G j) (b : B) :
    m ⊗ₜ[R] b ∈ projectiveTensorPiece (B := B) G j :=
  ⟨(⟨m, hm⟩ : G j) ⊗ₜ[R] b, rfl⟩

variable (G : ℕ → Submodule R M)
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]

/-- 単項式の作用は、テンソル像で定めた次数を加える。 -/
theorem projectiveTensorPiece_monomial_smul_mem {i j : ℕ} (k : ι →₀ ℕ)
    (hk : k.degree = i) (b : B) (z : M ⊗[R] B)
    (hz : z ∈ projectiveTensorPiece (B := B) G j) :
    MvPolynomial.monomial k b • z ∈ projectiveTensorPiece (B := B) G (i + j) := by
  obtain ⟨w, rfl⟩ := hz
  induction w using TensorProduct.inductionOn with
  | tmul m c =>
    change MvPolynomial.monomial k b • (m.val ⊗ₜ[R] c) ∈ _
    rw [projectiveTensorPolynomial_monomial_tmul]
    have hmono : MvPolynomial.monomial k (1 : R) ∈
        MvPolynomial.homogeneousSubmodule ι R i :=
      MvPolynomial.isHomogeneous_monomial (1 : R) hk
    exact projectiveTensorPiece_tmul_mem G (i + j) _
      (SetLike.GradedSMul.smul_mem hmono m.property) _
  | add x y hx hy =>
    simpa only [map_add, smul_add] using (projectiveTensorPiece (B := B) G (i + j)).add_mem hx hy

/-- 基底変更後の B[X] の斉次作用は、テンソル像の次数を保つ。 -/
theorem projectiveTensorPiece_gradedSMul :
    SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι B)
      (projectiveTensorPiece (B := B) G) where
  smul_mem {i j} {p} {z} hp hz := by
    classical
    rw [← p.support_sum_monomial_coeff, Finset.sum_smul]
    apply Submodule.sum_mem
    intro k hk
    apply projectiveTensorPiece_monomial_smul_mem G k _ _ z hz
    exact (Finsupp.degree_apply k).trans (hp.degree_eq_sum_deg_support hk).symm

section Naturality
variable {N : Type*} [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N]
variable [IsScalarTower R (MvPolynomial ι R) N]
variable (H : ℕ → Submodule R N) (f : M →ₗ[MvPolynomial ι R] N)

omit [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G] in
/-- 次数を保つ元の加群写像は、テンソル像の次数成分も保つ。 -/
theorem projectiveTensorPiece_map_mem (hf : ∀ j, ∀ m ∈ G j, f m ∈ H j)
    (j : ℕ) (z : M ⊗[R] B) (hz : z ∈ projectiveTensorPiece (B := B) G j) :
    projectiveTensorPolynomialMap (B := B) f z ∈ projectiveTensorPiece (B := B) H j := by
  obtain ⟨w, rfl⟩ := hz
  induction w using TensorProduct.inductionOn with
  | tmul m b =>
    change projectiveTensorPolynomialMap f (m.val ⊗ₜ[R] b) ∈ _
    rw [projectiveTensorPolynomialMap_tmul]
    exact projectiveTensorPiece_tmul_mem H j _ (hf j m.val m.property) b
  | add x y hx hy =>
    simpa only [map_add] using (projectiveTensorPiece (B := B) H j).add_mem hx hy

end Naturality
end SerrePositivity.AlgebraicGeometry
