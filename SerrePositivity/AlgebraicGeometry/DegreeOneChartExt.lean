module

public import SerrePositivity.AlgebraicGeometry.HomogeneousDegreeOneAlgebraMaps

/-!
概要：次数一の標準開の正規化の全射性と代数写像の生成元での外延性。
方針：斉次分数を正規化の像で表し、全射な多項式表示へ戻す。
規約：既存の標準開の代数構造を保つ。
使われ方：Segre チャートの合成を生成元の計算から照合する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
universe u v
variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
variable (G : ℕ → Submodule R A) [GradedRing G] {f : A} (hf : f ∈ G 1)

/-- 次数一の分母による正規化は、斉次分数の全体へ全射。 -/
theorem homogeneousDegreeOneNormalize_surjective :
    Function.Surjective (homogeneousDegreeOneNormalize G hf) := by
  intro z
  obtain ⟨n, x, hx, rfl⟩ := HomogeneousLocalization.Away.mk_surjective G hf z
  exact ⟨x, homogeneousDegreeOneNormalize_of_mem G hf x (by simpa using hx)⟩

end SerrePositivity.AlgebraicGeometry

namespace SerrePositivity.AlgebraicGeometry
universe u
variable {R A C : Type u} {ι : Type} [CommRing R] [CommRing A] [CommRing C]
variable [Algebra R A] [Algebra R C]
variable (G : ℕ → Submodule R A) [GradedRing G] {f : A} (hf : f ∈ G 1)
local instance degreeOneChartExtAlgebra : Algebra R (HomogeneousLocalization.Away G f) :=
  projectiveHomogeneousAwayAlgebra G f

/-- 全射な次数一表示では、正規化した生成元上の一致がチャートの代数写像を決める。 -/
theorem degreeOneChart_algHom_ext (a : ι → A)
    (hs : Function.Surjective (MvPolynomial.aeval (R := R) a))
    {φ ψ : HomogeneousLocalization.Away G f →ₐ[R] C}
    (h : ∀ k, φ (homogeneousDegreeOneNormalize G hf (a k)) =
      ψ (homogeneousDegreeOneNormalize G hf (a k))) : φ = ψ := by
  have he : (φ.comp (homogeneousDegreeOneNormalizeAlgHom G hf)).comp (MvPolynomial.aeval a) =
      (ψ.comp (homogeneousDegreeOneNormalizeAlgHom G hf)).comp (MvPolynomial.aeval a) := by
    ext k
    simp only [AlgHom.comp_apply, MvPolynomial.aeval_X]
    change φ (homogeneousDegreeOneNormalize G hf (a k)) =
      ψ (homogeneousDegreeOneNormalize G hf (a k))
    exact h k
  apply AlgHom.ext
  intro z
  obtain ⟨x, rfl⟩ := homogeneousDegreeOneNormalize_surjective G hf z
  obtain ⟨p, rfl⟩ := hs x
  exact AlgHom.congr_fun he p

end SerrePositivity.AlgebraicGeometry
