module

public import SerrePositivity.LengthAlgebra.HomologyExactBounds
public import SerrePositivity.PerfectComplex.NormalizedEuler

/-! # 短完全列に対する正規化 Euler 評価

ホモロジーの長完全列を、共通の長さ付きアーベル圏の Euler 定理へ渡す。
項の有限生成性、射影性、環の Noether 性は用いない。
-/

@[expose] public section
universe u
namespace SerrePositivity
open CategoryTheory Limits
variable {R : Type u} [CommRing R] {J : Ideal R} (lam : NormalizedLength R J)

/-- 有界な短完全列で、冪ねじれ性と全ホモロジーの長さの有限性を確認すれば Euler 評価は加法的。 -/
theorem lambdaEuler_shortExact
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)) (hS : S.ShortExact)
    (hb₂ : ∃ a b : ℤ, ∀ i, (i < a ∨ b < i) → IsZero (S.X₂.X i))
    (hb₃ : ∃ a b : ℤ, ∀ i, (i < a ∨ b < i) → IsZero (S.X₃.X i))
    (t₁ : ∀ i, IsPowTorsion J (S.X₁.homology i))
    (t₂ : ∀ i, IsPowTorsion J (S.X₂.homology i))
    (t₃ : ∀ i, IsPowTorsion J (S.X₃.homology i))
    (l₁ : ∀ i, lam.len (S.X₁.homology i) ≠ ⊤)
    (l₂ : ∀ i, lam.len (S.X₂.homology i) ≠ ⊤)
    (l₃ : ∀ i, lam.len (S.X₃.homology i) ≠ ⊤) :
    lambdaEuler lam S.X₂ = lambdaEuler lam S.X₁ + lambdaEuler lam S.X₃ := by
  exact LengthAlgebra.normalizedLength_euler_exact_sequence lam
    (fun i ↦ S.X₁.homology i) (fun i ↦ S.X₂.homology i) (fun i ↦ S.X₃.homology i)
    (fun i ↦ HomologicalComplex.homologyMap S.f i)
    (fun i ↦ HomologicalComplex.homologyMap S.g i)
    (fun i ↦ hS.δ i (i + 1) rfl)
    (fun i ↦ hS.homology_exact₂ i)
    (fun i ↦ hS.homology_exact₃ i (i + 1) rfl)
    (fun i ↦ hS.homology_exact₁ i (i + 1) rfl) t₁ t₂ t₃ l₁ l₂ l₃
    (by
      obtain ⟨a, b, hab⟩ := hb₂
      exact ⟨a, b, fun i hi ↦ isZero_homology_of_isZero_X S.X₂ i (hab i hi)⟩)
    (by
      obtain ⟨a, b, hab⟩ := hb₃
      exact ⟨a, b, fun i hi ↦ isZero_homology_of_isZero_X S.X₃ i (hab i hi)⟩)

end SerrePositivity
