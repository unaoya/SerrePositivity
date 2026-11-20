module

public import SerrePositivity.AlgebraicGeometry.GenericPureFreeBaseLocalization
public import SerrePositivity.AlgebraicGeometry.BasicOpenCoverLifts

/-!
概要：KST §5、Stacks 0811 の基礎を覆う自由化基本開の始域開被覆に関する局所性。
方針：各試験素点の基本開を被覆成分へ持ち上げ、一般点自由性を係数局所化から戻す。
規約：元の代数の実分裂を明示し、共通階数は要求しない。
使われ方：第二段チャートごとの自由化を一つの blowup 上でまとめる。
-/

@[expose] public noncomputable section
universe u v w
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
open scoped TensorProduct

/--
概要：開被覆の各成分で全 Noether アフィン引き戻しに自由化基本開があれば、全体でも同じ性質が成り立つ。
方針：基本開上の持ち上げと純変換の一般点自由性の局所化比較を使う。
規約：KST §5、Stacks 0811、元の代数は平坦有限表示かつ幾何学的整、加群はその上有限。
使われ方：階数の異なる第二段自由化チャートを大域で貼り合わせる。
-/
theorem hasBoundaryFreeOpenPullbacks_of_openCover
    {A : CommRingCat.{u}} (B : Type u) [CommRing B] [Algebra A B]
    [Module.Flat A B] [Algebra.FinitePresentation A B]
    [GeometricallyIntegral (Spec.map (CommRingCat.ofHom (algebraMap A B)))]
    {M ι : Type*} [AddCommGroup M] [Module B M] [Module.Finite B M]
    (e : B →ₗ[A] (ι →₀ A)) (s : (ι →₀ A) →ₗ[A] B) (hse : s.comp e = LinearMap.id)
    {X : Scheme.{u}} (p : X ⟶ Spec A) (f : A) (𝒰 : X.OpenCover.{w})
    (h𝒰 : ∀ i, HasBoundaryFreeOpenPullbacks B (𝒰.f i ≫ p) f M) :
    HasBoundaryFreeOpenPullbacks B p f M := by
  intro C hC j
  dsimp only
  let φ := pureTransformCoefficientMap p j
  let : Algebra A C := φ.toAlgebra
  intro hf
  apply (boundaryPureFreeOpens_iff_genericPureFree A B C M (φ f)).mpr
  dsimp only
  intro P
  obtain ⟨r, i, g, hPr, hg⟩ := exists_basicOpen_cover_lift 𝒰 C j P
  let E : CommRingCat.{u} := .of (Localization.Away r)
  let ψ : A →+* E := (algebraMap C E).comp φ
  let : Algebra A E := ψ.toAlgebra
  let : @IsScalarTower A C E (inferInstance : Algebra A C).toSMul
      (inferInstance : Algebra C E).toSMul (inferInstance : Algebra A E).toSMul :=
    IsScalarTower.of_algebraMap_eq' (R := A) (S := C) (A := E) rfl
  have hreg : IsRegular (ψ f) :=
    isRegular_iff_mem_nonZeroDivisors.mpr
      (IsLocalization.nonZeroDivisors_le_comap (S := E) (Submonoid.powers r)
        (isRegular_iff_mem_nonZeroDivisors.mp hf))
  have hcoeff : pureTransformCoefficientMap (𝒰.f i ≫ p) g = ψ :=
    pureTransformCoefficientMap_factor p (𝒰.f i) j g
      (CommRingCat.ofHom (algebraMap C E)) hg
  have hN : BoundaryPureFreeOpens A B E M (ψ f) := by
    let T (θ : A →+* E) : Prop :=
      letI : Algebra A E := θ.toAlgebra
      IsRegular (θ f) → BoundaryPureFreeOpens A B E M (θ f)
    exact ((congrArg T hcoeff).mp (h𝒰 i E g)) hreg
  have hP : P ∈ Set.range (PrimeSpectrum.comap (algebraMap C E)) := by
    rw [PrimeSpectrum.localization_away_comap_range E r]
    exact hPr
  obtain ⟨Q, hQ⟩ := hP
  have hfree := (boundaryPureFreeOpens_iff_genericPureFree A B E M (ψ f)).mp hN Q
  have h := (genericPureTransformFree_baseLocalization_iff A B C E M e s hse
    (Submonoid.powers r) (φ f) Q).mp hfree
  rwa [hQ] at h

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
