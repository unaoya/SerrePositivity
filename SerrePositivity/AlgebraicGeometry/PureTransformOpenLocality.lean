module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.PureTransformPullbacks
public import SerrePositivity.AlgebraicGeometry.BasicOpenCoverLifts
public import SerrePositivity.AlgebraicGeometry.TensorCoefficientLocalization
public import SerrePositivity.AlgebraicGeometry.FlatLocalizationFamily

/-!
概要：KST §5、Stacks 0815 のアフィン引き戻しの純変換の平坦性の開被覆に関する局所性。
方針：試験対象の基本開上に射を持ち上げ、係数局所化と局所平坦性判定を使う。
規約：中心の存在や平坦化定理を仮定するのではなく、各被覆上の実際の平坦性を貼り合わせる。
使われ方：局所平坦化した blowup の被覆と共通細分の大域化。
-/

@[expose] public noncomputable section
universe u v w
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
open scoped TensorProduct

/--
概要：各開被覆上で全アフィン引き戻しの純変換が平坦なら全体でも同じ性質が成り立つ。
方針：基本開の持ち上げで局所平坦性を得て、純変換の係数局所化に沿って降下する。
規約：KST §5、Stacks 0815、正則な境界を持つ試験対象について検証する。
使われ方：局所平坦化中心から得た射を共通細分上で貼り合わせる。
-/
theorem hasFlatPurePullbacks_of_openCover {R : CommRingCat.{u}} {X : Scheme.{u}}
    (p : X ⟶ Spec R) (f : R) (M : Type v) [AddCommGroup M] [Module R M]
    (𝒰 : X.OpenCover.{w}) (h𝒰 : ∀ i, HasFlatPurePullbacks (𝒰.f i ≫ p) f M) :
    HasFlatPurePullbacks p f M := by
  intro A j
  dsimp only
  let φ := pureTransformCoefficientMap p j
  let : Algebra R A := φ.toAlgebra
  intro hf
  obtain ⟨r, idx, g, hspan, hg⟩ := exists_basicOpen_cover_lifts 𝒰 A j
  let B (x : PrimeSpectrum A) : CommRingCat.{u} := .of (Localization.Away (r x))
  let ψ (x : PrimeSpectrum A) : R →+* B x := (algebraMap A (B x)).comp φ
  let (x : PrimeSpectrum A) : Algebra R (B x) := (ψ x).toAlgebra
  let (x : PrimeSpectrum A) : Module R (B x) := Algebra.toModule
  let (x : PrimeSpectrum A) : SMul R (B x) := (inferInstance : Algebra R (B x)).toSMul
  have (x : PrimeSpectrum A) : IsScalarTower R A (B x) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let N (x : PrimeSpectrum A) := modulePureTransform (ψ x f) (B x ⊗[R] M)
  have hreg (x : PrimeSpectrum A) : IsRegular (ψ x f) := by
    exact isRegular_iff_mem_nonZeroDivisors.mpr
      (IsLocalization.nonZeroDivisors_le_comap (S := B x)
        (Submonoid.powers (r x)) hf.mem_nonZeroDivisors)
  have hcoeff (x : PrimeSpectrum A) :
      pureTransformCoefficientMap (𝒰.f (idx x) ≫ p) (g x) = ψ x :=
    pureTransformCoefficientMap_factor p (𝒰.f (idx x)) j (g x)
      (CommRingCat.ofHom (algebraMap A (B x))) (hg x)
  have (x : PrimeSpectrum A) : Module.Flat (B x) (N x) := by
    let P (θ : R →+* B x) : Prop :=
      letI : Algebra R (B x) := θ.toAlgebra
      letI : Module R (B x) := Algebra.toModule
      letI : SMul R (B x) := (inferInstance : Algebra R (B x)).toSMul
      IsRegular (θ f) → Module.Flat (B x) (modulePureTransform (θ f) (B x ⊗[R] M))
    have hx : P (ψ x) := (congrArg P (hcoeff x)).mp (h𝒰 (idx x) (B x) (g x))
    exact hx (hreg x)
  have (x : PrimeSpectrum A) : Module.Flat A (B x) :=
    IsLocalization.flat (B x) (Submonoid.powers (r x))
  have (x : PrimeSpectrum A) : Module.Flat A (N x) := Module.Flat.trans A (B x) (N x)
  let η (x : PrimeSpectrum A) : modulePureTransform (φ f) (A ⊗[R] M) →ₗ[A] N x :=
    tensorPureTransformLocalizationMap R A (B x) M (φ f)
  have (x : PrimeSpectrum A) : IsLocalizedModule.Away (r x) (η x) :=
    inferInstanceAs (IsLocalizedModule.Away (r x)
      (tensorPureTransformLocalizationMap R A (B x) M (φ f)))
  exact flat_of_isLocalized_family_span r hspan N η

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
