module

public import SerrePositivity.AlgebraicGeometry.PureTransformBaseLocalization
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-!
概要：KST §5、Stacks 0810・0811 の純変換の局所化と自由 locus の照合。
方針：純変換の局所化比較を素点局所環上の実際の線形同型へ延長する。
規約：元の純変換を境界ねじれによる商として保持する。
使われ方：特別な局所環で得た純変換の自由性を元の純変換の自由 locus へ移す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/--
概要：純変換の素点局所化とテンソル局所化後の純変換の実際の局所環線形同型。
方針：既証の基礎環線形な局所化比較を局所化環上線形な同型へ延長する。
規約：KST §5、Stacks 0810・0811、加群の有限性は不要。
使われ方：局所化後の純変換の自由性から元の純変換の自由 locus を判定する。
-/
def pureTransformAtPrimeTensorEquiv (P : Ideal R) [P.IsPrime] (f : R) :
    LocalizedModule P.primeCompl (modulePureTransform f M) ≃ₗ[Localization.AtPrime P]
      modulePureTransform (algebraMap R (Localization.AtPrime P) f)
        ((Localization.AtPrime P) ⊗[R] M) :=
  (pureTransformBaseLocalizationEquiv (A := Localization.AtPrime P) P.primeCompl f
    (TensorProduct.mk R (Localization.AtPrime P) M 1)).extendScalarsOfIsLocalization
      P.primeCompl (Localization.AtPrime P)

/--
概要：テンソル局所化後の純変換が自由なら、その素点は元の純変換の自由 locus に属する。
方針：実際の素点局所化比較同型で自由性を運ぶ。
規約：KST §5、Stacks 0810・0811、元の純変換の対象を変更しない。
使われ方：一般点の自由性から開自由 locus の基礎環への被覆性を得る。
-/
theorem mem_freeLocus_pureTransform_of_tensorPureFree (P : PrimeSpectrum R) (f : R)
    [Module.Free (Localization.AtPrime P.asIdeal)
      (modulePureTransform (algebraMap R (Localization.AtPrime P.asIdeal) f)
        ((Localization.AtPrime P.asIdeal) ⊗[R] M))] :
    P ∈ Module.freeLocus R (modulePureTransform f M) := by
  apply Module.mem_freeLocus.mpr
  exact Module.Free.of_equiv (pureTransformAtPrimeTensorEquiv (M := M) P.asIdeal f).symm

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
