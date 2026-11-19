module

public meta import SerrePositivity.Util.DeprecatedAlias
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-!
概要：KST §5、Stacks 0810・0811 の自由な素点での局所階数と任意の基底変更。
方針：素点局所化の実同型と自由加群のスカラー拡大の階数保存を使う。
規約：元の加群の全体での平坦性は要求しない。
使われ方：一般点で自由な相対平坦加群の階数を blowup チャートへ移す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct
open TensorProduct

variable {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M]

/--
概要：縮約した素点で自由なら、その素点での階数は任意の基底変更で保たれる。
方針：局所化と基底変更の取消同型を合成して、自由な局所加群の階数保存へ還元する。
規約：KST §5、Stacks 0810・0811、加群の全体での平坦性や有限性は不要。
使われ方：拡大一般点における階数の基底変更の照合。
-/
theorem rankAtStalk_baseChange_of_mem_freeLocus (P : PrimeSpectrum S)
    (hfree : P.comap (algebraMap R S) ∈ Module.freeLocus R M) :
    Module.rankAtStalk (S ⊗[R] M) P =
      Module.rankAtStalk M (P.comap (algebraMap R S)) := by
  let Q : PrimeSpectrum R := P.comap (algebraMap R S)
  let : Module.Free (Localization.AtPrime Q.asIdeal) (LocalizedModule Q.asIdeal.primeCompl M) :=
    Module.mem_freeLocus.mp hfree
  let := Localization.AtPrime.algebraOfLiesOver Q.asIdeal P.asIdeal
  let E : LocalizedModule P.asIdeal.primeCompl (S ⊗[R] M) ≃ₗ[Localization.AtPrime P.asIdeal]
      Localization.AtPrime P.asIdeal ⊗[Localization.AtPrime Q.asIdeal]
        LocalizedModule Q.asIdeal.primeCompl M :=
    LocalizedModule.equivTensorProduct _ _ ≪≫ₗ
      (AlgebraTensorModule.cancelBaseChange R S _ _ M) ≪≫ₗ
      (AlgebraTensorModule.cancelBaseChange R _ _ _ M).symm ≪≫ₗ
      (AlgebraTensorModule.congr (LinearEquiv.refl _ _)
        (LocalizedModule.equivTensorProduct _ M).symm)
  rw [Module.rankAtStalk, E.finrank_eq]
  exact Module.finrank_baseChange

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
