module

public import SerrePositivity.AlgebraicGeometry.ExtendedIdealTensor
public import SerrePositivity.AlgebraicGeometry.RelativeFlatTensor
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
概要：KST §5、Stacks 0810 の拡大素点での有限表示加群の自由性。
方針：基礎環上の平坦性を局所化後へ移し、極大イデアルが拡大であることを使う。
規約：拡大イデアルが素であることを明示し、基礎環の局所化を経由しない。
使われ方：係数イデアルによる平坦化の境界外の局所自由性を確かめる。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct

variable {R S M : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]

/--
概要：基礎環上平坦な有限表示加群は拡大素点で局所化すると自由。
方針：拡大素点での極大イデアルを基礎環のイデアルの像と同定する。
規約：KST §5、Stacks 0810、代数の有限性や幾何学的整性はこの補題には不要。
使われ方：幾何学的整性から拡大素点の素性を得た後の局所自由性の入力。
-/
theorem free_at_extended_prime [Module.Flat R M] [Module.FinitePresentation S M]
    (I : Ideal R) [(I.map (algebraMap R S)).IsPrime] :
    Module.Free (Localization.AtPrime (I.map (algebraMap R S)))
      ((Localization.AtPrime (I.map (algebraMap R S))) ⊗[S] M) := by
  let Q := I.map (algebraMap R S)
  let L := Localization.AtPrime Q
  let : Module.Flat R (L ⊗[S] M) :=
    relativeFlat_localization (R := R) (M := M) Q.primeCompl
  apply free_of_flat_of_maximalIdeal_eq_extendedIdeal (R := R) (S := L)
    (M := L ⊗[S] M) I
  rw [← Localization.AtPrime.map_eq_maximalIdeal]
  change (I.map (algebraMap R S)).map (algebraMap S L) = I.map (algebraMap R L)
  rw [Ideal.map_map, IsScalarTower.algebraMap_eq R S L]

/--
概要：Noether 代数上有限生成で基礎環上平坦な加群は拡大素点で自由。
方針：Noether 性から有限表示性を得て拡大素点での自由性を適用する。
規約：KST §5、Stacks 0810、環の有限生成性と加群の有限生成性を区別する。
使われ方：有限型 Noether 代数での境界外の局所自由性。
-/
theorem free_at_extended_prime_of_finite [IsNoetherianRing S]
    [Module.Flat R M] [Module.Finite S M]
    (I : Ideal R) [(I.map (algebraMap R S)).IsPrime] :
    Module.Free (Localization.AtPrime (I.map (algebraMap R S)))
      ((Localization.AtPrime (I.map (algebraMap R S))) ⊗[S] M) := by
  let : Module.FinitePresentation S M := Module.finitePresentation_of_finite S M
  exact free_at_extended_prime (M := M) I

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
