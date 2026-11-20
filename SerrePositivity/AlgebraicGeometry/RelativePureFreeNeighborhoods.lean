module

public import SerrePositivity.AlgebraicGeometry.PureTransformModule
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus

/-!
概要：KST §5、Stacks 0810・0811 の実際の代数と加群に対する自由化基本開の条件。
方針：基礎素点上の拡大イデアルに属さない自由化元を直接量化する。
規約：定義には押し出しや幾何学的整性の仮定を含めない。
使われ方：テンソル積の表示を変えた後も同じ自由化基本開の結論を扱う。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry

/--
概要：実際の代数上の加群の境界純変換が、基礎環を覆う共通階数の自由化基本開を持つ条件。
方針：各基礎素点の拡大イデアルの外の元で純変換を局所化し、自由性と階数を指定する。
規約：KST §5、Stacks 0810・0811、定義自体に Noether 性や有限性は不要。
使われ方：押し出しの任意の実現で得た自由化元を保持する。
-/
def RelativePureFreeNeighborhoods (R S M : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module S M] (f : R) (r : ℕ) : Prop :=
  ∀ P : PrimeSpectrum R,
    ∃ g ∉ P.asIdeal.map (algebraMap R S),
      Module.Free (Localization.Away g)
          (LocalizedModule.Away g (modulePureTransform (algebraMap R S f) M)) ∧
        Module.finrank (Localization.Away g)
          (LocalizedModule.Away g (modulePureTransform (algebraMap R S f) M)) = r

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
