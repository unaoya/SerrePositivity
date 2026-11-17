module

public import SerrePositivity.AlgebraicGeometry.FrobeniusAugmentedRingCoefficients
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
概要：相対アフィン平坦全射の元のアフィン開上に、実際の忠実平坦なČech係数を供給する。
方針：MathlibのappTopの忠実平坦性を、既存のFrobenius係数の完全性へ渡す。
規約：非アフィン基底の大域切断環の平坦性を仮定しない。
使われ方：有限アフィン交叉ごとの相対fppf比較の正の軸。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
universe u
set_option backward.isDefEq.respectTransparency false

/-- 元のアフィン平坦全射のappTopの、同じ増大Frobenius係数のČech完全性。 -/
theorem affineFlatSurjective_appTop_frobeniusCechExact
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine X] [IsAffine Y] [Flat f] [Surjective f]
    (p : ℕ) (hp : p.Prime) (hY : (p : Γ(Y, ⊤)) = 0) :
    SerrePositivity.Cech.AugmentedRingCechExact
      (frobeniusAugmentedRingCoefficients (Arrow.mk f.appTop) p hp hY) := by
  let B : Under Γ(Y, ⊤) := Under.mk f.appTop
  have hff : f.appTop.hom.FaithfullyFlat :=
    (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine f).mp
      ⟨inferInstance, inferInstance⟩
  letI : Module.FaithfullyFlat Γ(Y, ⊤) B.right := hff
  exact frobeniusAugmentedRingCoefficients_exact_of_faithfullyFlat B p hp hY

/-- 元の相対アフィン平坦全射をアフィン開に制限した、同じ係数のČech完全性。 -/
theorem affineFlatSurjective_restrict_frobeniusCechExact
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f] [Flat f] [Surjective f]
    (V : Y.Opens) (hV : IsAffineOpen V) (p : ℕ) (hp : p.Prime)
    (hY : (p : Γ(V.toScheme, ⊤)) = 0) :
    SerrePositivity.Cech.AugmentedRingCechExact
      (frobeniusAugmentedRingCoefficients (Arrow.mk (f ∣_ V).appTop) p hp hY) := by
  letI : IsAffine V.toScheme := hV
  letI : IsAffine (f ⁻¹ᵁ V).toScheme := hV.preimage f
  letI : Surjective (f ∣_ V) := by
    dsimp [morphismRestrict]
    infer_instance
  exact affineFlatSurjective_appTop_frobeniusCechExact (f ∣_ V) p hp hY

end SerrePositivity.AlgebraicGeometry
