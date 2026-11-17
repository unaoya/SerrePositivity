module

public import SerrePositivity.AlgebraicGeometry.FrobeniusDirectLimitInvariance
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
概要：実際のnil閉厚化のアフィン切断の写像を、同じFrobenius順極限の同型へ送る。
方針：元のappTopの全射性とSpecの全射性からnil核を得る。
規約：元の環準同型を保ち、一様な冪零指数やNoether性は仮定しない。
使われ方：Noether帰納の被約化と元のタプル被覆の閉厚化の係数移送。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
universe u
set_option backward.isDefEq.respectTransparency false

/-- 実際のアフィンなnil閉厚化のappTopは、元の環の普遍同相である。 -/
theorem affineNilImmersion_appTop_universalHomeomorphism
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine X] [IsAffine Y]
    [IsClosedImmersion f] [Surjective f] :
    SerrePositivity.CommutativeAlgebra.IsUniversalHomeomorphism f.appTop.hom := by
  have hs : Surjective (Spec.map f.appTop) :=
    (MorphismProperty.arrow_mk_iso_iff @Surjective (arrowIsoSpecΓOfIsAffine f)).mp
      inferInstance
  have hs' : Function.Surjective (PrimeSpectrum.comap f.appTop.hom) :=
    (surjective_iff (Spec.map f.appTop)).mp hs
  have hk : RingHom.ker f.appTop.hom ≤ nilradical Γ(Y, ⊤) :=
    (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical f.appTop.hom).mp hs'.denseRange
  exact SerrePositivity.CommutativeAlgebra.isUniversalHomeomorphism_of_nil_kernel
    f.appTop.hom (f.app_surjective ⊤ (isAffineOpen_top Y)) hk

/-- 非アフィンでもよい基底のアフィン開への元のnil閉厚化の制限にも同じ係数を使う。 -/
theorem affineNilImmersion_restrict_appTop_universalHomeomorphism
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f] [Surjective f]
    (V : Y.Opens) (hV : IsAffineOpen V) :
    SerrePositivity.CommutativeAlgebra.IsUniversalHomeomorphism (f ∣_ V).appTop.hom := by
  letI : IsAffine V.toScheme := hV
  letI : IsAffine (f ⁻¹ᵁ V).toScheme := hV.preimage f
  letI : Surjective (f ∣_ V) := by
    dsimp [morphismRestrict]
    infer_instance
  exact affineNilImmersion_appTop_universalHomeomorphism (f ∣_ V)

/-- 実際のnil閉厚化の元のappTopによるcanonicalなFrobenius順極限の環同型。 -/
def affineNilImmersion_frobeniusEquiv
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine X] [IsAffine Y]
    [IsClosedImmersion f] [Surjective f] (p : ℕ) (hp : p.Prime)
    (hY : (p : Γ(Y, ⊤)) = 0) (hX : (p : Γ(X, ⊤)) = 0) :
    FrobeniusDirectLimit Γ(Y, ⊤) p hp hY ≃+* FrobeniusDirectLimit Γ(X, ⊤) p hp hX :=
  frobeniusDirectLimitUniversalHomeomorphismEquiv p hp hY hX f.appTop.hom
    (affineNilImmersion_appTop_universalHomeomorphism f)

/-- 同じcanonicalな同型の順方向は、元のappTopの実際のFrobenius写像。 -/
theorem affineNilImmersion_frobeniusEquiv_toRingHom
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffine X] [IsAffine Y]
    [IsClosedImmersion f] [Surjective f] (p : ℕ) (hp : p.Prime)
    (hY : (p : Γ(Y, ⊤)) = 0) (hX : (p : Γ(X, ⊤)) = 0) :
    (affineNilImmersion_frobeniusEquiv f p hp hY hX).toRingHom =
      frobeniusDirectLimitMap p hp hY hX f.appTop.hom := rfl

end SerrePositivity.AlgebraicGeometry
