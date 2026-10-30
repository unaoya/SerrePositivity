module

public import SerrePositivity.CLMST.Prop247RankLoci
public import SerrePositivity.CommutativeAlgebra.Localization.Away

/-! # Prop 2.4.7：元の主開上の rank の底変換

g の外の有限 étale な加群の既存 stalk rank 底変換を、元の通常 tensor に移す。
元の S や底変換環の大域的平坦性は要求しない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.CLMST
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- g が可逆な底変換環の元の点の rank は、元の D(g) の対応点の rank と一致する。 -/
theorem prop247_rankAtStalk_baseChange_on_away_point
    (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S]
    (g : R) (hetale : letI := GenericEtale.awayAlgebra R S g
      Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap R S g)))
    (T : Type u) [CommRing T] [Algebra R T] (hg : IsUnit (algebraMap R T g))
    (x : PrimeSpectrum T) (y : PrimeSpectrum.basicOpen g)
    (hy : (y : PrimeSpectrum R) = x.comap (algebraMap R T)) :
    Module.rankAtStalk (R := T) (T ⊗[R] S) x = prop247_awayRank R S g y := by
  let A := Localization.Away g
  let M := Localization.Away (algebraMap R S g)
  letI := GenericEtale.awayAlgebra R S g
  letI : IsScalarTower R A M := GenericEtale.awayAlgebra_scalarTower R S g
  let l : A →ₐ[R] T := IsLocalization.Away.liftAlgHom g (f := Algebra.ofId R T) hg
  letI : Algebra A T := l.toRingHom.toAlgebra
  letI : IsScalarTower R A T := IsScalarTower.of_algHom l
  letI : Algebra.Etale A M := hetale
  letI : Module.Finite A M := GenericEtale.finite_away R S g
  let e : T ⊗[R] S ≃ₐ[T] T ⊗[A] M :=
    (Algebra.TensorProduct.cancelBaseChange R A T T S).symm.trans
      (Algebra.TensorProduct.congr (AlgEquiv.refl : T ≃ₐ[T] T) (originalAwayTensorEquiv R S g))
  let q := x.comap (algebraMap A T)
  have hq : prop247_awaySpectrumHomeomorph R g q = y := by
    apply Subtype.ext
    rw [prop247_awaySpectrumHomeomorph_apply]
    change PrimeSpectrum.comap (algebraMap R A)
      (PrimeSpectrum.comap (algebraMap A T) x) = (y : PrimeSpectrum R)
    rw [← PrimeSpectrum.comap_comp_apply, ← IsScalarTower.algebraMap_eq R A T]
    exact hy.symm
  calc
    Module.rankAtStalk (R := T) (T ⊗[R] S) x =
        Module.rankAtStalk (R := T) (T ⊗[A] M) x :=
      congrFun (Module.rankAtStalk_eq_of_equiv e.toLinearEquiv) x
    _ = Module.rankAtStalk (R := A) M q := Module.rankAtStalk_baseChange (M := M) x
    _ = prop247_awayRank R S g y := by
      rw [← hq]
      exact (prop247_awayRank_at_localization R S g q).symm

/-- 元の D(g) 上の定 rank は、任意の実通常底変換の D(g) 上で保存される。 -/
theorem prop247_awayRank_baseChange_constant
    (R S B : Type u) [CommRing R] [CommRing S] [CommRing B]
    [Algebra R S] [Algebra R B] [Module.Finite R S]
    (g : R) (hetale : letI := GenericEtale.awayAlgebra R S g
      Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap R S g)))
    (r : ℕ) (hRank : ∀ x : PrimeSpectrum.basicOpen g, prop247_awayRank R S g x = r) :
    ∀ x : PrimeSpectrum.basicOpen (algebraMap R B g),
      prop247_awayRank B (B ⊗[R] S) (algebraMap R B g) x = r := by
  let A := B ⊗[R] S
  let d := algebraMap R B g
  let L := Localization.Away d
  let M := Localization.Away (algebraMap B A d)
  letI := GenericEtale.awayAlgebra B A d
  letI : IsScalarTower B L M := GenericEtale.awayAlgebra_scalarTower B A d
  have hg : IsUnit (algebraMap R L g) := by
    rw [IsScalarTower.algebraMap_apply R B L]
    exact IsLocalization.Away.algebraMap_isUnit (S := L) d
  let e : M ≃ₐ[L] L ⊗[R] S := (originalAwayTensorEquiv B A d).symm.trans
    (Algebra.TensorProduct.cancelBaseChange R B L L S)
  intro x
  let z := (prop247_awaySpectrumHomeomorph B d).symm x
  have hz : algebraMap R L g ∉ z.asIdeal := fun h =>
    z.isPrime.ne_top (z.asIdeal.eq_top_of_isUnit_mem h hg)
  let y : PrimeSpectrum.basicOpen g := ⟨z.comap (algebraMap R L), hz⟩
  change Module.rankAtStalk (R := L) M z = r
  calc
    Module.rankAtStalk (R := L) M z = Module.rankAtStalk (R := L) (L ⊗[R] S) z :=
      congrFun (Module.rankAtStalk_eq_of_equiv e.toLinearEquiv) z
    _ = prop247_awayRank R S g y :=
      prop247_rankAtStalk_baseChange_on_away_point R S g hetale L hg z y rfl
    _ = r := hRank y

end SerrePositivity.CLMST
