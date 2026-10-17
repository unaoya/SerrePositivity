module

public import SerrePositivity.CLMST.Prop247RankImages
public import SerrePositivity.CommutativeAlgebra.DoubleLocalizationTensorComparison

/-! # Prop 2.4.7：原典の Ri を通る基底変更の rank

Ri への元の写像を保ち、g を反転した任意の Ri 代数上で元の tensor の rank が一定になる。
Ri の perfectoid 化の存在や Cor 8.12 は使わない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.CLMST
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Ri 上の任意の実基底変更の g の外の点は、元の rank 部分の点に写る。 -/
theorem prop247_awayRank_of_point_over_rankImage
    (R S : Type u) [CommRing R] [IsReduced R] [CommRing S] [Algebra R S]
    [Module.Finite R S] (g : R)
    (hetale : letI := GenericEtale.awayAlgebra R S g
      Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap R S g))) (n : ℕ)
    (T : Type u) [CommRing T] [Algebra R T]
    [Algebra (prop247_openSectionImage R (prop247_rankOpen R S g hetale n)) T]
    [IsScalarTower R (prop247_openSectionImage R (prop247_rankOpen R S g hetale n)) T]
    (x : PrimeSpectrum T) (hx : algebraMap R T g ∉ x.asIdeal) :
    prop247_awayRank R S g ⟨x.comap (algebraMap R T), hx⟩ = n := by
  let I := prop247_openSectionImage R (prop247_rankOpen R S g hetale n)
  have hr : (⟨x.comap (algebraMap R T), hx⟩ : PrimeSpectrum.basicOpen g) ∈
      (Subtype.val : (PrimeSpectrum.basicOpen g) → PrimeSpectrum R) ⁻¹'
        Set.range (PrimeSpectrum.comap
          (prop247_toOpenSectionImage R (prop247_rankOpen R S g hetale n)).toRingHom) := by
    refine ⟨x.comap (algebraMap I T), ?_⟩
    change PrimeSpectrum.comap (algebraMap R I)
      (PrimeSpectrum.comap (algebraMap I T) x) = PrimeSpectrum.comap (algebraMap R T) x
    rw [← PrimeSpectrum.comap_comp_apply, ← IsScalarTower.algebraMap_eq R I T]
  rw [prop247_rankSectionImage_spectrum_on_away] at hr
  exact hr

/-- 任意の Ri 代数 T で g が可逆なら、元の T⊗R S の全ての stalk rank は n である。
元の S の R 上の平坦性や T の平坦性は仮定しない。 -/
theorem prop247_rankAtStalk_baseChange_of_isUnit
    (R S : Type u) [CommRing R] [IsReduced R] [CommRing S] [Algebra R S]
    [Module.Finite R S] (g : R)
    (hetale : letI := GenericEtale.awayAlgebra R S g
      Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap R S g))) (n : ℕ)
    (T : Type u) [CommRing T] [Algebra R T]
    [Algebra (prop247_openSectionImage R (prop247_rankOpen R S g hetale n)) T]
    [IsScalarTower R (prop247_openSectionImage R (prop247_rankOpen R S g hetale n)) T]
    (hg : IsUnit (algebraMap R T g)) (x : PrimeSpectrum T) :
    Module.rankAtStalk (R := T) (T ⊗[R] S) x = n := by
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
  have hx : algebraMap R T g ∉ x.asIdeal := fun h =>
    x.2.ne_top (x.asIdeal.eq_top_of_isUnit_mem h hg)
  have hq : prop247_awaySpectrumHomeomorph R g q =
      (⟨x.comap (algebraMap R T), hx⟩ : PrimeSpectrum.basicOpen g) := by
    apply Subtype.ext
    rw [prop247_awaySpectrumHomeomorph_apply]
    change PrimeSpectrum.comap (algebraMap R A)
      (PrimeSpectrum.comap (algebraMap A T) x) = PrimeSpectrum.comap (algebraMap R T) x
    rw [← PrimeSpectrum.comap_comp_apply, ← IsScalarTower.algebraMap_eq R A T]
  calc
    Module.rankAtStalk (R := T) (T ⊗[R] S) x =
        Module.rankAtStalk (R := T) (T ⊗[A] M) x :=
      congrFun (Module.rankAtStalk_eq_of_equiv e.toLinearEquiv) x
    _ = Module.rankAtStalk (R := A) M q := Module.rankAtStalk_baseChange (M := M) x
    _ = prop247_awayRank R S g (prop247_awaySpectrumHomeomorph R g q) :=
      (prop247_awayRank_at_localization R S g q).symm
    _ = n := by
      rw [hq]
      exact prop247_awayRank_of_point_over_rankImage R S g hetale n T x hx

/-- 任意の Ri 代数 T に対し、元の底変換 T⊗R S の rank は D(g) 上で一定である。
指定した (Ri)_perfd への適用にも、T の平坦性や g 正則性を要求しない。 -/
theorem prop247_awayRank_baseChange_over_rankImage
    (R S : Type u) [CommRing R] [IsReduced R] [CommRing S] [Algebra R S]
    [Module.Finite R S] (g : R)
    (hetale : letI := GenericEtale.awayAlgebra R S g
      Algebra.Etale (Localization.Away g) (Localization.Away (algebraMap R S g))) (n : ℕ)
    (T : Type u) [CommRing T] [Algebra R T]
    [Algebra (prop247_openSectionImage R (prop247_rankOpen R S g hetale n)) T]
    [IsScalarTower R (prop247_openSectionImage R (prop247_rankOpen R S g hetale n)) T]
    (x : PrimeSpectrum.basicOpen (algebraMap R T g)) :
    prop247_awayRank T (T ⊗[R] S) (algebraMap R T g) x = n := by
  let I := prop247_openSectionImage R (prop247_rankOpen R S g hetale n)
  let d := algebraMap R T g
  let L := Localization.Away d
  letI := GenericEtale.awayAlgebra T (T ⊗[R] S) d
  let e : L ⊗[R] S ≃ₐ[L]
      Localization.Away (algebraMap T (T ⊗[R] S) d) :=
    (Algebra.TensorProduct.cancelBaseChange R T L L S).symm.trans
      (originalAwayTensorEquiv T (T ⊗[R] S) d)
  let y := (prop247_awaySpectrumHomeomorph T d).symm x
  change Module.rankAtStalk (R := L)
    (Localization.Away (algebraMap T (T ⊗[R] S) d)) y = n
  rw [← congrFun (Module.rankAtStalk_eq_of_equiv e.toLinearEquiv) y]
  exact prop247_rankAtStalk_baseChange_of_isUnit R S g hetale n L
    (IsLocalization.Away.algebraMap_isUnit d) y

end SerrePositivity.CLMST
