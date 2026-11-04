module

public import SerrePositivity.CommutativeAlgebra.EtaleStratification.Factorization

/-!
# 商環の初層と元の環の層の比較

## 概要
R/I の被約化を R/√I と同一視し、主開集合の局所化にも同型を移す。

## 方針
R → (R/I)_red の核を計算して第一同型定理を適用する。

## 規約
同型は R の元の標準像を標準像へ送る。

## 使われ方
Noetherian 帰納の商環上の分解を、元の環の層へ戻す。
-/

@[expose] public section
noncomputable section
universe u

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.CommutativeAlgebra

theorem ker_reducedQuotientMap {R : Type u} [CommRing R] (I : Ideal R) :
    RingHom.ker ((Ideal.Quotient.mk (nilradical (R ⧸ I))).comp (Ideal.Quotient.mk I)) =
      I.radical := by
  ext x
  change Ideal.Quotient.mk (nilradical (R ⧸ I)) (Ideal.Quotient.mk I x) = 0 ↔ x ∈ I.radical
  simp only [Ideal.Quotient.eq_zero_iff_mem, mem_nilradical, IsNilpotent,
    ← map_pow, Ideal.mem_radical_iff]

/-- 商環の被約化と根基による商の標準同型。 -/
def reducedQuotientEquiv {R : Type u} [CommRing R] (I : Ideal R) :
    R ⧸ I.radical ≃+* (R ⧸ I) ⧸ (⊥ : Ideal (R ⧸ I)).radical :=
  (Ideal.quotEquivOfEq (ker_reducedQuotientMap I).symm).trans
    (((Ideal.Quotient.mk (nilradical (R ⧸ I))).comp (Ideal.Quotient.mk I)).quotientKerEquivOfSurjective
      ((Ideal.Quotient.mk_surjective).comp Ideal.Quotient.mk_surjective))

@[simp]
theorem reducedQuotientEquiv_mk {R : Type u} [CommRing R] (I : Ideal R) (x : R) :
    reducedQuotientEquiv I (Ideal.Quotient.mk I.radical x) =
      Ideal.Quotient.mk (nilradical (R ⧸ I)) (Ideal.Quotient.mk I x) := by
  simp [reducedQuotientEquiv]
  rfl

/-- 商環の初層は、元の環で I の上に取った層と標準的に同型。 -/
def stratumQuotientEquiv {R : Type u} [CommRing R] (I : Ideal R) (g : R) :
    StratumRing I g ≃+* StratumRing (⊥ : Ideal (R ⧸ I)) (Ideal.Quotient.mk I g) :=
  IsLocalization.ringEquivOfRingEquiv
    (M := Submonoid.powers (Ideal.Quotient.mk I.radical g))
    (T := Submonoid.powers (Ideal.Quotient.mk (⊥ : Ideal (R ⧸ I)).radical
      (Ideal.Quotient.mk I g)))
    (StratumRing I g) (StratumRing ⊥ (Ideal.Quotient.mk I g)) (reducedQuotientEquiv I) (by
    rw [Submonoid.map_powers]
    exact congrArg Submonoid.powers (reducedQuotientEquiv_mk I g))

@[simp]
theorem stratumQuotientEquiv_unit {R : Type u} [CommRing R] (I : Ideal R) (g x : R) :
    stratumQuotientEquiv I g (stratumUnit I g x) =
      stratumUnit (⊥ : Ideal (R ⧸ I)) (Ideal.Quotient.mk I g) (Ideal.Quotient.mk I x) := by
  change stratumQuotientEquiv I g
    (algebraMap (R ⧸ I.radical) _ (Ideal.Quotient.mk I.radical x)) = _
  rw [stratumQuotientEquiv, IsLocalization.ringEquivOfRingEquiv_eq, reducedQuotientEquiv_mk]
  rfl

/-- 商環上に誘導される射。 -/
def quotientStratumBaseMap {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (I : Ideal R) : R ⧸ I →+* S ⧸ I.map f :=
  Ideal.quotientMap (I.map f) f Ideal.le_comap_map

@[simp]
theorem quotientStratumBaseMap_mk {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (I : Ideal R) (x : R) :
    quotientStratumBaseMap f I (Ideal.Quotient.mk I x) = Ideal.Quotient.mk (I.map f) (f x) := rfl

/-- 商環の初層の目標に合わせた、目標側の標準同型。 -/
def stratumQuotientTargetEquiv {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (I : Ideal R) (g : R) :
    StratumRing (I.map f) (f g) ≃+*
      StratumRing ((⊥ : Ideal (R ⧸ I)).map (quotientStratumBaseMap f I))
        (quotientStratumBaseMap f I (Ideal.Quotient.mk I g)) :=
  (stratumQuotientEquiv (I.map f) (f g)).trans
    (stratumRingEquivOfIdealEq (Ideal.map_bot (f := quotientStratumBaseMap f I)).symm
      (Ideal.Quotient.mk (I.map f) (f g)))

@[simp]
theorem stratumQuotientTargetEquiv_unit {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (I : Ideal R) (g : R) (y : S) :
    stratumQuotientTargetEquiv f I g (stratumUnit (I.map f) (f g) y) =
      stratumUnit ((⊥ : Ideal (R ⧸ I)).map (quotientStratumBaseMap f I))
        (quotientStratumBaseMap f I (Ideal.Quotient.mk I g)) (Ideal.Quotient.mk (I.map f) y) := by
  simp only [stratumQuotientTargetEquiv, RingEquiv.trans_apply, stratumQuotientEquiv_unit,
    stratumRingEquivOfIdealEq_unit]

/-- 商環の初層と元の環の層の比較は、誘導される射と可換。 -/
theorem stratumQuotientEquiv_naturality {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (I : Ideal R) (g : R) :
    (stratumQuotientTargetEquiv f I g).toRingHom.comp (stratumMap f I g) =
      (stratumMap (quotientStratumBaseMap f I) ⊥ (Ideal.Quotient.mk I g)).comp
        (stratumQuotientEquiv I g).toRingHom := by
  apply stratumRing_hom_ext I g
  intro x
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
    stratumMap_unit, stratumQuotientTargetEquiv_unit, stratumQuotientEquiv_unit,
    quotientStratumBaseMap_mk]

/-- 商環の初層の有限エタール分解を、元の環の対応する層に戻す。 -/
theorem hasEtaleFactorization_of_quotient_stratum
    {R S : Type u} [CommRing R] [CommRing S] (p : ℕ) (f : R →+* S)
    (I : Ideal R) (g : R)
    (h : HasEtaleFactorization p
      (stratumMap (quotientStratumBaseMap f I) ⊥ (Ideal.Quotient.mk I g))) :
    HasEtaleFactorization p (stratumMap f I g) := by
  have ht := hasEtaleFactorization_transport p (stratumQuotientEquiv I g).symm
    (stratumQuotientTargetEquiv f I g).symm _ h
  have he : ((stratumQuotientTargetEquiv f I g).symm.toRingHom.comp
      (stratumMap (quotientStratumBaseMap f I) ⊥ (Ideal.Quotient.mk I g))).comp
        (stratumQuotientEquiv I g).toRingHom = stratumMap f I g := by
    ext x
    apply (stratumQuotientTargetEquiv f I g).injective
    simpa only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
      RingEquiv.apply_symm_apply] using
      (RingHom.congr_fun (stratumQuotientEquiv_naturality f I g) x).symm
  simpa only [RingEquiv.symm_symm, he] using ht

end SerrePositivity.CommutativeAlgebra
