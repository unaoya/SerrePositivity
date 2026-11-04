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

namespace SerrePositivity.CommutativeAlgebra

private theorem ker_reducedQuotientMap {R : Type u} [CommRing R] (I : Ideal R) :
    RingHom.ker ((Ideal.Quotient.mk (nilradical (R ⧸ I))).comp (Ideal.Quotient.mk I)) =
      I.radical := by
  ext x
  change Ideal.Quotient.mk (nilradical (R ⧸ I)) (Ideal.Quotient.mk I x) = 0 ↔ x ∈ I.radical
  simp only [Ideal.Quotient.eq_zero_iff_mem, mem_nilradical, IsNilpotent,
    ← map_pow, Ideal.mem_radical_iff]

/-- 商環の被約化と根基による商の標準同型。 -/
def reducedQuotientEquiv {R : Type u} [CommRing R] (I : Ideal R) :
    R ⧸ I.radical ≃+* (R ⧸ I) ⧸ nilradical (R ⧸ I) :=
  (Ideal.quotEquivOfEq (ker_reducedQuotientMap I).symm).trans
    (((Ideal.Quotient.mk (nilradical (R ⧸ I))).comp (Ideal.Quotient.mk I)).quotientKerEquivOfSurjective
      ((Ideal.Quotient.mk_surjective).comp Ideal.Quotient.mk_surjective))

@[simp]
theorem reducedQuotientEquiv_mk {R : Type u} [CommRing R] (I : Ideal R) (x : R) :
    reducedQuotientEquiv I (Ideal.Quotient.mk I.radical x) =
      Ideal.Quotient.mk (nilradical (R ⧸ I)) (Ideal.Quotient.mk I x) := by
  simp [reducedQuotientEquiv]

/-- 商環の初層は、元の環で I の上に取った層と標準的に同型。 -/
def stratumQuotientEquiv {R : Type u} [CommRing R] (I : Ideal R) (g : R) :
    StratumRing I g ≃+* StratumRing (⊥ : Ideal (R ⧸ I)) (Ideal.Quotient.mk I g) :=
  IsLocalization.ringEquivOfRingEquiv _ _ (reducedQuotientEquiv I) (by
    rw [Submonoid.map_powers]
    congr 1
    exact reducedQuotientEquiv_mk I g)

@[simp]
theorem stratumQuotientEquiv_unit {R : Type u} [CommRing R] (I : Ideal R) (g x : R) :
    stratumQuotientEquiv I g (stratumUnit I g x) =
      stratumUnit (⊥ : Ideal (R ⧸ I)) (Ideal.Quotient.mk I g) (Ideal.Quotient.mk I x) := by
  change stratumQuotientEquiv I g
    (algebraMap (R ⧸ I.radical) _ (Ideal.Quotient.mk I.radical x)) = _
  rw [stratumQuotientEquiv, IsLocalization.ringEquivOfRingEquiv_eq, reducedQuotientEquiv_mk]
  rfl

end SerrePositivity.CommutativeAlgebra
