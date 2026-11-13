module

public import SerrePositivity.AlgebraicGeometry.ReesClosedHomogeneousProjection

/-!
概要：閉厚化への実際の環の射が Frobenius 順極限の比較を保つことを示す。
方針：有限段の比較、評価と余極限の自然性、環の順極限の自然性を合成する。
規約：元の係数図式の閉厚化への射をそのまま用いる。
使われ方：F6 の正次数の全単射性を標準開環の Čech 複体へ移す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
universe u
variable {R A : Type u} {ι : Type} [CommRing R] [CommRing A]
variable [LinearOrder ι] [Fintype ι]
variable [Algebra R A] [Algebra (MvPolynomial ι R) A]
variable [IsScalarTower R (MvPolynomial ι R) A]
variable (I : Ideal R) (G : ℕ → Submodule R A) [GradedRing G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]

local instance (n : ℕ) :
    GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) :=
  reesClosedRingGradedRing I G n

variable (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hA : (p : A) = 0)

/-- 各標準開で、係数順極限と環の順極限の比較は閉厚化への制限に自然。 -/
theorem reesClosedChartFrobeniusRingColimitIso_projection (n : ℕ) (T : Finset ι) :
    (colim.map (reesClosedFrobeniusCoefficientNatTrans I G p hp hR hA n)).app T ≫
        (projectiveChartFrobeniusRingColimitIso
          (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) p hp hR
          (frobeniusQuotientPrimeCast p hA ((I ^ n).map (algebraMap R A))) T).hom =
      (projectiveChartFrobeniusRingColimitIso G p hp hR hA T).hom ≫
        ModuleCat.ofHom (frobeniusDirectLimitMap p hp
          (projectiveHomogeneousChart_primeCast G p hR T)
          (projectiveHomogeneousChart_primeCast
            (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) p hR T)
          (reesClosedHomogeneousChartProjection I G n T)).toAddMonoidHom.toIntLinearMap := by
  let H := projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G
  let hH := frobeniusQuotientPrimeCast p hA ((I ^ n).map (algebraMap R A))
  let rG := ringDirectLimitIntColimitIso
    (frobeniusDirectSystemMap _ p hp (projectiveHomogeneousChart_primeCast G p hR T))
  let rH := ringDirectLimitIntColimitIso
    (frobeniusDirectSystemMap _ p hp (projectiveHomogeneousChart_primeCast H p hR T))
  have hr : colim.map (reesClosedChartRingFrobeniusNatTrans I G p hp hR n T) ≫ rH.inv =
      rG.inv ≫ ModuleCat.ofHom (frobeniusDirectLimitMap p hp
        (projectiveHomogeneousChart_primeCast G p hR T)
        (projectiveHomogeneousChart_primeCast H p hR T)
        (reesClosedHomogeneousChartProjection I G n T)).toAddMonoidHom.toIntLinearMap := by
    apply (cancel_mono rH.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [frobeniusDirectLimitIntColimitIso_naturality]
    simp only [← Category.assoc, rG, Iso.inv_hom_id, Category.id_comp,
      reesClosedChartRingFrobeniusNatTrans, H]
  let ev := (evaluation (Finset ι) (ModuleCat.{u} ℤ)).obj T
  have he := (preservesColimitNatIso ev).hom.naturality
    (reesClosedFrobeniusCoefficientNatTrans I G p hp hR hA n)
  change (colim.map (reesClosedFrobeniusCoefficientNatTrans I G p hp hR hA n)).app T ≫
      (preservesColimitIso ev (projectiveCechFrobeniusCoefficientFunctor H p hp hR hH)).hom =
    (preservesColimitIso ev (projectiveCechFrobeniusCoefficientFunctor G p hp hR hA)).hom ≫
      colim.map (whiskerRight (reesClosedFrobeniusCoefficientNatTrans I G p hp hR hA n) ev) at he
  have hs := congrArg (fun η ↦ colim.map η)
    (reesClosedChartFrobeniusRingSystemIso_projection I G p hp hR hA n T)
  simp only [Functor.map_comp] at hs
  simp only [projectiveChartFrobeniusRingColimitIso, Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc, ← Category.assoc, he]
  simp only [Category.assoc]
  let eG := preservesColimitIso ev (projectiveCechFrobeniusCoefficientFunctor G p hp hR hA)
  have hs' := congrArg (fun k ↦ eG.hom ≫ k ≫ rH.inv) hs
  calc
    _ = eG.hom ≫ (colim.mapIso
        (projectiveChartFrobeniusRingSystemIso G p hp hR hA T)).hom ≫
        colim.map (reesClosedChartRingFrobeniusNatTrans I G p hp hR n T) ≫ rH.inv := by
      simpa only [Category.assoc, Functor.mapIso_hom, eG, ev, rH, H, hH] using hs'
    _ = _ := by rw [hr]

end SerrePositivity.AlgebraicGeometry
