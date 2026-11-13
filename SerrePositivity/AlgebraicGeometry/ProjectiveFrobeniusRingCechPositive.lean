module

public import SerrePositivity.AlgebraicGeometry.ReesClosedFrobeniusRingCech
public import SerrePositivity.AlgebraicGeometry.ProjectiveCechFrobeniusColimitPositive

/-!
概要：標準開の実際の環の Frobenius 順極限の Čech H で、閉厚化の正次数の比較を閉じる。
方針：既存の正次数の全単射性を、同じ制限写像と可換な複体の同型で移す。
規約：核の消滅や像の安定化を追加仮定として残さない。
使われ方：F7 の次数零と合わせ、F8 の同じ環の係数による全複体へ渡す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory CategoryTheory.Limits
universe u
variable {R A : Type u} {ι : Type} [CommRing R] [CommRing A]
variable [LinearOrder ι] [Fintype ι]
variable [Algebra R A] [Algebra (MvPolynomial ι R) A]
variable [IsScalarTower R (MvPolynomial ι R) A]
variable (G : ℕ → Submodule R A) [GradedRing G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]
variable [IsNoetherianRing R] [Module.Finite (MvPolynomial ι R) A]
variable (hspan : (HomogeneousIdeal.irrelevant G).toIdeal ≤ Ideal.span
  (Set.range (fun i : ι ↦ algebraMap (MvPolynomial ι R) A (MvPolynomial.X i))))
variable (I : Ideal R)
variable [IsIso (schemeScalarMorphism (Proj G) (projectiveScalarToGlobalSections G) ∣_
  affineCenterComplement I)]
variable (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hA : (p : A) = 0)


local instance (n : ℕ) :
    GradedRing (projectiveRingQuotientGrade ((I ^ n).map (algebraMap R A)) G) :=
  reesClosedRingGradedRing I G n

include hspan

/-- 標準開の環の Frobenius 順極限による Čech H では、閉厚化への制限は正次数で全単射。
BST13 Lemma 3.9、BS17 Lemma 4.6(i) の Hⁱ に用いる Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem reesClosedFrobeniusRingCechHomologyMap_bijective (q : ℕ) (hq : 0 < q) :
    Function.Bijective
      ((HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (.up ℕ) q).map
        (reesClosedFrobeniusRingCechMap (ι := ι) I G p hp hR hA 1)).hom := by
  let H := HomologicalComplex.homologyFunctor (ModuleCat.{u} ℤ) (.up ℕ) q
  let eG := H.mapIso (projectiveFrobeniusRingChartCechIso (ι := ι) G p hp hR hA)
  let eE := H.mapIso (projectiveFrobeniusRingChartCechIso (ι := ι)
    (projectiveRingQuotientGrade ((I ^ 1).map (algebraMap R A)) G) p hp hR
    (frobeniusQuotientPrimeCast p hA ((I ^ 1).map (algebraMap R A))))
  have hb : Function.Bijective
      (H.map (reesClosedFrobeniusColimitCechMap (ι := ι) G p hp hR hA I 1)).hom :=
    reesClosedFrobeniusColimitCechHomologyMap_bijective G hspan I p hp hR hA q hq
  have : IsIso (H.map (reesClosedFrobeniusColimitCechMap (ι := ι) G p hp hR hA I 1)) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hb
  have hh := congrArg (fun f ↦ H.map f)
    (reesClosedFrobeniusRingCechIso_projection (ι := ι) I G p hp hR hA 1)
  simp only [Functor.map_comp] at hh
  have he : H.map (reesClosedFrobeniusRingCechMap (ι := ι) I G p hp hR hA 1) =
      eG.inv ≫ H.map (reesClosedFrobeniusColimitCechMap (ι := ι) G p hp hR hA I 1) ≫ eE.hom := by
    apply (cancel_epi eG.hom).mp
    simp only [← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    exact hh.symm
  have : IsIso (H.map (reesClosedFrobeniusRingCechMap (ι := ι) I G p hp hR hA 1)) := by
    rw [he]
    infer_instance
  exact (ConcreteCategory.isIso_iff_bijective _).mp inferInstance

end SerrePositivity.AlgebraicGeometry
