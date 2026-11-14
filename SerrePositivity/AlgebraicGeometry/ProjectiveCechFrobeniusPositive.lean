module

public import SerrePositivity.AlgebraicGeometry.ProjectiveCechFrobeniusDirectLimit
public import SerrePositivity.AlgebraicGeometry.ProjectiveCechSupportGradedPower

/-!
概要：中心外で同型な射影スキームの正次数 Čech H の Frobenius 順極限を、閉厚化と比較する。
方針：F5 の幾何学的な零化と、2e の核・像評価からの順極限判定を組み合わせる。
規約：BST13 Lemma 3.9 の正次数の Hⁱ に使う Čech 版。分離的なスキームの準連接層では
アフィン被覆の Čech と一致する（Stacks 30.2.6）が、この比較は形式化しない。
使われ方：F6 の核・像の計算。完全化した係数図式の H との比較は別途行う。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry CategoryTheory
universe u
variable {R A : Type u} {ι : Type} [CommRing R] [CommRing A]
variable [LinearOrder ι] [Fintype ι]
variable [Algebra R A] [Algebra (MvPolynomial ι R) A]
variable [IsScalarTower R (MvPolynomial ι R) A]
variable (G : ℕ → Submodule R A) [GradedRing G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]
variable [IsNoetherianRing R] [Module.Finite (MvPolynomial ι R) A]

/-- 中心外で同型な射影スキームの正次数の実際の Čech H の Frobenius 順極限は、
閉厚化の同じ順極限へ実際の制限写像によって全単射に移る。 -/
theorem projectiveCechFrobeniusDirectLimit_closed_bijective
    (hspan : (HomogeneousIdeal.irrelevant G).toIdeal ≤ Ideal.span
      (Set.range (fun i : ι ↦ algebraMap (MvPolynomial ι R) A (MvPolynomial.X i))))
    (I : Ideal R)
    [IsIso (schemeScalarMorphism (Proj G) (projectiveScalarToGlobalSections G) ∣_
      affineCenterComplement I)]
    (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hA : (p : A) = 0)
    (q : ℕ) (hq : 0 < q) :
    Function.Bijective (reesClosedCechFrobeniusDirectLimitMap (ι := ι) G p hp hR hA I q) := by
  constructor
  · exact reesClosedCechFrobeniusDirectLimitMap_injective (ι := ι) G p hp hR hA I q
      (projectiveCechSupport_graded_power_annihilates (ι := ι) G hspan I q hq)
  · exact reesClosedCechFrobeniusDirectLimitMap_surjective (ι := ι) G p hp hR hA I q

end SerrePositivity.AlgebraicGeometry
