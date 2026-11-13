module

public import SerrePositivity.AlgebraicGeometry.ReesClosedCechIntFrobeniusBounds
public import SerrePositivity.AlgebraicGeometry.LinearDirectLimitComparison

/-!
概要：実際の Čech H の Frobenius 順極限と、閉厚化への比較を作る。
方針：有限段の核の消滅と像の持ち上げを、加群の順極限判定へ渡す。
規約：BST13 Lemma 3.9 の正次数の Hⁱ に対応する Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。
使われ方：F6 の正次数の比較。完全化した係数図式の Čech H との比較は別途行う。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u
variable {R A : Type u} {ι : Type} [CommRing R] [CommRing A]
variable [Algebra R A] [Algebra (MvPolynomial ι R) A]
variable [IsScalarTower R (MvPolynomial ι R) A]
variable [LinearOrder ι] [Fintype ι]
variable (G : ℕ → Submodule R A) [DirectSum.Decomposition G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]
variable [SetLike.GradedMonoid G]
variable (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hA : (p : A) = 0)

/-- 実際の標準開 Čech H の Frobenius に沿う加群の順極限。 -/
abbrev ProjectiveCechFrobeniusDirectLimit (q : ℕ) :=
  DirectLimit (fun _ : ℕ ↦ ProjectiveCechIntHomology (ι := ι) G q)
    (fun i j (_h : i ≤ j) ↦ projectiveCechIntFrobeniusHomology (ι := ι) G p hp hR hA (j - i) q)

variable (I : Ideal R)

/-- 実際の閉厚化への射影が誘導する、Čech H の Frobenius 順極限の写像。 -/
def reesClosedCechFrobeniusDirectLimitMap (q : ℕ) :
    ProjectiveCechFrobeniusDirectLimit (ι := ι) G p hp hR hA q →ₗ[ℤ]
    ProjectiveCechFrobeniusDirectLimit (ι := ι)
      (projectiveRingQuotientGrade ((I ^ 1).map (algebraMap R A)) G) p hp hR
      (frobeniusQuotientPrimeCast p hA ((I ^ 1).map (algebraMap R A))) q :=
  linearDirectLimitComparison
    (fun i j (_h : i ≤ j) ↦ projectiveCechIntFrobeniusHomology (ι := ι) G p hp hR hA (j - i) q)
    (fun i j (_h : i ≤ j) ↦ projectiveCechIntFrobeniusHomology (ι := ι)
      (projectiveRingQuotientGrade ((I ^ 1).map (algebraMap R A)) G) p hp hR
      (frobeniusQuotientPrimeCast p hA ((I ^ 1).map (algebraMap R A))) (j - i) q)
    (fun _ ↦ reesClosedCechIntProjection (ι := ι) I G 1 q)
    (fun i j _ x ↦ (reesClosedCechIntProjection_frobenius (ι := ι) I G p hp hR hA 1 (j - i) q x).symm)

variable [IsNoetherianRing R] [Module.Finite (MvPolynomial ι R) A]

/-- 中心の冪による零化の下で、閉厚化への Čech H の Frobenius 順極限の射は単射。 -/
theorem reesClosedCechFrobeniusDirectLimitMap_injective (q : ℕ)
    (hkill : ∃ k : ℕ, I ^ k •
      (⊤ : Submodule R (reesAdicProjectiveCechTarget (ι := ι) G 0 q)) = ⊥) :
    Function.Injective (reesClosedCechFrobeniusDirectLimitMap (ι := ι) G p hp hR hA I q) := by
  have h := linearDirectLimitComparison_injective
    (R := ℤ)
    (fun i j (_h : i ≤ j) ↦ projectiveCechIntFrobeniusHomology (ι := ι) G p hp hR hA (j - i) q)
    (fun i j (_h : i ≤ j) ↦ projectiveCechIntFrobeniusHomology (ι := ι)
      (projectiveRingQuotientGrade ((I ^ 1).map (algebraMap R A)) G) p hp hR
      (frobeniusQuotientPrimeCast p hA ((I ^ 1).map (algebraMap R A))) (j - i) q)
    (fun _ ↦ reesClosedCechIntProjection (ι := ι) I G 1 q)
    (fun i j _ x ↦ (reesClosedCechIntProjection_frobenius (ι := ι) I G p hp hR hA 1 (j - i) q x).symm)
    (by
      intro n x hx
      obtain ⟨e, he⟩ := reesClosedCechIntProjection_kernel_eventually_zero
        (ι := ι) I G p hp hR hA q hkill x hx
      refine ⟨n + e, Nat.le_add_right n e, ?_⟩
      simpa only [Nat.add_sub_cancel_left] using he)
  exact h

/-- 閉厚化への Čech H の Frobenius 順極限の射は、像の安定化により全射。 -/
theorem reesClosedCechFrobeniusDirectLimitMap_surjective (q : ℕ) :
    Function.Surjective (reesClosedCechFrobeniusDirectLimitMap (ι := ι) G p hp hR hA I q) := by
  have h := linearDirectLimitComparison_surjective
    (R := ℤ)
    (fun i j (_h : i ≤ j) ↦ projectiveCechIntFrobeniusHomology (ι := ι) G p hp hR hA (j - i) q)
    (fun i j (_h : i ≤ j) ↦ projectiveCechIntFrobeniusHomology (ι := ι)
      (projectiveRingQuotientGrade ((I ^ 1).map (algebraMap R A)) G) p hp hR
      (frobeniusQuotientPrimeCast p hA ((I ^ 1).map (algebraMap R A))) (j - i) q)
    (fun _ ↦ reesClosedCechIntProjection (ι := ι) I G 1 q)
    (fun i j _ x ↦ (reesClosedCechIntProjection_frobenius (ι := ι) I G p hp hR hA 1 (j - i) q x).symm)
    (by
      intro n x
      obtain ⟨e, y, hy⟩ := reesClosedCechIntProjection_frobenius_eventually_lifts
        (ι := ι) I G p hp hR hA q x
      refine ⟨n + e, Nat.le_add_right n e, y, ?_⟩
      simpa only [Nat.add_sub_cancel_left] using hy)
  exact h

end SerrePositivity.AlgebraicGeometry
