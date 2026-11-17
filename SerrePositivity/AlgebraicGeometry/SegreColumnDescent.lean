module

public import SerrePositivity.AlgebraicGeometry.SegreColumnEvaluation

/-!
概要：次数一の全射表示の関係式を保つ、因子から Segre 座標環への列の写像。
方針：斉次な核の次数成分を照合し、全射代数写像の降下を使う。
規約：選んだ列の座標だけを使い、平坦性を仮定しない。
使われ方：二因子のチャートから Segre 標準開への逆写像。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
universe u
variable {R A B : Type u} {ι κ : Type} [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra R B] (a : ι → A) (b : κ → B) (j : κ)

/-- 一列への代入を同じ商へ送る実際の多項式代数写像。 -/
def segreColumnPolynomialMap : MvPolynomial ι R →ₐ[R] SegreCoordinateRing (R := R) a b :=
  (segreCoordinateProjection (R := R) a b).comp (MvPolynomial.rename (fun k ↦ (k, j)))

variable (G : ℕ → Submodule R A) [GradedRing G] (ha : ∀ k, a k ∈ G 1)
attribute [local instance] MvPolynomial.gradedAlgebra
include G ha

/-- 次数一評価の核は斉次な核である。 -/
theorem degreeOne_aeval_kernel_homogeneous :
    (RingHom.ker (MvPolynomial.aeval (R := R) a).toRingHom).IsHomogeneous
      (MvPolynomial.homogeneousSubmodule ι R) :=
  ((⊥ : HomogeneousIdeal G).comap
    (degreeOneGradedEvaluation G (SetLike.algebraMap_mem_graded G) a ha)).isHomogeneous

/-- 次数一表示の全関係式は、列の評価で消える。 -/
theorem segreColumnPolynomialMap_kernel_le :
    RingHom.ker (MvPolynomial.aeval (R := R) a).toRingHom ≤
      RingHom.ker (segreColumnPolynomialMap (R := R) a b j).toRingHom := by
  classical
  intro p hp
  change segreColumnPolynomialMap (R := R) a b j p = 0
  have hK := degreeOne_aeval_kernel_homogeneous a G ha
  rw [← DirectSum.sum_support_decompose (MvPolynomial.homogeneousSubmodule ι R) p, map_sum]
  apply Finset.sum_eq_zero
  intro n hn
  apply segreCoordinateProjection_column_zero a b j
  · exact (MvPolynomial.mem_homogeneousSubmodule n _).mp
      (DirectSum.decompose (MvPolynomial.homogeneousSubmodule ι R) p n).property
  · exact hK.mem_iff.mp hp n

/-- 次数一の全射表示を使い、列の写像を実際の因子へ降ろす。 -/
def segreColumnFromFactor (hs : Function.Surjective (MvPolynomial.aeval (R := R) a)) :
    A →ₐ[R] SegreCoordinateRing (R := R) a b :=
  AlgHom.liftOfSurjective (MvPolynomial.aeval (R := R) a) hs
    (segreColumnPolynomialMap (R := R) a b j) (segreColumnPolynomialMap_kernel_le a b j G ha)

/-- 因子の次数一生成元の像は、同じ列の座標。 -/
theorem segreColumnFromFactor_generator
    (hs : Function.Surjective (MvPolynomial.aeval (R := R) a)) (k : ι) :
    segreColumnFromFactor a b j G ha hs (a k) =
      segreCoordinateProjection (R := R) a b (MvPolynomial.X (k, j)) := by
  rw [← MvPolynomial.aeval_X (R := R) (f := a) k]
  change AlgHom.liftOfSurjective _ hs _ _ (MvPolynomial.aeval a (MvPolynomial.X k)) = _
  rw [AlgHom.liftOfSurjective_apply]
  simp [segreColumnPolynomialMap]

end SerrePositivity.AlgebraicGeometry
