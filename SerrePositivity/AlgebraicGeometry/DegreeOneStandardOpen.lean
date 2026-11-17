module

public import SerrePositivity.AlgebraicGeometry.DegreeOneGradedEvaluation
public import SerrePositivity.AlgebraicGeometry.ProjectiveProjScalarSections
public import Mathlib.RingTheory.GradedAlgebra.RingHom
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
概要：全射な次数一表示から、斉次原像と標準開の被覆条件を得る。
方針：graded な評価の次数分解との整合性と、正次数の斉次多項式のイデアルを使う。
規約：irrelevant ideal の条件を追加仮定にしない。
使われ方：Segre の二つの因子の標準開被覆。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
universe u v
variable {R A : Type u} {ι : Type v} [CommRing R] [CommRing A] [Algebra R A]
variable (G : ℕ → Submodule R A) [GradedRing G] (a : ι → A) (ha : ∀ i, a i ∈ G 1)
attribute [local instance] MvPolynomial.gradedAlgebra
include ha

/-- 全射な次数一表示の斉次元には、同じ次数の斉次原像がある。 -/
theorem exists_degreeOne_homogeneous_lift
    (hs : Function.Surjective (MvPolynomial.aeval (R := R) a))
    {d : ℕ} (x : A) (hx : x ∈ G d) :
    ∃ f : MvPolynomial ι R, f.IsHomogeneous d ∧ MvPolynomial.aeval (R := R) a f = x := by
  classical
  obtain ⟨f, hf⟩ := hs x
  let g := degreeOneGradedEvaluation G (fun r ↦ (projectiveScalarToZero G r).property) a ha
  refine ⟨DirectSum.decompose (MvPolynomial.homogeneousSubmodule ι R) f d,
    (DirectSum.decompose (MvPolynomial.homogeneousSubmodule ι R) f d).property, ?_⟩
  have H := g.map_directSumDecompose (x := f) (i := d)
  change MvPolynomial.aeval (R := R) a
      (DirectSum.decompose (MvPolynomial.homogeneousSubmodule ι R) f d) =
    (DirectSum.decompose G (MvPolynomial.aeval (R := R) a f) d : A) at H
  rw [hf, DirectSum.decompose_of_mem_same G hx] at H
  exact H

/-- 全射な次数一表示の生成元のイデアルは irrelevant ideal を含む。 -/
theorem degreeOne_irrelevant_le_span
    (hs : Function.Surjective (MvPolynomial.aeval (R := R) a)) :
    (HomogeneousIdeal.irrelevant G).toIdeal ≤ Ideal.span (Set.range a) := by
  apply (HomogeneousIdeal.toIdeal_irrelevant_le _).mpr
  intro d hd x hx
  obtain ⟨f, hf, he⟩ := exists_degreeOne_homogeneous_lift G a ha hs x hx
  apply Ideal.pow_le_self (Nat.ne_of_gt hd)
  rw [Ideal.mem_span_pow_iff_exists_isHomogeneous]
  refine ⟨MvPolynomial.map (algebraMap R A) f, hf.map _, ?_⟩
  rw [MvPolynomial.eval_map]
  exact he

end SerrePositivity.AlgebraicGeometry
