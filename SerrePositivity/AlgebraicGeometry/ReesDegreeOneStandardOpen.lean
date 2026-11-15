module

public import SerrePositivity.AlgebraicGeometry.ReesDegreeOnePolynomialAction
public import Mathlib.RingTheory.GradedAlgebra.RingHom

/-!
概要：Rees の有限な次数一表示から、射影 Čech の標準開の被覆条件を得る。
方針：graded な評価と次数成分の比較で斉次原像を選び、正次数の元を生成イデアルへ入れる。
規約：実際の全射評価から導き、irrelevant ideal の条件を追加仮定にしない。
使われ方：G3 の Rees Proj の標準開と 2f の射影四角形の接続。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open _root_.AlgebraicGeometry
universe u v
variable {R : Type u} {ι : Type v} [CommRing R] (I : Ideal R) (a : ι → I)
attribute [local instance] MvPolynomial.gradedAlgebra

/-- 実際の次数一評価を束ねた graded な環準同型。 -/
def reesDegreeOneGradedHom :
    (MvPolynomial.homogeneousSubmodule ι R) →+*ᵍ (reesGrade I) where
  toRingHom := (MvPolynomial.aeval (R := R) (fun j ↦ reesDegreeOne I (a j))).toRingHom
  map_mem := fun hf ↦ reesDegreeOne_aeval_mem I a _ hf

/-- 全射な次数一評価の各斉次元には同じ次数の斉次原像がある。 -/
theorem exists_reesDegreeOne_homogeneous_lift
    (h : Function.Surjective (MvPolynomial.aeval (R := R) (fun j ↦ reesDegreeOne I (a j))))
    {d : ℕ} (x : reesAlgebra I) (hx : x ∈ reesGrade I d) :
    ∃ f : MvPolynomial ι R, f.IsHomogeneous d ∧
      MvPolynomial.aeval (R := R) (fun j ↦ reesDegreeOne I (a j)) f = x := by
  classical
  obtain ⟨f, hf⟩ := h x
  let g := reesDegreeOneGradedHom I a
  refine ⟨DirectSum.decompose (MvPolynomial.homogeneousSubmodule ι R) f d,
    (DirectSum.decompose (MvPolynomial.homogeneousSubmodule ι R) f d).property, ?_⟩
  have H := g.map_directSumDecompose (x := f) (i := d)
  change MvPolynomial.aeval (R := R) (fun j ↦ reesDegreeOne I (a j))
      (DirectSum.decompose (MvPolynomial.homogeneousSubmodule ι R) f d) =
    (DirectSum.decompose (reesGrade I)
      (MvPolynomial.aeval (R := R) (fun j ↦ reesDegreeOne I (a j)) f) d : reesAlgebra I) at H
  rw [hf, DirectSum.decompose_of_mem_same (reesGrade I) hx] at H
  exact H

/-- 全射な次数一評価の生成元は irrelevant ideal を生成する。 -/
theorem reesDegreeOne_irrelevant_le_span
    (h : Function.Surjective (MvPolynomial.aeval (R := R) (fun j ↦ reesDegreeOne I (a j)))) :
    (HomogeneousIdeal.irrelevant (reesGrade I)).toIdeal ≤
      Ideal.span (Set.range (fun j ↦ reesDegreeOne I (a j))) := by
  apply (HomogeneousIdeal.toIdeal_irrelevant_le _).mpr
  intro d hd x hx
  obtain ⟨f, hf, he⟩ := exists_reesDegreeOne_homogeneous_lift I a h x hx
  apply Ideal.pow_le_self (Nat.ne_of_gt hd)
  rw [Ideal.mem_span_pow_iff_exists_isHomogeneous]
  refine ⟨MvPolynomial.map (algebraMap R (reesAlgebra I)) f, hf.map _, ?_⟩
  rw [MvPolynomial.eval_map]
  exact he

/-- 同じ評価の次数一元の標準開は実際の Rees Proj を被覆する。 -/
theorem iSup_reesDegreeOne_basicOpen
    (h : Function.Surjective (MvPolynomial.aeval (R := R) (fun j ↦ reesDegreeOne I (a j)))) :
    ⨆ j, Proj.basicOpen (reesGrade I) (reesDegreeOne I (a j)) = ⊤ :=
  Proj.iSup_basicOpen_eq_top _ _ (reesDegreeOne_irrelevant_le_span I a h)

end SerrePositivity.AlgebraicGeometry
