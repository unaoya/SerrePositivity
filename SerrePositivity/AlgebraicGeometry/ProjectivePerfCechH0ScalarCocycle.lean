module

public import SerrePositivity.AlgebraicGeometry.ProjectiveHomogeneousFrobeniusH0Stage
public import SerrePositivity.AlgebraicGeometry.ProjectiveHomogeneousFrobeniusChartStage
public import SerrePositivity.AlgebraicGeometry.FullCechH0KernelEvaluation

/-!
概要：順極限後のスカラー H⁰ 類を、実際の標準開環の零次コサイクルで表示する。
方針：H⁰・核の自然性と、各標準開の Frobenius 標準写像の公式を合成する。
規約：右辺は基底のスカラーを各標準開へ送った同じ段の元。
使われ方：F7 の左辺の写像と F8 の実際の Čech 増大写像を同定する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits
universe u
variable {R A : Type u} {ι : Type} [CommRing R] [CommRing A]
variable [LinearOrder ι] [Fintype ι]
variable [Algebra R A] [Algebra (MvPolynomial ι R) A]
variable [IsScalarTower R (MvPolynomial ι R) A]
variable (G : ℕ → Submodule R A) [GradedRing G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]
variable (p : ℕ) (hp : p.Prime) (hR : (p : R) = 0) (hA : (p : A) = 0)

/-- 有限段のスカラー類の零次コサイクルは各標準開の実際の同じスカラーである。
BST13 Lemma 3.8・3.9 の H⁰ に用いる Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem projectivePerfCechH0ScalarClass_of_cocycle
    (n : ℕ) (r : R) (t : Fin 1 → ι) :
    ((fullCechH0KernelIso
      (projectiveFrobeniusRingChartDiagram (ι := ι) G p hp hR hA)).hom.hom
        (projectivePerfCechH0ScalarClass (ι := ι) G p hp hR hA
          (frobeniusDirectLimitOf R p hp hR n r))).val t =
    frobeniusDirectLimitOf _ p hp
      (projectiveHomogeneousChart_primeCast G p hR (cechTupleSupport t)) n
      (algebraMap R ((projectiveHomogeneousChartAlgebraDiagram (ι := ι) G).obj
        (cechTupleSupport t)) r) := by
  rw [projectivePerfCechH0ScalarClass_stage, projectiveHomogeneousFrobeniusRingCechIso_inv]
  rw [fullCechH0KernelIso_naturality_apply, fullCechH0KernelIso_naturality_apply]
  have h := congrArg (fun x ↦
    ((projectiveHomogeneousFrobeniusChartColimitIso (ι := ι) G p hp hR hA).inv.app
      (cechTupleSupport t)).hom
      (((colimit.ι (algebraCechFrobeniusCoefficientFunctor
        (projectiveHomogeneousChartAlgebraDiagram (ι := ι) G) p hp hR) n).app
          (cechTupleSupport t)).hom x))
    (projectiveHomogeneousScalarCechIntH0_cocycle (ι := ι) G r t)
  exact h.trans (projectiveHomogeneousFrobeniusChartColimitIso_stage G p hp hR hA
    (cechTupleSupport t) n _)

/-- 任意の順極限のスカラー類のコサイクルは、各標準開への実際のスカラー写像。 -/
theorem projectivePerfCechH0ScalarClass_cocycle
    (a : FrobeniusDirectLimit R p hp hR) (t : Fin 1 → ι) :
    ((fullCechH0KernelIso
      (projectiveFrobeniusRingChartDiagram (ι := ι) G p hp hR hA)).hom.hom
        (projectivePerfCechH0ScalarClass (ι := ι) G p hp hR hA a)).val t =
      frobeniusDirectLimitMap p hp hR
        (projectiveHomogeneousChart_primeCast G p hR (cechTupleSupport t))
        (algebraMap R ((projectiveHomogeneousChartAlgebraDiagram (ι := ι) G).obj
          (cechTupleSupport t))) a := by
  obtain ⟨n, r, rfl⟩ := DirectLimit.exists_eq_mk
    (frobeniusDirectSystemMap R p hp hR) a
  exact projectivePerfCechH0ScalarClass_of_cocycle G p hp hR hA n r t

end SerrePositivity.AlgebraicGeometry
