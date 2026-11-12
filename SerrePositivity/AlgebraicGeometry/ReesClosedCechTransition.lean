module

public import SerrePositivity.AlgebraicGeometry.ReesAdicProjectiveQuotientTransition
public import SerrePositivity.AlgebraicGeometry.ReesClosedCechHomology
public import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-!
概要：閉厚化の I 進遷移に関する、Čech 長完全列の自然性を示す。
方針：係数写像の合成則から短完全列の間の射を作り、連結写像の自然性を使う。
規約：中間の M 上の写像は恒等写像。
使われ方：Rees で得た核の零化を、実際の閉厚化の Čech 像の安定化へ渡す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u
variable {R M : Type u} {ι : Type} [CommRing R] [LinearOrder ι] [Fintype ι]
variable [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
variable [IsScalarTower R (MvPolynomial ι R) M]
variable (I : Ideal R) (G : ℕ → Submodule R M) [DirectSum.Decomposition G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]

local instance closedTransitionSourceModule (n : ℕ) : Module (MvPolynomial ι R)
    (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n) :=
  reesAdicProjectivePolynomialModule (ι := ι) (M := M) I n
local instance closedTransitionSourceTower (n : ℕ) : IsScalarTower R (MvPolynomial ι R)
    (reesAdicProjectiveSubmodule (ι := ι) (M := M) I n) :=
  reesAdicProjectivePolynomialModule_scalarTower (ι := ι) (M := M) I n
local instance closedTransitionSourceGraded (n : ℕ) :
    SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R)
      (reesAdicProjectivePiece (ι := ι) I G n) :=
  reesAdicProjectivePieceGradedSMul (ι := ι) I G n
local instance closedTransitionSourceDecomposition (n : ℕ) :
    DirectSum.Decomposition (reesAdicProjectivePiece (ι := ι) I G n) :=
  reesAdicProjectivePieceDecomposition (ι := ι) I G n
local instance closedTransitionQuotientModule (n : ℕ) : Module (MvPolynomial ι R)
    (reesAdicProjectiveQuotient (ι := ι) (M := M) I n) :=
  reesAdicProjectiveQuotientPolynomialModule (ι := ι) (M := M) I n
local instance closedTransitionQuotientTower (n : ℕ) : IsScalarTower R (MvPolynomial ι R)
    (reesAdicProjectiveQuotient (ι := ι) (M := M) I n) :=
  reesAdicProjectiveQuotientPolynomialModule_scalarTower (ι := ι) (M := M) I n
local instance closedTransitionQuotientGraded (n : ℕ) :
    SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R)
      (reesAdicProjectiveQuotientPiece (ι := ι) I G n) :=
  reesAdicProjectiveQuotientPieceGradedSMul (ι := ι) I G n
local instance closedTransitionQuotientDecomposition (n : ℕ) :
    DirectSum.Decomposition (reesAdicProjectiveQuotientPiece (ι := ι) I G n) :=
  reesAdicProjectiveQuotientPieceDecomposition (ι := ι) I G n

/-- IⁱM→IʲM の写像が誘導する、標準開の係数図式の遷移。 -/
def reesAdicProjectiveCechTransitionChartMap (i j : ℕ) (h : j ≤ i) (d : ℤ) :=
  projectiveNatGradedModuleChartMap (ι := ι)
    (reesAdicProjectivePiece (ι := ι) I G i) (reesAdicProjectivePiece (ι := ι) I G j)
    (reesAdicProjectiveTransition (ι := ι) (M := M) I i j h)
    (fun k m hm ↦ reesAdicProjectiveTransition_preservesPiece (ι := ι) I G i j k h m hm) d

/-- 閉厚化の商の間の写像が誘導する、標準開の係数図式の遷移。 -/
def reesAdicProjectiveClosedCechTransitionChartMap (i j : ℕ) (h : j ≤ i) (d : ℤ) :=
  projectiveNatGradedModuleChartMap (ι := ι)
    (reesAdicProjectiveQuotientPiece (ι := ι) I G i)
    (reesAdicProjectiveQuotientPiece (ι := ι) I G j)
    (reesAdicProjectiveQuotientTransition (ι := ι) (M := M) I i j h)
    (reesAdicProjectiveQuotientTransition_preservesPiece (ι := ι) I G i j h) d

/-- 閉厚化の Čech 短完全列の間の、I 進遷移による射。 -/
def reesAdicProjectiveClosedCechShortComplexMap (i j : ℕ) (h : j ≤ i) (d : ℤ) :
    reesAdicProjectiveClosedCechShortComplex (ι := ι) I G i d ⟶
      reesAdicProjectiveClosedCechShortComplex (ι := ι) I G j d where
  τ₁ := fullCechComplexMap (reesAdicProjectiveCechTransitionChartMap (ι := ι) I G i j h d)
  τ₂ := 𝟙 _
  τ₃ := fullCechComplexMap (reesAdicProjectiveClosedCechTransitionChartMap (ι := ι) I G i j h d)
  comm₁₂ := by
    change fullCechComplexMap (reesAdicProjectiveCechTransitionChartMap (ι := ι) I G i j h d) ≫
        fullCechComplexMap (reesAdicProjectiveCechInclusionChartMap (ι := ι) I G j d) =
      fullCechComplexMap (reesAdicProjectiveCechInclusionChartMap (ι := ι) I G i d) ≫ 𝟙 _
    rw [Category.comp_id]
    have hchart : reesAdicProjectiveCechTransitionChartMap (ι := ι) I G i j h d ≫
        reesAdicProjectiveCechInclusionChartMap (ι := ι) I G j d =
      reesAdicProjectiveCechInclusionChartMap (ι := ι) I G i d := by
      unfold reesAdicProjectiveCechTransitionChartMap reesAdicProjectiveCechInclusionChartMap
      rw [projectiveNatGradedModuleChartMap_comp]
      congr 1
    have hm := congrArg (fun η ↦ (fullCechComplexFunctor (R := R) (ι := ι)).map η) hchart
    simp only [Functor.map_comp] at hm
    exact hm
  comm₂₃ := by
    change 𝟙 _ ≫
        fullCechComplexMap (reesAdicProjectiveClosedCechProjectionChartMap (ι := ι) I G j d) =
      fullCechComplexMap (reesAdicProjectiveClosedCechProjectionChartMap (ι := ι) I G i d) ≫
        fullCechComplexMap (reesAdicProjectiveClosedCechTransitionChartMap (ι := ι) I G i j h d)
    rw [Category.id_comp]
    have hchart : reesAdicProjectiveClosedCechProjectionChartMap (ι := ι) I G i d ≫
        reesAdicProjectiveClosedCechTransitionChartMap (ι := ι) I G i j h d =
      reesAdicProjectiveClosedCechProjectionChartMap (ι := ι) I G j d := by
      unfold reesAdicProjectiveClosedCechProjectionChartMap
        reesAdicProjectiveClosedCechTransitionChartMap
      rw [projectiveNatGradedModuleChartMap_comp]
      congr 1
    have hm := congrArg (fun η ↦ (fullCechComplexFunctor (R := R) (ι := ι)).map η) hchart
    simp only [Functor.map_comp] at hm
    exact hm.symm

/-- 実際の閉厚化の Čech コホモロジーの間の I 進遷移。 -/
def reesAdicProjectiveClosedCechTransition (i j : ℕ) (h : j ≤ i) (d : ℤ) (q : ℕ) :
    reesAdicProjectiveClosedCechHomology (ι := ι) I G i d q ⟶
      reesAdicProjectiveClosedCechHomology (ι := ι) I G j d q :=
  HomologicalComplex.homologyMap
    (reesAdicProjectiveClosedCechShortComplexMap (ι := ι) I G i j h d).τ₃ q

/-- 閉厚化への Čech 射影は、I 進遷移と可換。 -/
theorem reesAdicProjectiveClosedCechTransition_projection
    (i j : ℕ) (h : j ≤ i) (d : ℤ) (q : ℕ) :
    reesAdicProjectiveClosedCechProjection (ι := ι) I G i d q ≫
        reesAdicProjectiveClosedCechTransition (ι := ι) I G i j h d q =
      reesAdicProjectiveClosedCechProjection (ι := ι) I G j d q := by
  have hc := (reesAdicProjectiveClosedCechShortComplexMap (ι := ι) I G i j h d).comm₂₃
  change 𝟙 _ ≫ _ = _ at hc
  rw [Category.id_comp] at hc
  have hm := congrArg
    (fun f ↦ (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q).map f) hc
  simp only [Functor.map_comp] at hm
  exact hm.symm

/-- 閉厚化の Čech 連結写像は、I 進遷移と可換。
原典 Stacks 30.20.4(3) の Hⁱ の像の安定化に用いる Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem reesAdicProjectiveClosedCechTransition_connecting
    (i j : ℕ) (h : j ≤ i) (d : ℤ) (q : ℕ) :
    reesAdicProjectiveClosedCechTransition (ι := ι) I G i j h d q ≫
        reesAdicProjectiveClosedCechConnecting (ι := ι) I G j d q =
      reesAdicProjectiveClosedCechConnecting (ι := ι) I G i d q ≫
        reesAdicProjectiveCechTransition (ι := ι) I G i j h d (q + 1) :=
  (HomologicalComplex.HomologySequence.δ_naturality
    (reesAdicProjectiveClosedCechShortComplexMap (ι := ι) I G i j h d)
    (reesAdicProjectiveClosedCechShortComplex_shortExact (ι := ι) I G i d)
    (reesAdicProjectiveClosedCechShortComplex_shortExact (ι := ι) I G j d)
    q (q + 1) rfl).symm

end SerrePositivity.AlgebraicGeometry
