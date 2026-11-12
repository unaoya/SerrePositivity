module

public import SerrePositivity.AlgebraicGeometry.ReesIteratedClosedTransition
public import SerrePositivity.AlgebraicGeometry.ReesClosedCechTransition

/-!
概要：二重閉厚化と一重の商の Čech 比較は、I 進遷移と可換。
方針：標準開の係数図式の合成則と、二重商の比較の可換式を使う。
規約：Proj 次数と Čech 次数を固定する。
使われ方：非 flat な閉厚化の形式関数を、一重の商の互換族で表す。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u
variable {R M : Type u} {ι : Type} [CommRing R] [LinearOrder ι] [Fintype ι]
variable [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
variable [IsScalarTower R (MvPolynomial ι R) M]
variable (I J : Ideal R) (G : ℕ → Submodule R M) [DirectSum.Decomposition G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]

local instance iteratedComparisonModule : Module (MvPolynomial ι R)
    (reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) :=
  reesAdicProjectiveQuotientPolynomialModule (ι := ι) (M := M) J 1
local instance iteratedComparisonTower : IsScalarTower R (MvPolynomial ι R)
    (reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) :=
  reesAdicProjectiveQuotientPolynomialModule_scalarTower (ι := ι) (M := M) J 1
local instance iteratedComparisonGraded :
    SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R)
      (reesAdicProjectiveQuotientPiece (ι := ι) J G 1) :=
  reesAdicProjectiveQuotientPieceGradedSMul (ι := ι) J G 1
local instance iteratedComparisonDecomposition :
    DirectSum.Decomposition (reesAdicProjectiveQuotientPiece (ι := ι) J G 1) :=
  reesAdicProjectiveQuotientPieceDecomposition (ι := ι) J G 1
local instance iteratedComparisonQuotientModule (n : ℕ) : Module (MvPolynomial ι R)
    (reesAdicProjectiveQuotient (ι := ι)
      (M := reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) I n) :=
  reesAdicProjectiveQuotientPolynomialModule (ι := ι) I n
local instance iteratedComparisonQuotientTower (n : ℕ) : IsScalarTower R (MvPolynomial ι R)
    (reesAdicProjectiveQuotient (ι := ι)
      (M := reesAdicProjectiveQuotient (ι := ι) (M := M) J 1) I n) :=
  reesAdicProjectiveQuotientPolynomialModule_scalarTower (ι := ι) I n
local instance iteratedComparisonQuotientGraded (n : ℕ) :
    SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R)
      (reesAdicProjectiveQuotientPiece (ι := ι) I
        (reesAdicProjectiveQuotientPiece (ι := ι) J G 1) n) :=
  reesAdicProjectiveQuotientPieceGradedSMul (ι := ι) I
    (reesAdicProjectiveQuotientPiece (ι := ι) J G 1) n

local instance comparisonSumGraded (n : ℕ) :
    SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R)
      (reesIteratedClosedSumPiece (ι := ι) I J G n) :=
  reesIteratedClosedSumPieceGradedSMul (ι := ι) I J G n

/-- 一重の商の遷移が誘導する、標準開の係数図式の写像。 -/
def reesIteratedClosedSumChartTransition (i j : ℕ) (h : j ≤ i) (d : ℤ) :=
  projectiveNatGradedModuleChartMap
    (reesIteratedClosedSumPiece (ι := ι) I J G i)
    (reesIteratedClosedSumPiece (ι := ι) I J G j)
    (reesIteratedClosedSumTransition (ι := ι) (M := M) I J i j h)
    (reesIteratedClosedSumTransition_preservesPiece (ι := ι) I J G i j h) d

/-- 一重の商 M/(JM+IⁿM) の Čech コホモロジーの対象。 -/
abbrev reesIteratedClosedSumCechHomology (n : ℕ) (d : ℤ) (q : ℕ) : ModuleCat.{u} R :=
  (fullCechComplex (projectiveNatGradedModuleChartDiagram (ι := ι)
    (reesIteratedClosedSumPiece (ι := ι) I J G n) d)).homology q

/-- 一重の商の遷移が誘導する、Čech コホモロジーの写像。 -/
def reesIteratedClosedSumCechTransition (i j : ℕ) (h : j ≤ i) (d : ℤ) (q : ℕ) :
    reesIteratedClosedSumCechHomology (ι := ι) I J G i d q ⟶
      reesIteratedClosedSumCechHomology (ι := ι) I J G j d q :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q).map
    (fullCechComplexMap (reesIteratedClosedSumChartTransition (ι := ι) I J G i j h d))

/-- 二重閉厚化と一重の商の、標準開の係数図式の比較同型。 -/
def reesIteratedClosedChartIso (n : ℕ) (d : ℤ) :=
  projectiveNatGradedModuleChartIso
    (reesAdicProjectiveQuotientPiece (ι := ι) I
      (reesAdicProjectiveQuotientPiece (ι := ι) J G 1) n)
    (reesIteratedClosedSumPiece (ι := ι) I J G n)
    (reesIteratedClosedQuotientLinearEquiv (ι := ι) (M := M) I J n)
    (reesIteratedClosedQuotientLinearEquiv_preservesPiece (ι := ι) I J G n)
    (reesIteratedClosedQuotientLinearEquiv_symm_preservesPiece (ι := ι) I J G n) d

/-- 二重閉厚化の標準開での比較は、実際の遷移と可換。 -/
theorem reesIteratedClosedChartIso_transition (i j : ℕ) (h : j ≤ i) (d : ℤ) :
    (reesIteratedClosedChartIso (ι := ι) I J G i d).hom ≫
        reesIteratedClosedSumChartTransition (ι := ι) I J G i j h d =
      reesAdicProjectiveClosedCechTransitionChartMap (ι := ι) I
        (reesAdicProjectiveQuotientPiece (ι := ι) J G 1) i j h d ≫
        (reesIteratedClosedChartIso (ι := ι) I J G j d).hom := by
  dsimp only [reesIteratedClosedChartIso, projectiveNatGradedModuleChartIso]
  unfold reesIteratedClosedSumChartTransition reesAdicProjectiveClosedCechTransitionChartMap
  rw [projectiveNatGradedModuleChartMap_comp, projectiveNatGradedModuleChartMap_comp]
  congr 1
  exact reesIteratedClosedQuotientLinearEquiv_transition (ι := ι) (M := M) I J i j h

/-- 二重閉厚化の Čech 比較は、実際の I 進遷移と可換。
原典 Stacks 30.20.5 の Hⁱ の形式関数に用いる、閉厚化の自然性の Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem reesIteratedClosedCechHomologyIso_transition
    (i j : ℕ) (h : j ≤ i) (d : ℤ) (q : ℕ) :
    (reesIteratedClosedCechHomologyIso (ι := ι) I J G i d q).hom ≫
        reesIteratedClosedSumCechTransition (ι := ι) I J G i j h d q =
      reesAdicProjectiveClosedCechTransition (ι := ι) I
        (reesAdicProjectiveQuotientPiece (ι := ι) J G 1) i j h d q ≫
        (reesIteratedClosedCechHomologyIso (ι := ι) I J G j d q).hom := by
  let K := fullCechComplexFunctor (R := R) (ι := ι) ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q
  calc
    _ = K.map (reesIteratedClosedChartIso (ι := ι) I J G i d).hom ≫
        K.map (reesIteratedClosedSumChartTransition (ι := ι) I J G i j h d) := rfl
    _ = K.map ((reesIteratedClosedChartIso (ι := ι) I J G i d).hom ≫
        reesIteratedClosedSumChartTransition (ι := ι) I J G i j h d) := (K.map_comp _ _).symm
    _ = K.map (reesAdicProjectiveClosedCechTransitionChartMap (ι := ι) I
        (reesAdicProjectiveQuotientPiece (ι := ι) J G 1) i j h d ≫
        (reesIteratedClosedChartIso (ι := ι) I J G j d).hom) := congrArg (fun η ↦ K.map η)
      (reesIteratedClosedChartIso_transition (ι := ι) I J G i j h d)
    _ = _ := K.map_comp _ _

end SerrePositivity.AlgebraicGeometry
