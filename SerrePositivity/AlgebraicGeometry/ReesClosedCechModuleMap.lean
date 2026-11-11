module

public import SerrePositivity.AlgebraicGeometry.ReesAdicProjectiveModuleMap
public import SerrePositivity.AlgebraicGeometry.ReesClosedCechTransition

/-!
概要：次数を保つ加群写像から、実際の閉厚化の Čech 写像を作る。
方針：商加群の標準開図式の写像を Čech 関手へ送り、合成則で可換性を示す。
規約：基底環と多項式環を固定し、flat 性は仮定しない。
使われ方：係数写像と閉厚化に対する形式関数の自然性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory
universe u
variable {R M N : Type u} {ι : Type} [CommRing R] [LinearOrder ι] [Fintype ι]
variable [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
variable [IsScalarTower R (MvPolynomial ι R) M]
variable [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N]
variable [IsScalarTower R (MvPolynomial ι R) N]
variable (I : Ideal R) (G : ℕ → Submodule R M) (H : ℕ → Submodule R N)
variable [DirectSum.Decomposition G] [DirectSum.Decomposition H]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) G]
variable [SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R) H]
variable (f : M →ₗ[MvPolynomial ι R] N) (hf : ∀ j, ∀ x ∈ G j, f x ∈ H j)

local instance moduleCechSourceQuotientModule (n : ℕ) : Module (MvPolynomial ι R)
    (reesAdicProjectiveQuotient (ι := ι) (M := M) I n) :=
  reesAdicProjectiveQuotientPolynomialModule (ι := ι) (M := M) I n
local instance moduleCechSourceQuotientTower (n : ℕ) : IsScalarTower R (MvPolynomial ι R)
    (reesAdicProjectiveQuotient (ι := ι) (M := M) I n) :=
  reesAdicProjectiveQuotientPolynomialModule_scalarTower (ι := ι) (M := M) I n
local instance moduleCechSourceQuotientGraded (n : ℕ) :
    SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R)
      (reesAdicProjectiveQuotientPiece (ι := ι) I G n) :=
  reesAdicProjectiveQuotientPieceGradedSMul (ι := ι) I G n
local instance moduleCechTargetQuotientModule (n : ℕ) : Module (MvPolynomial ι R)
    (reesAdicProjectiveQuotient (ι := ι) (M := N) I n) :=
  reesAdicProjectiveQuotientPolynomialModule (ι := ι) (M := N) I n
local instance moduleCechTargetQuotientTower (n : ℕ) : IsScalarTower R (MvPolynomial ι R)
    (reesAdicProjectiveQuotient (ι := ι) (M := N) I n) :=
  reesAdicProjectiveQuotientPolynomialModule_scalarTower (ι := ι) (M := N) I n
local instance moduleCechTargetQuotientGraded (n : ℕ) :
    SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R)
      (reesAdicProjectiveQuotientPiece (ι := ι) I H n) :=
  reesAdicProjectiveQuotientPieceGradedSMul (ι := ι) I H n
/-- 加群写像から得られる、実際の閉厚化の標準開図式の写像。 -/
def reesAdicProjectiveClosedCechModuleChartMap (n : ℕ) (d : ℤ) :=
  projectiveNatGradedModuleChartMap (ι := ι)
    (reesAdicProjectiveQuotientPiece (ι := ι) I G n)
    (reesAdicProjectiveQuotientPiece (ι := ι) I H n)
    (reesAdicProjectiveQuotientMap I f n)
    (reesAdicProjectiveQuotientMap_preservesPiece I f G H hf n) d

/-- 加群写像が誘導する、実際の閉厚化の Čech コホモロジーの写像。 -/
def reesAdicProjectiveClosedCechModuleMap (n : ℕ) (d : ℤ) (q : ℕ) :
    reesAdicProjectiveClosedCechHomology (ι := ι) I G n d q ⟶
      reesAdicProjectiveClosedCechHomology (ι := ι) I H n d q :=
  (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q).map
    (fullCechComplexMap (reesAdicProjectiveClosedCechModuleChartMap I G H f hf n d))

/-- 標準開の図式の商写像は、閉厚化への射影と可換。 -/
theorem reesAdicProjectiveClosedCechModuleChartMap_projection (n : ℕ) (d : ℤ) :
    reesAdicProjectiveClosedCechProjectionChartMap (ι := ι) I G n d ≫
        reesAdicProjectiveClosedCechModuleChartMap I G H f hf n d =
      projectiveNatGradedModuleChartMap G H f hf d ≫
        reesAdicProjectiveClosedCechProjectionChartMap (ι := ι) I H n d := by
  unfold reesAdicProjectiveClosedCechProjectionChartMap reesAdicProjectiveClosedCechModuleChartMap
  rw [projectiveNatGradedModuleChartMap_comp, projectiveNatGradedModuleChartMap_comp]
  congr 1

/-- 標準開の図式の商写像は、I 進遷移と可換。 -/
theorem reesAdicProjectiveClosedCechModuleChartMap_transition
    (i j : ℕ) (h : j ≤ i) (d : ℤ) :
    reesAdicProjectiveClosedCechModuleChartMap I G H f hf i d ≫
        reesAdicProjectiveClosedCechTransitionChartMap (ι := ι) I H i j h d =
      reesAdicProjectiveClosedCechTransitionChartMap (ι := ι) I G i j h d ≫
        reesAdicProjectiveClosedCechModuleChartMap I G H f hf j d := by
  unfold reesAdicProjectiveClosedCechModuleChartMap reesAdicProjectiveClosedCechTransitionChartMap
  rw [projectiveNatGradedModuleChartMap_comp, projectiveNatGradedModuleChartMap_comp]
  congr 1
  exact reesAdicProjectiveQuotientMap_transition I f i j h

/-- 実際の閉厚化の Čech 写像は、元の Čech コホモロジーからの射影と可換。
原典 Stacks 30.20.5 の Hⁱ の形式関数に用いる自然性の Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem reesAdicProjectiveClosedCechModuleMap_projection (n : ℕ) (d : ℤ) (q : ℕ) :
    reesAdicProjectiveClosedCechProjection (ι := ι) I G n d q ≫
        reesAdicProjectiveClosedCechModuleMap I G H f hf n d q =
      projectiveNatGradedModuleCechHomologyMap G H f hf d q ≫
        reesAdicProjectiveClosedCechProjection (ι := ι) I H n d q := by
  let K := fullCechComplexFunctor (R := R) (ι := ι) ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q
  calc
    _ = K.map (reesAdicProjectiveClosedCechProjectionChartMap (ι := ι) I G n d) ≫
        K.map (reesAdicProjectiveClosedCechModuleChartMap I G H f hf n d) := rfl
    _ = K.map (reesAdicProjectiveClosedCechProjectionChartMap (ι := ι) I G n d ≫
        reesAdicProjectiveClosedCechModuleChartMap I G H f hf n d) := (K.map_comp _ _).symm
    _ = K.map (projectiveNatGradedModuleChartMap G H f hf d ≫
        reesAdicProjectiveClosedCechProjectionChartMap (ι := ι) I H n d) := congrArg
      (fun η ↦ K.map η) (reesAdicProjectiveClosedCechModuleChartMap_projection I G H f hf n d)
    _ = _ := K.map_comp _ _

/-- 実際の閉厚化の Čech 写像は、I 進遷移と可換。
原典 Stacks 30.20.5 の Hⁱ の形式関数に用いる自然性の Čech 版。
分離的なスキームの準連接層ではアフィン被覆の Čech と一致する（Stacks 30.2.6）が、
この比較は形式化しない。 -/
theorem reesAdicProjectiveClosedCechModuleMap_transition
    (i j : ℕ) (h : j ≤ i) (d : ℤ) (q : ℕ) :
    reesAdicProjectiveClosedCechModuleMap I G H f hf i d q ≫
        reesAdicProjectiveClosedCechTransition (ι := ι) I H i j h d q =
      reesAdicProjectiveClosedCechTransition (ι := ι) I G i j h d q ≫
        reesAdicProjectiveClosedCechModuleMap I G H f hf j d q := by
  let K := fullCechComplexFunctor (R := R) (ι := ι) ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q
  calc
    _ = K.map (reesAdicProjectiveClosedCechModuleChartMap I G H f hf i d) ≫
        K.map (reesAdicProjectiveClosedCechTransitionChartMap (ι := ι) I H i j h d) := rfl
    _ = K.map (reesAdicProjectiveClosedCechModuleChartMap I G H f hf i d ≫
        reesAdicProjectiveClosedCechTransitionChartMap (ι := ι) I H i j h d) :=
      (K.map_comp _ _).symm
    _ = K.map (reesAdicProjectiveClosedCechTransitionChartMap (ι := ι) I G i j h d ≫
        reesAdicProjectiveClosedCechModuleChartMap I G H f hf j d) := congrArg
      (fun η ↦ K.map η) (reesAdicProjectiveClosedCechModuleChartMap_transition I G H f hf i j h d)
    _ = _ := K.map_comp _ _

end SerrePositivity.AlgebraicGeometry
