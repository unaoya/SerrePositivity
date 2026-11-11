module

public import SerrePositivity.AlgebraicGeometry.ReesQuotientTransitionLaws
public import SerrePositivity.AlgebraicGeometry.ReesClosedCechCompletion

/-!
概要：実際の閉厚化の Čech コホモロジーを、自然数の反対圏上の逆系にする。
方針：商写像の恒等・合成則を、標準開の図式と Čech 関手へ送る。
規約：Proj 次数と Čech 次数は固定する。
使われ方：形式関数と §9 の自然性を、逆系の射として扱う。
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

local instance inverseCechQuotientModule (n : ℕ) : Module (MvPolynomial ι R)
    (reesAdicProjectiveQuotient (ι := ι) (M := M) I n) :=
  reesAdicProjectiveQuotientPolynomialModule (ι := ι) (M := M) I n
local instance inverseCechQuotientTower (n : ℕ) : IsScalarTower R (MvPolynomial ι R)
    (reesAdicProjectiveQuotient (ι := ι) (M := M) I n) :=
  reesAdicProjectiveQuotientPolynomialModule_scalarTower (ι := ι) (M := M) I n
local instance inverseCechQuotientGraded (n : ℕ) :
    SetLike.GradedSMul (MvPolynomial.homogeneousSubmodule ι R)
      (reesAdicProjectiveQuotientPiece (ι := ι) I G n) :=
  reesAdicProjectiveQuotientPieceGradedSMul (ι := ι) I G n

/-- 閉厚化の標準開の図式における、同じ段の遷移は恒等写像。 -/
theorem reesAdicProjectiveClosedCechTransitionChartMap_self (n : ℕ) (d : ℤ) :
    reesAdicProjectiveClosedCechTransitionChartMap (ι := ι) I G n n le_rfl d = 𝟙 _ := by
  unfold reesAdicProjectiveClosedCechTransitionChartMap
  apply Eq.trans _ (projectiveNatGradedModuleChartMap_id (ι := ι)
    (reesAdicProjectiveQuotientPiece (ι := ι) I G n) d)
  congr 1
  exact reesAdicProjectiveQuotientTransition_self (ι := ι) (M := M) I n

/-- 閉厚化の標準開の図式における、遷移の合成則。 -/
theorem reesAdicProjectiveClosedCechTransitionChartMap_comp
    (i j k : ℕ) (hij : j ≤ i) (hjk : k ≤ j) (d : ℤ) :
    reesAdicProjectiveClosedCechTransitionChartMap (ι := ι) I G i j hij d ≫
        reesAdicProjectiveClosedCechTransitionChartMap (ι := ι) I G j k hjk d =
      reesAdicProjectiveClosedCechTransitionChartMap (ι := ι) I G i k (hjk.trans hij) d := by
  unfold reesAdicProjectiveClosedCechTransitionChartMap
  rw [projectiveNatGradedModuleChartMap_comp]
  congr 1
  exact reesAdicProjectiveQuotientTransition_comp (ι := ι) (M := M) I i j k hij hjk

/-- 閉厚化の Čech コホモロジーの同じ段の間の遷移は恒等写像。 -/
theorem reesAdicProjectiveClosedCechTransition_self (n : ℕ) (d : ℤ) (q : ℕ) :
    reesAdicProjectiveClosedCechTransition (ι := ι) I G n n le_rfl d q = 𝟙 _ := by
  let K := fullCechComplexFunctor (R := R) (ι := ι) ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q
  calc
    _ = K.map (reesAdicProjectiveClosedCechTransitionChartMap (ι := ι) I G n n le_rfl d) := rfl
    _ = K.map (𝟙 _) := congrArg (fun η ↦ K.map η)
      (reesAdicProjectiveClosedCechTransitionChartMap_self (ι := ι) I G n d)
    _ = 𝟙 _ := K.map_id _

/-- 閉厚化の Čech コホモロジーの遷移の合成則。 -/
theorem reesAdicProjectiveClosedCechTransition_comp
    (i j k : ℕ) (hij : j ≤ i) (hjk : k ≤ j) (d : ℤ) (q : ℕ) :
    reesAdicProjectiveClosedCechTransition (ι := ι) I G i j hij d q ≫
        reesAdicProjectiveClosedCechTransition (ι := ι) I G j k hjk d q =
      reesAdicProjectiveClosedCechTransition (ι := ι) I G i k (hjk.trans hij) d q := by
  let K := fullCechComplexFunctor (R := R) (ι := ι) ⋙
    HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (.up ℕ) q
  calc
    _ = K.map (reesAdicProjectiveClosedCechTransitionChartMap (ι := ι) I G i j hij d) ≫
        K.map (reesAdicProjectiveClosedCechTransitionChartMap (ι := ι) I G j k hjk d) := rfl
    _ = K.map (reesAdicProjectiveClosedCechTransitionChartMap (ι := ι) I G i j hij d ≫
        reesAdicProjectiveClosedCechTransitionChartMap (ι := ι) I G j k hjk d) :=
      (K.map_comp _ _).symm
    _ = K.map (reesAdicProjectiveClosedCechTransitionChartMap
        (ι := ι) I G i k (hjk.trans hij) d) := congrArg (fun η ↦ K.map η)
      (reesAdicProjectiveClosedCechTransitionChartMap_comp (ι := ι) I G i j k hij hjk d)
    _ = _ := rfl

/-- 実際の閉厚化の Čech コホモロジーの逆系。 -/
def reesAdicProjectiveClosedCechInverseSystem (d : ℤ) (q : ℕ) : ℕᵒᵖ ⥤ ModuleCat.{u} R where
  obj n := reesAdicProjectiveClosedCechHomology (ι := ι) I G n.unop d q
  map f := reesAdicProjectiveClosedCechTransition (ι := ι) I G _ _ (leOfHom f.unop) d q
  map_id n := reesAdicProjectiveClosedCechTransition_self (ι := ι) I G n.unop d q
  map_comp f g := (reesAdicProjectiveClosedCechTransition_comp
    (ι := ι) I G _ _ _ (leOfHom f.unop) (leOfHom g.unop) d q).symm

end SerrePositivity.AlgebraicGeometry
