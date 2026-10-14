module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.KoszulTower
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Module
public import SerrePositivity.HomologicalAlgebra.KoszulCoordinateControl

/-! # 各有限Koszul段の導来完備性

各座標の零ホモトピーを用い、実際の導来圏で局所化からの全次数の射を消す。
座標の正則性やねじれの有界性は仮定しない。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R]

/-- 環係数のKoszul複体は、零次数環にKoszul関手を適用した複体に等しい。 -/
theorem koszulComplex_eq_functor : ∀ {e : ℕ} (a : Fin e → R),
    koszulComplex a = (koszulFunctor a).obj
      ((CochainComplex.singleFunctor (ModuleCat R) 0).obj (ModuleCat.of R R))
  | 0, _ => rfl
  | e + 1, a => by
    change CochainComplex.mappingCone (smulId (a (Fin.last e)) (koszulComplex (Fin.init a))) = _
    rw [koszulComplex_eq_functor]
    rfl

/-- Koszul複体の座標の作用は零ホモトピック。既存の係数複体版を再利用する。 -/
def koszulComplexCoordinateNullHomotopy {e : ℕ} (a : Fin e → R) (j : Fin e) :
    Homotopy (smulId (a j) (koszulComplex a)) 0 := by
  rw [koszulComplex_eq_functor]
  exact koszulCoordinateNullHomotopy a _ j

/-- 各冪の有限Koszul段は、その各座標に関して導来完備。 -/
theorem powerKoszulStage_isComplete {e : ℕ} (a : Fin e → R) (n : ℕ) (j : Fin e) :
    IsComplete R (a j) (DerivedCategory.Q.obj (powerKoszulTower R a n)) :=
  isComplete_Q_of_scalar_pow_nullHomotopic R (a j) _ n
    (koszulComplexCoordinateNullHomotopy R (fun i ↦ a i ^ n) j)

/-- 各冪のKoszulの任意の次数のホモロジーも、その各座標に関して導来完備。 -/
theorem powerKoszulStage_homology_isModuleComplete {e : ℕ} (a : Fin e → R)
    (n : ℕ) (j : Fin e) (q : ℤ) :
    IsModuleComplete R (a j) ((powerKoszulTower R a n).homology q) := by
  apply isModuleComplete_of_pow_smul_zero R (a j) _ n
  have h := (koszulComplexCoordinateNullHomotopy R (fun i ↦ a i ^ n) j).homologyMap_eq q
  rw [smulId, homologyMap_smul, HomologicalComplex.homologyMap_id,
    HomologicalComplex.homologyMap_zero] at h
  intro m
  exact congrArg (fun f ↦ f.hom m) h

end SerrePositivity.DerivedCompletion
