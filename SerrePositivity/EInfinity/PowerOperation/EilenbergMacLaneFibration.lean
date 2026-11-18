module

public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneStandardHom
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.NormalizedSimplexReedy
public import SerrePositivity.HomologicalAlgebra.SimplicialChains.AlexanderWhitney.SimplexCounitContraction
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.HornTensor

/-!
# Γ は実射影 fibration を Kan fibration へ送る

DAG XIII §2.2 の Ω 比較への前段。実射影モデルの正規化標準単体の frame を使い、
同じ Γ の射への作用を全自然同型で移す。SSet のモデル構造を仮定しない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.DifferentialGraded _root_.SerrePositivity.ComplexLimits
variable (A : Type u) [CommRing A]

/-- 元の正規化標準単体の射は、同じ余単位で準同型と判定できる。 -/
lemma gammaStandardSimplex_map_quasiIso {n m : SimplexCategory} (f : n ⟶ m) :
    QuasiIso ((SSet.stdSimplex ⋙ BarrattEccles.normalizedFunctor A).map f) := by
  have : QuasiIso (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainCounit A (SSet.stdSimplex.obj m)) :=
    (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainCounitStdSimplexHomotopyEquiv A m).quasiIso_hom
  have : QuasiIso (((SSet.stdSimplex ⋙ BarrattEccles.normalizedFunctor A).map f) ≫
      _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainCounit A (SSet.stdSimplex.obj m)) := by
    rw [show ((SSet.stdSimplex ⋙ BarrattEccles.normalizedFunctor A).map f) ≫
      _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainCounit A (SSet.stdSimplex.obj m) =
        _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainCounit A (SSet.stdSimplex.obj n) from
          _root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainCounit_natural A (SSet.stdSimplex.map f)]
    exact (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainCounitStdSimplexHomotopyEquiv A n).quasiIso_hom
  exact quasiIso_of_comp_right _ (_root_.SerrePositivity.SimplicialChains.AlexanderWhitney.cochainCounit A (SSet.stdSimplex.obj m))

open SSet.modelCategoryQuillen in
/-- 構成済みの射影 fibration を、指定 Γ の Kan fibration へ送る。 -/
lemma gammaMap_fibration {M N : Complex A} (p : M ⟶ N)
    (hp : _root_.SerrePositivity.ProjectiveModel.projectiveFibrations A p) :
    Fibration ((_root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A).map p) := by
  let := _root_.SerrePositivity.ProjectiveModel.projectiveModelCategory A
  have : Fibration p := ⟨hp⟩
  have h : Fibration ((gammaStandardHom A).map p) :=
    SerrePositivity.HomotopyFunctionComplex.cosimplicialHom_fibration
      (SSet.stdSimplex ⋙ BarrattEccles.normalizedFunctor A)
      (_root_.SerrePositivity.ComplexLimits.normalizedSimplex_reedyCofibrant A)
      (fun f => gammaStandardSimplex_map_quasiIso A f) p
  let e := gammaStandardHomFunctorIso A
  have he : e.inv.app M ≫ (gammaStandardHom A).map p ≫ e.hom.app N =
      (_root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A).map p := by
    rw [e.hom.naturality, ← Category.assoc, e.inv_hom_id_app, Category.id_comp]
  have : Fibration (e.inv.app M ≫ (gammaStandardHom A).map p ≫ e.hom.app N) := by
    infer_instance
  rw [he] at this
  exact this

end SerrePositivity.EInfinity.PowerOperation
