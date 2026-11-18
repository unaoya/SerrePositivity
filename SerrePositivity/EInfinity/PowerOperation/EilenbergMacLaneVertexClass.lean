module

public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneGammaUnitClass
public import SerrePositivity.EInfinity.PowerOperation.EilenbergMacLaneVertexUnit
public import SerrePositivity.EInfinity.BarrattEccles.Theory.HomologyAlgebraFunctor

/-!
# Γ の頂点から回収した指定複体射の H⁰ の類

DAG XIII §2.2 の零次数の Ω 比較への前段。同じ頂点からの実随伴の射と
元の π₀/H⁰ 比較が、単位の自然性の下で一致する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.PowerOperation
open CategoryTheory MonoidalCategory
open scoped Simplicial
open SerrePositivity.DifferentialGraded _root_.SerrePositivity.ComplexLimits
variable (A : Type u) [CommRing A]

lemma gammaPiZeroCohomologyEquiv_mk (M : Complex A)
    (x : (gammaModule A M).obj (Opposite.op ⦋0⦌)) :
    gammaPiZeroCohomologyEquiv A M (SSet.π₀.mk x) =
      _root_.SerrePositivity.HomologyZero.unitClass M (gammaVertexUnitHomEquiv A M x) := by
  have h := gammaPiZeroCohomologyEquiv_naturality A (gammaVertexUnitHomEquiv A M x)
    (SSet.π₀.mk (gammaUnitSimplex A ⦋0⦌))
  rw [gammaPiZeroCohomologyEquiv_unit, HomologyZero.unitClass_naturality] at h
  change gammaPiZeroCohomologyEquiv A M
    (SSet.π₀.mk (((_root_.SerrePositivity.ComplexLimits.truncatedDoldKanFunctor A).map (gammaVertexUnitHomEquiv A M x)).app
      (Opposite.op ⦋0⦌) (gammaUnitSimplex A ⦋0⦌))) =
      _root_.SerrePositivity.HomologyZero.unitClass M (𝟙 _ ≫ gammaVertexUnitHomEquiv A M x) at h
  simpa only [gammaUnit_vertex_generates, Category.id_comp] using h

end SerrePositivity.EInfinity.PowerOperation
