module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGFunctorZeroObjects
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.NativeEvaluationSpace
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.PinchedPiCohomology
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanWhiteheadComparison
/-!
概要：native 評価空間の実頂点で、全基点の正次数 π を評価コホモロジーへ同定する。
方針：同じ基礎空間関手の実値比較を通じ、単体的加群の全基点チャートを使う。
規約：頂点の同定だけから余極限保存や関手自然性を主張しない。
使われ方：同じ実 bar 余錐のホモロジーチャートを構成する頂点の比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
open CategoryTheory DifferentialGraded SSet
open _root_.SerrePositivity.KST.Spectra
open scoped _root_.Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] [Small.{u} D]

/-- native 評価関手の同じ実頂点値と、評価複体の実 pinched 模型との同値。 -/
def dgBarCompactEvaluationValueEquivalence (x : D) (M : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ProjectiveDGModules R D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityObject ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactProjectiveEvaluationSpaceInfinity R D x).app
        (Opposite.op ⦋0⦌) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex M)))).obj
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, max (u + 1) v} (M.val.obj (Opposite.op x))) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityObject ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomUnderlyingSpaceInfinity R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ProjectiveDGModules R D)).app
      (Opposite.op ⦋0⦌) (ULift.up ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map
        ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactProjectiveEvaluationModuleDG R D x).comp
          (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp R (RightModule R PUnit.{1})))).app
            (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex M))))).obj _
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex]
  exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgHomUnderlyingSpaceValueEquivalence R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ProjectiveDGModules R D)
    ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactProjectiveEvaluationModuleDG R D x).obj M)

/-- 任意の native 評価基点を保った、元の評価コホモロジーへの比較。 -/
def dgBarCompactEvaluationValuePiCohomologyEquiv (x : D) (M : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ProjectiveDGModules R D)
    (n : ℕ)
    (z : (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityObject ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactProjectiveEvaluationSpaceInfinity R D x).app
      (Opposite.op ⦋0⦌) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex M)))).obj _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityObject ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactProjectiveEvaluationSpaceInfinity R D x).app
        (Opposite.op ⦋0⦌) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex M)))).obj n z ≃*
      Multiplicative ((M.val.obj (Opposite.op x)).homology (-((n + 1 : ℕ) : ℤ))) := by
  let e := dgBarCompactEvaluationValueEquivalence R D x M
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.kanPiIsomorphism_of_homotopyEquivalence e.hom
    e.isQCatEquivalence.isSimplicialHomotopyEquivalence
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.equivOfPiIsomorphism n e.hom he rfl).trans
    (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactComplexPinchedPiCohomologyEquiv (M.val.obj (Opposite.op x)) n
      (e.hom.app _ z))

/-- 同じ native 頂点値の連結成分と、元の評価複体の H⁰。 -/
def dgBarCompactEvaluationValuePiZeroCohomologyEquiv (x : D) (M : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.ProjectiveDGModules R D) :
    SSet.π₀ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityObject ((_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactProjectiveEvaluationSpaceInfinity R D x).app
      (Opposite.op ⦋0⦌) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex M)))).obj ≃
      (M.val.obj (Opposite.op x)).homology 0 := by
  let e := dgBarCompactEvaluationValueEquivalence R D x M
  exact (Equiv.ofBijective (SSet.mapπ₀ e.hom)
    e.isQCatEquivalence.isSimplicialHomotopyEquivalence.mapPiZero_bijective).trans
      (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact.dgBarCompactComplexPinchedPiZeroCohomologyEquiv (M.val.obj (Opposite.op x)))

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.Compact
