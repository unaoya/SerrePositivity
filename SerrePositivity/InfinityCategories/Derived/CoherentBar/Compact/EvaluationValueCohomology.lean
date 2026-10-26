module
public import SerrePositivity.InfinityCategories.Derived.DGFunctorZeroObjects
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.NativeEvaluationSpace
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Compact.PinchedPiCohomology
public import SerrePositivity.InfinityCategories.HomotopyLimits.KanWhiteheadComparison
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
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve SSet
open SerrePositivity.KST.Spectra
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]

/-- native 評価関手の同じ実頂点値と、評価複体の実 pinched 模型との同値。 -/
def dgBarCompactEvaluationValueEquivalence (x : D) (M : ProjectiveDGModules R D) :
    QCatEquivalence
      (spaceInfinityObject ((dgBarCompactProjectiveEvaluationSpaceInfinity R D x).app
        (Opposite.op ⦋0⦌) (ULift.up (Simplex.vertex M)))).obj
      (complexPinchedSpace.{u, max (u + 1) v} (M.val.obj (Opposite.op x))) := by
  change QCatEquivalence
    (spaceInfinityObject ((dgHomUnderlyingSpaceInfinity R (ProjectiveDGModules R D)).app
      (Opposite.op ⦋0⦌) (ULift.up ((dgNerve.map
        ((dgBarCompactProjectiveEvaluationModuleDG R D x).comp
          (dgUniverseLiftUp R (RightModule R PUnit.{1})))).app
            (Opposite.op ⦋0⦌) (Simplex.vertex M))))).obj _
  rw [dgFunctorNerve_vertex]
  exact dgHomUnderlyingSpaceValueEquivalence R (ProjectiveDGModules R D)
    ((dgBarCompactProjectiveEvaluationModuleDG R D x).obj M)

/-- 任意の native 評価基点を保った、元の評価コホモロジーへの比較。 -/
def dgBarCompactEvaluationValuePiCohomologyEquiv (x : D) (M : ProjectiveDGModules R D)
    (n : ℕ)
    (z : (spaceInfinityObject ((dgBarCompactProjectiveEvaluationSpaceInfinity R D x).app
      (Opposite.op ⦋0⦌) (ULift.up (Simplex.vertex M)))).obj _⦋0⦌) :
    KanHomotopyGroup
      (spaceInfinityObject ((dgBarCompactProjectiveEvaluationSpaceInfinity R D x).app
        (Opposite.op ⦋0⦌) (ULift.up (Simplex.vertex M)))).obj n z ≃*
      Multiplicative ((M.val.obj (Opposite.op x)).homology (-((n + 1 : ℕ) : ℤ))) := by
  let e := dgBarCompactEvaluationValueEquivalence R D x M
  have he := HomotopyLimits.kanPiIsomorphism_of_homotopyEquivalence e.hom
    e.isQCatEquivalence.isSimplicialHomotopyEquivalence
  exact (KanHomotopyGroup.equivOfPiIsomorphism n e.hom he rfl).trans
    (dgBarCompactComplexPinchedPiCohomologyEquiv (M.val.obj (Opposite.op x)) n
      (e.hom.app _ z))

/-- 同じ native 頂点値の連結成分と、元の評価複体の H⁰。 -/
def dgBarCompactEvaluationValuePiZeroCohomologyEquiv (x : D) (M : ProjectiveDGModules R D) :
    SSet.π₀ (spaceInfinityObject ((dgBarCompactProjectiveEvaluationSpaceInfinity R D x).app
      (Opposite.op ⦋0⦌) (ULift.up (Simplex.vertex M)))).obj ≃
      (M.val.obj (Opposite.op x)).homology 0 := by
  let e := dgBarCompactEvaluationValueEquivalence R D x M
  exact (Equiv.ofBijective (SSet.mapπ₀ e.hom)
    e.isQCatEquivalence.isSimplicialHomotopyEquivalence.mapPiZero_bijective).trans
      (dgBarCompactComplexPinchedPiZeroCohomologyEquiv (M.val.obj (Opposite.op x)))

end SerrePositivity.InfinityCategories
