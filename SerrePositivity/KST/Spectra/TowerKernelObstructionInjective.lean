module

public import SerrePositivity.KST.Spectra.TowerCompatibleHomotopies
public import SerrePositivity.KST.Spectra.TowerObstructionAlignment
public import SerrePositivity.KST.Spectra.TowerKernelObstruction
public import SerrePositivity.KST.Spectra.TowerRelativeHomotopyLimit

/-!
概要：塔の比較の核から lim¹ への障害写像は単射。
方針：等しい障害を等しい隣接差へ直し、整合する相対ホモトピーを極限へ組み立てる。
規約：零障害の検出だけを用いず、任意の二つの核の元を比較する。
使われ方：Goerss–Jardine VIII §1。Milnor の核と lim¹ の同定。
-/

@[expose] public section
universe u
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped Simplicial
namespace SerrePositivity.KST.Spectra.PointedFibrationTower
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 同じ lim¹ 障害を持つ任意の二つの核の元は等しい。 -/
theorem kernelObstruction_injective
    (X : ℕ → PointedSimplicialSet.{u}) (p : ∀ n, X (n + 1) ⟶ X n)
    [∀ n, KanComplex (X n).right] [∀ n, Fibration (p n).right] (r : ℕ) :
    Function.Injective (kernelObstruction X p r) := by
  intro b c he
  let s := kernelSphereRepresentative X p r b
  let t := kernelSphereRepresentative X p r c
  let R := projectedNullHomotopy X p r s (kernelSphereRepresentative_mem X p r b)
  let S := projectedNullHomotopy X p r t (kernelSphereRepresentative_mem X p r c)
  have hobs : nullHomotopyObstruction X p r (projectedSimplex X p r s)
      (projectedSimplex_comp X p r s) R =
    nullHomotopyObstruction X p r (projectedSimplex X p r t)
      (projectedSimplex_comp X p r t) S := he
  obtain ⟨R', hR'⟩ := exists_equal_difference_family X p r
    (projectedSimplex X p r s) (projectedSimplex X p r t)
    (projectedSimplex_comp X p r s) (projectedSimplex_comp X p r t) R S hobs
  obtain ⟨A, hA⟩ := exists_compatible_relStruct_of_differenceFamily_eq X p r
    (projectedSimplex X p r s) (projectedSimplex X p r t)
    (projectedSimplex_comp X p r s) (projectedSimplex_comp X p r t) R' S hR'
  have hm := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.sound (limitRelStruct X p r s t A hA)
  apply Subtype.ext
  exact (kernelSphereRepresentative_mk X p r b).symm.trans
    (hm.trans (kernelSphereRepresentative_mk X p r c))

end
end SerrePositivity.KST.Spectra.PointedFibrationTower
