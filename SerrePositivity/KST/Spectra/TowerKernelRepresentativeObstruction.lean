module

public import SerrePositivity.KST.Spectra.TowerNullHomotopyObstruction
public import SerrePositivity.KST.Spectra.TowerGroupLimitComparison

/-!
概要：塔の比較の核の球面代表から lim¹ の障害を構成する。
方針：各射影の零性から零ホモトピーを選び、選択によらない差の軌道へ送る。
規約：球面代表は固定する。代表変更への不変性と核との全単射はまだ含まない。
使われ方：Goerss–Jardine VIII §1。Milnor の比較の核の幾何的な障害。
-/

@[expose] public section
universe u
open CategoryTheory SSet HomotopicalAlgebra
open SSet.modelCategoryQuillen
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra.PointedFibrationTower

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable (X : ℕ → PointedSimplicialSet.{u}) (p : ∀ n, X (n + 1) ⟶ X n) (r : ℕ)
  (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.limit (fun n ↦ (X n).right) (fun n ↦ (p n).right)).PtSimplex
    (r + 1) (limitBasepoint X p))

/-- 極限の球面の各段への厳密な射影。 -/
def projectedSimplex (n : ℕ) : (X n).right.PtSimplex (r + 1) (X n).basepoint :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.projection (fun n ↦ (X n).right) (fun n ↦ (p n).right) n) rfl s

/-- 極限の球面の各射影は、単体として厳密に整合する。 -/
lemma projectedSimplex_comp (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapSimplex (p n).right (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.pointedMap_basepoint (p n))
      (projectedSimplex X p r s (n + 1)) = projectedSimplex X p r s n := by
  apply RelativeMorphism.ext
  change (s.map ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.projection _ _ (n + 1)) ≫ (p n).right =
    s.map ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.projection _ _ n
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.projection_comp]

variable [∀ n, KanComplex (X n).right] [∀ n, Fibration (p n).right]
  (hzero : limitGroupComparison X p r (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk s) = 1)

include hzero in
/-- 比較の核の代表の各段には、実際の零ホモトピーが存在する。 -/
lemma exists_projected_nullHomotopy (n : ℕ) :
    Nonempty (PtSimplex.RelStruct .const (projectedSimplex X p r s n) (Fin.last (r + 1))) := by
  have he := (limitGroupComparison_eq_one_iff X p r (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk s)).1 hzero n
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map _ rfl (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk s) = 1 at he
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map_mk] at he
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.simplexRel_iff_relStruct (Fin.last (r + 1))).1
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk_eq_iff _ _).1
  exact he.symm

/-- 比較の核の代表に対して各段の零ホモトピーを選ぶ。 -/
def projectedNullHomotopy (n : ℕ) :
    PtSimplex.RelStruct .const (projectedSimplex X p r s n) (Fin.last (r + 1)) :=
  Classical.choice (exists_projected_nullHomotopy X p r s hzero n)

/-- 比較の核の固定した球面代表に付随する lim¹ の障害。 -/
def kernelRepresentativeObstruction :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.limOne (fun n ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (X n).right (r + 1) (X n).basepoint)
      (fun n ↦ pointedGroupMap (r + 1) (p n)) :=
  nullHomotopyObstruction X p r (projectedSimplex X p r s) (projectedSimplex_comp X p r s)
    (projectedNullHomotopy X p r s hzero)

/-- 核の代表の障害は、任意の段ごとの零ホモトピーから計算できる。 -/
lemma kernelRepresentativeObstruction_eq
    (R : ∀ n, PtSimplex.RelStruct .const (projectedSimplex X p r s n) (Fin.last (r + 1))) :
    kernelRepresentativeObstruction X p r s hzero =
      nullHomotopyObstruction X p r (projectedSimplex X p r s) (projectedSimplex_comp X p r s) R :=
  nullHomotopyObstruction_eq X p r _ _ _ R

include hzero in
/-- 整合する零ホモトピーを持つ核の代表の障害は基点になる。 -/
theorem kernelRepresentativeObstruction_eq_point_of_compatible
    (R : ∀ n, PtSimplex.RelStruct .const (projectedSimplex X p r s n) (Fin.last (r + 1)))
    (hc : ∀ n, (R (n + 1)).map ≫ (p n).right = (R n).map) :
    kernelRepresentativeObstruction X p r s hzero = _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.point _ _ := by
  rw [kernelRepresentativeObstruction_eq X p r s hzero R]
  exact nullHomotopyObstruction_eq_point_of_compatible X p r _ _ R hc

/-- 極限での零ホモトピーを射影した場合、代表の障害は基点になる。 -/
theorem kernelRepresentativeObstruction_eq_point_of_null
    (R : PtSimplex.RelStruct .const s (Fin.last (r + 1))) :
    kernelRepresentativeObstruction X p r s hzero = _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.point _ _ := by
  let R' n := NullHomotopyDifference.mapNull
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.projection (fun n ↦ (X n).right) (fun n ↦ (p n).right) n) rfl R
  apply kernelRepresentativeObstruction_eq_point_of_compatible X p r s hzero R'
  intro n
  change (R.map ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.projection _ _ (n + 1)) ≫ (p n).right =
    R.map ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.projection _ _ n
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.projection_comp]

/-- 極限のホモトピー群で零となる代表は lim¹ の零障害を持つ。 -/
theorem kernelRepresentativeObstruction_eq_point_of_mk_eq_one
    (he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk s = 1) :
    kernelRepresentativeObstruction X p r s hzero = _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.point _ _ := by
  obtain ⟨R⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.simplexRel_iff_relStruct (Fin.last (r + 1))).1
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk_eq_iff .const s).1 he.symm)
  exact kernelRepresentativeObstruction_eq_point_of_null X p r s hzero R

end
end SerrePositivity.KST.Spectra.PointedFibrationTower
