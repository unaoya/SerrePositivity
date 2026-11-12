module

public import SerrePositivity.KST.Spectra.TowerKernelRepresentativeObstruction
public import SerrePositivity.KST.Spectra.TowerObstructionTransport

/-!
概要：塔の比較の核から lim¹ への基点を保つ障害写像。
方針：極限の球面の相対ホモトピーを射影し、零ホモトピーの移送不変性で商へ降ろす。
規約：核との全単射や零障害からの充填はここでは主張しない。
使われ方：Goerss–Jardine VIII §1。Milnor 完全列の核の解析。
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

variable (X : ℕ → PointedSimplicialSet.{u}) (p : ∀ n, X (n + 1) ⟶ X n)
  [∀ n, KanComplex (X n).right] [∀ n, Fibration (p n).right] (r : ℕ)
  (s t : (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.limit (fun n ↦ (X n).right) (fun n ↦ (p n).right)).PtSimplex
    (r + 1) (limitBasepoint X p))
  (hs : limitGroupComparison X p r (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk s) = 1)
  (ht : limitGroupComparison X p r (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk t) = 1)

/-- 極限の相対ホモトピーによって核の代表の障害は変わらない。 -/
theorem kernelRepresentativeObstruction_eq_of_relStruct
    (A : PtSimplex.RelStruct s t (Fin.last (r + 1))) :
    kernelRepresentativeObstruction X p r s hs = kernelRepresentativeObstruction X p r t ht := by
  let A' n := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.mapRelStruct
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.projection (fun n ↦ (X n).right) (fun n ↦ (p n).right) n) rfl A
  let R := projectedNullHomotopy X p r s hs
  have hA (n : ℕ) : (A' (n + 1)).map ≫ (p n).right = (A' n).map := by
    change (A.map ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.projection _ _ (n + 1)) ≫ (p n).right =
      A.map ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.projection _ _ n
    rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.projection_comp]
  rw [kernelRepresentativeObstruction_eq X p r s hs R,
    kernelRepresentativeObstruction_eq X p r t ht
      (fun n ↦ _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.NullHomotopyTransport.transport (R n) (A' n))]
  exact nullHomotopyObstruction_transport X p r _ _ _ _ A' hA R

/-- 同じ極限のホモトピー類を表す球面は、同じ lim¹ 障害を持つ。 -/
theorem kernelRepresentativeObstruction_congr (he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk s = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk t) :
    kernelRepresentativeObstruction X p r s hs = kernelRepresentativeObstruction X p r t ht := by
  obtain ⟨A⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.simplexRel_iff_relStruct (Fin.last (r + 1))).1
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk_eq_iff s t).1 he)
  exact kernelRepresentativeObstruction_eq_of_relStruct X p r s t hs ht A

/-- 比較の核の元を表す球面を一つ選ぶ。 -/
def kernelSphereRepresentative (b : (limitGroupComparison X p r).ker) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.limit (fun n ↦ (X n).right) (fun n ↦ (p n).right)).PtSimplex
      (r + 1) (limitBasepoint X p) := Classical.choose (Quotient.exists_rep b.val)

/-- 選んだ球面は元の核の元を表す。 -/
lemma kernelSphereRepresentative_mk (b : (limitGroupComparison X p r).ker) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (kernelSphereRepresentative X p r b) = b.val :=
  Classical.choose_spec (Quotient.exists_rep b.val)

/-- 選んだ球面は比較の核に属する。 -/
lemma kernelSphereRepresentative_mem (b : (limitGroupComparison X p r).ker) :
    limitGroupComparison X p r (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk (kernelSphereRepresentative X p r b)) = 1 := by
  rw [kernelSphereRepresentative_mk]
  exact b.property

/-- 球面の代表選択から独立した、比較の核から lim¹ への障害写像。 -/
def kernelObstruction (b : (limitGroupComparison X p r).ker) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.limOne (fun n ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (X n).right (r + 1) (X n).basepoint)
      (fun n ↦ pointedGroupMap (r + 1) (p n)) :=
  kernelRepresentativeObstruction X p r (kernelSphereRepresentative X p r b)
    (kernelSphereRepresentative_mem X p r b)

/-- 核の障害写像は指定した任意の球面代表で計算できる。 -/
lemma kernelObstruction_mk :
    kernelObstruction X p r ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk s, hs⟩ =
      kernelRepresentativeObstruction X p r s hs :=
  kernelRepresentativeObstruction_congr X p r _ s _ hs
    (kernelSphereRepresentative_mk X p r ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.mk s, hs⟩)

/-- 核の障害写像は単位元を lim¹ の基点へ送る。 -/
theorem kernelObstruction_one : kernelObstruction X p r 1 = _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.TowerLimOne.point _ _ := by
  exact kernelRepresentativeObstruction_eq_point_of_mk_eq_one X p r
    (kernelSphereRepresentative X p r 1) (kernelSphereRepresentative_mem X p r 1)
    (kernelSphereRepresentative_mk X p r 1)

end
end SerrePositivity.KST.Spectra.PointedFibrationTower
