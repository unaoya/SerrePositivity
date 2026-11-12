module

public import SerrePositivity.KST.Spectra.UnbasedHomotopyIsomorphism

/-!
概要：指定された実際の path に沿う、正次数 Kan ホモトピー群の基点移送。
方針：指数 path 対象の二端点評価の全単射性を合成する。
規約：基点の等号を仮定せず、path 対象の頂点を保持する。
使われ方：filtered な段階間の押し出しと余錐の coherent な基点移送。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion
open KST.Spectra
variable {X : SSet.{u}} [KanComplex X]

/-- 指定 path の両端における正次数ホモトピー群の同値。 -/
def pathPiEquiv (z : (KanPath.object X) _⦋0⦌) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X n ((KanPath.evaluation X 0).app _ z) ≃
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup X n ((KanPath.evaluation X 1).app _ z) :=
  (Equiv.ofBijective
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (n := n) (KanPath.evaluation X 0) (x := z) rfl)
    (KanPath.evaluation_piIsomorphism X 0 z (n + 1))).symm.trans
  (Equiv.ofBijective
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (n := n) (KanPath.evaluation X 1) (x := z) rfl)
    (KanPath.evaluation_piIsomorphism X 1 z (n + 1)))

/-- 同じ path 上のホモトピー類の二端点は、この基点移送で対応する。 -/
lemma pathPiEquiv_map_zero (z : (KanPath.object X) _⦋0⦌) (n : ℕ)
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup (KanPath.object X) n z) :
    pathPiEquiv z n (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (KanPath.evaluation X 0) rfl a) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (KanPath.evaluation X 1) rfl a := by
  exact congrArg
    (Equiv.ofBijective
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (n := n) (KanPath.evaluation X 1) (x := z) rfl)
      (KanPath.evaluation_piIsomorphism X 1 z (n + 1)))
    ((Equiv.ofBijective
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopyGroup.map (n := n) (KanPath.evaluation X 0) (x := z) rfl)
      (KanPath.evaluation_piIsomorphism X 0 z (n + 1))).symm_apply_apply a)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.PiCriterion
