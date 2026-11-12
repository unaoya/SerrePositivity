module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGNerveCommonMap
/-!
概要：対象だけの dg 宇宙持ち上げは共通 nerve 上の実同型を与える。
方針：元の上げ下げ dg 関手の厳密逆関係と共通 nerve の合成則を使う。
規約：Small 仮定は不要。単体集合の同型であり H⁰ の同値に置き換えない。
使われ方：混在宇宙の完全性で始域の対象持ち上げを除去する。
-/
@[expose] public section
noncomputable section
universe u v s t
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R D]

def dgNerveCommonLiftIso :
    (SSet.uliftFunctor.{max u v s t, max u v}).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R D) ≅
      (SSet.uliftFunctor.{max u v s t, max u v s}).obj
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGUniverseLift.{v, s} D)) where
  hom := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCommonMap.{u, v, max v s, max u v s t} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp.{u, v, s} R D)
  inv := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCommonMap.{u, max v s, v, max u v s t} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown.{u, v, s} R D)
  hom_inv_id := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCommonMap_comp.{u, v, max v s, v, max u v s t},
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftUp_comp_down, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCommonMap_id]
  inv_hom_id := by
    rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCommonMap_comp.{u, max v s, v, max v s, max u v s t},
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgUniverseLiftDown_comp_up, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgNerveCommonMap_id]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
