module
public import SerrePositivity.InfinityCategories.Derived.DGNerveCommonMap
/-!
概要：対象だけの dg 宇宙持ち上げは共通 nerve 上の実同型を与える。
方針：元の上げ下げ dg 関手の厳密逆関係と共通 nerve の合成則を使う。
規約：Small 仮定は不要。単体集合の同型であり H⁰ の同値に置き換えない。
使われ方：混在宇宙の完全性で始域の対象持ち上げを除去する。
-/
@[expose] public section
noncomputable section
universe u v s t
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D]

def dgNerveCommonLiftIso :
    (SSet.uliftFunctor.{max u v s t, max u v}).obj (dgNerve R D) ≅
      (SSet.uliftFunctor.{max u v s t, max u v s}).obj
        (dgNerve R (DGUniverseLift.{v, s} D)) where
  hom := dgNerveCommonMap.{u, v, max v s, max u v s t} (dgUniverseLiftUp.{u, v, s} R D)
  inv := dgNerveCommonMap.{u, max v s, v, max u v s t} (dgUniverseLiftDown.{u, v, s} R D)
  hom_inv_id := by
    rw [dgNerveCommonMap_comp.{u, v, max v s, v, max u v s t},
      dgUniverseLiftUp_comp_down, dgNerveCommonMap_id]
  inv_hom_id := by
    rw [dgNerveCommonMap_comp.{u, max v s, v, max v s, max u v s t},
      dgUniverseLiftDown_comp_up, dgNerveCommonMap_id]

end SerrePositivity.InfinityCategories
