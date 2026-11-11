module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.PullbackOverFiber
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeCosliceCancellation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.BaseChange

/-!
概要：共通の底上の引き戻しで、両成分の cartesian な辺から全体の cartesian 性を得る。
方針：第一成分の合成射の消去、引き戻し、第二成分との合成を使う。
規約：引き戻す射 f だけに inner fibration 性を要求する。
使われ方：全空間の相対 Kan 比較が底方向の cartesian 輸送を保つことの判定。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 概要：底を保つ引き戻しの両成分が cartesian なら全体も cartesian。
方針：第一成分を f に関して cartesian とし、底変換して第二成分の輸送と合成する。
規約：f による第一成分の像にも cartesian 性を要求する。
使われ方：相対比較の像の cartesian 性を二つの成分から証明する。 -/
lemma isCartesianEdge_pullback_over {X Y Z C : SSet.{u}}
    [Quasicategory X] [Quasicategory Z] [Quasicategory C]
    (p : X ⟶ C) (q : Y ⟶ C) (r : Z ⟶ C) (f : X ⟶ Z) (g : Y ⟶ Z)
    [InnerFibration f] (hf : f ≫ r = p) (hg : g ≫ r = q)
    (e : (pullback f g) _⦋1⦌)
    (ha : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge p ((pullback.fst f g).app (Opposite.op ⦋1⦌) e))
    (hb : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge q ((pullback.snd f g).app (Opposite.op ⦋1⦌) e))
    (hfa : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge r
      (f.app (Opposite.op ⦋1⦌) ((pullback.fst f g).app (Opposite.op ⦋1⦌) e))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge (pullback.fst f g ≫ p) e := by
  have hfirst : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge f ((pullback.fst f g).app (Opposite.op ⦋1⦌) e) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanIsCartesianEdge_of_comp f r _ (by rw [hf]; exact ha) hfa
  have hpair : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCartesianEdge (pullback.snd f g) e :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isCartesianEdge_pullback f g e hfirst
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pullbackOver_snd_projection p q r f g hf hg]
  exact hpair.comp hb

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
