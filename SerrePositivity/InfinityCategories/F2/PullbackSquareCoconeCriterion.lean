module

public import SerrePositivity.InfinityCategories.F2.PullbackSquareConeCriterion
public import SerrePositivity.InfinityCategories.F2.CoconeReversePostcomp

/-!
概要：厳密な引き戻し正方形内の指定余錐の成分ごとの余極限性。
方針：正方形と元の余錐を反転し、極限側の判定を使う。
規約：元の脚の後合成と反転後の錐の脚を全射の等式で比較する。
使われ方：Tamme Lemma 8(i) の余極限の成分判定への入力。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：二射影と底の余錐が余極限なら引き戻し内の元の余錐も余極限。
方針：反対関手で引き戻しを保ち、指定余錐の反転後の極限性を判定する。
規約：元の p が inner fibration であること以外に保存性を要求しない。
使われ方：lax pullback の余極限と射影の保存への接続。 -/
lemma isColimitCone_of_isPullback_of_components {J W E D B : SSet.{u}}
    [Quasicategory W] [Quasicategory E] [Quasicategory D] [Quasicategory B]
    {a : W ⟶ E} {b : W ⟶ D} {p : E ⟶ B} {q : D ⟶ B}
    (s : IsPullback a b p q) [InnerFibration p] {r : J ⟶ W} (c : JoinCocone r)
    (ha : IsColimitCone (F1B.kanPostcomposeCocone a c))
    (hb : IsColimitCone (F1B.kanPostcomposeCocone b c))
    (hp : IsColimitCone (F1B.kanPostcomposeCocone p (F1B.kanPostcomposeCocone a c))) :
    IsColimitCone c := by
  have : SSet.opFunctor.{u}.IsEquivalence := SSet.opEquivalence.isEquivalence_functor
  apply (F1B.kanIsColimitCone_iff_reverseCone c).2
  apply isLimitCone_of_isPullback_of_components (s.map SSet.opFunctor)
    (F1B.kanCoconeReverseCone c)
  · exact (isLimitCone_reverse_postcomp_iff c a).2 ha
  · exact (isLimitCone_reverse_postcomp_iff c b).2 hb
  · apply (isLimitCone_iff_of_cone_val_eq _ _ ?_).2
      ((F1B.kanIsColimitCone_iff_reverseCone _).1 hp)
    change ((F1B.kanCoconeReverseCone c).val ≫ SSet.opFunctor.map a) ≫
      SSet.opFunctor.map p = _
    rw [F1B.kanCoconeReverseCone_val, F1B.kanCoconeReverseCone_val]
    simp only [F1B.kanPostcomposeCocone, CategoryTheory.Functor.map_comp, Category.assoc]

end SerrePositivity.InfinityCategories.F2
