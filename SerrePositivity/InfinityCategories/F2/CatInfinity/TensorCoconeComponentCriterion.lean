module

public import SerrePositivity.InfinityCategories.F2.CatInfinity.TensorConeComponentCriterion
public import SerrePositivity.InfinityCategories.F2.CatInfinity.CoconeReversePostcomp
public import SerrePositivity.InfinityCategories.Core.PrismOpposite

/-!
概要：直積内の指定余錐の成分ごとの余極限性。
方針：反転と直積の標準同型を使って極限側の判定を適用する。
規約：元の二射影による余錐を保持する。
使われ方：lax pullback の入力と両端の余極限性。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：両射影が余極限余錐である直積内の余錐は余極限余錐。
方針：直積の反転同型は元の二射影を反転した二射影と一致させる。
規約：添字 J は任意で、選択された別の余錐へ変更しない。
使われ方：Tamme Lemma 8(i) の両入力による判定。 -/
lemma isColimitCone_tensor_of_components {J X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] {r : J ⟶ X ⊗ Y} (c : JoinCocone r)
    (hx : IsColimitCone (F1B.kanPostcomposeCocone (fst X Y) c))
    (hy : IsColimitCone (F1B.kanPostcomposeCocone (snd X Y) c)) : IsColimitCone c := by
  have : Quasicategory (X ⊗ Y) := quasicategory_tensor X Y
  have : Quasicategory (X.op ⊗ Y.op) := quasicategory_tensor X.op Y.op
  let e := (opTensorIso X Y).symm
  apply (F1B.kanIsColimitCone_iff_reverseCone c).2
  apply ((qCatEquivalenceOfIso e).isLimitCone_iff (F1B.kanCoconeReverseCone c)).2
  apply isLimitCone_tensor_of_components
  · apply (isLimitCone_iff_of_cone_val_eq _ _ ?_).2
      ((isLimitCone_reverse_postcomp_iff c (fst X Y)).2 hx)
    change ((F1B.kanCoconeReverseCone c).val ≫ e.hom) ≫ fst X.op Y.op =
      (F1B.kanCoconeReverseCone c).val ≫ SSet.opFunctor.map (fst X Y)
    have he : e.hom ≫ fst X.op Y.op = SSet.opFunctor.map (fst X Y) := rfl
    rw [Category.assoc, he]
  · apply (isLimitCone_iff_of_cone_val_eq _ _ ?_).2
      ((isLimitCone_reverse_postcomp_iff c (snd X Y)).2 hy)
    change ((F1B.kanCoconeReverseCone c).val ≫ e.hom) ≫ snd X.op Y.op =
      (F1B.kanCoconeReverseCone c).val ≫ SSet.opFunctor.map (snd X Y)
    have he : e.hom ≫ snd X.op Y.op = SSet.opFunctor.map (snd X Y) := rfl
    rw [Category.assoc, he]

end SerrePositivity.InfinityCategories.F2
