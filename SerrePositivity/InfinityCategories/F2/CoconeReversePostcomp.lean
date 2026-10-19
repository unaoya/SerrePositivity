module

public import SerrePositivity.InfinityCategories.F2.ConeValEquality
public import SerrePositivity.InfinityCategories.F1B.KanCosliceOpposite
public import SerrePositivity.InfinityCategories.F1B.KanRelativeCoconeAbsolute

/-!
概要：余錐の後合成と反転した錐の後合成の極限性の照合。
方針：反転した全錐の射の式と反対関手の合成保存を使う。
規約：元の指定余錐と元の後合成を保持する。
使われ方：成分ごとの極限判定を余極限へ移す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：反転した指定余錐の後合成の極限性は元の像の余極限性と同値。
方針：二つの反転錐の全射の一致から極限性を比較する。
規約：二つの図式の括弧付けは厳密な射の等式で照合する。
使われ方：引き戻しの余極限性の三成分への双対化。 -/
lemma isLimitCone_reverse_postcomp_iff {J X Y : SSet.{u}}
    {r : J ⟶ X} (c : JoinCocone r) (f : X ⟶ Y) :
    IsLimitCone (mapJoinCone (SSet.opFunctor.map f) (F1B.kanCoconeReverseCone c)) ↔
      IsColimitCone (F1B.kanPostcomposeCocone f c) := by
  rw [F1B.kanIsColimitCone_iff_reverseCone]
  apply isLimitCone_iff_of_cone_val_eq
  change (F1B.kanCoconeReverseCone c).val ≫ SSet.opFunctor.map f = _
  rw [F1B.kanCoconeReverseCone_val, F1B.kanCoconeReverseCone_val]
  simp only [F1B.kanPostcomposeCocone, CategoryTheory.Functor.map_comp, Category.assoc]

end SerrePositivity.InfinityCategories.F2
