module

public import SerrePositivity.InfinityCategories.F1.MappingSpaces.IntervalDiagramColimitCone

/-!
概要：底上の同型による区間 Hom の同じ制限は同型。
方針：元の反変制限関手が同型を保存することを使う。
規約：元の図式と制限写像を保持する。
使われ方：標準単体と nerve セルの表示の変更。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 底上の同型による同じ区間 Hom の制限は同型。 -/
lemma intervalDiagramOverPre_isIso_of_isIso {B X : SSet.{u}} (F G : B ⟶ X)
    {a b : Over B} (i : a ⟶ b) [IsIso i] : IsIso (intervalDiagramOverPre F G i) := by
  change IsIso ((intervalDiagramOverFunctor F G).map i.op)
  infer_instance

end SerrePositivity.InfinityCategories
