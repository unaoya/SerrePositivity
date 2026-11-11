module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.IntervalBoundary

/-!
概要：指定二端点の境界図式は標的の射による後合成と交換する。
方針：境界単体の端点による二つの分岐を照合する。
規約：全次数の厳密な式。
使われ方：元の相対 path 境界を Kan 単位で写した全境界の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange

/-- 概要：二端点の境界図式を標的へ写すと、元の二端点を写した境界図式。
方針：境界の各単体が選ぶ端点で計算する。
規約：全円柱境界。使われ方：相対有限 path の厳密な anchor 式。 -/
lemma intervalBoundaryDiagram_postcomp {A X Y : SSet.{u}} (f g : A ⟶ X) (q : X ⟶ Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram f g ≫ q = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.intervalBoundaryDiagram (f ≫ q) (g ≫ q) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨s, x⟩
  change q.app _ (if s.val 0 = 0 then f.app _ x else g.app _ x) =
    (if s.val 0 = 0 then q.app _ (f.app _ x) else q.app _ (g.app _ x))
  split_ifs <;> rfl

end SerrePositivity.InfinityCategories.Project.FilteredExchange
