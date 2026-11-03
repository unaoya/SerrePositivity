module
public import SerrePositivity.InfinityCategories.Core.Join
public import SerrePositivity.InfinityCategories.Core.Square
public import SerrePositivity.InfinityCategories.Core.UniverseSSetMaps
public import SerrePositivity.InfinityCategories.Core.PushoutShape
public import SerrePositivity.InfinityCategories.Core.UniverseOuterHornJoins
public import SerrePositivity.InfinityCategories.Core.UniverseStandardJoins

/-! # 外側ホーンの錐の二三角形の宇宙比較

概要：span/cospan の普遍四角形を構成する二つの三角形を宇宙同型で照合する。
方針：標準 join の逆同型とホーン面への自然性を合成する。
規約：対角の面も保つ実単体集合の等式。使われ方：四角形の形状同型の整合性。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory SSet HomotopyLimits
open scoped Simplicial

/-- cospan の錐の左三角形を保持する。 -/
lemma uliftCospanConeIso_left :
    (SSet.uliftFunctor.{v, u}).map cospanConeTriangleLeft ≫ uliftCospanConeIso.hom =
      (uliftStdSimplexIso.{u, v} 2).hom ≫ cospanConeTriangleLeft := by
  unfold cospanConeTriangleLeft
  rw [Functor.map_comp, Category.assoc, uliftCospanConeIso_face,
    ← Category.assoc, uliftStandardJoinIso_std_inv, Category.assoc]

/-- cospan の錐の右三角形を保持する。 -/
lemma uliftCospanConeIso_right :
    (SSet.uliftFunctor.{v, u}).map cospanConeTriangleRight ≫ uliftCospanConeIso.hom =
      (uliftStdSimplexIso.{u, v} 2).hom ≫ cospanConeTriangleRight := by
  unfold cospanConeTriangleRight
  rw [Functor.map_comp, Category.assoc, uliftCospanConeIso_face,
    ← Category.assoc, uliftStandardJoinIso_std_inv, Category.assoc]

/-- span の余錐の左三角形を保持する。 -/
lemma uliftSpanCoconeIso_left :
    (SSet.uliftFunctor.{v, u}).map spanCoconeTriangleLeft ≫ uliftSpanCoconeIso.hom =
      (uliftStdSimplexIso.{u, v} 2).hom ≫ spanCoconeTriangleLeft := by
  unfold spanCoconeTriangleLeft
  rw [Functor.map_comp, Category.assoc, uliftSpanCoconeIso_face,
    ← Category.assoc, uliftStandardJoinIso_std_inv, Category.assoc]

/-- span の余錐の右三角形を保持する。 -/
lemma uliftSpanCoconeIso_right :
    (SSet.uliftFunctor.{v, u}).map spanCoconeTriangleRight ≫ uliftSpanCoconeIso.hom =
      (uliftStdSimplexIso.{u, v} 2).hom ≫ spanCoconeTriangleRight := by
  unfold spanCoconeTriangleRight
  rw [Functor.map_comp, Category.assoc, uliftSpanCoconeIso_face,
    ← Category.assoc, uliftStandardJoinIso_std_inv, Category.assoc]

end SerrePositivity.InfinityCategories
