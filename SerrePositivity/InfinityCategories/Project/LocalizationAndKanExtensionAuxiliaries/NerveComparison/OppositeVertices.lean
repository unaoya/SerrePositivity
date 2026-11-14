module

public import SerrePositivity.InfinityCategories.HTT.Section6_1_2.OppositeIso
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.NerveCone

/-!
概要：通常の余錐の脚と反対圏の nerve の表示を比較する。
方針：反転した錐の脚の公式と図式同型の射への作用を使う。
規約：元の指定された図式・頂点・脚を保持する。
使われ方：B5 の指定単位の左 Kan 局所余錐の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet Opposite
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison


/-- 概要：反対圏の nerve の同型は元の対象の頂点を保つ。
方針：反対 nerve の辺と反転した錐の脚を計算する。
規約：同じ宇宙の小さい圏の元の指定図式を扱う。
使われ方：B5 の余錐の古典比較。 -/
lemma nerveOppositeIso_vertex {C : Type u} [Category.{u} C] (x : C) :
    (_root_.SerrePositivity.InfinityCategories.HTT.Section6_1_2.nerveOppositeIso C).hom.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (op x)) =
      SSet.opObjEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex x) := by
  change (SSet.opObjEquiv (X := nerve C) (n := Opposite.op ⦋0⦌)).symm
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.oppositeNerveSimplex (ComposableArrows.mk₀ (op x))) = _
  congr 1

/-- 概要：反対圏の nerve の同型は元の指定射の辺を反転して保つ。
方針：反対 nerve の辺と反転した錐の脚を計算する。
規約：同じ宇宙の小さい圏の元の指定図式を扱う。
使われ方：B5 の余錐の古典比較。 -/
lemma nerveOppositeIso_edge {C : Type u} [Category.{u} C] {x y : C} (f : x ⟶ y) :
    (_root_.SerrePositivity.InfinityCategories.HTT.Section6_1_2.nerveOppositeIso C).hom.app (Opposite.op ⦋1⦌) (ComposableArrows.mk₁ f.op) =
      SSet.opObjEquiv.symm (ComposableArrows.mk₁ f) := by
  change (SSet.opObjEquiv (X := nerve C) (n := Opposite.op ⦋1⦌)).symm
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.oppositeNerveSimplex (ComposableArrows.mk₁ f.op)) = _
  congr 1
  refine ComposableArrows.ext₁ ?_ ?_ ?_
  · rfl
  · rfl
  · simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl

/-- 概要：反転した反対 nerve を戻す同型は元の指定射の辺を保つ。
方針：反対圏の射列の順序と矢印の反転を一次元で計算する。
規約：元の指定射を選び直さない。
使われ方：Over の比較射の脚の同定。 -/
lemma nerveUnopIso_edge {C : Type u} [Category.{u} C] {x y : C} (f : x ⟶ y) :
    (_root_.SerrePositivity.InfinityCategories.HTT.Section6_1_2.nerveUnopIso C).hom.app (Opposite.op ⦋1⦌)
      (SSet.opObjEquiv.symm (ComposableArrows.mk₁ f.op)) = ComposableArrows.mk₁ f := by
  change _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.oppositeNerveSimplex (ComposableArrows.mk₁ f.op) = _
  refine ComposableArrows.ext₁ ?_ ?_ ?_
  · rfl
  · rfl
  · simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl

end SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
