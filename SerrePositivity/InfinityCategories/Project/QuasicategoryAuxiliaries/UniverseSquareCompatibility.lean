module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Square
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.UniverseSSetMaps
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PushoutShape
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.UniverseOuterHornJoins
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.UniverseSquareShape
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.UniverseSquareTriangles

/-! # 四角形と外側ホーンの錐の宇宙整合性

概要：四角形と span/cospan の錐の同型は宇宙持ち上げと可換。
方針：二つの標準三角形上で照合し、pushout の一意性を使う。
規約：h 圏での比較ではなく実写像の等式。使われ方：普遍四角形の宇宙降下。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
open CategoryTheory SSet
open scoped _root_.Simplicial

private lemma inverse_square {A B C D : SSet.{u}} (e : A ≅ B) (f : C ≅ D)
    (g : A ⟶ C) (h : B ⟶ D) (w : g ≫ f.hom = e.hom ≫ h) :
    h ≫ f.inv = e.inv ≫ g := by
  apply (cancel_epi e.hom).1
  rw [← Category.assoc, ← w, Category.assoc, f.hom_inv_id, Category.comp_id,
    ← Category.assoc, e.hom_inv_id, Category.id_comp]

/-- Cospan の錐と四角形の実同型は宇宙比較と可換。 -/
lemma uliftCospanConeIso_square :
    (SSet.uliftFunctor.{v, u}).map _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.hom ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSquareIso.hom =
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftCospanConeIso.{u, v}.hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso.hom := by
  apply (cancel_epi _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftCospanConeIso.inv).1
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanCone_isPushout.hom_ext
  · have ht := inverse_square (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso.{u, v} 2)
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftCospanConeIso ((SSet.uliftFunctor.{v, u}).map _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeTriangleLeft)
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeTriangleLeft _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftCospanConeIso_left
    simp only [← Category.assoc]
    rw [ht]
    simp only [Category.assoc, ← Functor.map_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso_left]
    rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSquareIso_triangle]
    simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  · have ht := inverse_square (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso.{u, v} 2)
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftCospanConeIso ((SSet.uliftFunctor.{v, u}).map _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeTriangleRight)
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeTriangleRight _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftCospanConeIso_right
    simp only [← Category.assoc]
    rw [ht]
    simp only [Category.assoc, ← Functor.map_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cospanConeSquareIso_right]
    rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSquareIso_triangle]
    simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- Span の錐と四角形の実同型は宇宙比較と可換。 -/
lemma uliftSpanCoconeIso_square :
    (SSet.uliftFunctor.{v, u}).map _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.hom ≫ _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSquareIso.hom =
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSpanCoconeIso.{u, v}.hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.hom := by
  apply (cancel_epi _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSpanCoconeIso.inv).1
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCocone_isPushout.hom_ext
  · have ht := inverse_square (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso.{u, v} 2)
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSpanCoconeIso ((SSet.uliftFunctor.{v, u}).map _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeTriangleLeft)
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeTriangleLeft _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSpanCoconeIso_left
    simp only [← Category.assoc]
    rw [ht]
    simp only [Category.assoc, ← Functor.map_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso_left]
    rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSquareIso_triangle]
    simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  · have ht := inverse_square (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftStdSimplexIso.{u, v} 2)
      _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSpanCoconeIso ((SSet.uliftFunctor.{v, u}).map _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeTriangleRight)
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeTriangleRight _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSpanCoconeIso_right
    simp only [← Category.assoc]
    rw [ht]
    simp only [Category.assoc, ← Functor.map_comp, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso_right]
    rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftSquareIso_triangle]
    simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

end SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
