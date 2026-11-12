module
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHomCorrespondence
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Equivalence
public import Mathlib.CategoryTheory.Comma.Arrow
/-!
概要：指定した両端の等式と同じ同型の HEq から、元の射の Arrow 等式を得る。
方針：実 fiber の射影の恒等性と、同じ宇宙比較・端点輸送を使う。
規約：元の指定同型と実切断を保持する。使われ方：kernel の指定余単位の厳密回収。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open CategoryTheory SSet
/-- 指定した両端の等式と同型の HEq は、同じ Hom 射の Arrow 表示を保つ。 -/
lemma functorIso_hom_arrow_of_heq {X Y : SSet.{u}} {f g f' g' : X ⟶ Y}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (e' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f' g') (hf : f = f') (hg : g = g')
    (h : HEq e e') : Arrow.mk e.hom = Arrow.mk e'.hom := by
  subst f' g'
  cases eq_of_heq h
  rfl
/-- 同じ同型と同じ後続射の合成は、始点輸送に依存しない Arrow を与える。 -/
lemma functorIso_hom_comp_arrow_of_heq
    {X Y : SSet.{u}} {f f' g t : X ⟶ Y}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (e' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f' g)
    (hf : f = f') (h : HEq e e') (k : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom g t) :
    Arrow.mk (e.hom ≫ k) = Arrow.mk (e'.hom ≫ k) := by
  subst f'
  cases eq_of_heq h
  rfl
end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
