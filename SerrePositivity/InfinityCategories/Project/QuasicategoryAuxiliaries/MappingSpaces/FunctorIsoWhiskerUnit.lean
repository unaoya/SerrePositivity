module

public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.MappingSpaces.FunctorIsoWhiskerAlgebra

/-!
概要：恒等関手による指定関手同型の後合成の簡約。
方針：誘導されるホモトピー圏の関手が恒等関手となることを使う。
規約：指定された三角形と同型の値を保持する。
使われ方：引き戻し錐と指定 path の比較を簡約する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries

/-- 概要：恒等関手による指定関手同型の後合成の簡約。
方針：誘導されるホモトピー圏の関手が恒等関手となることを使う。
規約：元の指定同型の値を保持する。
使われ方：二射影の指定比較と指定 path の整合。 -/
lemma mapIso_heq_of_functor_eq {D E : Type u} [Category D] [Category E]
    {F G : D ⥤ E} (h : F = G) {a b : D} (e : a ≅ b) :
    HEq (F.mapIso e) (G.mapIso e) := by
  cases h
  rfl
/-- 概要：恒等関手による指定関手同型の後合成の簡約。
方針：誘導されるホモトピー圏の関手が恒等関手となることを使う。
規約：元の指定同型の値を保持する。
使われ方：二射影の指定比較と指定 path の整合。 -/
lemma functorIso_postcomp_id {X Y : SSet.{u}} {f g : X ⟶ Y} (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) :
    e.postcomp (𝟙 Y) = e := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIso_postcomp_eq_mapIso]
  have h : SSet.mapHomotopyCategory ((ihom X).map (𝟙 Y)) =
      𝟭 (SSet.HomotopyCategory ((ihom X).obj Y)) := by
    change (hoFunctor.map ((ihom X).map (𝟙 Y))).toFunctor = _
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
    rfl
  exact eq_of_heq (mapIso_heq_of_functor_eq h e)

end SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
