module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.OppositeWeakHomotopy
public import SerrePositivity.KST.ProExcision.NerveOppositeIso
public import SerrePositivity.HomotopicalAlgebra.Simplicial.NerveHomotopy
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PrecompositionTensor

/-!
# 元の nerve の圏同値と反対圏による弱同値の移送

概要：元の圏同値の nerve は弱同値で、元の関手の反対関手も弱同値を保つ。
方針：単位・余単位の実ホモトピーと nerve 反転の自然な同型を使う。
規約：圏の groupoid 性や nerve の Kan 性を要求しない。
使われ方：二方向の Grothendieck 構成の左右交換。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock
open CategoryTheory SerrePositivity.InfinityCategories

lemma nerveMap_equivalence_isWeakHomotopyEquivalence {C D : Type u}
    [Category.{u} C] [Category.{u} D] (e : C ≌ D) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (nerveMap e.functor) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence.isWeakHomotopyEquivalence
  refine ⟨nerveMap e.inverse, ⟨?_⟩, ⟨?_⟩⟩
  · change SSet.Homotopy (nerveMap (e.functor ⋙ e.inverse)) (nerveMap (𝟭 C))
    exact SerrePositivity.NerveHomotopy.homotopy e.unitIso.inv
  · change SSet.Homotopy (nerveMap (e.inverse ⋙ e.functor)) (nerveMap (𝟭 D))
    exact SerrePositivity.NerveHomotopy.homotopy e.counitIso.hom

lemma nerveMap_op_isWeakHomotopyEquivalence {C D : Type u}
    [Category.{u} C] [Category.{u} D] (F : C ⥤ D)
    (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (nerveMap F)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (nerveMap F.op) := by
  have h := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso
    (SerrePositivity.KST.ProExcision.nerveOppositeIso C)).isWeakHomotopyEquivalence.comp
      (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.opposite_map_isWeakHomotopyEquivalence _ hF)
  rw [← SerrePositivity.KST.ProExcision.nerveOppositeIso_natural C F] at h
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso
    (SerrePositivity.KST.ProExcision.nerveOppositeIso D)).isWeakHomotopyEquivalence.cancel_right h

end SerrePositivity.EInfinity.Hammock
