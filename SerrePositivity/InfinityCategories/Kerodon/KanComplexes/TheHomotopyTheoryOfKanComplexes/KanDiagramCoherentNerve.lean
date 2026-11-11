module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.OrderDiagrams

/-!
概要：小さい通常の圏の Kan 値図式の coherent nerve での表示。
方針：各有限射列に通常の関手を合成し、定値な豊穣 Hom の図式として写す。
規約：底の nerve は u+1 に持ち上げ、値域は coherent nerve による SpaceInfinity とする。
使われ方：Kerodon Construction 5.3.1.5（Tag 035J）、Corollary 5.6.0.6（Tag 028T）、strict transport の空間値表示。

対応節は Kerodon 3.1（Tag 00SZ）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes

/-- 概要：通常の Kan 値図式を、持ち上げた底の nerve から 𝒮 への射にする。
方針：各射列を図式に写し、その通常の合成を定値な豊穣 Hom にする。
規約：一般の coherent diagram の strictification はこの定義の主張に含めない。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、strict な表現を coherent な空間値図式として扱う。 -/
noncomputable def kanDiagramCoherentNerve
    {C : Type u} [Category.{u} C] (F : C ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    (SSet.uliftFunctor.{u + 1, u}).obj (nerve C) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} where
  app n := ↾fun s ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.enrichedFunctorOfOrderDiagram
    ((⟨ULift.down, fun _ _ h ↦ h⟩ :
      ULift.{u} (Fin (n.unop.len + 1)) →o Fin (n.unop.len + 1)).toFunctor ⋙ s.down ⋙ F)
  naturality {n m} α := by
    apply ConcreteCategory.hom_ext
    intro s
    change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.enrichedFunctorOfOrderDiagram _ =
      (SimplicialThickening.functor α.unop.toOrderHom.uliftMap).comp SSet
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.enrichedFunctorOfOrderDiagram _)
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.enrichedFunctorOfOrderDiagram_precomp]
    rfl

/-- 概要：Kan 値図式の coherent 表示は各頂点で元の Kan 複体を表す。
方針：零単体の唯一の対象を取り出して、coherent nerve の頂点を復元する。
規約：底の頂点は u+1 への ULift で表示する。
使われ方：Kerodon Corollary 5.6.0.6（Tag 028T）、unstraightening の fiber の値の同定。 -/
lemma kanDiagramCoherentNerve_vertex
    {C : Type u} [Category.{u} C] (F : C ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) (c : C) :
    (kanDiagramCoherentNerve F).app (Opposite.op ⦋0⦌) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.spaceInfinityVertex (F.obj c) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityVertex_eq_coherent]
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex_object
    ((kanDiagramCoherentNerve F).app (Opposite.op ⦋0⦌) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c)))).symm

/-- 概要：Kan 値図式の coherent 表示は通常の底の関手による前合成と可換。
方針：各単体で底の射列と係数図式の関手合成を比較する。
規約：底の射は nerveMap を宇宙持ち上げした射。
使われ方：Kerodon Remark 5.6.2.18（Tag 0271）、strict 表現と coherent 図式の底変換の整合性。 -/
lemma kanDiagramCoherentNerve_precomp
    {C D : Type u} [Category.{u} C] [Category.{u} D]
    (H : D ⥤ C) (F : C ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u}) :
    (SSet.uliftFunctor.{u + 1, u}).map (nerveMap H) ≫ kanDiagramCoherentNerve F =
      kanDiagramCoherentNerve (H ⋙ F) := rfl

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
