module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeNativeDiagramEndpoints
public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeAssociativityFamily
public import SerrePositivity.InfinityCategories.F1.Cocartesian.IsoTransportFamily
public import SerrePositivity.InfinityCategories.F1.Categories.QuasicategoryEnrichedDiagramArrowPrecompose

/-!
概要：全局所比較の族は、元の全 fibration の二重底変換上で既存の大域結合比較の族を回収。
方針：両端の豊穣図式と同じ全比較成分を照合し、共同実現へ渡す。
規約：同じ全相対 Hom 作用・指定結合同型・全ての底の射を保持する。
使われ方：結合 Hom 比較の全局所版と元の大域版の厳密な接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

variable {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C]
  (l : A ⥤ D) (k : D ⥤ C)

/-- 全局所比較の同じ区間図式を元の fibration に制限すると、元の結合比較全体となる。 -/
lemma cocartesianBaseChangeNativeEnriched_arrowDiagram :
    (cocartesianIsoTransportDiagramComparison A).arrowDiagram.precompose
        (cocartesianBaseChangeNativeEnriched l k) =
      (cocartesianBaseChangeAssociativityDiagramComparison l k).arrowDiagram := by
  rw [← QuasicategoryEnrichedDiagramComparison.arrowDiagram_precompose]
  apply QuasicategoryEnrichedDiagramComparison.arrowDiagram_eq_of_components
    (cocartesianBaseChangeNativeEnriched_sourceDiagram l k)
    (cocartesianBaseChangeNativeEnriched_targetDiagram l k)
  intro a p
  exact heq_of_eq (cocartesianIsoTransportDiagramComparison_native_component l k p a)

/-- 元の全相対 Hom の core に作用する、同じ指定結合同型の ∞ 関手。 -/
def cocartesianBaseChangeNativeInfinityMap :
    CocartesianFibrationInfinity (nerve C) ⟶ CocartesianIsoTransportInfinity A :=
  coherentNerveMap (cocartesianBaseChangeNativeCoreEnriched l k)

/-- 全局所比較の族を元の二重底変換へ戻すと、元の大域結合比較の同じ全区間族となる。 -/
lemma cocartesianBaseChangeNativeInfinityMap_family :
    cocartesianBaseChangeNativeInfinityMap l k ≫ cocartesianIsoTransportFamily A =
      cocartesianBaseChangeAssociativityFamily l k := by
  letI : SimplicialCategory (TransportEnrichment quasicategoryCoreFunctor.{u}
      (CocartesianFibrationObject (nerve C))) :=
    cocartesianFibrationCategory_simplicialCategory (nerve C)
  letI : SimplicialCategory (TransportEnrichment quasicategoryCoreFunctor.{u}
      (IsoTransportObject (CocartesianFibrationObject (nerve A)))) :=
    cocartesianIsoTransportCategory_simplicialCategory A
  change coherentNerveMap (quasicategoryCoreEnrichedFunctor
    (cocartesianBaseChangeNativeEnriched l k)) ≫
      (cocartesianIsoTransportDiagramComparison A).arrowDiagram.realization = _
  rw [← QuasicategoryEnrichedDiagram.realization_precompose,
    cocartesianBaseChangeNativeEnriched_arrowDiagram]
  rfl

end SerrePositivity.InfinityCategories
