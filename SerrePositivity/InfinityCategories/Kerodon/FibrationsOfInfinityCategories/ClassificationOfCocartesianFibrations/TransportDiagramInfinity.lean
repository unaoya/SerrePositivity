module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.TransportDiagramCategory

/-!
概要：cocartesian strict transport 図式と可逆な変換からなる中間 ∞ 圏。
方針：元の全変換空間の core を Hom に取り、局所 Kan な単体的圏の coherent nerve を使う。
規約：標的は strict transport の像であり、全ての Cat∞ 値図式との同値は別途証明する。
使われ方：元の cocartesian fibration の ∞ 圏から分類主写像への比較の中間項。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- strict transport 図式の全変換空間の core を Hom とする単体的圏。 -/
def CocartesianTransportDiagramCategory (C : Type u) [Category.{u} C] : Type (u + 1) :=
  TransportEnrichment _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor.{u} (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianTransportDiagramObject C)

/-- core による移送は元の通常の strict な変換を保持する。 -/
instance cocartesianTransportDiagramCategory_category (C : Type u) [Category.{u} C] :
    Category.{u} (CocartesianTransportDiagramCategory C) :=
  inferInstanceAs (Category.{u}
    (TransportEnrichment _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor.{u} (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianTransportDiagramObject C)))

/-- core の Hom と元の通常の strict な変換は単体的圏をなす。 -/
instance cocartesianTransportDiagramCategory_simplicialCategory (C : Type u) [Category.{u} C] :
    SimplicialCategory (CocartesianTransportDiagramCategory C) :=
  TransportEnrichment.enrichedOrdinaryCategory (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianTransportDiagramObject C)
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor.{u} _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.quasicategoryCoreUnitHomEquiv _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.quasicategoryCoreUnitHomEquiv_eq

/-- 図式間の豊穣 Hom は、元の strict な全変換空間の core そのもの。 -/
lemma cocartesianTransportDiagramCategory_sHom {C : Type u} [Category.{u} C]
    (F G : CocartesianTransportDiagramCategory C) :
    SimplicialCategory.sHom F G =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingSpace F.val G.val) : SSet.{u}) := rfl

/-- 全変換空間の quasicategory 性により、core の Hom は Kan 複体。 -/
instance cocartesianTransportDiagramCategory_sHom_kanComplex
    {C : Type u} [Category.{u} C] (F G : CocartesianTransportDiagramCategory C) :
    KanComplex (SimplicialCategory.sHom F G) := by
  rw [cocartesianTransportDiagramCategory_sHom]
  let : Quasicategory (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingSpace F.val G.val) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramObject_sHom_quasicategory F G
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.quasicategoryCore_kanComplex _

/-- 元の strict transport 図式と可逆な変換の全高次からなる ∞ 圏。 -/
def CocartesianTransportDiagramInfinity (C : Type u) [Category.{u} C] : SSet.{u + 1} :=
  SimplicialNerve (CocartesianTransportDiagramCategory C)

/-- 全ての Hom の局所 Kan 性から中間の ∞ 圏は quasicategory。 -/
instance cocartesianTransportDiagramInfinity_quasicategory (C : Type u) [Category.{u} C] :
    Quasicategory (CocartesianTransportDiagramInfinity C) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.simplicialNerve_quasicategory (CocartesianTransportDiagramCategory C)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
