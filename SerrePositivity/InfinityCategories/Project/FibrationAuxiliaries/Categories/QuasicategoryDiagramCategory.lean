module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCatSimplicial
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.StrictDiagramComposition
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.CoreEnrichedFunctor

/-!
概要：strict な quasicategory 値図式と元の全変換空間の core による豊穣化。
方針：各対象の充填性だけを束ね、全変換の単位・合成を core 関手で移す。
規約：全変換空間の quasicategory 性も core の Kan 性も仮定しない。
使われ方：全 Hom に自然な quasicategory 値の比較を coherent な図式の族にする。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories

/-- 元の quasicategory の underlying 単体集合への忘却。 -/
def quasicategoryObjectForget : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QuasicategoryObject.{u} ⥤ SSet.{u} where
  obj X := X.obj
  map f := f

/-- 任意の strict な quasicategory 値図式を、独立の豊穣 Hom を与えるために束縛する。 -/
def QuasicategoryDiagramObject (C : Type u) [Category.{u} C] :=
  {F : C ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QuasicategoryObject.{u} // True}

/-- 元の全 strict な変換空間による豊穣構造。 -/
instance quasicategoryDiagramObject_enrichedCategory (C : Type u) [Category.{u} C] :
    EnrichedCategory SSet.{u} (QuasicategoryDiagramObject C) where
  Hom F G := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingSpace
    (F.val ⋙ quasicategoryObjectForget) (G.val ⋙ quasicategoryObjectForget)
  id F := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMappingIdentity (F.val ⋙ quasicategoryObjectForget)
  comp F G H := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMappingComposition (F.val ⋙ quasicategoryObjectForget)
    (G.val ⋙ quasicategoryObjectForget) (H.val ⋙ quasicategoryObjectForget)
  id_comp F G := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMappingIdentity_comp
    (F.val ⋙ quasicategoryObjectForget) (G.val ⋙ quasicategoryObjectForget)
  comp_id F G := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMappingComposition_id
    (F.val ⋙ quasicategoryObjectForget) (G.val ⋙ quasicategoryObjectForget)
  assoc F G H I := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMappingComposition_assoc
    (F.val ⋙ quasicategoryObjectForget) (G.val ⋙ quasicategoryObjectForget)
    (H.val ⋙ quasicategoryObjectForget) (I.val ⋙ quasicategoryObjectForget)

/-- 通常の射は元の全変換空間の零単体。 -/
instance quasicategoryDiagramObject_category (C : Type u) [Category.{u} C] :
    Category.{u} (QuasicategoryDiagramObject C) :=
  inferInstanceAs (Category (ForgetEnrichment SSet.{u} (QuasicategoryDiagramObject C)))

/-- 元の通常の射を、同じ豊穣 Hom の単位からの射へ対応させる。 -/
instance quasicategoryDiagramObject_simplicialCategory (C : Type u) [Category.{u} C] :
    SimplicialCategory (QuasicategoryDiagramObject C) where
  homEquiv := Equiv.refl _
  homEquiv_id F := ForgetEnrichment.homTo_id (W := SSet.{u}) (C := QuasicategoryDiagramObject C) F
  homEquiv_comp f g := ForgetEnrichment.homTo_comp
    (W := SSet.{u}) (C := QuasicategoryDiagramObject C) f g

/-- 元の全変換空間の core を Hom とする strict な図式の圏。 -/
def QuasicategoryDiagramCategory (C : Type u) [Category.{u} C] : Type (u + 1) :=
  TransportEnrichment _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor.{u} (QuasicategoryDiagramObject C)

/-- core を取る移送は、元の通常の対象と射の圏を保つ。 -/
instance quasicategoryDiagramCategory_category (C : Type u) [Category.{u} C] :
    Category.{u} (QuasicategoryDiagramCategory C) :=
  inferInstanceAs (Category.{u}
    (TransportEnrichment _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor.{u} (QuasicategoryDiagramObject C)))

/-- core による同じ豊穣構造と通常の圏構造を整合させる。 -/
instance quasicategoryDiagramCategory_simplicialCategory (C : Type u) [Category.{u} C] :
    SimplicialCategory (QuasicategoryDiagramCategory C) :=
  TransportEnrichment.enrichedOrdinaryCategory (QuasicategoryDiagramObject C)
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCoreFunctor.{u} _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.quasicategoryCoreUnitHomEquiv _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.quasicategoryCoreUnitHomEquiv_eq

/-- 元の図式と全高次の変換を、底の一対象で評価する豊穣関手。 -/
def quasicategoryDiagramEvaluationEnriched {C : Type u} [Category.{u} C] (c : C) :
    EnrichedFunctor SSet.{u} (QuasicategoryDiagramObject C) _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QuasicategoryObject.{u} where
  obj F := F.val.obj c
  map F G := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.strictDiagramMappingComponent
    (F.val ⋙ quasicategoryObjectForget) (G.val ⋙ quasicategoryObjectForget) c
  map_id F := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMappingIdentity_component (F.val ⋙ quasicategoryObjectForget) c
  map_comp F G H := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.strictDiagramMappingComposition_component
    (F.val ⋙ quasicategoryObjectForget) (G.val ⋙ quasicategoryObjectForget)
    (H.val ⋙ quasicategoryObjectForget) c

/-- 元の図式の全変換の core 上でも、同じ対象成分を評価する。 -/
def quasicategoryDiagramCoreEvaluationEnriched {C : Type u} [Category.{u} C] (c : C) :
    EnrichedFunctor SSet.{u} (QuasicategoryDiagramCategory C) _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.QCat.{u} :=
  _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.quasicategoryCoreEnrichedFunctor (quasicategoryDiagramEvaluationEnriched c)

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories
