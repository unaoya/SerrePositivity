module

public import SerrePositivity.InfinityCategories.F2.CoherentCospanConeRelativePathClass
public import SerrePositivity.InfinityCategories.F2.KanHomotopyExtensionClass

/-!
概要：元の底固定円柱と既存の全空間円柱の指定 Kan 延長は同じ可換同型を与える。
方針：単位上の指定類の一致を前合成の忠実性で反映する。
規約：元の両円柱と指定延長を保持。使われ方：全空間模型と native 比較候補の path 照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}} [Quasicategory B]
  (F X Y Z : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})
  (C : CoherentTransformationCospanCone F X Y Z)

/-- 概要：底固定円柱と既存円柱の Kan 延長が定める同型は元の指定値で一致する。
方針：元の単位上の指定類の一致を Kan 延長の同型の等式へ反映する。
規約：π₀ の一致に弱めない。使われ方：比較候補の全 path の照合。 -/
lemma coherentCospanConeRelativePathHomotopy_kan_iso :
    functorIsoOfSimplicialHomotopy
      (specifiedContinuousKanHomotopy (coherentCospanConeRelativePathHomotopy F X Y Z C)).val =
    functorIsoOfSimplicialHomotopy
      (specifiedContinuousKanHomotopy (coherentCospanConeTotalPathHomotopy F X Y Z C)).val :=
  kanHomotopyExtension_iso_eq
    (coherentCospanConeRelativePathHomotopy F X Y Z C)
    (coherentCospanConeTotalPathHomotopy F X Y Z C) _ _
    (specifiedContinuousKanHomotopy (coherentCospanConeRelativePathHomotopy F X Y Z C)).property
    (specifiedContinuousKanHomotopy (coherentCospanConeTotalPathHomotopy F X Y Z C)).property
    (coherentCospanConeRelativePathHomotopy_unit_hom F X Y Z C)

end SerrePositivity.InfinityCategories.F2
