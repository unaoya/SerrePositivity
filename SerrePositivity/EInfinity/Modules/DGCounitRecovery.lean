module

public import SerrePositivity.EInfinity.Modules.DGGraphNerveAdjunction
public import SerrePositivity.EInfinity.Modules.DGResolutionAdjunction
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CounitMappingAdjunctionRecovery

/-!
# dg 加群随伴の指定余単位の回収

概要：HA §4.2.3 の二つの native 随伴の余単位を、元の全ホモトピーの類へ同定する。
方針：全区間条件からの随伴の余単位回収公式を使う。
規約：頂点成分だけでなく全関手圏の射の等式。使われ方：同じ単位・余単位の照合。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.EInfinity.Modules
open CategoryTheory SSet
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
variable (A : Type u) [CommRing A] (D E : Type v)
  [DGCategory A D] [Small.{u} D] [DGCategory A E] [Small.{u} E]

/-- 概要：生の graph 随伴の余単位は同じ dg 余単位（HA §4.2.3）。
方針：随伴構成の余単位回収公式を適用。
規約：全関手圏の射の等式。使われ方：指定 graph 比較との整合性。 -/
lemma graphRawAdjunction_counitHom (F : DGFunctor A D E) :
    (graphRawAdjunction A D E F).counitHom =
      Truncated.HomotopyCategory.homMk
        (functorEdgeOfSimplicialHomotopy (graphCounitHomotopy A D E F)) := by
  unfold graphRawAdjunction
  exact qcatAdjunctionOfCounitIntervalCondition_counitHom _ _

omit [DGCategory A E] [Small.{u} E] in
/-- 概要：包含・解像度随伴の余単位は同じ augmentation（HA §1.3.1）。
方針：随伴構成の余単位回収公式を適用。
規約：全関手圏の射の等式。使われ方：指定解像度との整合性。 -/
lemma moduleResolutionAdjunction_counitHom :
    (moduleResolutionAdjunction A D).counitHom =
      Truncated.HomotopyCategory.homMk
        (functorEdgeOfSimplicialHomotopy (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.DerivedCategories.dgModuleResolutionAugmentationHomotopy A D)) := by
  unfold moduleResolutionAdjunction
  exact qcatAdjunctionOfCounitIntervalCondition_counitHom _ _

end SerrePositivity.EInfinity.Modules
