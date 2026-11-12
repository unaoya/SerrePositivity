module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.CoconePathSpaceFibration
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceSquareLimits

/-! 同じ mapping cocone の空間模型を頂点に持つ、空間の ∞ 圏での実極限錐。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits DifferentialGraded CochainComplex HomotopicalAlgebra
open SSet.modelCategoryQuillen
variable {R : Type u} [CommRing R]

def dgGluingComplexPinchedKanObject (K : Complex R) : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{max u v} :=
  ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedSpace.{u, v} K, inferInstance⟩

def dgGluingComplexPinchedKanMap {K L : Complex R} (φ : K ⟶ L) :
    dgGluingComplexPinchedKanObject.{u, v} K ⟶ dgGluingComplexPinchedKanObject.{u, v} L :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap φ

variable {P Q : Complex R} (d : P ⟶ Q)

def dgGluingCoconePathSpaceDiagram : AsSmall.{max u v} WalkingCospan ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{max u v} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.kanPullbackDiagram
    (dgGluingComplexPinchedKanMap.{u, v} (mappingCocone.fst (𝟙 Q)))
    (dgGluingComplexPinchedKanMap.{u, v} d)

def dgGluingCoconePathSpaceCone :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCone (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve (dgGluingCoconePathSpaceDiagram.{u, v} d)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.spaceSquareCone (K := dgGluingComplexPinchedKanObject.{u, v} (mappingCocone d))
    (dgGluingComplexPinchedKanMap.{u, v} (mappingCocone.fst (𝟙 Q)))
    (dgGluingComplexPinchedKanMap.{u, v} d)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, v} (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconePathMap d))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, v} (mappingCocone.fst d))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconePathSpace_isPullback.{u, v} d)

lemma dgGluingCoconePathSpaceCone_isLimit :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (dgGluingCoconePathSpaceCone.{u, v} d) := by
  let : Fibration
      (show (dgGluingComplexPinchedKanObject.{u, v} (mappingCocone (𝟙 Q))).obj ⟶
        (dgGluingComplexPinchedKanObject.{u, v} Q).obj from
        dgGluingComplexPinchedKanMap.{u, v} (mappingCocone.fst (𝟙 Q))) := by
    change Fibration (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.complexPinchedMap.{u, v} (mappingCocone.fst (𝟙 Q)))
    exact _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.dgGluingCoconePathSpaceProjection_fibration Q
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.spaceSquareCone_isLimit _ _ _ _ _

lemma dgGluingCoconePathSpaceCone_vertex :
    (dgGluingCoconePathSpaceCone.{u, v} d).vertex =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.coherentVertex
        (dgGluingComplexPinchedKanObject.{u, v} (mappingCocone d)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.spaceSquareCone_vertex _ _ _ _ _

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
