module
public import SerrePositivity.InfinityCategories.Derived.Gluing.CoconePathSpaceFibration
public import SerrePositivity.InfinityCategories.F2.SpaceSquareLimits

/-! 同じ mapping cocone の空間模型を頂点に持つ、空間の ∞ 圏での実極限錐。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded CochainComplex HomotopicalAlgebra
open SSet.modelCategoryQuillen
variable {R : Type u} [CommRing R]

def dgGluingComplexPinchedKanObject (K : Complex R) : KanObject.{max u v} :=
  ⟨complexPinchedSpace.{u, v} K, inferInstance⟩

def dgGluingComplexPinchedKanMap {K L : Complex R} (φ : K ⟶ L) :
    dgGluingComplexPinchedKanObject.{u, v} K ⟶ dgGluingComplexPinchedKanObject.{u, v} L :=
  complexPinchedMap φ

variable {P Q : Complex R} (d : P ⟶ Q)

def dgGluingCoconePathSpaceDiagram : AsSmall.{max u v} WalkingCospan ⥤ KanObject.{max u v} :=
  HomotopyLimits.kanPullbackDiagram
    (dgGluingComplexPinchedKanMap.{u, v} (mappingCocone.fst (𝟙 Q)))
    (dgGluingComplexPinchedKanMap.{u, v} d)

def dgGluingCoconePathSpaceCone :
    JoinCone (kanDiagramCoherentNerve (dgGluingCoconePathSpaceDiagram.{u, v} d)) :=
  F2.spaceSquareCone (K := dgGluingComplexPinchedKanObject.{u, v} (mappingCocone d))
    (dgGluingComplexPinchedKanMap.{u, v} (mappingCocone.fst (𝟙 Q)))
    (dgGluingComplexPinchedKanMap.{u, v} d)
    (complexPinchedMap.{u, v} (dgGluingCoconePathMap d))
    (complexPinchedMap.{u, v} (mappingCocone.fst d))
    (dgGluingCoconePathSpace_isPullback.{u, v} d)

lemma dgGluingCoconePathSpaceCone_isLimit :
    IsLimitCone (dgGluingCoconePathSpaceCone.{u, v} d) := by
  let : Fibration
      (show (dgGluingComplexPinchedKanObject.{u, v} (mappingCocone (𝟙 Q))).obj ⟶
        (dgGluingComplexPinchedKanObject.{u, v} Q).obj from
        dgGluingComplexPinchedKanMap.{u, v} (mappingCocone.fst (𝟙 Q))) := by
    change Fibration (complexPinchedMap.{u, v} (mappingCocone.fst (𝟙 Q)))
    exact dgGluingCoconePathSpaceProjection_fibration Q
  exact F2.spaceSquareCone_isLimit _ _ _ _ _

lemma dgGluingCoconePathSpaceCone_vertex :
    (dgGluingCoconePathSpaceCone.{u, v} d).vertex =
      F2.coherentVertex
        (dgGluingComplexPinchedKanObject.{u, v} (mappingCocone d)) :=
  F2.spaceSquareCone_vertex _ _ _ _ _

end SerrePositivity.InfinityCategories
