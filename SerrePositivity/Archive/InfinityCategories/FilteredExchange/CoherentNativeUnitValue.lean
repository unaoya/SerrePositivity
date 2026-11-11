module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentNativeUnitRepresentation
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoherentConstantRepresentationLarge

/-!
概要：元の native 単位表現の全空間作用を、元の値と具体的な単位射の間の比較として保持する。
方針：同じ指定単位表現の大きい比較を使う。
規約：単位表現を選び直さない。使われ方：全三角形との交換則と指定外側因子の消去。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2
variable {B : SSet.{u}}
  (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})

/-- 元の native 単位表現の全空間作用を、元の fiber の値へ射影した実射。 -/
def coherentNativeUnitValueAction :=
  (leftUnstraighteningMappingVertexMap F (SSet.const (coherentDiagramTotalVertex F))
    (coherentNativeUnitRepresentation F).1).val ≫
    constantUnstraighteningFiberProjection ((SSet.uliftFunctor.{u + 1, u}).obj B)
      (coherentDiagramTotalVertex F) ≫
        (pointedSpaceFiberValueEquivalence (coherentDiagramTotalVertex F)).hom

/-- 元の指定単位表現の作用は、元の具体的な大きい単位射と同じ指定比較で結ばれる。 -/
def coherentNativeUnitValueIso :
    FunctorIso (coherentNativeUnitValueAction F) (coherentLargeTotalUnit F) :=
  CoherentConstantRepresentation.largeIso F (coherentDiagramTotalVertex F)
    (coherentDiagramTotalUnit F) (coherentNativeUnitRepresentation F)

end SerrePositivity.InfinityCategories.F2
