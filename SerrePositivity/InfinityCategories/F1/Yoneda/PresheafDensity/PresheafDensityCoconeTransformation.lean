module

public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.PresheafDensityCocone
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.CoconeRealizationTransformation
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.YonedaHomotopyVertex

/-!
概要：同じ native 密度余錐の標準変換を、元の大域密度変換へ比較する。
方針：F2 の両端固定実現の円柱を変換空間へ戻し、その Kan 性で同型として保持する。
規約：元の図式・元の F・元の変換頂点を全て固定する。
使われ方：評価後の native 余錐の fiber 写像を、証明済みの大域評価へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {C : SSet.{u}} [Quasicategory C]
  (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u})

/-- 指定頂点 F で正規化した、同じ native 密度余錐の標準変換。 -/
def presheafDensityCoconeTransformationVertex :=
  (F2.coconeTransformationMap (presheafElementsYonedaDiagram F) (functorVertex F)).app
    (Opposite.op ⦋0⦌) (F2.coconeMappingPointAt (presheafDensityCocone F)
      (functorVertex F) (presheafDensityCocone_vertex F))

/-- 同じ native 変換から元の大域変換への、実際の変換空間内の円柱。 -/
def presheafDensityCoconeTransformationHomotopy :
    SSet.Homotopy (SSet.yonedaEquiv.symm (presheafDensityCoconeTransformationVertex F))
      (SSet.yonedaEquiv.symm (presheafDensityTransformationVertex F)) :=
  F2.coconeRealizationTransformationHomotopy (presheafDensityTransformationVertex F)
    (presheafDensityCoconeRealization F)

/-- 同じ native 密度余錐の元の変換は、同じ大域評価からの変換と同型。 -/
def presheafDensityCoconeTransformationIso :
    VertexIso (presheafDensityCoconeTransformationVertex F)
      (presheafDensityTransformationVertex F) :=
  F2.vertexIsoOfYonedaHomotopy (presheafDensityCoconeTransformationHomotopy F)

end SerrePositivity.InfinityCategories.F2.Ind
