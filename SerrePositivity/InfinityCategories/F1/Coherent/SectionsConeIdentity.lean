module

public import SerrePositivity.InfinityCategories.F1.Joins.ConeRealizationTransformation
public import SerrePositivity.InfinityCategories.F1.Coherent.DiagramSectionsCone
public import SerrePositivity.InfinityCategories.F1.Yoneda.PresheafDensity.Support.YonedaHomotopyVertex

/-!
概要：全切断の錐の標準変換の像を、同じ全切断の恒等射と比較する。
方針：実現の比較を写し、元の恒等射を表す指定同型と合成する。
規約：元の図式・全切断対象・恒等射を保持する。
使われ方：全 Hom による native な極限性の判定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
variable {B : SSet.{u}}
  (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u})

/-- 実現した全切断の錐の標準変換の像は、元の全切断の恒等射と同型。 -/
def coherentSectionsConeIdentityIso :
    VertexIso (X := (SSet.uliftFunctor.{u + 1, u}).obj
      ((ihom (spaceInfinityObject (coherentSpaceSectionsVertex F)).obj).obj
        (coherentSpaceSectionsObject F).obj))
      ((coherentSmallConstantSourceMap F (coherentSpaceSectionsVertex F)).app (Opposite.op ⦋0⦌)
        (coneTransformationPointAt (coherentDiagramSectionsCone F) (coherentSpaceSectionsVertex F)
          (coherentDiagramSectionsCone_vertex F)))
      (ULift.up.{u + 1, u} (functorVertex (coherentSpaceSectionsIdentity F))) := by
  let H := coneRealizationTransformationHomotopy
    (coherentSectionsIdentityRepresentation F).1 (coherentSectionsConeRealization F)
  exact (F2.vertexIsoOfYonedaHomotopy H).map
    (coherentSmallConstantSourceMap F (coherentSpaceSectionsVertex F)) ≪≫
      (coherentSectionsIdentityRepresentation F).2

end SerrePositivity.InfinityCategories
