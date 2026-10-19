module

public import SerrePositivity.InfinityCategories.HomotopyLimits.ColimitAttachmentPointHom

/-!
概要：部分余極限頂点の点 Hom と左 pinched Hom の cospan・end を厳密に同型にする。
方針：始対象の底の fiber 同型を三成分で束ね、重み付き切断関手で end へ移す。
規約：付加比較辺の選択を変えない。使われ方：native な span の余錐空間との共通模型。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {A B C D X : SSet.{u}} [Quasicategory X] {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) (p : D ⟶ X) (y : X _⦋0⦌)
  (c : JoinCocone (f ≫ (i ≫ p))) (hc : IsColimitCone c)
  (dB : JoinCocone (i ≫ p)) (dC : JoinCocone (j ≫ p))

/-- 部分余極限の実際の比較辺で前合成する、三つの点 Hom の cospan。 -/
def partialColimitPointHomCospan : AsSmall.{u} WalkingCospan ⥤ SSet.{u} :=
  pointHomCospan (coconeVertexDiagram c) (coconeVertexDiagram dB) (coconeVertexDiagram dC)
    (colimitAttachmentPointEdge c hc f (i ≫ p) rfl dB)
    (colimitAttachmentPointEdge c hc g (j ≫ p) (coconePushoutBoundary_eq hp p) dC)
    (colimitAttachmentPointEdge_source c hc f (i ≫ p) rfl dB)
    (colimitAttachmentPointEdge_target c hc f (i ≫ p) rfl dB)
    (colimitAttachmentPointEdge_source c hc g (j ≫ p) (coconePushoutBoundary_eq hp p) dC)
    (colimitAttachmentPointEdge_target c hc g (j ≫ p) (coconePushoutBoundary_eq hp p) dC) y

/-- 同じ三頂点の点 Hom と左 pinched Hom の cospan は、全単体で自然同型。 -/
def partialColimitPointHomCospanIso :
    partialColimitPointHomCospan hp p y c hc dB dC ≅ partialColimitHomCospan hp p y c hc dB dC :=
  Functor.isoWhiskerLeft AsSmall.down (cospanIsoMk
    (leftFibrationInitialBaseIso (sliceUnderProjection (f ≫ (i ≫ p))) c y)
    (leftFibrationInitialBaseIso (sliceUnderProjection (j ≫ p)) dC y)
    (leftFibrationInitialBaseIso (sliceUnderProjection (i ≫ p)) dB y)
    (colimitAttachmentPointHom_square c hc g (j ≫ p) (coconePushoutBoundary_eq hp p) dC y)
    (colimitAttachmentPointHom_square c hc f (i ≫ p) rfl dB y))

/-- 三頂点の点 Hom の end と左 pinched Hom の end の実際の同型。 -/
def partialColimitPointHomEndIso :
    weightedSections (bousfieldKanWeight (AsSmall.{u} WalkingCospan))
        (partialColimitPointHomCospan hp p y c hc dB dC) ≅
      weightedSections (bousfieldKanWeight (AsSmall.{u} WalkingCospan))
        (partialColimitHomCospan hp p y c hc dB dC) :=
  (weightedSectionsFunctor _).mapIso (partialColimitPointHomCospanIso hp p y c hc dB dC)

end
end SerrePositivity.InfinityCategories.HomotopyLimits
