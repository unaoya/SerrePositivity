module

public import SerrePositivity.InfinityCategories.HomotopyLimits.PartialColimitPointHomEnd
public import SerrePositivity.InfinityCategories.HomotopyLimits.StrictSpanHornEdges

/-!
概要：部分余極限対象の native な span の余錐空間を、元の図式側と同じ左 Hom の end へ移す。
方針：strict な span の二辺を付加比較辺と同定し、点図式と左 Hom の自然同型を合成する。
規約：元の図式の余錐の普遍点の照合は別工程。使われ方：coherent 図式の余極限の貼り合わせ。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
variable {A B C D : SSet.{u + 1}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) (p : D ⟶ SpaceInfinity.{u})
  (c : JoinCocone (f ≫ (i ≫ p))) (hc : IsColimitCone c)
  (dB : JoinCocone (i ≫ p)) (dC : JoinCocone (j ≫ p))

/-- 部分余極限 span のホーン表示の左辺は、実際の左付加比較辺。 -/
lemma partialColimitSpanHorn_left_edge :
    horn₂₀.ι₀₁ ≫ strictSpanHornDiagram (strictCoherentDiagram
        (partialColimitApexSpan c hc f (i ≫ p) rfl dB
          g (j ≫ p) (coconePushoutBoundary_eq hp p) dC)) =
      colimitAttachmentPointEdge c hc f (i ≫ p) rfl dB := by
  rw [strictSpanHornDiagram_left_edge, colimitAttachmentPointEdge_eq]
  exact congrArg SSet.yonedaEquiv.symm (colimitAttachmentApexHom_edge c hc f (i ≫ p) rfl dB)

/-- 部分余極限 span のホーン表示の右辺も、実際の右付加比較辺。 -/
lemma partialColimitSpanHorn_right_edge :
    horn₂₀.ι₀₂ ≫ strictSpanHornDiagram (strictCoherentDiagram
        (partialColimitApexSpan c hc f (i ≫ p) rfl dB
          g (j ≫ p) (coconePushoutBoundary_eq hp p) dC)) =
      colimitAttachmentPointEdge c hc g (j ≫ p) (coconePushoutBoundary_eq hp p) dC := by
  rw [strictSpanHornDiagram_right_edge, colimitAttachmentPointEdge_eq]
  exact congrArg SSet.yonedaEquiv.symm
    (colimitAttachmentApexHom_edge c hc g (j ≫ p) (coconePushoutBoundary_eq hp p) dC)

variable (y : SpaceInfinity.{u} _⦋0⦌)

/-- native な span の点 Hom の図式は、元の付加比較辺の点 Hom の図式と厳密に自然同型。 -/
def partialColimitSpanPointHomCospanIso :
    spanPointHomCospan (strictSpanHornDiagram (strictCoherentDiagram
        (partialColimitApexSpan c hc f (i ≫ p) rfl dB
          g (j ≫ p) (coconePushoutBoundary_eq hp p) dC))) y ≅
      partialColimitPointHomCospan hp p y c hc dB dC := by
  apply pointHomCospanPresentationIso rfl rfl
    (coconePushoutBoundary_eq horn₂₀.isPushout _) rfl
    (colimitAttachmentPointEdge_source c hc f (i ≫ p) rfl dB)
    (colimitAttachmentPointEdge_target c hc f (i ≫ p) rfl dB)
    (colimitAttachmentPointEdge_source c hc g (j ≫ p) (coconePushoutBoundary_eq hp p) dC)
    (colimitAttachmentPointEdge_target c hc g (j ≫ p) (coconePushoutBoundary_eq hp p) dC)
    (partialColimitSpanHorn_left_edge hp p c hc dB dC)
    (partialColimitSpanHorn_right_edge hp p c hc dB dC)
  · rw [partialColimitSpanHorn_left_edge hp p c hc dB dC, colimitAttachmentPointEdge_source]
  · rw [partialColimitSpanHorn_left_edge hp p c hc dB dC, colimitAttachmentPointEdge_target]
  · rw [partialColimitSpanHorn_right_edge hp p c hc dB dC, colimitAttachmentPointEdge_target]

/-- native な span の点 Hom の end と、元の図式側の左 Hom の end の厳密な同型。 -/
def partialColimitSpanHomEndIso :
    weightedSections (bousfieldKanWeight (AsSmall.{u + 1} WalkingCospan))
        (spanPointHomCospan (strictSpanHornDiagram (strictCoherentDiagram
          (partialColimitApexSpan c hc f (i ≫ p) rfl dB
            g (j ≫ p) (coconePushoutBoundary_eq hp p) dC))) y) ≅
      weightedSections (bousfieldKanWeight (AsSmall.{u + 1} WalkingCospan))
        (partialColimitHomCospan hp p y c hc dB dC) :=
  (weightedSectionsFunctor _).mapIso (partialColimitSpanPointHomCospanIso hp p c hc dB dC y) ≪≫
    partialColimitPointHomEndIso hp p y c hc dB dC

/-- 部分余極限対象の strict な span の余錐空間から、元の図式と共通の左 Hom の end への射。 -/
def partialColimitSpanCoconeToHomEnd :
    coconeMappingSpace (strictCoherentDiagram
        (partialColimitApexSpan c hc f (i ≫ p) rfl dB
          g (j ≫ p) (coconePushoutBoundary_eq hp p) dC)) y ⟶
      weightedSections (bousfieldKanWeight (AsSmall.{u + 1} WalkingCospan))
        (partialColimitHomCospan hp p y c hc dB dC) :=
  strictSpanCoconeToPointHomEnd _ y ≫ (partialColimitSpanHomEndIso hp p c hc dB dC y).hom

/-- 元の図式側と同じ左 Hom の end への、native な span 側の比較もホモトピー同値。 -/
lemma partialColimitSpanCoconeToHomEnd_homotopyEquivalence :
    IsSimplicialHomotopyEquivalence (partialColimitSpanCoconeToHomEnd hp p c hc dB dC y) := by
  have : KanComplex (coconeMappingSpace (strictCoherentDiagram
      (partialColimitApexSpan c hc f (i ≫ p) rfl dB
        g (j ≫ p) (coconePushoutBoundary_eq hp p) dC)) y) := coconeMappingSpace_kanComplex _ _
  exact (strictSpanCoconeToPointHomEnd_homotopyEquivalence _ y).comp
    (homotopyEquivalence_of_isIso (partialColimitSpanHomEndIso hp p c hc dB dC y).hom)

end
end SerrePositivity.InfinityCategories.HomotopyLimits
