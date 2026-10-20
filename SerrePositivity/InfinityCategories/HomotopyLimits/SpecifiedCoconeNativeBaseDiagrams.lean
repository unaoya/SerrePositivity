module

public import SerrePositivity.InfinityCategories.HomotopyLimits.DiagramBaseFiberPresentation
public import SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeAttachmentRetractions
public import SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeLeftRootEdgeFamily
public import SerrePositivity.InfinityCategories.HomotopyLimits.SpecifiedCoconeRootEdgeFamily

/-!
概要：元の付加辺面と根辺の底を、同じ native な三角形・四面体の全族へ束ねる。
方針：元の rooted 全族の底だけを表示変更し、両辺の固定終点族を厳密に回収する。
規約：右は同じ σ2 退化を保持。使われ方：指定した二単体経路と円柱の高次照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
noncomputable section
attribute [local irreducible] partialColimitStrictSpanCocone partialColimitApexSpan
  partialColimitSpanRootLeg partialColimitSpanLeftLeg partialColimitSpanRightLeg
variable {A B C D : SSet.{u + 1}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) [Mono g] (p : D ⟶ SpaceInfinity.{u})
  (c : JoinCocone (f ≫ (i ≫ p))) (hc : IsColimitCone c)
  (dB : JoinCocone (i ≫ p)) (dC : JoinCocone (j ≫ p)) (y : SpaceInfinity.{u} _⦋0⦌)
local notation "q" => sliceUnderProjection (f ≫ (i ≫ p))
local notation "T" => pinchedHomLeft
  (JoinCocone.vertex (partialColimitSpecifiedPathCocone hp p c hc dB dC)) y
local notation "root" => specifiedCoconeNativeRootEdge hp p c hc dB dC

section
local notation "s" => specifiedCoconeLeftRootedTriangle hp p c hc dB dC
local notation "G" => specifiedCoconeLeftRootedHomFamily hp p c hc dB dC y
local notation "hG" => specifiedCoconeLeftRootedHomFamily_fixed hp p c hc dB dC y
local notation "σ" => SSet.yonedaEquiv.symm (SSet.Edge.CompStruct.simplex
  (partialColimitSpanLeftTriangle c hc f (i ≫ p) rfl dB
    g (j ≫ p) (coconePushoutBoundary_eq hp p) dC))
local notation "hs" => specifiedCoconeLeftRootedTriangle_projection hp p c hc dB dC
local notation "e" => colimitAttachmentRestrictionEdge c hc f (i ≫ p) rfl dB
local notation "t" => SSet.yonedaEquiv.symm (SSet.Edge.edge e)
local notation "face" => stdSimplex.δ (2 : Fin 3)
local notation "F" => specifiedCoconeLeftAttachmentFaceFamily hp p c hc dB dC y
local notation "hF" => specifiedCoconeLeftAttachmentFaceFamily_fixed hp p c hc dB dC y
local notation "first" => specifiedCoconeLeftRootedTriangle_first hp p c hc dB dC
local notation "rootEdge" => stdSimplex.δ (1 : Fin 3)
local notation "hroot" => specifiedCoconeLeftRootDiagram_rootEdge hp p c hc dB dC

/-- 左の底の全族を、元の同じ native 図式そのものの固定終点 fiber に表示する。 -/
def specifiedCoconeLeftNativeBaseDiagramFamily : T ⟶ coconeMappingSpace σ y :=
  diagramBaseFiberFamily q s y G hG ≫
    eqToHom (congrArg (fun d ↦ coconeMappingSpace d y) hs)
local notation "N" => specifiedCoconeLeftNativeBaseDiagramFamily hp p c hc dB dC y

/-- native 表示の包含後も、元の同じ rooted 全族の底を保持する。 -/
lemma specifiedCoconeLeftNativeBaseDiagramFamily_ι :
    N ≫ vertexFiberι (sliceUnderProjection σ) y =
      (G ≫ sliceUnderPostcomp s q) ≫ eqToHom (congrArg sliceUnder hs) := by
  rw [specifiedCoconeLeftNativeBaseDiagramFamily, Category.assoc, coconeDiagramEqFiber_ι hs y]
  exact (Category.assoc (diagramBaseFiberFamily q s y G hG)
    (vertexFiberι (sliceUnderProjection (s ≫ q)) y)
    (eqToHom (congrArg sliceUnder hs))).symm.trans
      (congrArg (· ≫ eqToHom (congrArg sliceUnder hs))
        (diagramBaseFiberFamily_ι q s y G hG))

/-- native 図式の付加辺は、同じ元の付加辺の底そのものである。 -/
lemma specifiedCoconeLeftNativeBaseDiagram_attachment : face ≫ σ = t ≫ q :=
  (congrArg (face ≫ ·) (hs).symm).trans
    ((Category.assoc face s q).symm.trans (congrArg (· ≫ q) first))

/-- native 図式全体の同じ族を付加辺へ制限すると、元の付加辺面の底を回収する。 -/
lemma specifiedCoconeLeftNativeBaseDiagramFamily_attachment :
    N ≫ normalizedCoconeRestrictionFiber σ face
        (specifiedCoconeLeftNativeBaseDiagram_attachment hp p c hc dB dC) y =
      relativeEdgeFamilyBase t q F y hF := by
  exact (diagramBaseFiberFamily_restrict_of_eq q s σ hs y G hG face t first
    (specifiedCoconeLeftNativeBaseDiagram_attachment hp p c hc dB dC)).symm

/-- native 図式の根辺も、同じ元の共通脚そのものである。 -/
lemma specifiedCoconeLeftNativeBaseDiagram_root : rootEdge ≫ σ = root :=
  (congrArg (rootEdge ≫ ·) (hs).symm).trans hroot

/-- 付加辺と同じ native 全族の根辺制限は、既存の元の根辺全族に厳密に一致する。 -/
lemma specifiedCoconeLeftNativeBaseDiagramFamily_root :
    N ≫ normalizedCoconeRestrictionFiber σ rootEdge
        (specifiedCoconeLeftNativeBaseDiagram_root hp p c hc dB dC) y =
      specifiedCoconeLeftRootBaseEdgeFiberFamily hp p c hc dB dC y := by
  rw [specifiedCoconeLeftNativeBaseDiagramFamily, Category.assoc,
    normalizedCoconeRestrictionFiber_diagramEq hs rootEdge root hroot]
  apply vertexFiber_hom_ext (sliceUnderProjection root) y
  simp only [Category.assoc, normalizedCoconeRestrictionFiber, vertexFiberMap_ι]
  have h := congrArg (· ≫ normalizedCoconeRestriction (s ≫ q) rootEdge hroot)
    (diagramBaseFiberFamily_ι q s y G hG)
  simpa only [Category.assoc, specifiedCoconeLeftRootBaseEdgeFiberFamily, vertexFiberLift_ι,
    specifiedCoconeLeftRootBaseEdgeFamily] using h
end

section
local notation "s" => specifiedCoconeRootedRightTetrahedron hp p c hc dB dC
local notation "G" => specifiedCoconeRootedHomTetrahedronFamily hp p c hc dB dC y
local notation "hG" => specifiedCoconeRootedHomTetrahedronFamily_fixed hp p c hc dB dC y
local notation "σ" => stdSimplex.σ (2 : Fin 3) ≫ SSet.yonedaEquiv.symm (SSet.Edge.CompStruct.simplex
  (partialColimitSpanRightTriangle c hc f (i ≫ p) rfl dB
    g (j ≫ p) (coconePushoutBoundary_eq hp p) dC))
local notation "hs" => specifiedCoconeRootedRightTetrahedron_base hp p c hc dB dC
local notation "e" => colimitAttachmentRestrictionEdge c hc g (j ≫ p)
    (coconePushoutBoundary_eq hp p) dC
local notation "t" => SSet.yonedaEquiv.symm (SSet.Edge.edge e)
local notation "face" => stdSimplex.δ (2 : Fin 3) ≫ stdSimplex.δ (3 : Fin 4)
local notation "F" => specifiedCoconeRightAttachmentFaceFamily hp p c hc dB dC y
local notation "hF" => specifiedCoconeRightAttachmentFaceFamily_fixed hp p c hc dB dC y
local notation "first" => specifiedCoconeRootedRightTetrahedron_firstEdge hp p c hc dB dC
local notation "rootEdge" => tetrahedronRootEdge
local notation "hroot" => specifiedCoconeRootedTetrahedron_rootEdge hp p c hc dB dC

/-- 右の底の全族を、元の同じ native 図式そのものの固定終点 fiber に表示する。 -/
def specifiedCoconeRightNativeBaseDiagramFamily : T ⟶ coconeMappingSpace σ y :=
  diagramBaseFiberFamily q s y G hG ≫
    eqToHom (congrArg (fun d ↦ coconeMappingSpace d y) hs)
local notation "N" => specifiedCoconeRightNativeBaseDiagramFamily hp p c hc dB dC y

/-- native 表示の包含後も、元の同じ rooted 全族の底を保持する。 -/
lemma specifiedCoconeRightNativeBaseDiagramFamily_ι :
    N ≫ vertexFiberι (sliceUnderProjection σ) y =
      (G ≫ sliceUnderPostcomp s q) ≫ eqToHom (congrArg sliceUnder hs) := by
  rw [specifiedCoconeRightNativeBaseDiagramFamily, Category.assoc, coconeDiagramEqFiber_ι hs y]
  exact (Category.assoc (diagramBaseFiberFamily q s y G hG)
    (vertexFiberι (sliceUnderProjection (s ≫ q)) y)
    (eqToHom (congrArg sliceUnder hs))).symm.trans
      (congrArg (· ≫ eqToHom (congrArg sliceUnder hs))
        (diagramBaseFiberFamily_ι q s y G hG))

/-- native 図式の付加辺は、同じ元の付加辺の底そのものである。 -/
lemma specifiedCoconeRightNativeBaseDiagram_attachment : face ≫ σ = t ≫ q :=
  (congrArg (face ≫ ·) (hs).symm).trans
    ((Category.assoc face s q).symm.trans (congrArg (· ≫ q) first))

/-- native 図式全体の同じ族を付加辺へ制限すると、元の付加辺面の底を回収する。 -/
lemma specifiedCoconeRightNativeBaseDiagramFamily_attachment :
    N ≫ normalizedCoconeRestrictionFiber σ face
        (specifiedCoconeRightNativeBaseDiagram_attachment hp p c hc dB dC) y =
      relativeEdgeFamilyBase t q F y hF := by
  exact (diagramBaseFiberFamily_restrict_of_eq q s σ hs y G hG face t first
    (specifiedCoconeRightNativeBaseDiagram_attachment hp p c hc dB dC)).symm

/-- native 図式の根辺も、同じ元の共通脚そのものである。 -/
lemma specifiedCoconeRightNativeBaseDiagram_root : rootEdge ≫ σ = root :=
  (congrArg (rootEdge ≫ ·) (hs).symm).trans hroot

/-- 付加辺と同じ native 全族の根辺制限は、既存の元の根辺全族に厳密に一致する。 -/
lemma specifiedCoconeRightNativeBaseDiagramFamily_root :
    N ≫ normalizedCoconeRestrictionFiber σ rootEdge
        (specifiedCoconeRightNativeBaseDiagram_root hp p c hc dB dC) y =
      specifiedCoconeRootBaseEdgeFiberFamily hp p c hc dB dC y := by
  rw [specifiedCoconeRightNativeBaseDiagramFamily, Category.assoc,
    normalizedCoconeRestrictionFiber_diagramEq hs rootEdge root hroot]
  apply vertexFiber_hom_ext (sliceUnderProjection root) y
  simp only [Category.assoc, normalizedCoconeRestrictionFiber, vertexFiberMap_ι]
  have h := congrArg (· ≫ normalizedCoconeRestriction (s ≫ q) rootEdge hroot)
    (diagramBaseFiberFamily_ι q s y G hG)
  simpa only [Category.assoc, specifiedCoconeRootBaseEdgeFiberFamily, vertexFiberLift_ι,
    specifiedCoconeRootBaseEdgeFamily] using h
end

end
end SerrePositivity.InfinityCategories.HomotopyLimits
