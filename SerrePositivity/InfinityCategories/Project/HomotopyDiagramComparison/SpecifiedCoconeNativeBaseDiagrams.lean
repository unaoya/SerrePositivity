module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.DiagramBaseFiberPresentation
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCoconeAttachmentRetractions
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCoconeLeftRootEdgeFamily
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SpecifiedCoconeRootEdgeFamily

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
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
noncomputable section
attribute [local irreducible] _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitStrictSpanCocone _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitApexSpan
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRootLeg _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanLeftLeg _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRightLeg
variable {A B C D : SSet.{u + 1}} {f : A ⟶ B} {g : A ⟶ C}
  {i : B ⟶ D} {j : C ⟶ D} (hp : IsPushout f g i j) [Mono g] (p : D ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
  (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (f ≫ (i ≫ p))) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c)
  (dB : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (i ≫ p)) (dC : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (j ≫ p)) (y : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌)
local notation "q" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (f ≫ (i ≫ p))
local notation "T" => _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomLeft
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpecifiedPathCocone hp p c hc dB dC)) y
local notation "root" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeNativeRootEdge hp p c hc dB dC

section
local notation "s" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftRootedTriangle hp p c hc dB dC
local notation "G" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftRootedHomFamily hp p c hc dB dC y
local notation "hG" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftRootedHomFamily_fixed hp p c hc dB dC y
local notation "σ" => SSet.yonedaEquiv.symm (SSet.Edge.CompStruct.simplex
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanLeftTriangle c hc f (i ≫ p) rfl dB
    g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC))
local notation "hs" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftRootedTriangle_projection hp p c hc dB dC
local notation "e" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitAttachmentRestrictionEdge c hc f (i ≫ p) rfl dB
local notation "t" => SSet.yonedaEquiv.symm (SSet.Edge.edge e)
local notation "face" => stdSimplex.δ (2 : Fin 3)
local notation "F" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftAttachmentFaceFamily hp p c hc dB dC y
local notation "hF" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftAttachmentFaceFamily_fixed hp p c hc dB dC y
local notation "first" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftRootedTriangle_first hp p c hc dB dC
local notation "rootEdge" => stdSimplex.δ (1 : Fin 3)
local notation "hroot" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftRootDiagram_rootEdge hp p c hc dB dC

/-- 左の底の全族を、元の同じ native 図式そのものの固定終点 fiber に表示する。 -/
def specifiedCoconeLeftNativeBaseDiagramFamily : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace σ y :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.diagramBaseFiberFamily q s y G hG ≫
    eqToHom (congrArg (fun d ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace d y) hs)
local notation "N" => specifiedCoconeLeftNativeBaseDiagramFamily hp p c hc dB dC y

/-- native 表示の包含後も、元の同じ rooted 全族の底を保持する。 -/
lemma specifiedCoconeLeftNativeBaseDiagramFamily_ι :
    N ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection σ) y =
      (G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp s q) ≫ eqToHom (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder hs) := by
  rw [specifiedCoconeLeftNativeBaseDiagramFamily, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coconeDiagramEqFiber_ι hs y]
  exact (Category.assoc (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.diagramBaseFiberFamily q s y G hG)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (s ≫ q)) y)
    (eqToHom (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder hs))).symm.trans
      (congrArg (· ≫ eqToHom (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder hs))
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.diagramBaseFiberFamily_ι q s y G hG))

/-- native 図式の付加辺は、同じ元の付加辺の底そのものである。 -/
lemma specifiedCoconeLeftNativeBaseDiagram_attachment : face ≫ σ = t ≫ q :=
  (congrArg (face ≫ ·) (hs).symm).trans
    ((Category.assoc face s q).symm.trans (congrArg (· ≫ q) first))

/-- native 図式全体の同じ族を付加辺へ制限すると、元の付加辺面の底を回収する。 -/
lemma specifiedCoconeLeftNativeBaseDiagramFamily_attachment :
    N ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber σ face
        (specifiedCoconeLeftNativeBaseDiagram_attachment hp p c hc dB dC) y =
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.relativeEdgeFamilyBase t q F y hF := by
  exact (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.diagramBaseFiberFamily_restrict_of_eq q s σ hs y G hG face t first
    (specifiedCoconeLeftNativeBaseDiagram_attachment hp p c hc dB dC)).symm

/-- native 図式の根辺も、同じ元の共通脚そのものである。 -/
lemma specifiedCoconeLeftNativeBaseDiagram_root : rootEdge ≫ σ = root :=
  (congrArg (rootEdge ≫ ·) (hs).symm).trans hroot

/-- 付加辺と同じ native 全族の根辺制限は、既存の元の根辺全族に厳密に一致する。 -/
lemma specifiedCoconeLeftNativeBaseDiagramFamily_root :
    N ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber σ rootEdge
        (specifiedCoconeLeftNativeBaseDiagram_root hp p c hc dB dC) y =
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftRootBaseEdgeFiberFamily hp p c hc dB dC y := by
  rw [specifiedCoconeLeftNativeBaseDiagramFamily, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.normalizedCoconeRestrictionFiber_diagramEq hs rootEdge root hroot]
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection root) y
  simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_ι]
  have h := congrArg (· ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestriction (s ≫ q) rootEdge hroot)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.diagramBaseFiberFamily_ι q s y G hG)
  simpa only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftRootBaseEdgeFiberFamily, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι,
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeLeftRootBaseEdgeFamily] using h
end

section
local notation "s" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootedRightTetrahedron hp p c hc dB dC
local notation "G" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootedHomTetrahedronFamily hp p c hc dB dC y
local notation "hG" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootedHomTetrahedronFamily_fixed hp p c hc dB dC y
local notation "σ" => stdSimplex.σ (2 : Fin 3) ≫ SSet.yonedaEquiv.symm (SSet.Edge.CompStruct.simplex
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.partialColimitSpanRightTriangle c hc f (i ≫ p) rfl dB
    g (j ≫ p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC))
local notation "hs" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootedRightTetrahedron_base hp p c hc dB dC
local notation "e" => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitAttachmentRestrictionEdge c hc g (j ≫ p)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePushoutBoundary_eq hp p) dC
local notation "t" => SSet.yonedaEquiv.symm (SSet.Edge.edge e)
local notation "face" => stdSimplex.δ (2 : Fin 3) ≫ stdSimplex.δ (3 : Fin 4)
local notation "F" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightAttachmentFaceFamily hp p c hc dB dC y
local notation "hF" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRightAttachmentFaceFamily_fixed hp p c hc dB dC y
local notation "first" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootedRightTetrahedron_firstEdge hp p c hc dB dC
local notation "rootEdge" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.tetrahedronRootEdge
local notation "hroot" => _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootedTetrahedron_rootEdge hp p c hc dB dC

/-- 右の底の全族を、元の同じ native 図式そのものの固定終点 fiber に表示する。 -/
def specifiedCoconeRightNativeBaseDiagramFamily : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace σ y :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.diagramBaseFiberFamily q s y G hG ≫
    eqToHom (congrArg (fun d ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace d y) hs)
local notation "N" => specifiedCoconeRightNativeBaseDiagramFamily hp p c hc dB dC y

/-- native 表示の包含後も、元の同じ rooted 全族の底を保持する。 -/
lemma specifiedCoconeRightNativeBaseDiagramFamily_ι :
    N ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection σ) y =
      (G ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp s q) ≫ eqToHom (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder hs) := by
  rw [specifiedCoconeRightNativeBaseDiagramFamily, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coconeDiagramEqFiber_ι hs y]
  exact (Category.assoc (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.diagramBaseFiberFamily q s y G hG)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (s ≫ q)) y)
    (eqToHom (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder hs))).symm.trans
      (congrArg (· ≫ eqToHom (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder hs))
        (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.diagramBaseFiberFamily_ι q s y G hG))

/-- native 図式の付加辺は、同じ元の付加辺の底そのものである。 -/
lemma specifiedCoconeRightNativeBaseDiagram_attachment : face ≫ σ = t ≫ q :=
  (congrArg (face ≫ ·) (hs).symm).trans
    ((Category.assoc face s q).symm.trans (congrArg (· ≫ q) first))

/-- native 図式全体の同じ族を付加辺へ制限すると、元の付加辺面の底を回収する。 -/
lemma specifiedCoconeRightNativeBaseDiagramFamily_attachment :
    N ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber σ face
        (specifiedCoconeRightNativeBaseDiagram_attachment hp p c hc dB dC) y =
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.relativeEdgeFamilyBase t q F y hF := by
  exact (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.diagramBaseFiberFamily_restrict_of_eq q s σ hs y G hG face t first
    (specifiedCoconeRightNativeBaseDiagram_attachment hp p c hc dB dC)).symm

/-- native 図式の根辺も、同じ元の共通脚そのものである。 -/
lemma specifiedCoconeRightNativeBaseDiagram_root : rootEdge ≫ σ = root :=
  (congrArg (rootEdge ≫ ·) (hs).symm).trans hroot

/-- 付加辺と同じ native 全族の根辺制限は、既存の元の根辺全族に厳密に一致する。 -/
lemma specifiedCoconeRightNativeBaseDiagramFamily_root :
    N ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber σ rootEdge
        (specifiedCoconeRightNativeBaseDiagram_root hp p c hc dB dC) y =
      _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootBaseEdgeFiberFamily hp p c hc dB dC y := by
  rw [specifiedCoconeRightNativeBaseDiagramFamily, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.normalizedCoconeRestrictionFiber_diagramEq hs rootEdge root hroot]
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection root) y
  simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestrictionFiber, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.vertexFiberMap_ι]
  have h := congrArg (· ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.normalizedCoconeRestriction (s ≫ q) rootEdge hroot)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.diagramBaseFiberFamily_ι q s y G hG)
  simpa only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootBaseEdgeFiberFamily, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι,
    _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.specifiedCoconeRootBaseEdgeFamily] using h
end

end
end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
