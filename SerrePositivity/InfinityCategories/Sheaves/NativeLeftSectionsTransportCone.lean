module

public import SerrePositivity.InfinityCategories.Sheaves.NativeLeftSectionsComparisonLaws
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.EquivalentShapeLimitVertexComputations

/-!
概要：元の同じ指定余単位から選んだ輸送錐を、left全空間へ制限した錐の表示。
方針：既存の値比較の中の同じ錐と同じ図式等式を名前で固定する。
規約：HTT 5.1.5.6、Kerodon §9.5（Tag 06NC）の既存構成の計算法則。
使われ方：S8 の固定値比較を指定余単位に沿って照合する。新しい錐を選ばない。
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
namespace SerrePositivity.InfinityCategories.Sheaves
variable {A : SSet.{u}} [Quasicategory A]
  (P : (SSet.uliftFunctor.{u + 1, u}).obj A.op ⟶ SpaceInfinity.{u})
  {E : SSet.{u + 1}} [Quasicategory E]
  (O : ((SSet.uliftFunctor.{u + 1, u}).obj A).op ⟶ E)


/-- 元の指定輸送の錐を、同じleft全空間への既存比較で制限した錐。 -/
def nativeLeftSectionsTransportCone
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E) :
    JoinCone (nativeLeftSectionsDiagram P O) := by
  let c := (nativeWeightedSections_valueTransport O hE
    (SSet.opObjEquiv.symm (functorVertex P))).cone
  have he : leftElementsRightKanComparison P ≫
      SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanDiagram
        (SSet.opFunctor.map (SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.yonedaInfinityMap A)) O
        (SSet.opObjEquiv.symm (functorVertex P)) = nativeLeftSectionsDiagram P O := by
    rw [SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.rightKanDiagram,
      ← Category.assoc, leftElementsRightKanComparison_projection]
    rfl
  exact (restrictJoinCone c (leftElementsRightKanComparison P)).cast he

/-- 制限後の頂点も同じ全切断関手の値である。 -/
lemma nativeLeftSectionsTransportCone_vertex
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E) :
    (nativeLeftSectionsTransportCone P O hE).vertex = nativeLeftSectionsValue P O hE := by
  unfold nativeLeftSectionsTransportCone
  rw [JoinCone.vertex_cast, restrictJoinCone_vertex]
  exact nativeWeightedSections_valueTransport_vertex O hE _

/-- 同じ指定余単位による元の輸送の極限性を、同値なleft全空間へ制限する。 -/
lemma nativeLeftSectionsTransportCone_isLimit
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E) :
    IsLimitCone (nativeLeftSectionsTransportCone P O hE) := by
  let v := SSet.opObjEquiv.symm (functorVertex P)
  letI : LeftFibration (rightKanProjection (SSet.opFunctor.map (yonedaInfinityMap A)) v) :=
    ⟨leftFibrations.pullback_snd _ _ (LeftFibration.mem (p := sliceUnderProjection _))⟩
  letI : Quasicategory (rightKanShape (SSet.opFunctor.map (yonedaInfinityMap A)) v) :=
    quasicategory_of_innerFibration (rightKanProjection _ _)
  unfold nativeLeftSectionsTransportCone
  apply IsLimitCone.cast
  exact (isLimitCone_iff_restrict_equivalentShape (leftElementsRightKanComparison P)
    (leftElementsRightKanComparison_isQCatEquivalence P) _).mp
      (nativeWeightedSections_valueTransport_isLimit O hE v)

/-- 元の値比較は、同じ輸送錐との標準極限比較と同じ頂点移送である。 -/
lemma nativeLeftSectionsValueIso_hom_transportCone
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E)
    (d : JoinCone (nativeLeftSectionsDiagram P O)) (hd : IsLimitCone d)
    (hc : IsLimitCone (nativeLeftSectionsTransportCone P O hE)) :
    (nativeLeftSectionsValueIso P O hE d hd).hom =
      eqToHom (congrArg HomotopyCategory.mk
        (nativeLeftSectionsTransportCone_vertex P O hE).symm) ≫
          (limitVertexIso (nativeLeftSectionsTransportCone P O hE) d hc hd).hom := by
  simp only [nativeLeftSectionsValueIso, nativeWeightedSections_leftLimitIso,
    vertexIso_transport_source_hom, limitVertexIsoOfDiagramEq_hom]
  rfl

end SerrePositivity.InfinityCategories.Sheaves
