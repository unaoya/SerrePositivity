module

public import SerrePositivity.InfinityCategories.Sheaves.NativeWeightedSectionsData
public import SerrePositivity.InfinityCategories.Sheaves.NativeWeightedSectionsValueTransport
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresheafElementsKanProjection
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.EquivalentShapeLimitVertex

/-!
概要：実際の重み付き切断の値を、小さい left 全空間上の指定極限と比較する。
方針：既存の小さい元の圏の比較を二重反転の同型で送り、同じ底係数を保って錐を制限する。
  文献対応：HTT 5.1.5.6、Kerodon §9.5（Tag 06NC）、S8 の集合重みとの比較。
規約：新しい unstraightening を選ばず、既存の同じ射影と指定極限錐を使う。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
namespace SerrePositivity.InfinityCategories.Sheaves
variable {A : SSet.{u}} [Quasicategory A]
  (P : (SSet.uliftFunctor.{u + 1, u}).obj A.op ⟶ SpaceInfinity.{u})

/-- 既存の小さい元の圏の比較を、その left 全空間へ反転して戻す合成。
Kerodon §9.5（Tag 06NC）、既存の同型と比較写像の合成。 -/
def leftElementsRightKanComparison :
    (SSet.uliftFunctor.{u + 1, u}).obj (smallLeftUnstraightening P) ⟶
      rightKanShape (SSet.opFunctor.map (yonedaInfinityMap A))
        (SSet.opObjEquiv.symm (functorVertex P)) :=
  (SSet.uliftFunctor.{u + 1, u}).map (smallRightUnstraighteningOppositeIso P).inv ≫
    (uliftOppositeIso (smallRightUnstraightening P)).hom ≫ presheafElementsRightKanComparison P

/-- 同じ比較の合成は同値。Kerodon §9.5（Tag 06NC）、同型・同値の合成則。 -/
lemma leftElementsRightKanComparison_isQCatEquivalence :
    IsQCatEquivalence (leftElementsRightKanComparison P) :=
  (qCatEquivalenceOfIso ((SSet.uliftFunctor.{u + 1, u}).mapIso
    (smallRightUnstraighteningOppositeIso P).symm)).isQCatEquivalence.comp
      ((qCatEquivalenceOfIso (uliftOppositeIso (smallRightUnstraightening P))).isQCatEquivalence.comp
        (presheafElementsRightKanComparison_isQCatEquivalence P))

/-- 同じ比較は、元の left 射影と反対の底同型を保つ。
Kerodon §9.5（Tag 06NC）、既存の係数移送の合成則。 -/
lemma leftElementsRightKanComparison_projection :
    leftElementsRightKanComparison P ≫
      rightKanProjection (SSet.opFunctor.map (yonedaInfinityMap A))
        (SSet.opObjEquiv.symm (functorVertex P)) =
    (SSet.uliftFunctor.{u + 1, u}).map (smallLeftUnstraighteningProjection P) ≫
      (uliftOppositeIso A).hom := by
  simpa only [leftElementsRightKanComparison, Category.assoc] using
    presheafElementsRightKanComparison_leftProjection P

/-- 実際の全切断関手の値と、小さい left 全空間上の同じ係数の指定極限の頂点比較。
HTT 5.1.5.6、Kerodon §9.5（Tag 06NC）、同値な添字への制限と極限の一意性。 -/
def nativeWeightedSections_leftLimitIso {E : SSet.{u + 1}} [Quasicategory E]
    (O : ((SSet.uliftFunctor.{u + 1, u}).obj A).op ⟶ E)
    (hE : SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E)
    (d : JoinCone ((SSet.uliftFunctor.{u + 1, u}).map (smallLeftUnstraighteningProjection P) ≫
      (uliftOppositeIso A).hom ≫ O)) (hd : IsLimitCone d) :
    VertexIso ((nativeWeightedSections O hE).app _
      (SSet.opObjEquiv.symm (functorVertex P))) d.vertex := by
  let c := (nativeWeightedSections_valueTransport O hE
    (SSet.opObjEquiv.symm (functorVertex P))).cone
  have hc := And.intro (nativeWeightedSections_valueTransport_isLimit O hE
    (SSet.opObjEquiv.symm (functorVertex P)))
    (nativeWeightedSections_valueTransport_vertex O hE
      (SSet.opObjEquiv.symm (functorVertex P)))
  let j := leftElementsRightKanComparison P
  letI : LeftFibration (rightKanProjection (SSet.opFunctor.map (yonedaInfinityMap A))
      (SSet.opObjEquiv.symm (functorVertex P))) :=
    ⟨leftFibrations.pullback_snd _ _ (LeftFibration.mem (p := sliceUnderProjection _))⟩
  letI : Quasicategory (rightKanShape (SSet.opFunctor.map (yonedaInfinityMap A))
      (SSet.opObjEquiv.symm (functorVertex P))) :=
    quasicategory_of_innerFibration (rightKanProjection _ _)
  let t := restrictJoinCone c j
  have ht := (isLimitCone_iff_restrict_equivalentShape j
    (leftElementsRightKanComparison_isQCatEquivalence P) c).mp hc.1
  have he : j ≫ rightKanDiagram (SSet.opFunctor.map (yonedaInfinityMap A)) O
      (SSet.opObjEquiv.symm (functorVertex P)) =
      (SSet.uliftFunctor.{u + 1, u}).map (smallLeftUnstraighteningProjection P) ≫
        (uliftOppositeIso A).hom ≫ O := by
    rw [rightKanDiagram, ← Category.assoc, leftElementsRightKanComparison_projection, Category.assoc]
  have e := limitVertexIsoOfDiagramEq he t d ht hd
  have hv : t.vertex = (nativeWeightedSections O hE).app _
      (SSet.opObjEquiv.symm (functorVertex P)) := (restrictJoinCone_vertex c j).trans hc.2
  exact hv ▸ e

end SerrePositivity.InfinityCategories.Sheaves
