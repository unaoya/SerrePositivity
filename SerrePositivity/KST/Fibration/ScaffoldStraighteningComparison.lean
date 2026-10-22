module
public import SerrePositivity.KST.Fibration.FirstVertexTransportDiagramComponent
public import SerrePositivity.KST.Fibration.ScaffoldNerveRepresentationPoint
public import SerrePositivity.KST.LocalizingInvariants.LocalizationUniqueness

/-! # 指定 scaffold 三角形を保持した実分類・相対表現比較

初頂点制限を、元の scaffold の埋め込み・二脚・係数点を持つ比較へ送る。
底上の同値だけを選んだ nerve 表現の比較射から、指定点の一致を推論しない。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
variable {E B : SSet.{u}} (p : E ⟶ B) [LeftFibration p]
  (R : LeftTransportRepresentation ((SSet.uliftFunctor.{u + 1, u}).map p))

local instance : LeftFibration (pullback.snd p (transportSimplexFirstVertexMap B)) :=
  ⟨leftFibrations.pullback_snd p _ (LeftFibration.mem (p := p))⟩

/-- 元の初頂点制限と、指定 scaffold 三角形を保持する同じ係数比較を合成する。 -/
def scaffoldStraighteningRestrictionIso :
    FunctorIso
      ((SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap B) ≫
        leftStraighteningInfinityDiagram p)
      ((SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap B) ≫ R.diagram) :=
  leftStraighteningInfinityDiagram_firstVertexIso p ≪≫
    scaffoldNerveRepresentationIso (pullback.snd p (transportSimplexFirstVertexMap B))
      (R.nativeRestrict (transportSimplexFirstVertexMap B))

variable [Quasicategory B]

/-- 指定 scaffold 比較を Sp の全関手圏の前合成充満忠実性で元の底へ戻す。 -/
def scaffoldStraighteningRepresentationIso :
    FunctorIso (leftStraighteningInfinityDiagram p) R.diagram :=
  (localizationPre_fullyFaithful (Y := SpaceInfinity.{u}) _ _
    (transportSimplexFirstVertexMap_ulift_isLocalization.{u, u + 1} B)).preimageVertexIso
      (scaffoldStraighteningRestrictionIso p R)

/-- 同じ降下比較の制限は、指定した元の scaffold 比較そのもの。 -/
theorem scaffoldStraighteningRepresentationIso_pre :
    (hoFunctor.map ((pre ((SSet.uliftFunctor.{u + 1, u}).map
      (transportSimplexFirstVertexMap B))).app SpaceInfinity.{u})).toFunctor.map
        (scaffoldStraighteningRepresentationIso p R).hom =
      (scaffoldStraighteningRestrictionIso p R).hom := by
  exact (localizationPre_fullyFaithful (Y := SpaceInfinity.{u}) _ _
    (transportSimplexFirstVertexMap_ulift_isLocalization.{u, u + 1} B)
    ).toHoFullyFaithful.map_preimage _

end SerrePositivity.KST.Fibration
