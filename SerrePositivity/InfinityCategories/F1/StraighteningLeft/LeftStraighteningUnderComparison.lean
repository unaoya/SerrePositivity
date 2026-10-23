module

public import SerrePositivity.InfinityCategories.F1.Transport.SimplexUnderRealization
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.LeftStraighteningAllBases

/-!
概要：一般の底の straightening の初頂点制限を under の切断図式と比較する。
方針：共同降下の同型に、全対象と全高次で構成した切断の比較を合成する。
規約：辺や頂点の一致から全図式の比較を推測しない。
使われ方：通常の圏上の分類と既存の相対表現の比較へ戻る主経路。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories

/-- 二変数の交換で転置した族を戻すと、元の族に厳密に一致する。 -/
lemma internalHomFlipHomEquiv_transposeFunctorFamily {A I X : SSet.{u}}
    (F : A ⟶ (ihom I).obj X) :
    internalHomFlipHomEquiv I A X (transposeFunctorFamily F) = F :=
  (internalHomFlipHomEquiv I A X).apply_symm_apply F

/-- 概要：降下した共同図式の初頂点制限は under の共同切断図式と関手同型。
方針：既存の降下同型と under の共同切断の比較を合成する。
規約：全パラメーターで同じ一つの比較を用いる。
使われ方：引き戻した fibration の strict transport との接続。 -/
def leftStraighteningSectionJointDiagram_underIso (B : SSet.{u}) :
    FunctorIso
      ((SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap B) ≫
        leftStraighteningSectionJointDiagram B)
      (relativeSectionDiagramInfinity (transportSimplexUnderDomains B)) :=
  leftStraighteningSectionJointDiagram_restrictIso B ≪≫ transportSimplexUnderJointIso B

/-- 概要：straightening の初頂点制限は under の切断図式の共同実現と関手同型。
方針：元の制限同型、二変数交換の逆性、全高次の切断比較を合成する。
規約：全 left fibrations と全高次の相対射を同時に比較する。
使われ方：§5.6.5 の相対表現と単位・余単位への接続。 -/
def leftStraighteningInfinityMap_underRealizationIso (B : SSet.{u}) :
    FunctorIso
      (leftStraighteningInfinityMap B ≫
        (pre ((SSet.uliftFunctor.{u + 1, u}).map
          (transportSimplexFirstVertexMap B))).app SpaceInfinity.{u})
      (relativeSectionEnrichedDiagram (transportSimplexUnderDomains B)).realization :=
  leftStraighteningInfinityMap_restrictIso B ≪≫
    eqToIso (congrArg (fun f ↦ SSet.HomotopyCategory.mk (functorVertex f))
      (internalHomFlipHomEquiv_transposeFunctorFamily
        (relativeSectionEnrichedDiagram (transportSimplexDomainFunctor B)).realization)) ≪≫
    transportSimplexUnderRealizationIso B

end SerrePositivity.InfinityCategories
