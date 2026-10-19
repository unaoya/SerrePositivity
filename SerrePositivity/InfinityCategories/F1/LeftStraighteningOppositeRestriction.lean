module

public import SerrePositivity.InfinityCategories.F1.LeftStraighteningOppositeComparison
public import SerrePositivity.InfinityCategories.F1.TransportSimplexUnderBaseChange

/-!
概要：実際の分類写像の初頂点制限を、全対象の反転係数の transport の共同族へ接続する。
方針：初頂点の底変換の比較、Hom 解像の豊穣関手に関する自然性、係数反転の同型を合成する。
規約：全 left fibrations と全高次パラメーターを同じ始域の一つの関手同型で扱う。
使われ方：相対表現の標準図式と実際の分類写像の作用を照合する主経路。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 初頂点写像での底変換は Hom の共通解像の間でも豊穣関手。 -/
def leftFibrationEdgewiseFirstVertexBaseChange (B : SSet.{u}) :
    SimplicialNerve (EdgewiseEnrichedObject (LeftFibrationObject B)) ⟶
      SimplicialNerve (EdgewiseEnrichedObject
        (LeftFibrationObject (nerve (TransportSimplexCategory B)))) :=
  coherentNerveMap (edgewiseEnrichedFunctor
    (leftFibrationBaseChangeEnriched (transportSimplexFirstVertexMap B)))

/-- 同じ豊穣な底変換は、元の left fibrations への射影と厳密に可換。 -/
lemma leftFibrationEdgewiseFirstVertexBaseChange_projection (B : SSet.{u}) :
    leftFibrationEdgewiseFirstVertexBaseChange B ≫
      edgewiseEnrichedInfinityMap (LeftFibrationObject (nerve (TransportSimplexCategory B))) =
    edgewiseEnrichedInfinityMap (LeftFibrationObject B) ≫
      leftFibrationInfinityBaseChange (transportSimplexFirstVertexMap B) :=
  edgewiseEnrichedFunctor_infinity_right
    (leftFibrationBaseChangeEnriched (transportSimplexFirstVertexMap B))

/-- 共通解像上の底変換は、各対象を通常の引き戻しへ厳密に写す。 -/
lemma leftFibrationEdgewiseFirstVertexBaseChange_vertex (B : SSet.{u})
    (p : LeftFibrationObject B) :
    (leftFibrationEdgewiseFirstVertexBaseChange B).app (Opposite.op ⦋0⦌)
      (coherentNerveVertex (show EdgewiseEnrichedObject (LeftFibrationObject B) from
        ⟨p, trivial⟩)) =
    coherentNerveVertex (show EdgewiseEnrichedObject
      (LeftFibrationObject (nerve (TransportSimplexCategory B))) from
        ⟨leftFibrationBaseChangeObject (transportSimplexFirstVertexMap B) p, trivial⟩) :=
  coherentNerveMap_vertex
    (edgewiseEnrichedFunctor (leftFibrationBaseChangeEnriched (transportSimplexFirstVertexMap B))) _

/-- 実際の分類写像の初頂点制限と、引き戻しの反転 transport の全対象の族の同型。 -/
def leftStraighteningInfinityMap_firstVertexOppositeIso (B : SSet.{u}) :
    FunctorIso
      (edgewiseEnrichedInfinityMap (LeftFibrationObject B) ≫ leftStraighteningInfinityMap B ≫
        (pre ((SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap B))).app
          SpaceInfinity.{u})
      (leftFibrationEdgewiseFirstVertexBaseChange B ≫
        leftStraighteningOppositeCoherentMap (TransportSimplexCategory B)) := by
  have h : edgewiseEnrichedInfinityMap (LeftFibrationObject B) ≫
      (leftFibrationInfinityBaseChange (transportSimplexFirstVertexMap B) ≫
        leftStraighteningCoherentMap (TransportSimplexCategory B)) =
      leftFibrationEdgewiseFirstVertexBaseChange B ≫
        (edgewiseEnrichedInfinityMap
          (LeftFibrationObject (nerve (TransportSimplexCategory B))) ≫
            leftStraighteningCoherentMap (TransportSimplexCategory B)) := by
    rw [← Category.assoc, ← leftFibrationEdgewiseFirstVertexBaseChange_projection, Category.assoc]
  exact (leftStraighteningInfinityMap_firstVertexRestrictionIso B).precomp
      (edgewiseEnrichedInfinityMap (LeftFibrationObject B)) ≪≫
    eqToIso (congrArg (fun f ↦ HomotopyCategory.mk (functorVertex f)) h) ≪≫
    (leftStraighteningCoherentMap_oppositeIso (TransportSimplexCategory B)).precomp
      (leftFibrationEdgewiseFirstVertexBaseChange B)

end SerrePositivity.InfinityCategories
