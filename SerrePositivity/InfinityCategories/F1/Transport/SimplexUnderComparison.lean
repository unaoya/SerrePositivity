module

public import SerrePositivity.InfinityCategories.F1.Transport.SimplexUnderDomains
public import SerrePositivity.InfinityCategories.F1.Diagrams.RelativeSectionDiagramComparison
public import SerrePositivity.InfinityCategories.F1.Diagrams.RelativeSectionInitialRestriction

/-!
概要：単体の切断から under の切断への比較の各成分の同値性。
方針：二つの始対象の点包含での制限と可換な三角形を作り、同値性を反映する。
規約：底の quasicategory 性も制限射自体の単射性も仮定しない。
使われ方：共同切断図式と初頂点写像の strict transport の全高次の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：単体の切断を under の切断へ制限する射は同値。
方針：共通の初頂点からの二つの left anodyne な射と可換な三角形を使う。
規約：元の left fibration の全切断空間上の性質。
使われ方：図式全体の比較の可逆性の成分の判定。 -/
lemma transportSimplexUnderPre_isQCatEquivalence {E B : SSet.{u}}
    (p : E ⟶ B) [LeftFibration p] (s : TransportSimplexCategory B) :
    IsQCatEquivalence (relativeFunctorOverPre p
      ((transportSimplexUnderDomainTransformation B).app (Opposite.op s))) := by
  let c := Over.mk (scaffoldFirstVertex s.objDown.obj.unop.len ≫
    SSet.yonedaEquiv.symm s.objDown.val)
  let r : c ⟶ (transportSimplexUnderDomains B).obj (Opposite.op s) :=
    Over.homMk (nervePoint (Under.mk (𝟙 s))) (by
      change nervePoint (Under.mk (𝟙 s)) ≫
        (nerveMap (Under.forget s) ≫ transportSimplexFirstVertexMap B) =
        scaffoldFirstVertex s.objDown.obj.unop.len ≫ SSet.yonedaEquiv.symm s.objDown.val
      rw [← transportSimplexUnderDomainMap_projection s, ← Category.assoc,
        transportSimplexUnderDomainMap_initialPoint])
  let t : c ⟶ (transportSimplexDomainFunctor B).obj (Opposite.op s) :=
    Over.homMk (scaffoldFirstVertex s.objDown.obj.unop.len) rfl
  apply relativeFunctorOverPre_isQCatEquivalence_of_initialComparison p _ r t
    (nervePoint_leftAnodyne (Under.mkIdInitial (X := s)))
    (scaffoldFirstVertex_leftAnodyne s.objDown.obj.unop.len)
  apply Over.OverMorphism.ext
  exact transportSimplexUnderDomainMap_initialPoint s

/-- 概要：under の切断への制限は各添字で全対象上の指定された関手同型。
方針：同じ豊穣比較の成分の同値性を coherent な同型へ実現する。
規約：対象ごとの逆を独立に選ばない。
使われ方：全図式を同時に動かす比較の各添字での可逆性。 -/
def transportSimplexUnderSectionIso {B : SSet.{u}} (s : TransportSimplexCategory B) :
    FunctorIso
      (coherentNerveMap (relativeFunctorEnrichedEvaluation
        ((transportSimplexDomainFunctor B).obj (Opposite.op s))))
      (coherentNerveMap (relativeFunctorEnrichedEvaluation
        ((transportSimplexUnderDomains B).obj (Opposite.op s)))) :=
  kanEnrichedComparisonIso (relativeFunctorOverPreComparison
    ((transportSimplexUnderDomainTransformation B).app (Opposite.op s)))
    (fun p ↦ transportSimplexUnderPre_isQCatEquivalence p.val.hom s)

/-- 概要：単体の共同切断から under の共同切断への自然な図式の比較。
方針：定義域図式の自然変換を全切断へ反変に適用する。
規約：全添字の自然性を一つの自然変換として保持する。
使われ方：初頂点写像の引き戻しの strict transport との同定。 -/
def transportSimplexUnderSectionComparison {B : SSet.{u}} (p : LeftFibrationObject B) :
    (relativeSectionEnrichedDiagram (transportSimplexDomainFunctor B)).evaluate p ⋙
        kanObjectForget ⟶
      (relativeSectionEnrichedDiagram (transportSimplexUnderDomains B)).evaluate p ⋙
        kanObjectForget :=
  relativeSectionDiagramComparison (transportSimplexUnderDomainTransformation B) p

/-- 概要：under の切断図式への比較は各添字で同値。
方針：切断制限の成分の同値性を回収する。
規約：自然変換そのものの成分について述べる。
使われ方：図式の coherent な比較の可逆性の検証。 -/
lemma transportSimplexUnderSectionComparison_isQCatEquivalence {B : SSet.{u}}
    (p : LeftFibrationObject B) (s : TransportSimplexCategory B) :
    IsQCatEquivalence
      (X := relativeFunctorSpace p.val.hom (SSet.yonedaEquiv.symm s.objDown.val))
      (Y := relativeFunctorSpace p.val.hom
        (nerveMap (Under.forget s) ≫ transportSimplexFirstVertexMap B))
      ((transportSimplexUnderSectionComparison p).app s) :=
  transportSimplexUnderPre_isQCatEquivalence p.val.hom s

end SerrePositivity.InfinityCategories
