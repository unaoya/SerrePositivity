module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningUnderComparison
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.LeftClassificationBaseChangeHom

/-!
概要：元の分類Homの初頂点制限を、同じ全単体の共同切断作用で読む。
方針：指定された大域制限同型の自然性を、元の全空間射の辺で正規化する。
規約：分類関手・射・制限同型を選び直さない。
使われ方：Kerodon §5.6（Tag 027M）の指定底変換同型の反復合成の照合。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
open Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
open Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open Kerodon.LimitsAndColimits.LimitsAndColimits
open Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories
namespace ClassificationOfCocartesianFibrations

/-- 概要：指定初頂点制限同型の終点を元の共同切断の実現として読む。
方針：既存の指定制限同型と二重転置の厳密な等式を合成する。
規約：任意の単体集合を底に許す。使われ方：元の分類射の制限の自然性。 -/
def leftStraighteningSimplexRestrictionIso (B : SSet.{u}) :
    FunctorIso
      (leftStraighteningInfinityMap B ≫
        (pre ((SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap B))).app
          SpaceInfinity.{u})
      (relativeSectionEnrichedDiagram (transportSimplexDomainFunctor B)).realization :=
  leftStraighteningInfinityMap_restrictIso B ≪≫
    eqToIso (congrArg (fun f ↦ HomotopyCategory.mk (functorVertex f))
      (internalHomFlipHomEquiv_transposeFunctorFamily
        (relativeSectionEnrichedDiagram (transportSimplexDomainFunctor B)).realization))

/-- 概要：制限同型の元の始点は、同じ分類図式の初頂点制限の頂点。
方針：既存の分類の頂点式を前合成へ写す。規約：指定射影を保つ。
使われ方：分類射の制限の正規化。 -/
lemma leftClassificationSimplex_sourceEq {E B : SSet.{u}} (p : E ⟶ B) [LeftFibration p] :
    functorVertex ((SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap B) ≫
      leftStraighteningInfinityDiagram p) =
      (leftStraighteningInfinityMap B ≫
        (pre ((SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap B))).app
          SpaceInfinity.{u}).app (Opposite.op ⦋0⦌) (leftFibrationInfinityVertex p) :=
  leftClassificationBaseChange_sourceEq p (transportSimplexFirstVertexMap B)

/-- 概要：同じ共同切断実現の指定対象での値は、通常のKan値切断図式全体。
方針：共同実現の元の頂点式を使う。規約：各値だけへの弱化はしない。
使われ方：分類Homの制限の終点の正規化。 -/
lemma leftClassificationSimplex_targetEq {E B : SSet.{u}} (p : E ⟶ B) [LeftFibration p] :
    functorVertex (kanDiagramCoherentNerve
      ((relativeSectionEnrichedDiagram (transportSimplexDomainFunctor B)).evaluate
        (leftFibrationObjectOf p))) =
      (relativeSectionEnrichedDiagram (transportSimplexDomainFunctor B)).realization.app
        (Opposite.op ⦋0⦌) (leftFibrationInfinityVertex p) :=
  ((relativeSectionEnrichedDiagram (transportSimplexDomainFunctor B)).realization_vertex
    (leftFibrationObjectOf p)).symm

/-- 概要：指定分類図式の初頂点制限を元の全単体の切断図式へ移す。
方針：同じ大域制限同型の元の対象での成分を正規化する。
規約：同型を選び直さない。使われ方：実全空間射の分類と切断作用の自然性。 -/
def leftClassificationSimplexIso {E B : SSet.{u}} (p : E ⟶ B) [LeftFibration p] :
    FunctorIso
      ((SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap B) ≫
        leftStraighteningInfinityDiagram p)
      (kanDiagramCoherentNerve
        ((relativeSectionEnrichedDiagram (transportSimplexDomainFunctor B)).evaluate
          (leftFibrationObjectOf p))) :=
  normalizedFunctorIsoComponent (leftStraighteningSimplexRestrictionIso B)
    (leftFibrationInfinityVertex p) (leftClassificationSimplex_sourceEq p)
    (leftClassificationSimplex_targetEq p)

/-- 概要：指定大域同型の元の成分は、同じ分類図式の単体制限同型。
方針：元の定義を用いる。規約：同型を変更しない。使われ方：自然性の成分の計算。 -/
lemma leftClassificationSimplex_component {E B : SSet.{u}} (p : E ⟶ B)
    [LeftFibration p] :
    normalizedFunctorIsoComponent (leftStraighteningSimplexRestrictionIso B)
      (leftFibrationInfinityVertex p) (leftClassificationSimplex_sourceEq p)
      (leftClassificationSimplex_targetEq p) = leftClassificationSimplexIso p := rfl

/-- 概要：元の分類Homの初頂点制限は同じ共同切断実現の射作用と可換。
方針：同じ大域制限同型の自然性を、元の全空間射の辺に適用する。
規約：元の射自身と全単体図式を保持する。
使われ方：指定底変換の貼り合わせ比較と元の引き戻し同型の分類を照合する。 -/
lemma leftClassificationHom_simplexRestriction
    {E H B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) (q : H ⟶ B) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ H) (hf : f ≫ q = p) :
    precomposeFunctorHom
        ((SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap B))
        (leftClassificationHom p q f hf) ≫ (leftClassificationSimplexIso q).hom =
      (leftClassificationSimplexIso p).hom ≫
        normalizedVertexHomMap
          (relativeSectionEnrichedDiagram (transportSimplexDomainFunctor B)).realization
          (leftClassificationSimplex_targetEq p) (leftClassificationSimplex_targetEq q)
          (Truncated.HomotopyCategory.homMk (leftFibrationInfinityEdge p q f hf).toTruncated) := by
  let α := Truncated.HomotopyCategory.homMk (leftFibrationInfinityEdge p q f hf).toTruncated
  have h := normalizedVertexHomMap_naturality (leftStraighteningSimplexRestrictionIso B)
    (leftClassificationSimplex_sourceEq p) (leftClassificationSimplex_sourceEq q)
    (leftClassificationSimplex_targetEq p) (leftClassificationSimplex_targetEq q) α
  rw [leftClassificationSimplex_component, leftClassificationSimplex_component] at h
  have hL : normalizedVertexHomMap
      (leftStraighteningInfinityMap B ≫
        (pre ((SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap B))).app
          SpaceInfinity.{u})
      (leftClassificationSimplex_sourceEq p) (leftClassificationSimplex_sourceEq q) α =
      precomposeFunctorHom
        ((SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap B))
        (leftClassificationHom p q f hf) := by
    rw [leftClassificationHom_eq_normalizedMap]
    exact (normalizedVertexHomMap_comp (leftStraighteningInfinityMap B)
      ((pre ((SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap B))).app
        SpaceInfinity.{u}) (leftStraighteningInfinityDiagram_vertex p)
      (leftStraighteningInfinityDiagram_vertex q) rfl rfl α).symm
  rw [hL] at h
  exact h

end ClassificationOfCocartesianFibrations
end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories
