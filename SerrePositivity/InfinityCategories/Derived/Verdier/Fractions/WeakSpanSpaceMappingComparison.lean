module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.KST.Fibration.WeakSpanKanMappingComparison
public import SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.FractionKanDescent
public import SerrePositivity.KST.Fibration.LocalizationFactorizationHom

/-! # 同じ全分数比較を、元の底上の coherent な比較へ実際に降下する -/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
end SerrePositivity.KST.Fibration
namespace SerrePositivity.InfinityCategories.Derived.Verdier.Fractions
open SerrePositivity.KST.Fibration
variable {A B C : StableCategory.{u}} {i : ExactMap A B} {q : ExactMap B C}
  (h : IsVerdierSequence i q) (x : B.obj _⦋0⦌)

/-- 元の同じ実比較を、二つの制限同型で揃えた元の全単体圏上の二胞体。 -/
def weakSpanSpaceMappingComparison_restricted :
    FunctorHom
      ((SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap B.obj) ≫
        weakSpanKanSpaceDiagram i x)
      ((SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap B.obj) ≫
        fractionKanSpaceDiagram q.hom x) :=
  (weakSpanKanSpaceDiagram_restrictionIso i x).hom ≫
    Truncated.HomotopyCategory.homMk (weakSpanKanMappingComparisonEdge h x).toTruncated ≫
      (fractionKanSpaceDiagram_restrictionIso q.hom x).inv

/-- 全関手 ∞ 圏の写像空間の充満忠実性で、同じ指定二胞体を元の底へ持ち上げる。 -/
def weakSpanSpaceMappingComparison :
    FunctorHom (weakSpanKanSpaceDiagram i x) (fractionKanSpaceDiagram q.hom x) :=
  localizationFactorizationHom
    ((SSet.uliftFunctor.{u + 1, u}).map (transportSimplexFirstVertexMap B.obj))
    (transportSimplexInitialEdgesLifted B.obj)
    (transportSimplexFirstVertexMap_ulift_isLocalization B.obj)
    (weakSpanSpaceMappingComparison_restricted h x)

/-- 元の全単体圏へ制限すれば、指定した同じ比較を制限同型込みで厳密に回収する。 -/
theorem weakSpanSpaceMappingComparison_pre :
    (hoFunctor.map ((pre ((SSet.uliftFunctor.{u + 1, u}).map
      (transportSimplexFirstVertexMap B.obj))).app SpaceInfinity)).toFunctor.map
        (weakSpanSpaceMappingComparison h x) = weakSpanSpaceMappingComparison_restricted h x :=
  localizationFactorizationHom_map _ _ _ _

/-- 元の底上の同じ比較は、二つの coherent 図式間の実際のホモトピーで表示できる。 -/
def weakSpanSpaceMappingComparisonHomotopy :
    SSet.Homotopy (weakSpanKanSpaceDiagram i x) (fractionKanSpaceDiagram q.hom x) :=
  functorHomHomotopy (weakSpanSpaceMappingComparison h x)

end SerrePositivity.InfinityCategories.Derived.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanSpaceMappingComparison (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanSpaceMappingComparison := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanSpaceMappingComparison

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanSpaceMappingComparisonHomotopy (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanSpaceMappingComparisonHomotopy := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanSpaceMappingComparisonHomotopy

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanSpaceMappingComparison_pre := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanSpaceMappingComparison_pre

@[deprecated _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanSpaceMappingComparison_restricted (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanSpaceMappingComparison_restricted := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanSpaceMappingComparison_restricted

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanSpaceMappingComparison._proof_1 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanSpaceMappingComparison._proof_1

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.weakSpanSpaceMappingComparison._proof_2 := _root_.SerrePositivity.InfinityCategories.Derived.Verdier.Fractions.weakSpanSpaceMappingComparison._proof_2
