module

public import SerrePositivity.InfinityCategories.F2.Presentable.CompactMappingComparison
public import SerrePositivity.InfinityCategories.F2.Presentable.IndComparisonGenerators
public import SerrePositivity.InfinityCategories.F2.Presentable.IndAccessible
public import SerrePositivity.InfinityCategories.F2.Compact.RepresentableRetractions

/-!
概要：Ind 比較は、元の Yoneda 生成対象から任意の Ind 対象への全写像空間で同値。
方針：元の対象の単一 filtered 表示と、両側の compact 性で全 Hom 比較を拡張する。
規約：元の pinchedHomMap と元の対象を保持。全充満忠実性は別工程。
使われ方：κ-compact 生成から Ind 表現同値への充満忠実性の第一段階。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 元の Yoneda 生成対象から元の任意の Ind 対象への比較射自身は同値。 -/
lemma indComparison_yoneda_pinchedHomMap_isEquivalence {κ : Cardinal.{u}} [Fact κ.IsRegular]
    {A : SSet.{u}} [Quasicategory A] {C : SSet.{u + 1}} [Quasicategory C]
    {i : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ C} (hi : IsKappaCompactGenerating κ i)
    {G : Ind.IndInfinity κ A ⟶ C} (hG : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ G)
    (e : FunctorIso (Ind.indYoneda κ A ≫ G) i) (a : A _⦋0⦌)
    (y : Ind.IndInfinity κ A _⦋0⦌) :
    IsSimplicialHomotopyEquivalence (pinchedHomMap G
      ((Ind.indYoneda κ A).app (Opposite.op ⦋0⦌) (ULift.up a)) y) := by
  obtain ⟨I, hI, hκ, b, c, hv, hc⟩ := indYoneda_generatorPresentation κ A y
  have := hI
  have := hκ
  have hGx := (Compact.isKappaCompact_iff_of_iso (κ := κ) (e.app (ULift.up a))).mpr
    (hi.compact a)
  have h := pinchedHomMap_equivalence_of_compact_colimit G hG
    ((Ind.indYoneda κ A).app (Opposite.op ⦋0⦌) (ULift.up a))
    (Compact.indYoneda_isKappaCompact κ a) hGx
    ((SSet.uliftFunctor.{u + 1, u}).map b ≫ Ind.indYoneda κ A) c hc (by
      intro j
      change IsSimplicialHomotopyEquivalence (pinchedHomMap G _
        ((Ind.indYoneda κ A).app (Opposite.op ⦋0⦌) (ULift.up (b.app (Opposite.op ⦋0⦌) j))))
      exact indComparison_generator_pinchedHomMap_isEquivalence hi.fullyFaithful e a
        (b.app (Opposite.op ⦋0⦌) j))
  rwa [hv] at h

end SerrePositivity.InfinityCategories.F2.Presentable
