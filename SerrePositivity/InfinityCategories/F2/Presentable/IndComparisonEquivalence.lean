module

public import SerrePositivity.InfinityCategories.F2.Presentable.SourceColimitMapping
public import SerrePositivity.InfinityCategories.F2.Presentable.IndGeneratorMapping
public import SerrePositivity.InfinityCategories.Core.FullyFaithfulEquivalence

/-!
概要：κ-compact 全部分生成圏を回収する κ-連続な Ind 比較自身は ∞ 圏の同値。
方針：元の始域の単一 filtered 表示と全 Hom の極限表示で全充満忠実性を証明する。
規約：比較自身の同値性を仮定しない。同値データの順射は元の比較を保持する。
使われ方：κ-accessible 圏の Ind 表現。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
variable {κ : Cardinal.{u}} [Fact κ.IsRegular] {A : SSet.{u}} [Quasicategory A]
  {C : SSet.{u + 1}} [Quasicategory C]
  {i : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ C} (hi : IsKappaCompactGenerating κ i)
  {G : Ind.IndInfinity κ A ⟶ C} (hG : IsKappaAccessibleFunctor κ G)
  (e : FunctorIso (Ind.indYoneda κ A ≫ G) i)
include hi hG e

/-- 同じ Ind 比較は、任意の元の二対象間の写像空間で充満忠実。 -/
lemma indComparison_isFullyFaithful : IsFullyFaithful G := by
  intro x y
  obtain ⟨I, hI, hκ, b, c, hv, hc⟩ := indYoneda_generatorPresentation κ A x
  have := hI
  have := hκ
  have h := pinchedHomMap_equivalence_of_source_colimit G y c hc
    (hG I _ c hc) (by
      rintro ⟨j⟩
      change IsSimplicialHomotopyEquivalence (pinchedHomMap G
        ((Ind.indYoneda κ A).app (Opposite.op ⦋0⦌) (ULift.up (b.app (Opposite.op ⦋0⦌) j))) y)
      exact indComparison_yoneda_pinchedHomMap_isEquivalence hi hG e _ y)
  rwa [hv] at h

/-- 小さい compact 生成圏を回収する、元の κ-連続 Ind 比較自身は同値。 -/
lemma indComparison_isQCatEquivalence : IsQCatEquivalence G :=
  isQCatEquivalence_of_isFullyFaithful_of_isEssentiallySurjective G
    (indComparison_isFullyFaithful hi hG e)
    (indComparison_isEssentiallySurjective hi.presentation hG e)

/-- 同じ元の比較関手を順射とする、明示的な Ind 表現同値。 -/
def indComparisonEquivalence : QCatEquivalence (Ind.IndInfinity κ A) C :=
  (indComparison_isQCatEquivalence hi hG e).choose

lemma indComparisonEquivalence_hom : (indComparisonEquivalence hi hG e).hom = G := rfl

end SerrePositivity.InfinityCategories.F2.Presentable
