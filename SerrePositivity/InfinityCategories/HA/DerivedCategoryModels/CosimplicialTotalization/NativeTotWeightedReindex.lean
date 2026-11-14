module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeTotWeightedCellFamily
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization.NativeTotWeightedCellIdentification
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictSimplexEvaluationAtParameter

/-!
概要：元のweighted Totセルの全図式射・全高次単体の評価族。
方針：既存StrictSimplexCategoryと全評価を、元の指定セルと厳密写像へ適用。
規約：IS-W2 D01の既存構成の組み立て・表示則。同じ元の全joinセルへ戻す。
使われ方：HA 1.2.4、全錐族の局所セルの貼り合わせ。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
open CategoryTheory SSet MonoidalCategory CartesianMonoidalCategory
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open scoped Simplicial
variable (A : Type u) [CommRing A]

/-- 元のprefixの制限は、同じBK入力を制限したprefixと等しい。 -/
theorem nativeTotWeightedPrefix_reindex (X : CosimplicialObject (Complex A))
    {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (σ : ComposableArrows (AsSmall.{u} SimplexCategory) n) :
    nativeTotWeightedPrefix X ((SimplexCategory.toCat.map α).toFunctor ⋙ σ) =
      simplexPrefixWeightRestriction α ≫
        Functor.whiskerLeft (SimplexCategory.toCat.map α).toFunctor
          (nativeTotWeightedPrefix X σ) := by
  unfold nativeTotWeightedPrefix
  rw [prefixOverWeight_restriction, Category.assoc, Functor.whiskerLeft_comp]
  rfl

/-- 元のweightedセルの全HA単体は、初点を固定する全面・退化と可換。 -/
theorem nativeTotWeightedSimplex_reindex (X : CosimplicialObject (Complex A))
    {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (σ : ComposableArrows (AsSmall.{u} SimplexCategory) n) :
    coherentSimplex (weightedConeSimplex (liftedClosedDiagram X)
      (ForgetEnrichment.of (Complex A) ((productTotalFunctor A).obj X))
      (nativeTotWeightedPrefix X ((SimplexCategory.toCat.map α).toFunctor ⋙ σ))) =
    (coherentSimplex (weightedConeSimplex (liftedClosedDiagram X)
      (ForgetEnrichment.of (Complex A) ((productTotalFunctor A).obj X))
      (nativeTotWeightedPrefix X σ))).pullback (prependOrderHom α.toOrderHom) := by
  rw [nativeTotWeightedPrefix_reindex, ← weightedConeSimplex_reindex]
  exact coherentSimplex_pullback _ _

/-- 同じ全図式射の厳密HA成分も、同じ引き戻しと可換。 -/
theorem nativeTotWeightedSimplexMap_reindex
    {X Y : CosimplicialObject (Complex A)} (f : X ⟶ Y)
    {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (σ : ComposableArrows (AsSmall.{u} SimplexCategory) n) :
    HEq (nativeTotWeightedSimplexMap f ((SimplexCategory.toCat.map α).toFunctor ⋙ σ))
      ((nativeTotWeightedSimplexMap f σ).pullback (prependOrderHom α.toOrderHom)) := by
  apply StrictSimplexMap.hext
    (congrArg Simplex.toSimplexData (nativeTotWeightedSimplex_reindex A X α σ))
    (congrArg Simplex.toSimplexData (nativeTotWeightedSimplex_reindex A Y α σ))
  intro i
  induction i using Fin.cases <;> rfl

/-- セルの通常関手は、元の全HA引き戻し関手と厳密に可換。 -/
theorem nativeTotWeightedCellFunctor_reindex {m n : ℕ} (α : ⦋m⦌ ⟶ ⦋n⦌)
    (σ : ComposableArrows (AsSmall.{u} SimplexCategory) n) :
    nativeTotWeightedCellFunctor A ((SimplexCategory.toCat.map α).toFunctor ⋙ σ) =
      nativeTotWeightedCellFunctor A σ ⋙
        strictSimplexPullbackFunctor A (Complex A) (prependOrderHom α.toOrderHom) := by
  apply CategoryTheory.Functor.hext
  · intro X
    exact congrArg StrictSimplexCategory.mk (nativeTotWeightedSimplex_reindex A X α σ)
  · intro X Y f
    exact nativeTotWeightedSimplexMap_reindex A f α σ

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CosimplicialTotalization
