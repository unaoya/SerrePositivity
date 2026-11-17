module
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.Cofinality
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.RelativeFunctorOverEquivalence

/-!
概要：quasicategoryを標的とする前合成同値を、既存のleft cofinalityの定義へ照合する。
方針：既存の相対関手空間の前合成同値を、同じfiberで定義されたcofinalFunctorPreへ適用する。
規約：定義域の充填性は要求しない。元の前合成射を保持する。
使われ方：IS-W2 R03fの元のscaffold正方形と相対延長の比較。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes

/-- 元の相対前合成の同値性を、同じleft cofinal性の検査へ適用する。 -/
theorem isLeftCofinal_of_precompositionEquivalence
    {X Y : SSet.{u}} [Quasicategory Y] (f : X ⟶ Y) (hf : IsPrecompositionEquivalence f) :
    IsLeftCofinal f := by
  intro E p hp
  have h := relativeFunctorPre_isQCatEquivalence_of_precompositionEquivalence p (𝟙 Y) f hf
  change IsQCatEquivalence (cofinalFunctorPre p (𝟙 Y) f) at h
  exact h.isSimplicialHomotopyEquivalence

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality
