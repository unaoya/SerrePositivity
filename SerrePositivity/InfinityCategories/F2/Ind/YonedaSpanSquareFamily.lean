module

public import SerrePositivity.InfinityCategories.F2.Ind.YonedaSquarePreservation
public import SerrePositivity.InfinityCategories.F2.Ind.YonedaCoconeFamily
public import SerrePositivity.InfinityCategories.F2.Ind.FiniteCospanInclusion
public import SerrePositivity.InfinityCategories.Core.FilteredExchange.SpanSquareUniverseReading
public import SerrePositivity.InfinityCategories.Stable.Bicartesian

/-!
概要：C の同じ span 全余極限余錐族を、Ind の実 bicartesian 四角形族へ移す。
方針：元の全余錐の宇宙整合性で各値を回収し、C の安定性をその四角形へ適用する。
規約：全パラメーターと元の C 全余錐を固定し、交換入力は明示する。
使われ方：I-2 c の単一 filtered 表示の同じ各段の両普遍性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 同じ C の span 全余錐族を元の Ind Yoneda の全四角形族へ移す。 -/
def indYonedaSpanSquareFamily (κ : Cardinal.{u}) {A C : SSet.{u}} [Quasicategory C]
    (l : A ⟶ (ihom (join (horn 2 0) (Δ[0] : SSet.{u}))).obj C) :
    (SSet.uliftFunctor.{u + 1, u}).obj A ⟶
      (ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).obj (IndInfinity κ C) :=
  indYonedaCoconeFamily κ l ≫
    (pre (uliftSpanSquareReadingIso.{u, u + 1}).inv).app (IndInfinity κ C)

/-- 全四角形族の各値は、元の同じ C 全余錐の実四角形の Yoneda 像。 -/
lemma indYonedaSpanSquareFamily_vertex (κ : Cardinal.{u}) {A C : SSet.{u}}
    [Quasicategory C] (l : A ⟶ (ihom (join (horn 2 0) (Δ[0] : SSet.{u}))).obj C)
    (a : A _⦋0⦌) :
    functorVertexSquare ((indYonedaSpanSquareFamily κ l).app
      (Opposite.op ⦋0⦌) (ULift.up a)) =
      uliftSquare.{u, u + 1} (coconeSquare (kanCoconeFamilyAt l a)) ≫ indYoneda κ C := by
  change (functorVertexEquiv _ _).symm
    (((pre (uliftSpanSquareReadingIso.{u, u + 1}).inv).app (IndInfinity κ C)).app _
      ((indYonedaCoconeFamily κ l).app _ (ULift.up a))) = _
  rw [functorVertexMap_precomp]
  change (uliftSpanSquareReadingIso.{u, u + 1}).inv ≫
    (functorVertexCocone ((indYonedaCoconeFamily κ l).app _ (ULift.up a))).val = _
  rw [indYonedaCoconeFamily_vertex_val]
  change (uliftSpanSquareReadingIso.{u, u + 1}).inv ≫
    ((JoinCocone.ulift.{u, u + 1} (kanCoconeFamilyAt l a)).val ≫ indYoneda κ C) = _
  rw [← Category.assoc, uliftCoconeSquareReading]

/-- 同じ各段の実四角形は、包含後の引き戻しであり Ind 内の押し出しでもある。 -/
lemma indYonedaSpanSquareFamily_bicartesian (κ : Cardinal.{u}) [Fact κ.IsRegular]
    (hκ : Cardinal.aleph0 ≤ κ) (hex : IndFiniteLimitExchangeInput.{u})
    {A C : SSet.{u}} [Quasicategory C] [IsStable C] [HasFiniteLimits C]
    (l : A ⟶ (ihom (join (horn 2 0) (Δ[0] : SSet.{u}))).obj C)
    (hl : ∀ a, IsColimitCone (kanCoconeFamilyAt l a)) (a : A _⦋0⦌) :
    IsPullbackSquare (functorVertexSquare ((indYonedaSpanSquareFamily κ l).app
      (Opposite.op ⦋0⦌) (ULift.up a)) ≫ indInclusionPresheaf κ C) ∧
    IsPushoutSquare (functorVertexSquare ((indYonedaSpanSquareFamily κ l).app
      (Opposite.op ⦋0⦌) (ULift.up a))) := by
  rw [indYonedaSpanSquareFamily_vertex]
  have hp := coconeSquare_isPushout (kanCoconeFamilyAt l a) (hl a)
  exact ⟨ind_inclusion_preservesPullbackSquare κ hκ hex _
    (indYoneda_preservesPullbackSquare κ _ (IsStable.pullback_of_pushout_square _ hp)),
    indYoneda_preservesPushoutSquare κ hκ hex _ hp⟩

end SerrePositivity.InfinityCategories.F2.Ind
