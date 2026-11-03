module

public import SerrePositivity.InfinityCategories.F2.Ind.YonedaSquarePreservation
public import SerrePositivity.InfinityCategories.F2.Ind.FiniteCospanInclusion
public import SerrePositivity.InfinityCategories.F1.FilteredExchange.ConeSquareUniverseReading
public import SerrePositivity.InfinityCategories.Stable.Bicartesian

/-!
概要：C の同じ cospan 全極限錐族を、Ind の実 bicartesian 四角形族へ移す。
方針：元の全錐の宇宙整合性で各値を回収し、C の安定性をその四角形へ適用する。
規約：全パラメーターと元の C 全錐を固定し、交換入力は明示する。
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

/-- 同じ C の cospan 全錐族を元の Ind Yoneda の全四角形族へ移す。 -/
def indYonedaCospanSquareFamily (κ : Cardinal.{u}) {A C : SSet.{u}} [Quasicategory C]
    (l : A ⟶ (ihom (join (Δ[0] : SSet.{u}) (horn 2 2))).obj C) :
    (SSet.uliftFunctor.{u + 1, u}).obj A ⟶
      (ihom ((Δ[1] : SSet.{u + 1}) ⊗ Δ[1])).obj (IndInfinity κ C) :=
  indYonedaConeFamily κ l ≫
    (pre (uliftCospanSquareReadingIso.{u, u + 1}).inv).app (IndInfinity κ C)

/-- 全四角形族の各値は、元の同じ C 全錐の実四角形の Yoneda 像。 -/
lemma indYonedaCospanSquareFamily_vertex (κ : Cardinal.{u}) {A C : SSet.{u}}
    [Quasicategory C] (l : A ⟶ (ihom (join (Δ[0] : SSet.{u}) (horn 2 2))).obj C)
    (a : A _⦋0⦌) :
    functorVertexSquare ((indYonedaCospanSquareFamily κ l).app
      (Opposite.op ⦋0⦌) (ULift.up a)) =
      uliftSquare.{u, u + 1} (coneSquare (kanConeFamilyAt l a)) ≫ indYoneda κ C := by
  change (functorVertexEquiv _ _).symm
    (((pre (uliftCospanSquareReadingIso.{u, u + 1}).inv).app (IndInfinity κ C)).app _
      ((indYonedaConeFamily κ l).app _ (ULift.up a))) = _
  rw [functorVertexMap_precomp]
  change (uliftCospanSquareReadingIso.{u, u + 1}).inv ≫
    (functorVertexCone ((indYonedaConeFamily κ l).app _ (ULift.up a))).val = _
  rw [indYonedaConeFamily_vertex_val]
  change (uliftCospanSquareReadingIso.{u, u + 1}).inv ≫
    ((JoinCone.ulift.{u, u + 1} (kanConeFamilyAt l a)).val ≫ indYoneda κ C) = _
  rw [← Category.assoc, uliftConeSquareReading]

/-- 同じ各段の実四角形は、包含後の引き戻しであり Ind 内の押し出しでもある。 -/
lemma indYonedaCospanSquareFamily_bicartesian (κ : Cardinal.{u}) [Fact κ.IsRegular]
    (hκ : Cardinal.aleph0 ≤ κ) (hex : IndFiniteLimitExchangeInput.{u})
    {A C : SSet.{u}} [Quasicategory C] [IsStable C] [HasFiniteLimits C]
    (l : A ⟶ (ihom (join (Δ[0] : SSet.{u}) (horn 2 2))).obj C)
    (hl : ∀ a, IsLimitCone (kanConeFamilyAt l a)) (a : A _⦋0⦌) :
    IsPullbackSquare (functorVertexSquare ((indYonedaCospanSquareFamily κ l).app
      (Opposite.op ⦋0⦌) (ULift.up a)) ≫ indInclusionPresheaf κ C) ∧
    IsPushoutSquare (functorVertexSquare ((indYonedaCospanSquareFamily κ l).app
      (Opposite.op ⦋0⦌) (ULift.up a))) := by
  rw [indYonedaCospanSquareFamily_vertex]
  have hp := coneSquare_isPullback (kanConeFamilyAt l a) (hl a)
  exact ⟨ind_inclusion_preservesPullbackSquare κ hκ hex _
    (indYoneda_preservesPullbackSquare κ _ hp),
    indYoneda_preservesPushoutSquare κ hκ hex _ (IsStable.pushout_of_pullback_square _ hp)⟩

end SerrePositivity.InfinityCategories.F2.Ind
