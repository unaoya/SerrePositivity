module

public import SerrePositivity.InfinityCategories.F2.Ind.FullPosetSubsetCoconeLift
public import SerrePositivity.InfinityCategories.F1.Simplicial.FinitePosetLowerSet
public import SerrePositivity.InfinityCategories.F1.Simplicial.PosetSubsetPointRemoval
public import SerrePositivity.InfinityCategories.F1.Simplicial.OrderIsoNerve

/-!
概要：元の順序部分型への形状制限で指定全余錐を厳密に持ち上げる性質を保持する。
方針：元の全図式・試験族・指定余錐を量化する。
規約：同じ元の包含を用い、像の余錐そのものとの等号を要求する。
使われ方：固定下方部分の外の極大点を除く有限半順序帰納。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
/-- 概要：元の固定順序部分への制限が全ての指定余錐を厳密に持ち上げる性質。
方針：元の全族を量化。規約：κ-small な試験族。使われ方：有限帰納の命題。 -/
def HasPosetSubsetCoconeLifts (κ : Cardinal.{u}) (C : SSet.{u}) [Quasicategory C]
    (P : Type u) [PartialOrder P] (U : Set P) : Prop :=
  ∀ (D : (SSet.uliftFunctor.{u + 1, u}).obj (nerve P) ⟶ IndInfinity κ C)
    (A : SSet.{u}), IsKappaSmall κ A →
    ∀ q : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ diagramComma κ D,
    ∀ G : JoinCocone (q ≫ diagramCommaRestriction κ D
      (nerveMap (OrderHom.Subtype.val U).toFunctor)),
    ∃ c : JoinCocone q, mapJoinCocone
      (diagramCommaRestriction κ D (nerveMap (OrderHom.Subtype.val U).toFunctor)) c = G

/-- 概要：全ての点を含む固定部分では、指定全余錐を厳密に持ち上げる。
方針：元の包含の可逆性。規約：元の全族。使われ方：固定部分帰納の基底。 -/
lemma hasPosetSubsetCoconeLifts_of_full (κ : Cardinal.{u}) {C : SSet.{u}} [Quasicategory C]
    {P : Type u} [PartialOrder P] (U : Set P) (hU : ∀ p, p ∈ U) :
    HasPosetSubsetCoconeLifts κ C P U := by
  intro D A hA q G
  exact exists_diagramComma_cocone_lift_full_posetSubset κ U hU D q G

end SerrePositivity.InfinityCategories.F2.Ind
