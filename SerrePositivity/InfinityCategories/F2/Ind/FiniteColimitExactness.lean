module

public import SerrePositivity.InfinityCategories.F2.Ind.FiniteConeExactness
public import SerrePositivity.InfinityCategories.F2.Ind.PresheafSubcategory
public import SerrePositivity.InfinityCategories.F1B.Cones.CosliceOpposite
public import SerrePositivity.InfinityCategories.Core.FiniteOppositeSSet

/-!
概要：元の有限余極限全余錐は、Ind の各前層で反転後に極限全錐となる。
方針：同じ余錐の反転と同じ前層の実際の像へ有限交換の結果を適用する。
規約：交換定理は明示入力。有限余極限の Ind 内での存在は別工程。
使われ方：元の表現可能な有限余極限を Ind 内で普遍とするための全 Hom 条件。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 明示交換入力のもとで、Ind 前層は元の小さい圏の同じ有限余極限を反変に極限へ送る。 -/
lemma indPresheaf_finiteColimit_isLimit (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ)
    (hex : IndFiniteLimitExchangeInput.{u}) {K C : SSet.{u}} [K.Finite]
    [Quasicategory C] {D : K ⟶ C} (c : JoinCocone D) (hc : IsColimitCone c)
    (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u})
    (hF : IsIndVertex κ C (functorVertex F)) :
    IsLimitCone (mapJoinCone F (JoinCone.ulift.{u, u + 1} (SerrePositivity.InfinityCategories.F1B.coconeReverseCone c))) :=
  indPresheaf_finiteCone_isLimit κ hκ hex (SerrePositivity.InfinityCategories.F1B.coconeReverseCone c)
    ((SerrePositivity.InfinityCategories.F1B.isColimitCone_iff_reverseCone c).mp hc) F hF

/-- 任意の元の Ind 頂点について、同じ前層による同じ有限全余錐の像の極限性。 -/
lemma indObject_finiteColimit_isLimit (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ)
    (hex : IndFiniteLimitExchangeInput.{u}) {K C : SSet.{u}} [K.Finite]
    [Quasicategory C] {D : K ⟶ C} (c : JoinCocone D) (hc : IsColimitCone c)
    (w : (IndInfinity κ C).obj (Opposite.op (SimplexCategory.mk 0))) :
    IsLimitCone (mapJoinCone ((presheafInfinityObjectEquiv C).symm w.val)
      (JoinCone.ulift.{u, u + 1} (SerrePositivity.InfinityCategories.F1B.coconeReverseCone c))) := by
  apply indPresheaf_finiteColimit_isLimit κ hκ hex c hc
  have hw : functorVertex ((presheafInfinityObjectEquiv C).symm w.val) = w.val :=
    (presheafInfinityObjectEquiv C).apply_symm_apply w.val
  rw [hw]
  exact fullSubcomplexOnVertices_vertex w

end SerrePositivity.InfinityCategories.F2.Ind
