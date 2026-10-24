module

public import SerrePositivity.InfinityCategories.F2.Ind.FiniteYonedaSliceSections
public import SerrePositivity.InfinityCategories.F2.Ind.IndElementsLeftKanModel

/-!
概要：元の有限全余錐に沿う、実際の Ind Yoneda comma の切断制限自身の同値。
方針：元の前層の Yoneda slice と実際の Ind 内の comma の底上の厳密な同型で移す。
規約：同じ Ind 頂点・全余錐・元の射影を保持。交換は明示入力。
使われ方：全係数の native 余極限判定への最後の底変換入力。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
open HomotopyLimits

/-- 指定 Ind 頂点の実際の Yoneda comma の反転を、同じ元の反転底へ写す。 -/
def oppositeIndLeftKanProjection (κ : Cardinal.{u}) {C : SSet.{u}} [Quasicategory C]
    (w : (IndInfinity κ C) _⦋0⦌) :
    (leftKanShape (indYoneda κ C) w).op ⟶ (SSet.uliftFunctor.{u + 1, u}).obj C.op :=
  SSet.opFunctor.map (leftKanProjection (indYoneda κ C) w) ≫ (uliftOppositeIso C).inv

instance oppositeIndLeftKanProjection_leftFibration (κ : Cardinal.{u})
    {C : SSet.{u}} [Quasicategory C] (w : (IndInfinity κ C) _⦋0⦌) :
    LeftFibration (oppositeIndLeftKanProjection κ w) where
  mem := leftFibrations.comp_mem _ _
    (LeftFibration.mem (p := SSet.opFunctor.map (leftKanProjection (indYoneda κ C) w)))
    (MorphismProperty.of_isIso leftFibrations (uliftOppositeIso C).inv)

/-- 同じ元の comma 同型の逆の反転は、正規化した反転底射影も厳密に保つ。 -/
lemma oppositeIndLeftKanCommaIso_inv_projection (κ : Cardinal.{u})
    {C : SSet.{u}} [Quasicategory C] (w : (IndInfinity κ C) _⦋0⦌) :
    SSet.opFunctor.map (indLeftKanCommaIso κ w).inv ≫ oppositeIndLeftKanProjection κ w =
      oppositeYonedaSliceProjection (indVertexPresheaf κ w) := by
  rw [oppositeIndLeftKanProjection, ← Category.assoc, ← SSet.opFunctor.map_comp,
    indLeftKanCommaIso_inv_projection]
  rfl

/-- 任意の元の Ind 頂点の実際の comma 上で、同じ有限全余錐の反転の切断制限が同値。 -/
lemma ind_finiteColimit_commaSections_isQCatEquivalence
    (κ : Cardinal.{u}) (hκ : Cardinal.aleph0 ≤ κ) (hex : IndFiniteLimitExchangeInput.{u})
    {K C : SSet.{u}} [K.Finite] [Quasicategory C] {D : K ⟶ C}
    (c : JoinCocone D) (hc : IsColimitCone c) (w : (IndInfinity κ C) _⦋0⦌) :
    IsQCatEquivalence (leftFibrationConeRestriction (oppositeIndLeftKanProjection κ w)
      (JoinCone.ulift.{u, u + 1} (SerrePositivity.InfinityCategories.F1B.coconeReverseCone c))) := by
  let e := SSet.opFunctor.mapIso (indLeftKanCommaIso κ w).symm
  exact (leftFibrationConeRestriction_isQCatEquivalence_iff_of_comparison
    (oppositeYonedaSliceProjection (indVertexPresheaf κ w)) (oppositeIndLeftKanProjection κ w)
    e.hom (oppositeIndLeftKanCommaIso_inv_projection κ w) (isPrecompositionEquivalence_of_iso e)
    (JoinCone.ulift.{u, u + 1} (SerrePositivity.InfinityCategories.F1B.coconeReverseCone c))).mp
      (indPresheaf_finiteColimit_yonedaSliceSections_isQCatEquivalence κ hκ hex c hc
        (indVertexPresheaf κ w) (indVertexPresheaf_mem κ w))

end SerrePositivity.InfinityCategories.F2.Ind
