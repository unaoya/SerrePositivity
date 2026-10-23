module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PointedMorphismPrismEquality
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FiberTransportDiagonalPrismCoordinates

/-!
概要：元の全対角比較の実 prism を固定射へ制限し、元の同じ pointed prism へ戻す。
方針：元の二係数の同時制限を計算し、全 prism の既証の厳密な一致を適用する。
規約：元の全実 prism を保持。使われ方：元の固定射の指定値比較の二 prism 表示。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
open HomotopyLimits
variable {K L : KanObject.{u}} (f : K ⟶ L)
local notation "A" => CategoryTheory.Functor.obj SSet.uliftFunctor
  (CategoryTheory.Functor.obj SSet.opFunctor (SimplicialCategory.sHom pointKanObject K))
local notation "H" => CategoryTheory.Functor.obj SSet.uliftFunctor
  (CategoryTheory.Functor.obj SSet.opFunctor (SimplicialCategory.sHom K L))
local notation "v" => ULift.up (SSet.opObjEquiv.symm (functorVertex f))

/-- 元の全対角比較の実 prism の同じ固定射への制限は、元の同じ全 pointed prism。 -/
lemma pointedReverseDiagonalPrism_fixed_eq_coherent :
    (Δ[1] ◁ lift (𝟙 A) (SSet.const v)) ≫
      ((Δ[1] ◁ lift
        (fst A H ≫ (uliftOppositeIso (SimplicialCategory.sHom pointKanObject K)).hom)
        (snd A H ≫ (uliftOppositeIso (SimplicialCategory.sHom K L)).hom)) ≫
          (pointedReverseKanCompositionTransportFamily K L).prism) =
      pointedCoherentMorphismPrism f := by
  rw [pointedCoherentMorphismPrism_eq_reverse]
  unfold pointedReverseMorphismPrism
  rw [← Category.assoc, ← whiskerLeft_comp, comp_lift]
  simp only [← Category.assoc, lift_fst, lift_snd, Category.id_comp]

end SerrePositivity.InfinityCategories.F2
