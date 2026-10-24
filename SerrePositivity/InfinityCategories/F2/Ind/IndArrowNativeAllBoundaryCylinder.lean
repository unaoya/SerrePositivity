module

public import SerrePositivity.InfinityCategories.F2.Ind.IndArrowNativeAllBoundaryInterval
public import SerrePositivity.InfinityCategories.F2.Ind.FixedCoconeBoundaryUnderFamily
public import SerrePositivity.InfinityCategories.Core.EquivalenceCylinderFunctorIso
/-!
概要：元の両全余錐を結ぶ実可逆円柱は、三つの全固定条件を保つ。
方針：可縮持ち上げ空間で選んだ可逆区間族を、そのまま全写像へ展開する。
規約：元の全 C 図式・D・指定始点全余錐を全時刻で固定する。
使われ方：指定始点評価を保った join 円柱への延長と相対反映。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {κ : Cardinal.{u}} {C : SSet.{u}} [Quasicategory C]
  {D : (SSet.uliftFunctor.{u + 1, u}).obj (Δ[1] : SSet.{u}) ⟶ IndInfinity κ C}
  {T : SSet.{u + 1}} {q : T ⟶ diagramComma κ D}
  {H : T ⟶ pullback (indYoneda κ C) (sliceOverProjection D)}
  (W : IndArrowSlicePrism κ D q H)
local notation "p" => SSet.yonedaEquiv.symm (functorVertex (liftedIntervalToSmall ≫ D)) ≫
  arrowDiagramUniverseRestriction (IndInfinity κ C)
local notation "b" => curry (CategoryTheory.Iso.hom (β_ (Δ[1]) T) ≫
  indArrowOriginalFamily κ D q ≫ indYoneda κ C) ≫
    arrowDiagramUniverseRestriction (IndInfinity κ C)
local notation "s" => SSet.ι₀ ≫ indArrowNormalizedPrism κ D q
local notation "e" => evaluateFunctorAt (Y := IndInfinity κ C)
  (ULift.up (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))
local notation "r" => Iso.inv (arrowInterpolationCoconeIso T) ≫
  sliceOverUncurry (arrowInterpolationCornerInclusion T ≫ W.val)
local notation "f" => curry (CategoryTheory.Iso.hom (β_ (Δ[1]) (join T Δ[0])) ≫ r) ≫
  arrowDiagramUniverseRestriction (IndInfinity κ C)
local notation "g" => joinMap q (𝟙 Δ[0]) ≫ Subtype.val (diagramCommaCocone κ D)
/-- 概要：原の再構成余錐と元の余錐を結び、三境界を保つ実可逆円柱。
方針：同じ固定 fiber の族を展開。規約：両端と全固定条件を保持。使われ方：相対反映。 -/
lemma exists_indArrowNativeAllBoundaryCylinder :
    ∃ U : join T (Δ[0] : SSet.{u + 1}) ⊗ equivalenceInterval ⟶
      (ihom ((SSet.uliftFunctor.{u + 1, u}).obj (Δ[1] : SSet.{u}))).obj (IndInfinity κ C),
    equivalenceCylinderEndpoint (join T Δ[0]) false ≫ U = f ∧
    equivalenceCylinderEndpoint (join T Δ[0]) true ≫ U = g ∧
    (joinInl T Δ[0] ▷ equivalenceInterval) ≫ U = fst T equivalenceInterval ≫ b ∧
    (joinInr T Δ[0] ▷ equivalenceInterval) ≫ U = fst Δ[0] equivalenceInterval ≫ p ∧
    U ≫ e = fst (join T Δ[0]) equivalenceInterval ≫ s := by
  obtain ⟨G, h₀, h₁⟩ := exists_indArrowNativeAllBoundaryInterval W
  let U := fixedCoconeBoundaryUnderFamily p b e s G
  refine ⟨U, ?_, ?_, fixedCoconeBoundaryUnderFamily_old p b e s G,
    fixedCoconeBoundaryUnderFamily_tip p b e s G,
    fixedCoconeBoundaryUnderFamily_evaluation p b e s G⟩
  · apply functorVertex_injective
    change functorVertex (equivalenceCylinderEndpoint (join T Δ[0]) false ≫
      uncurry (G ≫ fixedCoconeBoundaryUnderInclusion p b e s)) = _
    rw [functorVertex_equivalenceCylinderEndpoint_uncurry]
    change ((G.app _ _).val.val) = _
    rw [h₀]
    exact indArrowPrismNativeAllBoundaryReconstructedVertex_val W
  · apply functorVertex_injective
    change functorVertex (equivalenceCylinderEndpoint (join T Δ[0]) true ≫
      uncurry (G ≫ fixedCoconeBoundaryUnderInclusion p b e s)) = _
    rw [functorVertex_equivalenceCylinderEndpoint_uncurry]
    change ((G.app _ _).val.val) = _
    rw [h₁]
    exact indArrowPrismNativeAllBoundaryOriginalVertex_val W
end SerrePositivity.InfinityCategories.F2.Ind
