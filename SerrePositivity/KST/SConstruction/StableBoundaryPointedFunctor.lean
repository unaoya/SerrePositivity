module
public import SerrePositivity.KST.SConstruction.StableBoundaryReducedLaws
public import SerrePositivity.KST.SConstruction.PointedEnrichedActionFunctor

/-! # 同じ境界商の完全関手族に関する標準点つき豊穣
概要：元の境界商と全自然同値パラメータを、同じ標準 basedHom への関手にする。
方針：全零境界を保つ実作用と同じ商の単位・合成を既存の包装へ渡す。
規約：BF の一般整流は行わない。使われ方：元の評価比較の基点固定ホモトピー。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet
open SerrePositivity.InfinityCategories LocalizingInvariants

/-- 元の同じ点つき境界商を保持する対象。 -/
def stableBoundaryPointedObject (r : ℕ) (C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) : PointedSSetObject.{u} :=
  ⟨boundaryReducedRealization r (stableCategoryModel C)⟩

/-- 元の境界商と全自然同値族を保持する標準点つき厳密豊穣関手。 -/
def stableBoundaryPointedEnrichedFunctor (r : ℕ) :
    EnrichedFunctor SSet.{u} _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u} PointedSSetObject.{u} :=
  pointedEnrichedFunctorOfAction (stableBoundaryPointedObject r)
    (stableBoundaryReducedAction r) (stableBoundaryReducedAction_unit r)
    (stableBoundaryReducedAction_comp r) (stableBoundaryReducedFamilyMap r)
    (stableBoundaryReducedFamilyMap_inclusion r)

/-- 元の完全射では、同じ元の境界商射を全 Hom 作用から回収する。 -/
lemma stableBoundaryPointedEnrichedFunctor_hom (r : ℕ)
    {C D : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}} (F : C ⟶ D) :
    eHomEquiv SSet.{u} F ≫ (stableBoundaryPointedEnrichedFunctor r).map C D =
      eHomEquiv SSet.{u}
        (show (stableBoundaryPointedEnrichedFunctor r).obj C ⟶
          (stableBoundaryPointedEnrichedFunctor r).obj D from
            boundaryReducedRealizationMap r (stableExactInputMap F)) :=
  pointedEnrichedFunctorOfAction_hom _ _ _ _ _ _ F _ (stableBoundaryReducedAction_hom r F)

end SerrePositivity.KST.SConstruction
