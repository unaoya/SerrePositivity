module
public import SerrePositivity.KST.SConstruction.StableOneDirectionReducedAction
public import SerrePositivity.KST.SConstruction.StableOneDirectionActionLaws

/-!
概要：一次方向商の同じ全作用を、標準点つき豊穣関手に束ねる。
方針：元の実現関手の単位・合成を、同じ商の普遍性で反映する。
規約：BF 構成を含まない段関手。使われ方：有限 native 図式の隣接段 span。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory MonoidalClosed SSet InfinityCategories LocalizingInvariants

/-- 概要：商作用の単位は元の豊穣単位。
方針：実現作用の単位を商に降ろす。
規約：全入力の厳密等号。使われ方：点つき関手の単位則。 -/
lemma stableOneDirectionReducedAction_unit (r : ℕ) (C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :
    (𝟙 (oneDirectionReducedRealization r (stableCategoryModel C)).right ⊗ₘ
      eId SSet.{u} C) ≫ stableOneDirectionReducedAction r C C =
        (ρ_ (oneDirectionReducedRealization r (stableCategoryModel C)).right).hom :=
  cofiberFamilyAction_unit _ _ _ (stableOneDirectionReducedAction_collapse r C C)
    (stableOneDirectionAction_unit (r + 1) C)

/-- 概要：商作用は同じ高次入力の合成を保存する。
方針：実現の豊穣合成を同じ商の二脚で反映する。
規約：全パラメータの等式。使われ方：点つき関手の合成則。 -/
lemma stableOneDirectionReducedAction_comp (r : ℕ) (C D E : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) :
    (stableOneDirectionReducedAction r C D ⊗ₘ 𝟙 (D ⟶[SSet.{u}] E)) ≫
        stableOneDirectionReducedAction r D E =
      (α_ (oneDirectionReducedRealization r (stableCategoryModel C)).right
        (C ⟶[SSet.{u}] D) (D ⟶[SSet.{u}] E)).hom ≫
          (𝟙 _ ⊗ₘ eComp SSet.{u} C D E) ≫ stableOneDirectionReducedAction r C E :=
  cofiberFamilyAction_comp
    (oneDirectionFatBoundary (r + 1) (stableCategoryModel C)).ι
    (oneDirectionFatBoundary (r + 1) (stableCategoryModel D)).ι
    (oneDirectionFatBoundary (r + 1) (stableCategoryModel E)).ι
    (stableOneDirectionAction (r + 1) C D) (stableOneDirectionAction (r + 1) D E)
    (stableOneDirectionAction (r + 1) C E) (eComp SSet.{u} C D E)
    (stableOneDirectionReducedAction_collapse r C D)
    (stableOneDirectionReducedAction_collapse r D E)
    (stableOneDirectionReducedAction_collapse r C E)
    (stableOneDirectionAction_comp (r + 1) C D E)

/-- 概要：同じ一次方向商の点つき値。
方針：元の商を標準の点つき対象に保持する。
規約：値の置換なし。使われ方：点つき段関手の対象。 -/
def stableOneDirectionPointedObject (r : ℕ) (C : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u}) : PointedSSetObject.{u} :=
  ⟨oneDirectionReducedRealization r (stableCategoryModel C)⟩

/-- 概要：同じ一次方向商と全自然同値族を保つ点つき段関手。
方針：全基点固定作用と検証した単位・合成を既存の包装へ渡す。
規約：入力 Hom を離散化しない。使われ方：同じ元の S₁ 比較の厳密自然変換。 -/
def stableOneDirectionPointedEnrichedFunctor (r : ℕ) :
    EnrichedFunctor SSet.{u} _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u} PointedSSetObject.{u} :=
  pointedEnrichedFunctorOfAction (stableOneDirectionPointedObject r)
    (stableOneDirectionReducedAction r) (stableOneDirectionReducedAction_unit r)
    (stableOneDirectionReducedAction_comp r) (stableOneDirectionReducedFamilyMap r)
    (stableOneDirectionReducedFamilyMap_inclusion r)

end SerrePositivity.KST.SConstruction
