module

public import SerrePositivity.InfinityCategories.F2.Presentable.PresheafElementsLeftKan
public import SerrePositivity.InfinityCategories.F2.Ind.EquivalentCoconeRestriction
public import SerrePositivity.InfinityCategories.F1B.KanExtension.LeftCanonicalRestrictionHom
public import SerrePositivity.InfinityCategories.F2.CatInfinity.CoconeValEquality

/-!
概要：全前層圏の元の密度による恒等単位の左 Kan 判定。
方針：小さい elements 比較で標準余錐を同じ密度余錐へ制限する。
規約：前層圏も標的も追加の宇宙へ持ち上げない。
使われ方：専用反映の単位を密度の普遍性から構成する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits Ind
variable {C : SSet.{u}} [Quasicategory C]

local instance (v : (PresheafInfinity C) _⦋0⦌) :
    RightFibration (leftKanProjection (yonedaInfinityMap C) v) :=
  ⟨rightFibrations.pullback_fst _ _ (RightFibration.mem (p :=
    sliceOverProjection (SSet.yonedaEquiv.symm v)))⟩

local instance (v : (PresheafInfinity C) _⦋0⦌) :
    Quasicategory (leftKanShape (yonedaInfinityMap C) v) :=
  quasicategory_of_innerFibration (leftKanProjection (yonedaInfinityMap C) v)

/-- 概要：恒等関手の元の Yoneda 標準余錐は全て余極限。
方針：同じ全密度余錐の余極限性を elements 比較で戻す。
規約：指定された元の標準余錐そのものを判定する。
使われ方：全前層圏の恒等関手の大域的 Kan 普遍性。 -/
lemma presheafIdentity_canonicalColimits (v : (PresheafInfinity C) _⦋0⦌) :
    IsColimitCone (leftKanCanonicalCocone (yonedaInfinityMap C) (𝟙 _) v) := by
  obtain ⟨F, rfl⟩ := (presheafInfinityObjectEquiv C).surjective v
  let c := leftKanCanonicalCocone (yonedaInfinityMap C) (𝟙 _) (functorVertex F)
  apply (isColimitCone_iff_restrict_equivalentShape
    (presheafElementsLeftKanComparison F) (presheafElementsLeftKanComparison_isQCatEquivalence F)
    c).mpr
  exact (F2.isColimitCone_iff_of_cocone_val_eq (c.restrict _) (presheafDensityCocone F)
    (presheafElementsLeftKanComparison_coconeMap F)).mpr (presheafDensityCocone_isColimit F)

/-- 概要：全前層圏の恒等関手は Yoneda の同じ恒等単位付き左 Kan 延長。
方針：全ての標準余錐の普遍性を元の判定へ渡す。
規約：単位を任意の同型で取り替えない。
使われ方：反映の単位の構成と一意性。 -/
lemma presheafIdentity_isLeftKanExtension :
    IsLeftKanExtension (yonedaInfinityMap C)
      (yonedaInfinityMap C ≫ 𝟙 _) (𝟙 (PresheafInfinity C))
      (functorHomotopyRefl (yonedaInfinityMap C ≫ 𝟙 _)) :=
  F1B.kanLeftKanExtension_refl_of_canonicalColimits _ _ presheafIdentity_canonicalColimits

end SerrePositivity.InfinityCategories.F2.Presentable
