module

public import SerrePositivity.InfinityCategories.F2.Presentable.PresheafElementsLeftKan
public import SerrePositivity.InfinityCategories.F2.Ind.EquivalentCoconeRestriction
public import SerrePositivity.InfinityCategories.HomotopyLimits.UniverseCoconeRestriction
public import SerrePositivity.InfinityCategories.HomotopyLimits.UniverseLeftKanCanonical
public import SerrePositivity.InfinityCategories.F1.Universe.QCatEquivalence

/-!
概要：元の全前層密度余錐の像が余極限なら、同じ全関手は元の Yoneda の左 Kan 延長。
方針：小さい元の圏への同値制限と、標準全余錐の厳密な宇宙比較を使う。
規約：指定された関手・元の全密度余錐・同じ恒等単位を保持する。
使われ方：Yoneda Hom 係数関手と指定前層宇宙変更を、同じ左 Kan 延長として比較する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
open F2.Ind
variable {C : SSet.{u}} [Quasicategory C] {E : SSet.{u + 2}} [Quasicategory E]
  (q : (SSet.uliftFunctor.{u + 2, u + 1}).obj (PresheafInfinity C) ⟶ E)

local instance (v : (PresheafInfinity C) _⦋0⦌) :
    RightFibration (leftKanProjection (yonedaInfinityMap C) v) :=
  ⟨rightFibrations.pullback_fst _ _ (RightFibration.mem (p :=
    sliceOverProjection (SSet.yonedaEquiv.symm v)))⟩

local instance (v : (PresheafInfinity C) _⦋0⦌) :
    Quasicategory (leftKanShape (yonedaInfinityMap C) v) :=
  quasicategory_of_innerFibration (leftKanProjection (yonedaInfinityMap C) v)

/-- 概要：元の全密度余錐像の余極限性は、同じ標準 Kan 全余錐像の余極限性を与える。
方針：小さい元の圏への同値制限と、標準全余錐の厳密な宇宙比較を使う。
規約：指定された関手・元の全密度余錐・同じ恒等単位を保持する。
使われ方：Yoneda Hom 係数関手と指定前層宇宙変更を、同じ左 Kan 延長として比較する。 -/
lemma presheafDensity_image_canonicalColimits
    (F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u})
    (h : IsColimitCone (mapJoinCocone q
      (JoinCocone.ulift.{u + 1, u + 2} (presheafDensityCocone F)))) :
    IsColimitCone (mapJoinCocone q (JoinCocone.ulift.{u + 1, u + 2}
      (leftKanCanonicalCocone (yonedaInfinityMap C) (𝟙 _) (functorVertex F)))) := by
  let c := leftKanCanonicalCocone (yonedaInfinityMap C) (𝟙 _) (functorVertex F)
  let e := presheafElementsLeftKanComparison F
  have he := IsQCatEquivalence.ulift.{u + 1, u + 2}
    (presheafElementsLeftKanComparison_isQCatEquivalence F)
  apply (isColimitCone_iff_restrict_equivalentShape
    ((SSet.uliftFunctor.{u + 2, u + 1}).map e) he _).mpr
  apply (F2.isColimitCone_iff_of_cocone_val_eq _ _ ?_).mpr h
  change joinMap ((SSet.uliftFunctor.{u + 2, u + 1}).map e) (𝟙 _) ≫
    ((JoinCocone.ulift.{u + 1, u + 2} c).val ≫ q) = _
  rw [← Category.assoc, ← ulift_restrictJoinCocone_val]
  change ((uliftCoconeShapeIso _ 0).inv ≫
    (SSet.uliftFunctor.{u + 2, u + 1}).map (c.restrict e).val) ≫ q = _
  rw [show (c.restrict e).val = (presheafDensityCocone F).val from
    presheafElementsLeftKanComparison_coconeMap F]
  rfl

/-- 概要：同じ元の全密度余錐を保つ全関手は、持ち上げた元の Yoneda の実際の左 Kan 延長。
方針：小さい元の圏への同値制限と、標準全余錐の厳密な宇宙比較を使う。
規約：指定された関手・元の全密度余錐・同じ恒等単位を保持する。
使われ方：Yoneda Hom 係数関手と指定前層宇宙変更を、同じ左 Kan 延長として比較する。 -/
lemma presheafDensity_image_isLeftKanExtension
    (h : ∀ F : (SSet.uliftFunctor.{u + 1, u}).obj C.op ⟶ SpaceInfinity.{u},
      IsColimitCone (mapJoinCocone q
        (JoinCocone.ulift.{u + 1, u + 2} (presheafDensityCocone F)))) :
    IsLeftKanExtension ((SSet.uliftFunctor.{u + 2, u + 1}).map (yonedaInfinityMap C))
      ((SSet.uliftFunctor.{u + 2, u + 1}).map (yonedaInfinityMap C) ≫ q) q
      (functorHomotopyRefl
        ((SSet.uliftFunctor.{u + 2, u + 1}).map (yonedaInfinityMap C) ≫ q)) := by
  have hcan : ∀ v : (PresheafInfinity C) _⦋0⦌,
      IsColimitCone (mapJoinCocone q (JoinCocone.ulift.{u + 1, u + 2}
        (leftKanCanonicalCocone (yonedaInfinityMap C) (𝟙 _) v))) := by
    intro v
    obtain ⟨F, rfl⟩ := (presheafInfinityObjectEquiv C).surjective v
    exact presheafDensity_image_canonicalColimits q F (h F)
  have hh := leftKanExtension_refl_post_ulift_of_canonicalColimits
    (yonedaInfinityMap C) (𝟙 (PresheafInfinity C)) q hcan
  erw [(SSet.uliftFunctor.{u + 2, u + 1}).map_id] at hh
  erw [Category.id_comp] at hh
  exact hh

end SerrePositivity.InfinityCategories.HomotopyLimits
