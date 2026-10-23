module

public import SerrePositivity.InfinityCategories.F2.Idempotent.UniverseLeftKanShape
public import SerrePositivity.InfinityCategories.HomotopyLimits.UniversePointSliceUncurry
public import SerrePositivity.InfinityCategories.F2.CoconeValEquality
public import SerrePositivity.InfinityCategories.Stable.TrivialFibrationCocone
public import SerrePositivity.InfinityCategories.Stable.UniverseLimits
public import SerrePositivity.InfinityCategories.Stable.ReindexSliceUnder
public import SerrePositivity.InfinityCategories.F1B.KanLeftCanonicalRestrictionHom

/-!
概要：左 Kan 標準全余錐の宇宙変更は、元の局所添字の同型を介して厳密に一致する。
方針：元の slice 射影の一致と、同じ全普遍錐族の展開の宇宙比較を使う。
規約：元の関手と指定点と全余錐写像を保持する。
使われ方：元の Hom 全族の局所極限を、持ち上げた元の左 Kan 条件へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits
open F2.Idempotent

/-- 元の左 Kan 添字の宇宙同型は、同じ標準全余錐の写像そのものを保つ。 -/
lemma leftKanCanonicalCocone_universe_val {K C D : SSet.{u}}
    (δ : K ⟶ C) (F : C ⟶ D) (c : C _⦋0⦌) :
    joinMap (leftKanShapeUniverseIso.{u, v} δ c).hom (𝟙 (Δ[0] : SSet.{max u v})) ≫
        (leftKanCanonicalCocone ((SSet.uliftFunctor.{v, u}).map δ)
          ((SSet.uliftFunctor.{v, u}).map F) (ULift.up c)).val =
      (JoinCocone.ulift.{u, v} (leftKanCanonicalCocone δ F c)).val := by
  change joinMap _ (𝟙 _) ≫ (sliceOverUncurry _ ≫ _) = _
  rw [← Category.assoc, ← sliceOverUncurry_precomp,
    leftKanShapeUniverseIso_slice, pointSliceUniverseIso_uncurry]
  change ((uliftCoconeShapeIso _ 0).inv ≫ (SSet.uliftFunctor.{v, u}).map _) ≫
      (SSet.uliftFunctor.{v, u}).map F =
    (uliftCoconeShapeIso _ 0).inv ≫ (SSet.uliftFunctor.{v, u}).map (_ ≫ F)
  rw [Functor.map_comp, Category.assoc]

/-- 元の左 Kan 標準全余錐の極限性は、同じ元の宇宙持ち上げの標準全余錐と同値。 -/
lemma leftKanCanonicalCocone_isColimit_iff_ulift {K C D : SSet.{u}}
    (δ : K ⟶ C) (F : C ⟶ D) (c : C _⦋0⦌) :
    IsColimitCone (leftKanCanonicalCocone δ F c) ↔
      IsColimitCone (leftKanCanonicalCocone ((SSet.uliftFunctor.{v, u}).map δ)
        ((SSet.uliftFunctor.{v, u}).map F) (ULift.up c)) := by
  let d := leftKanCanonicalCocone ((SSet.uliftFunctor.{v, u}).map δ)
    ((SSet.uliftFunctor.{v, u}).map F) (ULift.up c)
  let e := leftKanShapeUniverseIso.{u, v} δ c
  apply (isColimitCone_iff_ulift (leftKanCanonicalCocone δ F c)).trans
  apply Iff.trans ?_ (isColimitCone_iff_reindexIso d e).symm
  apply F2.isColimitCone_iff_of_cocone_val_eq
  exact (leftKanCanonicalCocone_universe_val δ F c).symm

/-- 元の標準余錐の持ち上げの指定像が極限なら、同じ後合成の標準左 Kan 錐も極限。 -/
lemma leftKanCanonicalCocone_post_ulift_isColimit {K C D : SSet.{u}} {E : SSet.{max u v}}
    (δ : K ⟶ C) (F : C ⟶ D) (c : C _⦋0⦌)
    (q : (SSet.uliftFunctor.{v, u}).obj D ⟶ E)
    (hc : IsColimitCone (mapJoinCocone q
      (JoinCocone.ulift.{u, v} (leftKanCanonicalCocone δ F c)))) :
    IsColimitCone (leftKanCanonicalCocone ((SSet.uliftFunctor.{v, u}).map δ)
      ((SSet.uliftFunctor.{v, u}).map F ≫ q) (ULift.up c)) := by
  let d := leftKanCanonicalCocone ((SSet.uliftFunctor.{v, u}).map δ)
    ((SSet.uliftFunctor.{v, u}).map F ≫ q) (ULift.up c)
  let e := leftKanShapeUniverseIso.{u, v} δ c
  apply (isColimitCone_iff_reindexIso d e).mpr
  apply (F2.isColimitCone_iff_of_cocone_val_eq (d.reindexIso e)
    (mapJoinCocone q (JoinCocone.ulift.{u, v} (leftKanCanonicalCocone δ F c))) ?_).mpr hc
  change joinMap e.hom (𝟙 _) ≫
    ((leftKanCanonicalCocone ((SSet.uliftFunctor.{v, u}).map δ)
      ((SSet.uliftFunctor.{v, u}).map F) (ULift.up c)).val ≫ q) = _
  rw [← Category.assoc, leftKanCanonicalCocone_universe_val]
  rfl

/-- 元の全標準余錐像の極限性は、持ち上げた元の射への実際の左 Kan 条件を与える。 -/
lemma leftKanExtension_refl_post_ulift_of_canonicalColimits
    {K C D : SSet.{u}} {E : SSet.{max u v}}
    (δ : K ⟶ C) (F : C ⟶ D) (q : (SSet.uliftFunctor.{v, u}).obj D ⟶ E)
    (h : ∀ c : C _⦋0⦌, IsColimitCone (mapJoinCocone q
      (JoinCocone.ulift.{u, v} (leftKanCanonicalCocone δ F c)))) :
    IsLeftKanExtension ((SSet.uliftFunctor.{v, u}).map δ)
      ((SSet.uliftFunctor.{v, u}).map δ ≫ ((SSet.uliftFunctor.{v, u}).map F ≫ q))
      ((SSet.uliftFunctor.{v, u}).map F ≫ q)
      (functorHomotopyRefl
        ((SSet.uliftFunctor.{v, u}).map δ ≫ ((SSet.uliftFunctor.{v, u}).map F ≫ q))) := by
  apply F1B.kanLeftKanExtension_refl_of_canonicalColimits
  rintro ⟨c⟩
  exact leftKanCanonicalCocone_post_ulift_isColimit δ F c q (h c)

end SerrePositivity.InfinityCategories.HomotopyLimits
