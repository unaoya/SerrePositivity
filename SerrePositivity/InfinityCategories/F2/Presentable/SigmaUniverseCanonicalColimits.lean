module

public import SerrePositivity.InfinityCategories.F2.Presentable.SigmaUniverseDensity
public import SerrePositivity.InfinityCategories.HomotopyLimits.UniverseCoconeRestriction
public import SerrePositivity.InfinityCategories.HomotopyLimits.UniverseLeftKanCanonical
public import SerrePositivity.InfinityCategories.F2.Presentable.SigmaSiftedContinuousLeftKan
public import SerrePositivity.InfinityCategories.F1.UniverseQCatEquivalence

/-!
概要：元の P_Σ の大きい前層値関手自身は、持ち上げた元の Yoneda の左 Kan 延長。
方針：同じ標準全余錐を小さい密度形状へ制限し、指定宇宙変更の保存性へ戻す。
規約：元の添字・同じ全余錐の射と元の恒等単位を保持する。
使われ方：自然変換空間の全族の実際の右 Kan 条件。
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
variable {C : SSet.{u}} [Quasicategory C]

/-- 元の標準 Kan 余錐の包含像の持ち上げは、同じ前層宇宙変更で余極限となる。 -/
lemma sigmaUniverseCanonical_image_isColimit (v : (SigmaPresheafInfinity C) _⦋0⦌) :
    IsColimitCone (mapJoinCocone (presheafUniverseDiagram C)
      (JoinCocone.ulift.{u + 1, u + 2}
        (leftKanCanonicalCocone (sigmaYonedaInfinityMap C)
          (sigmaPresheafInfinityInclusion C) v))) := by
  let c := leftKanCanonicalCocone (sigmaYonedaInfinityMap C)
    (sigmaPresheafInfinityInclusion C) v
  let e := sigmaElementsLeftKanComparison v
  have he := IsQCatEquivalence.ulift.{u + 1, u + 2}
    (sigmaElementsLeftKanComparison_isQCatEquivalence v)
  apply (isColimitCone_iff_restrict_equivalentShape
    ((SSet.uliftFunctor.{u + 2, u + 1}).map e) he _).mpr
  have hd := sigmaUniverseInclusion_density_isColimit v
  rw [sigmaUniverseInclusion, F2.Compact.mapJoinCocone_universe_comp] at hd
  apply (F2.isColimitCone_iff_of_cocone_val_eq _ _ ?_).mpr hd
  change joinMap ((SSet.uliftFunctor.{u + 2, u + 1}).map e) (𝟙 _) ≫
      ((JoinCocone.ulift.{u + 1, u + 2} c).val ≫ presheafUniverseDiagram C) = _
  rw [← Category.assoc, ← ulift_restrictJoinCocone_val]
  change ((uliftCoconeShapeIso _ 0).inv ≫
      (SSet.uliftFunctor.{u + 2, u + 1}).map (c.restrict e).val) ≫
      presheafUniverseDiagram C = _
  rw [show (c.restrict e).val =
      (mapJoinCocone (sigmaPresheafInfinityInclusion C) (sigmaVertexDensityCocone v)).val from
    sigmaLeftKanCanonicalCocone_restrict_val (sigmaPresheafInfinityInclusion C) v]
  rfl

/-- 元の大きい前層値関手の同じ標準 Kan 全余錐は、実際に余極限。 -/
lemma sigmaUniverseInclusion_canonicalColimits :
    ∀ v : ((SSet.uliftFunctor.{u + 2, u + 1}).obj (SigmaPresheafInfinity C)) _⦋0⦌,
      IsColimitCone (leftKanCanonicalCocone
        ((SSet.uliftFunctor.{u + 2, u + 1}).map (sigmaYonedaInfinityMap C))
        (sigmaUniverseInclusion C) v) := by
  rintro ⟨v⟩
  exact leftKanCanonicalCocone_post_ulift_isColimit (sigmaYonedaInfinityMap C)
    (sigmaPresheafInfinityInclusion C) v (presheafUniverseDiagram C)
    (sigmaUniverseCanonical_image_isColimit v)

/-- 元の大きい前層値関手自身は、持ち上げた元の Yoneda の実際の左 Kan 延長。 -/
lemma sigmaUniverseInclusion_isLeftKanExtension :
    IsLeftKanExtension ((SSet.uliftFunctor.{u + 2, u + 1}).map (sigmaYonedaInfinityMap C))
      ((SSet.uliftFunctor.{u + 2, u + 1}).map (sigmaYonedaInfinityMap C) ≫
        sigmaUniverseInclusion C) (sigmaUniverseInclusion C)
      (functorHomotopyRefl ((SSet.uliftFunctor.{u + 2, u + 1}).map (sigmaYonedaInfinityMap C) ≫
        sigmaUniverseInclusion C)) :=
  F1B.kanLeftKanExtension_refl_of_canonicalColimits _ _ sigmaUniverseInclusion_canonicalColimits

end SerrePositivity.InfinityCategories.HomotopyLimits
