module

public import SerrePositivity.InfinityCategories.F2.Presentable.PresheafOppositeRightKanCriterion
public import SerrePositivity.InfinityCategories.HomotopyLimits.UniverseConeRestriction
public import SerrePositivity.InfinityCategories.HomotopyLimits.UniverseRightKanCanonical
public import SerrePositivity.InfinityCategories.F1.Universe.QCatEquivalence

/-!
概要：反対密度錐の像から一段大きい宇宙の全右 Kan 条件を導く。
方針：同じ小さい elements 比較を持ち上げ、標準右 Kan 錐の宇宙比較を使う。
規約：元の前層圏や表現対象を大きい前層圏へ置き換えない。
使われ方：小さい空間値関手と元の大きい表現可能 Hom の全自然比較。
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
variable {A : SSet.{u}} [Quasicategory A] {E : SSet.{u + 2}} [Quasicategory E]
  (q : (SSet.uliftFunctor.{u + 2, u + 1}).obj (PresheafInfinity A).op ⟶ E)

/-- 概要：持ち上げた反対密度錐の像の極限性から標準右 Kan 錐の像の極限性を得る。
方針：持ち上げた元の elements 比較で制限し、全錐の射の一致を使う。
規約：指定した元の前層と元の全密度錐を保持する。
使われ方：元の反対 Yoneda に沿う宇宙を分けた右 Kan 判定。 -/
lemma presheaf_oppositeDensity_image_canonicalLimits
    (P : (SSet.uliftFunctor.{u + 1, u}).obj A.op ⟶ SpaceInfinity.{u})
    (h : IsLimitCone (mapJoinCone q (JoinCone.ulift.{u + 1, u + 2}
      (F1B.coconeReverseCone (presheafDensityCocone P))))) :
    IsLimitCone (mapJoinCone q (JoinCone.ulift.{u + 1, u + 2}
      (rightKanCanonicalCone (SSet.opFunctor.map (yonedaInfinityMap A)) (𝟙 _)
        (SSet.opObjEquiv.symm (functorVertex P))))) := by
  let c := rightKanCanonicalCone (SSet.opFunctor.map (yonedaInfinityMap A))
    (𝟙 _) (SSet.opObjEquiv.symm (functorVertex P))
  let e := presheafElementsRightKanComparison P
  have he := IsQCatEquivalence.ulift.{u + 1, u + 2}
    (presheafElementsRightKanComparison_isQCatEquivalence P)
  apply (isLimitCone_iff_restrict_equivalentShape
    ((SSet.uliftFunctor.{u + 2, u + 1}).map e) he _).mpr
  apply (F2.isLimitCone_iff_of_cone_val_eq _ _ ?_).mpr h
  change joinMap (𝟙 _) ((SSet.uliftFunctor.{u + 2, u + 1}).map e) ≫
    ((JoinCone.ulift.{u + 1, u + 2} c).val ≫ q) = _
  rw [← Category.assoc]
  change (restrictJoinCone (JoinCone.ulift.{u + 1, u + 2} c)
    ((SSet.uliftFunctor.{u + 2, u + 1}).map e)).val ≫ q = _
  have hv := presheafRightKanCanonicalCone_restrict_val (𝟙 (PresheafInfinity A).op) P
  have hv₀ : (restrictJoinCone c e).val =
      (F1B.coconeReverseCone (presheafDensityCocone P)).val :=
    hv.trans (Category.comp_id _)
  exact (congrArg (fun g ↦ g ≫ q)
    (ulift_restrictJoinCone_val.{u + 1, u + 2} c e).symm).trans
      (congrArg (fun g ↦ ((uliftConeShapeIso _ 0).inv ≫
        (SSet.uliftFunctor.{u + 2, u + 1}).map g) ≫ q) hv₀)

/-- 概要：全反対密度錐を保つ元の大きい空間値関手は右 Kan 延長。
方針：元の全標準右 Kan 錐の像の極限性を宇宙比較の判定へ渡す。
規約：元の反対 Yoneda と同じ恒等指定変換を使う。
使われ方：表現可能前層と小さい空間値関手の全自然同型。 -/
lemma presheaf_oppositeDensity_image_isRightKanExtension
    (h : ∀ P : (SSet.uliftFunctor.{u + 1, u}).obj A.op ⟶ SpaceInfinity.{u},
      IsLimitCone (mapJoinCone q (JoinCone.ulift.{u + 1, u + 2}
        (F1B.coconeReverseCone (presheafDensityCocone P))))) :
    IsRightKanExtension
      ((SSet.uliftFunctor.{u + 2, u + 1}).map (SSet.opFunctor.map (yonedaInfinityMap A)))
      ((SSet.uliftFunctor.{u + 2, u + 1}).map (SSet.opFunctor.map (yonedaInfinityMap A)) ≫ q) q
      (functorHomotopyRefl
        ((SSet.uliftFunctor.{u + 2, u + 1}).map
          (SSet.opFunctor.map (yonedaInfinityMap A)) ≫ q)) := by
  apply rightKanExtension_refl_post_ulift_of_canonicalLimits _ (𝟙 _) q
  intro v
  obtain ⟨P, hP⟩ := (presheafInfinityObjectEquiv A).surjective (SSet.opObjEquiv v)
  change functorVertex P = SSet.opObjEquiv v at hP
  have hv : v = SSet.opObjEquiv.symm (functorVertex P) := by rw [hP]; rfl
  rw [hv]
  exact presheaf_oppositeDensity_image_canonicalLimits q P (h P)

end SerrePositivity.InfinityCategories.F2.Presentable
