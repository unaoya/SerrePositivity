module

public import SerrePositivity.InfinityCategories.F2.Ind.PreservedColimitAttachment

/-!
概要：両側の保存された部分余極限を付加し、三頂点 span の保存へ帰着する。
方針：二回の部分余極限付加と right anodyne な点 span 制限を両圏で使う。
規約：元の全図式と指定部分余錐、および同じ像の普遍性を保持する。
使われ方：I-2 d′ の全有限形状の交換のための保存性帰納。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 両部分余錐が保存されれば、付加前後で全余極限の保存は同値。 -/
lemma hasPreservedColimit_coneSpan_iff {A B C X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (G : X ⟶ Y)
    (i : A ⟶ B) (j : A ⟶ C) (F : coneSpanShape i j ⟶ X)
    (hB : IsColimitCone (coneSpanLeftCocone i j F))
    (hC : IsColimitCone (coneSpanRightCocone i j F))
    (hGB : IsColimitCone (mapJoinCocone G (coneSpanLeftCocone i j F)))
    (hGC : IsColimitCone (mapJoinCocone G (coneSpanRightCocone i j F))) :
    HasPreservedColimit G F ↔ HasPreservedColimit G (coneSpanBaseMap i j ≫ F) := by
  let l := pushoutLeftExpansion i j (joinInl B Δ[0])
  let r := pushoutRightExpansion (i ≫ joinInl B Δ[0]) j (joinInl C Δ[0])
  have hr := hasPreservedColimit_iff_colimit_attachment G
    (coneSpanRightCocone i j F) hC hGC (pushout.inr (i ≫ joinInl B Δ[0]) j)
    (pushout.inr (i ≫ joinInl B Δ[0]) (j ≫ joinInl C Δ[0])) r
    (pushoutRightExpansion_isPushout (i ≫ joinInl B Δ[0]) j (joinInl C Δ[0])) F rfl
  have he : pushout.inl (i ≫ joinInl B Δ[0]) j ≫ (r ≫ F) =
      (coneSpanLeftCocone i j F).val := by
    simp only [r, pushoutRightExpansion, coneSpanLeftCocone,
      ← Category.assoc, pushout.inl_desc]
  have hl := hasPreservedColimit_iff_colimit_attachment G
    (coneSpanLeftCocone i j F) hB hGB (pushout.inl i j)
    (pushout.inl (i ≫ joinInl B Δ[0]) j) l
    (pushoutLeftExpansion_isPushout i j (joinInl B Δ[0])) (r ≫ F) he
  simpa only [coneSpanBaseMap, l, r, Category.assoc] using hr.trans hl

/-- 元の点 span の保存から、指定部分余錐を持つ元の底の余極限保存を得る。 -/
lemma hasPreservedColimit_coneSpanBase_of_pointSpan {A B C X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (G : X ⟶ Y)
    (a : (Δ[0] : SSet.{u}) ⟶ A) [Mono a] (i : A ⟶ B) (j : A ⟶ C) [Mono j]
    (ha : rightAnodyneExtensions a) (F : coneSpanShape i j ⟶ X)
    (hB : IsColimitCone (coneSpanLeftCocone i j F))
    (hC : IsColimitCone (coneSpanRightCocone i j F))
    (hGB : IsColimitCone (mapJoinCocone G (coneSpanLeftCocone i j F)))
    (hGC : IsColimitCone (mapJoinCocone G (coneSpanRightCocone i j F)))
    (hs : HasPreservedColimit G (coneSpanPointMap a i j ≫ F)) :
    HasPreservedColimit G (coneSpanBaseMap i j ≫ F) := by
  have hr := coneSpanPointMap_rightAnodyne a i j ha
  have : Mono (coneSpanPointMap a i j) := cofinalMono_of_rightAnodyne hr
  have := sliceUnderRestrict_trivialKanFibration F (coneSpanPointMap a i j) hr
  have := sliceUnderRestrict_trivialKanFibration (F ≫ G) (coneSpanPointMap a i j) hr
  apply (hasPreservedColimit_coneSpan_iff G i j F hB hC hGB hGC).mp
  exact (hasPreservedColimit_iff_nativeRestriction F (coneSpanPointMap a i j) G
    (qCatEquivalenceOfTrivialKanFibration
      (sliceUnderRestrict F (coneSpanPointMap a i j))).isQCatEquivalence
    (qCatEquivalenceOfTrivialKanFibration
      (sliceUnderRestrict (F ≫ G) (coneSpanPointMap a i j))).isQCatEquivalence).mpr hs

end SerrePositivity.InfinityCategories.F2.Ind
