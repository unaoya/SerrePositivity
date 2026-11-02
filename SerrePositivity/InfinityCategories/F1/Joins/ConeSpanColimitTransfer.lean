module

public import SerrePositivity.InfinityCategories.F1.Joins.ConeSpanBaseDiagram
public import SerrePositivity.InfinityCategories.Core.ColimitAttachment
public import SerrePositivity.InfinityCategories.F1B.Cofinality.CofinalAnodyneRecognition

/-!
概要：両部分が余極限余錐なら、それらの付加は全体の余極限存在を保ち反映する。
方針：左右の余極限を順に付加し、各 coslice 制限の自明 Kan 性を使う。
規約：元の図式と二つの指定余錐を保ち、有限性を要求しない。
使われ方：形状 pushout に沿う余極限の構成を三頂点 span へ帰着する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 二つの部分余極限の付加は、元の底の余極限存在と同値。 -/
lemma hasColimit_coneSpan_iff {A B C X : SSet.{u}} [Quasicategory X]
    (i : A ⟶ B) (j : A ⟶ C) (F : coneSpanShape i j ⟶ X)
    (hB : IsColimitCone (coneSpanLeftCocone i j F))
    (hC : IsColimitCone (coneSpanRightCocone i j F)) :
    HasColimit F ↔ HasColimit (coneSpanBaseMap i j ≫ F) := by
  let l := pushoutLeftExpansion i j (joinInl B Δ[0])
  let r := pushoutRightExpansion (i ≫ joinInl B Δ[0]) j (joinInl C Δ[0])
  have hr : TrivialKanFibration (sliceUnderRestrict F r) := by
    apply cosliceRestriction_trivialKanFibration_of_colimit_attachment
      (coneSpanRightCocone i j F) hC (pushout.inr (i ≫ joinInl B Δ[0]) j)
      (pushout.inr (i ≫ joinInl B Δ[0]) (j ≫ joinInl C Δ[0])) r
      (pushoutRightExpansion_isPushout (i ≫ joinInl B Δ[0]) j (joinInl C Δ[0])) F
    rfl
  have hl : TrivialKanFibration (sliceUnderRestrict (r ≫ F) l) := by
    apply cosliceRestriction_trivialKanFibration_of_colimit_attachment
      (coneSpanLeftCocone i j F) hB (pushout.inl i j)
      (pushout.inl (i ≫ joinInl B Δ[0]) j) l
      (pushoutLeftExpansion_isPushout i j (joinInl B Δ[0])) (r ≫ F)
    simp only [r, pushoutRightExpansion, coneSpanLeftCocone,
      ← Category.assoc, pushout.inl_desc]
  have h₁ := hasColimit_iff_of_trivialRestriction F r
  have h₂ := hasColimit_iff_of_trivialRestriction (r ≫ F) l
  simpa only [coneSpanBaseMap, l, r, Category.assoc] using h₁.trans h₂

/-- 三頂点 span の余極限が存在すれば、指定の貼り合わせの元の底にも存在する。 -/
lemma hasColimit_coneSpanBase_of_pointSpan {A B C X : SSet.{u}} [Quasicategory X]
    (a : (Δ[0] : SSet.{u}) ⟶ A) [Mono a] (i : A ⟶ B) (j : A ⟶ C) [Mono j]
    (ha : rightAnodyneExtensions a) (F : coneSpanShape i j ⟶ X)
    (hB : IsColimitCone (coneSpanLeftCocone i j F))
    (hC : IsColimitCone (coneSpanRightCocone i j F))
    (hs : HasColimit (coneSpanPointMap a i j ≫ F)) :
    HasColimit (coneSpanBaseMap i j ≫ F) := by
  have hr := coneSpanPointMap_rightAnodyne a i j ha
  have : Mono (coneSpanPointMap a i j) := cofinalMono_of_rightAnodyne hr
  have := sliceUnderRestrict_trivialKanFibration F (coneSpanPointMap a i j) hr
  exact (hasColimit_coneSpan_iff i j F hB hC).mp
    ((hasColimit_iff_of_trivialRestriction F (coneSpanPointMap a i j)).mpr hs)

end SerrePositivity.InfinityCategories
