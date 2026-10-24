module

public import SerrePositivity.InfinityCategories.F2.Presentable.ColimitPreservationRestriction
public import SerrePositivity.InfinityCategories.F2.Presentable.ColimitFromLocalLeftKan

/-!
概要：局所左 Kan 余極限と延長先の余極限の保存から元の図式の保存を得る。
方針：comma の相対 join の両端で全余錐制限同値を使う。
規約：指定全余錐の像の余極限性を保持する。
使われ方：小余積と幾何学的実現による全小余極限保存。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：両標的で fiber が余極限なら右端の保存から左端の保存へ移せる。
方針：左右の制限同値で保存を移し、comma の恒等矢印包含で元へ戻す。
規約：同じ相対 join 図式と元の余錐を使う。
使われ方：一般 bar 展開での余極限保存判定。 -/
lemma colimitPreservation_of_relativeJoin
    {A B X Y : SSet.{u}} [Quasicategory A] [Quasicategory B]
    [Quasicategory X] [Quasicategory Y] (δ : A ⟶ B) (F : A ⟶ X) (U : X ⟶ Y)
    (H : relativeJoin (F1B.kanLeftCommaProjection δ) (𝟙 B) ⟶ X)
    (hH : relativeJoinInl (F1B.kanLeftCommaProjection δ) (𝟙 B) ≫ H =
      F1B.kanLeftCommaSource δ ≫ F)
    (hcol : ∀ b, IsColimitCone
      (F1B.kanRelativeJoinFiberCocone (F1B.kanLeftCommaProjection δ) b H))
    (hcolU : ∀ b, IsColimitCone
      (F1B.kanRelativeJoinFiberCocone (F1B.kanLeftCommaProjection δ) b (H ≫ U)))
    (hB : ∀ (G : B ⟶ X) (c : JoinCocone G),
      IsColimitCone c → IsColimitCone (mapJoinCocone U c))
    (d : JoinCocone F) (hd : IsColimitCone d) : IsColimitCone (mapJoinCocone U d) := by
  let p := F1B.kanLeftCommaProjection δ
  have hwhole : ∀ c : JoinCocone H,
      IsColimitCone c → IsColimitCone (mapJoinCocone U c) := by
    intro c hc
    apply ((relativeJoinRight_sliceUnderRestrict_equivalence p (H ≫ U)).choose.isInitialVertex_iff
      (mapJoinCocone U c)).mpr
    have he := relativeJoinRight_sliceUnderRestrict_equivalence p H
    have hr := (he.choose.isInitialVertex_iff c).mp hc
    exact hB _ (c.restrict (relativeJoinInr p (𝟙 B))) hr
  have hl : ∀ c : JoinCocone (relativeJoinInl p (𝟙 B) ≫ H),
      IsColimitCone c → IsColimitCone (mapJoinCocone U c) :=
    colimitPreservation_of_restrictionEquivalences _ H U
      (Ind.sliceUnderRestrict_isQCatEquivalence_of_initialBoundary H _
        (F1B.kanRelativeJoinFunctor_initialBoundary_of_colimit_fibers p H hcol))
      (Ind.sliceUnderRestrict_isQCatEquivalence_of_initialBoundary (H ≫ U) _
        (F1B.kanRelativeJoinFunctor_initialBoundary_of_colimit_fibers p (H ≫ U) hcolU)) hwhole
  change ∀ c : JoinCocone (relativeJoinInl (F1B.kanLeftCommaProjection δ) (𝟙 B) ≫ H),
    IsColimitCone c → IsColimitCone (mapJoinCocone U c) at hl
  rw [hH] at hl
  have hsource : ∀ c : JoinCocone
      (F1B.kanLeftCommaInclusion δ ≫ (F1B.kanLeftCommaSource δ ≫ F)),
      IsColimitCone c → IsColimitCone (mapJoinCocone U c) :=
    colimitPreservation_of_restrictionEquivalences _ _ U
      (commaSource_sliceUnderRestrict_equivalence δ F)
      (commaSource_sliceUnderRestrict_equivalence δ (F ≫ U)) hl
  have heq : F1B.kanLeftCommaInclusion δ ≫ (F1B.kanLeftCommaSource δ ≫ F) = F := by
    rw [← Category.assoc, F1B.kanLeftCommaInclusion_source, Category.id_comp]
  rw [heq] at hsource
  exact hsource d hd

end SerrePositivity.InfinityCategories.F2.Presentable
