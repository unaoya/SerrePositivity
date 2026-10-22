module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGKanAssemblyCylinderMonomorphisms
public import SerrePositivity.KST.SConstruction.PointedSpanPushoutDesc
public import SerrePositivity.KST.SConstruction.EnrichedWhiskerNaturality

/-! # 同じ円柱押し出し候補の両比較の全 Hom 自然性
概要：元の左右標的から同じ実押し出しへの比較は、全厳密 dg 入力に自然。
方針：標準 end の頂点射影と元の円柱標的包含の全 Hom 自然性を合成する。
規約：同じ実成分と全高次入力を保持。使われ方：関手的 BF 帰納段。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory Limits SSet
open SerrePositivity.InfinityCategories
variable (A : Type u) [CommRing A]

/-- 元の円柱 span の左射影は、同じ実円柱関手の全 Hom 作用。 -/
lemma presentedPerfectDGKanAssemblyCylinderSpan_left (r : ℕ) (X Y : PerfDGInput.{u, v} A) :
    (presentedPerfectDGKanAssemblyCylinderSpanFunctor A r).map X Y ≫
        pointedSpanProjection ((presentedPerfectDGKanAssemblyCylinderSpanFunctor A r).obj X)
          ((presentedPerfectDGKanAssemblyCylinderSpanFunctor A r).obj Y) .left =
      (presentedPerfectDGKanAssemblyLeftCylinderFunctor A r).map X Y :=
  pointedEnrichedSpanHom_projection (presentedPerfectDGKanAssemblySourceFunctor A r)
    (presentedPerfectDGKanAssemblyLeftCylinderFunctor A r)
    (presentedPerfectDGKanAssemblyTargetFunctor A r)
    (presentedPerfectDGKanAssemblyCylinderSourceMap A r)
    (presentedPerfectDGKanAssemblyRightMap A r)
    (presentedPerfectDGKanAssemblyCylinderSource_whisker A r)
    (presentedPerfectDGKanAssemblyRight_whisker A r) X Y .left

/-- 元の円柱 span の右射影は、同じ元の右標的の全 Hom 作用。 -/
lemma presentedPerfectDGKanAssemblyCylinderSpan_right (r : ℕ) (X Y : PerfDGInput.{u, v} A) :
    (presentedPerfectDGKanAssemblyCylinderSpanFunctor A r).map X Y ≫
        pointedSpanProjection ((presentedPerfectDGKanAssemblyCylinderSpanFunctor A r).obj X)
          ((presentedPerfectDGKanAssemblyCylinderSpanFunctor A r).obj Y) .right =
      (presentedPerfectDGKanAssemblyTargetFunctor A r).map X Y :=
  pointedEnrichedSpanHom_projection (presentedPerfectDGKanAssemblySourceFunctor A r)
    (presentedPerfectDGKanAssemblyLeftCylinderFunctor A r)
    (presentedPerfectDGKanAssemblyTargetFunctor A r)
    (presentedPerfectDGKanAssemblyCylinderSourceMap A r)
    (presentedPerfectDGKanAssemblyRightMap A r)
    (presentedPerfectDGKanAssemblyCylinderSource_whisker A r)
    (presentedPerfectDGKanAssemblyRight_whisker A r) X Y .right

/-- 同じ実円柱から押し出しへの左包含は、全 Hom に自然。 -/
lemma presentedPerfectDGKanAssemblyCylinderPushoutInl_whisker (r : ℕ)
    (X Y : PerfDGInput.{u, v} A) :
    (presentedPerfectDGKanAssemblyLeftCylinderFunctor A r).map X Y ≫
        eHomWhiskerLeft SSet ((presentedPerfectDGKanAssemblyLeftCylinderFunctor A r).obj X)
          (pointedSpanPushoutInl ((presentedPerfectDGKanAssemblyCylinderSpanFunctor A r).obj Y)) =
      (presentedPerfectDGKanAssemblyCylinderPushoutFunctor A r).map X Y ≫
        eHomWhiskerRight SSet
          (pointedSpanPushoutInl ((presentedPerfectDGKanAssemblyCylinderSpanFunctor A r).obj X))
          ((presentedPerfectDGKanAssemblyCylinderPushoutFunctor A r).obj Y) := by
  have h := pointedEnrichedSpanPushout_inl
    (presentedPerfectDGKanAssemblyCylinderSpanFunctor A r) X Y
  rw [← Category.assoc, presentedPerfectDGKanAssemblyCylinderSpan_left A r X Y] at h
  exact h.symm

/-- 元の右標的から同じ押し出しへの包含は、全 Hom に自然。 -/
lemma presentedPerfectDGKanAssemblyCylinderPushoutRight_whisker (r : ℕ)
    (X Y : PerfDGInput.{u, v} A) :
    (presentedPerfectDGKanAssemblyTargetFunctor A r).map X Y ≫
        eHomWhiskerLeft SSet ((presentedPerfectDGKanAssemblyTargetFunctor A r).obj X)
          (presentedPerfectDGKanAssemblyCylinderPushoutRightMap A r Y) =
      (presentedPerfectDGKanAssemblyCylinderPushoutFunctor A r).map X Y ≫
        eHomWhiskerRight SSet (presentedPerfectDGKanAssemblyCylinderPushoutRightMap A r X)
          ((presentedPerfectDGKanAssemblyCylinderPushoutFunctor A r).obj Y) := by
  have h := pointedEnrichedSpanPushout_inr
    (presentedPerfectDGKanAssemblyCylinderSpanFunctor A r) X Y
  rw [← Category.assoc, presentedPerfectDGKanAssemblyCylinderSpan_right A r X Y] at h
  exact h.symm

/-- 元の左標的から同じ円柱押し出しへの比較も、全 Hom に自然。 -/
lemma presentedPerfectDGKanAssemblyCylinderPushoutLeft_whisker (r : ℕ)
    (X Y : PerfDGInput.{u, v} A) :
    (presentedPerfectDGKanAssemblyLeftTargetFunctor A r).map X Y ≫
        eHomWhiskerLeft SSet ((presentedPerfectDGKanAssemblyLeftTargetFunctor A r).obj X)
          (presentedPerfectDGKanAssemblyCylinderPushoutLeftMap A r Y) =
      (presentedPerfectDGKanAssemblyCylinderPushoutFunctor A r).map X Y ≫
        eHomWhiskerRight SSet (presentedPerfectDGKanAssemblyCylinderPushoutLeftMap A r X)
          ((presentedPerfectDGKanAssemblyCylinderPushoutFunctor A r).obj Y) :=
  enriched_whisker_naturality_comp SSet
    ((presentedPerfectDGKanAssemblyLeftTargetFunctor A r).map X Y)
    ((presentedPerfectDGKanAssemblyLeftCylinderFunctor A r).map X Y)
    ((presentedPerfectDGKanAssemblyCylinderPushoutFunctor A r).map X Y)
    (presentedPerfectDGKanAssemblyCylinderTargetMap A r X)
    (presentedPerfectDGKanAssemblyCylinderTargetMap A r Y)
    (pointedSpanPushoutInl ((presentedPerfectDGKanAssemblyCylinderSpanFunctor A r).obj X))
    (pointedSpanPushoutInl ((presentedPerfectDGKanAssemblyCylinderSpanFunctor A r).obj Y))
    (presentedPerfectDGKanAssemblyCylinderTarget_whisker A r X Y)
    (presentedPerfectDGKanAssemblyCylinderPushoutInl_whisker A r X Y)

end SerrePositivity.KST.SConstruction
