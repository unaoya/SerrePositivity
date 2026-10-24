module

public import SerrePositivity.InfinityCategories.F2.Idempotent.UniversePointSlice
public import SerrePositivity.InfinityCategories.HomotopyLimits.UniversePullbacks
public import SerrePositivity.InfinityCategories.F1B.KanExtension.Shapes

/-!
概要：元の左 Kan 添字の持ち上げと、持ち上げた同じ射・点の左 Kan 添字の厳密な同型。
方針：元の slice 射影の宇宙比較と、元の厳密な pullback の極限保存を組み合わせる。
規約：元の二射影を保持し、添字の頂点だけに縮約しない。
使われ方：前層に値を持つ元の左 Kan 延長の局所余極限。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Idempotent

/-- 元の左 Kan 添字の持ち上げと、同じ持ち上げた射・点での元の添字の厳密な同型。 -/
def leftKanShapeUniverseIso {K C : SSet.{u}} (δ : K ⟶ C) (c : C _⦋0⦌) :
    (SSet.uliftFunctor.{v, u}).obj (leftKanShape δ c) ≅
      leftKanShape ((SSet.uliftFunctor.{v, u}).map δ) (ULift.up c) :=
  HomotopyLimits.uliftPullbackIso δ (sliceOverProjection (SSet.yonedaEquiv.symm c)) ≪≫
    asIso (pullback.map _ _ _ _ (𝟙 _) (pointSliceUniverseIso c).hom (𝟙 _)
      (by simp only [Category.comp_id, Category.id_comp])
      ((Category.comp_id _).trans (pointSliceUniverseIso_projection c).symm))

/-- 元の添字の宇宙同型は、元の図式の始域への第一射影を厳密に保つ。 -/
lemma leftKanShapeUniverseIso_projection {K C : SSet.{u}} (δ : K ⟶ C) (c : C _⦋0⦌) :
    (leftKanShapeUniverseIso.{u, v} δ c).hom ≫
      leftKanProjection ((SSet.uliftFunctor.{v, u}).map δ) (ULift.up c) =
    (SSet.uliftFunctor.{v, u}).map (leftKanProjection δ c) := by
  dsimp only [leftKanShapeUniverseIso, Iso.trans_hom, asIso_hom, leftKanProjection]
  rw [Category.assoc, pullback.lift_fst, Category.comp_id,
    HomotopyLimits.uliftPullbackIso_hom_fst]

/-- 元の添字の宇宙同型は、元の全 slice への第二射影も同じ点の同型を介して保つ。 -/
lemma leftKanShapeUniverseIso_slice {K C : SSet.{u}} (δ : K ⟶ C) (c : C _⦋0⦌) :
    (leftKanShapeUniverseIso.{u, v} δ c).hom ≫
      pullback.snd ((SSet.uliftFunctor.{v, u}).map δ)
        (sliceOverProjection (SSet.yonedaEquiv.symm (ULift.up c))) =
    (SSet.uliftFunctor.{v, u}).map
      (pullback.snd δ (sliceOverProjection (SSet.yonedaEquiv.symm c))) ≫
      (pointSliceUniverseIso c).hom := by
  dsimp only [leftKanShapeUniverseIso, Iso.trans_hom, asIso_hom]
  rw [Category.assoc, pullback.lift_snd, ← Category.assoc,
    HomotopyLimits.uliftPullbackIso_hom_snd]

end SerrePositivity.InfinityCategories.F2.Idempotent
