module

public import SerrePositivity.InfinityCategories.HomotopyLimits.UniversePointCoslice
public import SerrePositivity.InfinityCategories.HomotopyLimits.UniversePullbacks
public import SerrePositivity.InfinityCategories.F1B.KanExtensionShapes

/-!
概要：元の右 Kan 添字の持ち上げと、持ち上げた同じ射・点の右 Kan 添字の厳密な同型。
方針：元の slice 射影の宇宙比較と、元の厳密な pullback の極限保存を組み合わせる。
規約：元の二射影を保持し、添字の頂点だけに縮約しない。
使われ方：前層に値を持つ元の右 Kan 延長の局所余極限。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HomotopyLimits

/-- 元の右 Kan 添字の持ち上げと、同じ持ち上げた射・点での元の添字の厳密な同型。 -/
def rightKanShapeUniverseIso {K C : SSet.{u}} (δ : K ⟶ C) (c : C _⦋0⦌) :
    (SSet.uliftFunctor.{v, u}).obj (rightKanShape δ c) ≅
      rightKanShape ((SSet.uliftFunctor.{v, u}).map δ) (ULift.up c) :=
  HomotopyLimits.uliftPullbackIso (sliceUnderProjection (SSet.yonedaEquiv.symm c)) δ ≪≫
    asIso (pullback.map _ _ _ _ (pointCosliceUniverseIso c).hom (𝟙 _) (𝟙 _)
      ((Category.comp_id _).trans (pointCosliceUniverseIso_projection c).symm)
      (by simp only [Category.comp_id, Category.id_comp]))

/-- 元の添字の宇宙同型は、元の図式の始域への第二射影を厳密に保つ。 -/
lemma rightKanShapeUniverseIso_projection {K C : SSet.{u}} (δ : K ⟶ C) (c : C _⦋0⦌) :
    (rightKanShapeUniverseIso.{u, v} δ c).hom ≫
      rightKanProjection ((SSet.uliftFunctor.{v, u}).map δ) (ULift.up c) =
    (SSet.uliftFunctor.{v, u}).map (rightKanProjection δ c) := by
  dsimp only [rightKanShapeUniverseIso, Iso.trans_hom, asIso_hom, rightKanProjection]
  rw [Category.assoc, pullback.lift_snd, Category.comp_id,
    HomotopyLimits.uliftPullbackIso_hom_snd]

/-- 元の添字の宇宙同型は、元の全 coslice への第一射影も同じ点の同型を介して保つ。 -/
lemma rightKanShapeUniverseIso_slice {K C : SSet.{u}} (δ : K ⟶ C) (c : C _⦋0⦌) :
    (rightKanShapeUniverseIso.{u, v} δ c).hom ≫
      pullback.fst (sliceUnderProjection (SSet.yonedaEquiv.symm (ULift.up c)))
        ((SSet.uliftFunctor.{v, u}).map δ) =
    (SSet.uliftFunctor.{v, u}).map
      (pullback.fst (sliceUnderProjection (SSet.yonedaEquiv.symm c)) δ) ≫
      (pointCosliceUniverseIso c).hom := by
  dsimp only [rightKanShapeUniverseIso, Iso.trans_hom, asIso_hom]
  rw [Category.assoc, pullback.lift_fst, ← Category.assoc,
    HomotopyLimits.uliftPullbackIso_hom_fst]

end SerrePositivity.InfinityCategories.HomotopyLimits
