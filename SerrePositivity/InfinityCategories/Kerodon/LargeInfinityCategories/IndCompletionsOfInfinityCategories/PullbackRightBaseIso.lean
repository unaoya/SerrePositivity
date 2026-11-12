module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic

/-!
概要：引き戻しの底のパラメータを同型で表示変更する。
方針：同じ第一射影と底同型の順逆による第二射影で全空間の同型を構成する。
規約：射影の厳密な等式を保持。使われ方：Ind comma の反転と宇宙の正規化。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory Limits
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

/-- 底の同型に沿う引き戻しの表示変更。 -/
def pullbackRightBaseIso {A B E X : SSet.{u}} (p : E ⟶ X) (k : B ⟶ X) (e : A ≅ B) :
    pullback p k ≅ pullback p (e.hom ≫ k) where
  hom := pullback.lift (pullback.fst p k) (pullback.snd p k ≫ e.inv) (by
    rw [Category.assoc, Iso.inv_hom_id_assoc]
    exact pullback.condition)
  inv := pullback.lift (pullback.fst p (e.hom ≫ k)) (pullback.snd p (e.hom ≫ k) ≫ e.hom) (by
    rw [Category.assoc]
    exact pullback.condition)
  hom_inv_id := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, Category.id_comp]
    · simp only [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc,
        Iso.inv_hom_id, Category.comp_id, Category.id_comp]
  inv_hom_id := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, Category.id_comp]
    · simp only [Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc,
        Iso.hom_inv_id, Category.comp_id, Category.id_comp]

/-- 表示変更は元の全空間への第一射影を変えない。 -/
lemma pullbackRightBaseIso_hom_fst {A B E X : SSet.{u}} (p : E ⟶ X) (k : B ⟶ X)
    (e : A ≅ B) : (pullbackRightBaseIso p k e).hom ≫ pullback.fst p (e.hom ≫ k) =
      pullback.fst p k := pullback.lift_fst _ _ _

/-- 表示変更の底への第二射影は、元の第二射影と底同型の逆の合成。 -/
lemma pullbackRightBaseIso_hom_snd {A B E X : SSet.{u}} (p : E ⟶ X) (k : B ⟶ X)
    (e : A ≅ B) : (pullbackRightBaseIso p k e).hom ≫ pullback.snd p (e.hom ≫ k) =
      pullback.snd p k ≫ e.inv := pullback.lift_snd _ _ _

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
