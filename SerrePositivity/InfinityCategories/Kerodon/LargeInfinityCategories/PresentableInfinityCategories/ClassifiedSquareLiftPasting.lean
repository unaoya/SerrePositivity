module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ClassifiedSquareHomNaturality

/-!
概要：二つの実正方形の持ち上げの合成を、同じ標準反復引き戻し比較で表す。
方針：標準比較の両射影と元の持ち上げの射影を使う。
規約：充填性や同値性の仮定を追加しない。
使われ方：Kerodon §5.6（Tag 027M）の実正方形の分類の合成則。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open SerrePositivity.InfinityCategories
open Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories
namespace PresentableInfinityCategories

/-- 概要：元の二つの実正方形の持ち上げの合成は、合成正方形の持ち上げと標準比較の逆。
方針：標準比較で後合成して、同じ二射影で検出する。
規約：元の持ち上げを保つ。使われ方：分類前の同じ合成射の照合。 -/
lemma squareLift_pasting {A B C E H J : SSet.{u}}
    (p : E ⟶ A) (q : H ⟶ B) (r : J ⟶ C)
    (k : A ⟶ B) (l : B ⟶ C)
    (f : E ⟶ H) (hf : f ≫ q = p ≫ k)
    (g : H ⟶ J) (hg : g ≫ r = q ≫ l) :
    pullback.lift f p hf ≫
      F1FibrationsFiberComparisonBaseChange.fiberComparisonBaseChange
        q (pullback.snd r l) (pullback.lift g q hg) (pullback.lift_snd _ _ _) k =
    pullback.lift (f ≫ g) p (by rw [Category.assoc, hg, ← Category.assoc, hf, Category.assoc]) ≫
      (pullbackLeftPullbackSndIso r l k).inv := by
  apply (cancel_mono (pullbackLeftPullbackSndIso r l k).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply pullback.hom_ext
  · simp only [Category.assoc, pullbackLeftPullbackSndIso_hom_fst,
      F1FibrationsFiberComparisonBaseChange.fiberComparisonBaseChange,
      pullback.lift_fst_assoc, pullback.lift_fst]
  · simp only [Category.assoc, pullbackLeftPullbackSndIso_hom_snd,
      F1FibrationsFiberComparisonBaseChange.fiberComparisonBaseChange,
      pullback.lift_snd]

end PresentableInfinityCategories
end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories
