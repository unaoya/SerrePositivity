module

public import SerrePositivity.InfinityCategories.F1.Cocartesian.BaseChangeEvaluationLaws
public import SerrePositivity.InfinityCategories.F1.Cocartesian.SectionsAction

/-!
概要：strict transport の底変換比較は、元の全 cocartesian 相対 Hom の作用と厳密に可換。
方針：同じ section 同型で元の全空間へ戻し、全パラメーターの評価の射影公式を使う。
規約：元の全 Hom の作用を使い、対象ごとの比較だけに置き換えない。
使われ方：元の分類主写像のセル制限の Hom 上の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories

/-- 底変換の同じ比較成分と、元の全相対 Hom の全高次の section 作用は厳密に可換。 -/
lemma cocartesianStrictTransportBaseChangeComponent_action
    {C D : Type u} [Category.{u} C] [Category.{u} D] {E F : SSet.{u}}
    (p : E ⟶ nerve C) [CocartesianFibration p] (q : F ⟶ nerve C) [CocartesianFibration q]
    (k : D ⥤ C) (d : D) :
    cocartesianSectionsAction (Over.mk (nerveMap (Under.forget (k.obj d))))
      (Over.mk p) (Over.mk q) ≫ cocartesianStrictTransportBaseChangeComponent q k d =
    (cocartesianStrictTransportBaseChangeComponent p k d ⊗ₘ
      cocartesianPullbackNativeRestriction p q (Over.mk (nerveMap k))) ≫
    cocartesianSectionsAction (Over.mk (nerveMap (Under.forget d)))
      (Over.mk (pullback.fst (nerveMap k) p)) (Over.mk (pullback.fst (nerveMap k) q)) := by
  apply (cancel_mono (cocartesianSectionsPullbackIso
    (IsPullback.of_hasPullback (nerveMap k) q).flip (nerveMap (Under.forget d))
    (nerveMap (Under.forget d) ≫ nerveMap k) rfl).hom).mp
  rw [Category.assoc, cocartesianStrictTransportBaseChangeComponent_iso]
  apply (cancel_mono (kanCocartesianSectionsι q
    (nerveMap (Under.forget d) ≫ nerveMap k))).mp
  apply relativeFunctorUncurry_injective q (nerveMap (Under.forget d) ≫ nerveMap k)
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨x, s, h⟩
  change h.val.val.app n (𝟙 n)
      (s.val.val.app n (𝟙 n) ((nerveMap (Under.post k)).app n x)) =
    (pullback.snd (nerveMap k) q).app n
      ((((cocartesianPullbackNativeRestriction p q (Over.mk (nerveMap k))).app n h).val.val.app
        n (𝟙 n))
        ((((cocartesianStrictTransportBaseChangeComponent p k d).app n s).val.val.app
          n (𝟙 n)) x))
  have hR := cocartesianPullbackNativeRestriction_apply_snd p q (Over.mk (nerveMap k)) h
    ((((cocartesianStrictTransportBaseChangeComponent p k d).app n s).val.val.app n (𝟙 n)) x)
  have hS := cocartesianStrictTransportBaseChangeComponent_apply_snd p k d s x
  exact (hR.trans (congrArg (fun y ↦ h.val.val.app n (𝟙 n) y) hS)).symm

end SerrePositivity.InfinityCategories
