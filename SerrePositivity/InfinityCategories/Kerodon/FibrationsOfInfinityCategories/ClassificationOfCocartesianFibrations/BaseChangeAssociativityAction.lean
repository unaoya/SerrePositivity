module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.BaseChangeAssociativityEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.StrictTransportBaseChangeAction

/-!
概要：同じ結合同型は、元の全相対 Hom の底変換後の section 作用と厳密に可換。
方針：元の全空間へ戻し、任意の次数の同じ射影と評価を照合する。
規約：二重底変換と直接の底変換の元の全高次 Hom の作用を使う。
使われ方：底全体と全 fibration に自然な結合比較。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 元の全相対 Hom の作用と、底変換の同じ結合同型は全パラメーターで可換。 -/
lemma cocartesianBaseChangeAssociativityComponent_action
    {A D C : Type u} [Category.{u} A] [Category.{u} D] [Category.{u} C] {E F : SSet.{u}}
    (p : E ⟶ nerve C) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p] (q : F ⟶ nerve C) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration q]
    (l : A ⥤ D) (k : D ⥤ C) (a : A) :
    (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransport
        (pullback.fst (nerveMap l) (pullback.fst (nerveMap k) p)) a) ⊗ₘ
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeRestriction p q (Over.mk (nerveMap k)) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeRestriction (pullback.fst (nerveMap k) p)
          (pullback.fst (nerveMap k) q) (Over.mk (nerveMap l)))) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSectionsAction (Over.mk (nerveMap (Under.forget a)))
        (Over.mk (pullback.fst (nerveMap l) (pullback.fst (nerveMap k) p)))
        (Over.mk (pullback.fst (nerveMap l) (pullback.fst (nerveMap k) q))) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeAssociativityComponent q l k a).hom =
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeAssociativityComponent p l k a).hom ⊗ₘ
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeRestriction p q (Over.mk (nerveMap (l ⋙ k)))) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSectionsAction (Over.mk (nerveMap (Under.forget a)))
        (Over.mk (pullback.fst (nerveMap (l ⋙ k)) p))
        (Over.mk (pullback.fst (nerveMap (l ⋙ k)) q)) := by
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianSectionsPullbackIso
    (IsPullback.of_hasPullback (nerveMap (l ⋙ k)) q).flip
    (nerveMap (Under.forget a)) (nerveMap (Under.forget a) ≫ nerveMap (l ⋙ k)) rfl).hom).mp
  simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeAssociativityComponent_iso]
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianSectionsι q
    (nerveMap (Under.forget a) ≫ nerveMap (l ⋙ k)))).mp
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.relativeFunctorUncurry_injective q (nerveMap (Under.forget a) ≫ nerveMap (l ⋙ k))
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  rintro ⟨x, s, h⟩
  have hl := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeRestriction_apply_snd (pullback.fst (nerveMap k) p)
    (pullback.fst (nerveMap k) q) (Over.mk (nerveMap l))
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeRestriction p q (Over.mk (nerveMap k))).app n h)
    (s.val.val.app n (𝟙 n) x)
  have hk := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeRestriction_apply_snd p q (Over.mk (nerveMap k)) h
    ((pullback.snd (nerveMap l) (pullback.fst (nerveMap k) p)).app n
      (s.val.val.app n (𝟙 n) x))
  have hd := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianPullbackNativeRestriction_apply_snd p q
    (Over.mk (nerveMap (l ⋙ k))) h
    ((((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeAssociativityComponent p l k a).hom.app n s).val.val.app
      n (𝟙 n)) x)
  have hs := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeAssociativityComponent_apply_snd p l k a s x
  exact ((congrArg ((pullback.snd (nerveMap k) q).app n) hl).trans hk).trans
    (hd.trans (congrArg (fun y ↦ h.val.val.app n (𝟙 n) y) hs)).symm

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
