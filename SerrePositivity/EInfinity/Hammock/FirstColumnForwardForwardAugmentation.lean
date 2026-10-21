module

public import SerrePositivity.EInfinity.Hammock.FirstColumnForwardForwardDiagram

/-!
# 元の前向き二列の二方向係数図式の augmentation

概要：元の全相対作用素と両端の表示を保って比較を図式に束ねる。
方針：元の切断関手の全自然性と底・両係数の関手則を使う。
規約：元の全圏・graph と同じ augmentation を保持する。
使われ方：DK10.3・5.7の元の対角比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.Hammock.FirstColumn
open CategoryTheory Opposite SimplicialLocalization
private lemma natTrans_hext {C E : Type*} [Category* C] [Category* E]
    {F F' G G' : C ⥤ E} (hF : F = F') (hG : G = G')
    (α : F ⟶ G) (β : F' ⟶ G') (ha : ∀ X, HEq (α.app X) (β.app X)) : HEq α β := by
  cases hF
  cases hG
  apply heq_of_eq
  ext X
  exact eq_of_heq (ha X)
variable {I : Type v} [Category I] (D : I ⥤ RelativeCategory.{u}) (C : RelativeCategory.{u})
  (p : (i : I) → C.category → (D.obj i).category)
  (hp : ∀ {i j : I} (θ : i ⟶ j) (X : C.category), (D.map θ).functor.obj (p i X) = p j X)
  (A : D ⟶ (Functor.const I).obj C) (ha : ∀ i X, (A.app i).functor.obj (p i X) = X)
  (w : Word) (X Y : C.category)

def forwardForwardAugmentation : forwardForwardDiagram D p hp w X Y ⟶
    (Functor.const I).obj (forwardForwardData C w X Y) where
  app i := forwardForwardDataMap w (A.app i) (ha i X) (ha i Y)
  naturality i j θ := by
    have hA : A.app i = D.map θ ≫ A.app j := by
      have he := (A.naturality θ).symm
      change A.app i ≫ 𝟙 C = D.map θ ≫ A.app j at he
      exact (Category.comp_id (A.app i : D.obj i ⟶ C)).symm.trans he
    have hb : markedCategoryMap (D.map θ) ⋙ markedCategoryMap (A.app j) =
        markedCategoryMap (A.app i) :=
      (congrArg (fun f : D.obj i ⟶ C => markedCategoryMap f) hA).symm
    change forwardForwardDataMap w (D.map θ) (hp θ X) (hp θ Y) ≫
        forwardForwardDataMap w (A.app j) (ha j X) (ha j Y) =
      forwardForwardDataMap w (A.app i) (ha i X) (ha i Y) ≫ 𝟙 _
    rw [Category.comp_id]
    refine TwoSidedDiagram.hom_ext _ _ hb ?_ ?_
    · refine natTrans_hext rfl ?_ _ _ ?_
      · change (markedCategoryMap (D.map θ) ⋙ markedCategoryMap (A.app j)).op ⋙ _ = _
        rw [hb]
        rfl
      · intro Z
        exact (Zigzag.Relative.fixedFunctor_comp_toCatHom_heq
          (D.map θ) (A.app j) (A.app i) hA Z.unop.obj
          (p i Y) (p j Y) Y (hp θ Y) (ha j Y) (ha i Y)).symm
    · refine natTrans_hext rfl ?_ _ _ ?_
      · change (markedCategoryMap (D.map θ) ⋙ markedCategoryMap (A.app j)) ⋙ _ = _
        rw [hb]
        rfl
      · intro Z
        exact (forwardForwardRightMap_comp_heq w (D.map θ) (A.app j) (A.app i) hA
          (p i X) (p i Y) (p j X) (p j Y) X Y (hp θ X) (ha j X) (ha i X) Z).symm
end SerrePositivity.EInfinity.Hammock.FirstColumn
