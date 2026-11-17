module

public import SerrePositivity.InfinityCategories.HA.Monads.WalkingAdjunctionComposition

/-!
概要：walking adjunctionの八つの水平合成の全単位則を実関手の等式で示す。
方針：空の順序和の作用とGalois双対の相互逆性を使い、任意の添字圏の射を保つ。
規約：対象の法則だけで終えず、全自然性を含む関手の等式とする。
使われ方：HA Proposition 4.7.3.3、Riehl–Verity Remark 3.3.8 の全随伴の添字。
Kerodon Remark 6.2.1.4（Tag 02EN）への忘却より前の単位則。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory Opposite MonoidalCategory

namespace SerrePositivity.InfinityCategories.HA.Monads

variable {I : Type u} [Category.{v} I]

/-- 概要：最大元保存の左作用に空を入れると全関手が変わらない。
方針：拡張関手の空での値と恒等射の保存を使う。
規約：全Iの射を量化する。使われ方：Riehl–Verity Remark 3.3.8 の単位則。 -/
lemma topOrdinalAction_leftUnit (F : I ⥤ TopSimplexCategory) :
    (((Functor.const I).obj WithInitial.star).prod' F ⋙ topOrdinalAction) = F := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro X Y f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  change (topOrdinalPrefixExtended.map (𝟙 (WithInitial.star : AugmentedSimplexCategory))).app
    (F.obj X) ≫ F.map f = F.map f
  simp only [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]

/-- 概要：最小元保存の右作用に空を入れると全関手が変わらない。
方針：拡張関手の空での値と恒等射の保存を使う。
規約：全射の等式。使われ方：Riehl–Verity Remark 3.3.8 の単位則。 -/
lemma bottomOrdinalAction_rightUnit (F : I ⥤ BottomSimplexCategory) :
    (F.prod' ((Functor.const I).obj WithInitial.star) ⋙ bottomOrdinalAction) = F := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro X Y f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  change F.map f ≫
    (bottomOrdinalSuffixExtended.map (𝟙 (WithInitial.star : AugmentedSimplexCategory))).app
      (F.obj Y) = F.map f
  simp only [CategoryTheory.Functor.map_id, NatTrans.id_app,
    bottomOrdinalSuffixExtended_empty, CategoryTheory.Functor.id_obj, Category.comp_id]

/-- 概要：双対側の最小元保存の左作用の全単位則。
方針：空での作用と有限Galois随伴の往復を照合する。
規約：逆の関手の一致を仮定しない。使われ方：Riehl–Verity Remark 3.3.8。 -/
lemma bottomOppositeOrdinalAction_leftUnit (F : I ⥤ BottomSimplexCategory) :
    (((Functor.const I).obj (op (WithInitial.star : AugmentedSimplexCategory))).prod' F ⋙
      bottomOppositeOrdinalAction) = F := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro X Y f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  change topSimplexLeftAdjoint
    ((topOrdinalPrefixExtended.map (𝟙 (WithInitial.star : AugmentedSimplexCategory))).app
      ⟨(F.obj Y).obj⟩ ≫ bottomSimplexRightAdjoint (F.map f)) = F.map f
  rw [CategoryTheory.Functor.map_id]
  simp only [NatTrans.id_app, Category.id_comp]
  apply WideSubcategory.hom_ext
  apply SimplexCategory.Hom.ext'
  exact ordinal_left_right (F.map f).hom.toOrderHom (F.map f).property

/-- 概要：双対側の最大元保存の右作用の全単位則。
方針：空での作用と逆順の有限Galois随伴の往復を使う。
規約：元の変数の向き。使われ方：Riehl–Verity Remark 3.3.8。 -/
lemma topOppositeOrdinalAction_rightUnit (F : I ⥤ TopSimplexCategory) :
    (F.prod' ((Functor.const I).obj (op (WithInitial.star : AugmentedSimplexCategory))) ⋙
      topOppositeOrdinalAction) = F := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro X Y f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  change bottomSimplexRightAdjoint
    (topSimplexLeftAdjoint (F.map f) ≫
      (bottomOrdinalSuffixExtended.map (𝟙 (WithInitial.star : AugmentedSimplexCategory))).app
        ⟨(F.obj X).obj⟩) = F.map f
  rw [CategoryTheory.Functor.map_id]
  simp only [NatTrans.id_app]
  apply WideSubcategory.hom_ext
  apply SimplexCategory.Hom.ext'
  exact ordinal_right_left (F.map f).hom.toOrderHom (F.map f).property

/-- 概要：反対の増大単体圏の順序和の全左単位則。
方針：証明済みの元の単位則の反対を取る。
規約：全Iの射を保つ関手等式。使われ方：HA §4.7.2 の双対側の合成。 -/
lemma oppositeOrdinalSum_leftUnit (F : I ⥤ AugmentedSimplexCategoryᵒᵖ) :
    (((Functor.const I).obj (op (WithInitial.star : AugmentedSimplexCategory))).prod' F ⋙
      (prodOpEquiv (C := AugmentedSimplexCategory) (D := AugmentedSimplexCategory)).inverse ⋙
        (tensor AugmentedSimplexCategory).op) = F := by
  exact congrArg (fun K : Iᵒᵖ ⥤ AugmentedSimplexCategory => K.rightOp)
    (ordinalSumFunctor_leftUnit F.leftOp)

/-- 概要：反対の増大単体圏の順序和の全右単位則。
方針：元の右単位則を反対に移す。規約：同じF上の等式。
使われ方：HA §4.7.2 の双対側の合成。 -/
lemma oppositeOrdinalSum_rightUnit (F : I ⥤ AugmentedSimplexCategoryᵒᵖ) :
    (F.prod' ((Functor.const I).obj (op (WithInitial.star : AugmentedSimplexCategory))) ⋙
      (prodOpEquiv (C := AugmentedSimplexCategory) (D := AugmentedSimplexCategory)).inverse ⋙
        (tensor AugmentedSimplexCategory).op) = F := by
  exact congrArg (fun K : Iᵒᵖ ⥤ AugmentedSimplexCategory => K.rightOp)
    (ordinalSumFunctor_rightUnit F.leftOp)

/-- 概要：四Homの全水平合成の全左単位則。
方針：四つの実関手の単位則を同じ型でまとめる。
規約：全単体に使える任意の添字圏。使われ方：HA Proposition 4.7.3.3 のwalking adjunction。 -/
lemma walkingAdjunctionHorizontal_leftUnit (X Y : WalkingAdjunctionPoint)
    (F : I ⥤ walkingAdjunctionHom X Y) :
    (((Functor.const I).obj (walkingAdjunctionIdentity X)).prod' F ⋙
      walkingAdjunctionHorizontal X X Y) = F := by
  cases X <;> cases Y
  · exact ordinalSumFunctor_leftUnit F
  · exact topOrdinalAction_leftUnit F
  · exact bottomOppositeOrdinalAction_leftUnit F
  · exact oppositeOrdinalSum_leftUnit F

/-- 概要：四Homの全水平合成の全右単位則。
方針：四つの実関手の単位則をまとめる。
規約：対象だけでなく射も一致する。使われ方：HA Proposition 4.7.3.3 のwalking adjunction。 -/
lemma walkingAdjunctionHorizontal_rightUnit (X Y : WalkingAdjunctionPoint)
    (F : I ⥤ walkingAdjunctionHom X Y) :
    (F.prod' ((Functor.const I).obj (walkingAdjunctionIdentity Y)) ⋙
      walkingAdjunctionHorizontal X Y Y) = F := by
  cases X <;> cases Y
  · exact ordinalSumFunctor_rightUnit F
  · exact topOppositeOrdinalAction_rightUnit F
  · exact bottomOrdinalAction_rightUnit F
  · exact oppositeOrdinalSum_rightUnit F

end SerrePositivity.InfinityCategories.HA.Monads
