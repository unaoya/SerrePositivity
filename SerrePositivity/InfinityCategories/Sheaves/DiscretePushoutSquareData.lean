module

public import SerrePositivity.InfinityCategories.Sheaves.DiscretePresheafEssentialImage
public import SerrePositivity.InfinityCategories.Sheaves.SpacePresheafYoneda
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.PushoutShape

/-!
概要：元の集合値前層の押し出し四角形と、その同じ二つの合成二単体を固定する。
方針：対角に沿う二三角形の押し出しで通常の四角形を作り、全離散埋め込みで送る。
  文献対応：HTT 4.2.4.1・6.2.2.7、Kerodon 7.5.4.6（Tag 03BB）、S8-3。
規約：型と二単体は drafts/Sheaves/SpaceValued と同じ。余極限判定は別に証明する。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet MonoidalCategory
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
open SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
namespace SerrePositivity.InfinityCategories.Sheaves
variable {C : Type u} [SmallCategory C] {P Q R : Cᵒᵖ ⥤ Type u}

/-- 元の集合値前層の押し出し。HTT 6.2.2.7、S8-3 の同じ通常の頂点。 -/
abbrev presheafPushout (f : P ⟶ Q) (g : P ⟶ R) := pushout f g

/-- 元の通常の押し出し四角形を、同じ二つの合成二単体で表示する。
HTT 4.2.4.1、Kerodon 7.5.4.6（Tag 03BB）、四角形の全高次資料を固定する法則。 -/
def presheafPushoutNerveSquare (f : P ⟶ Q) (g : P ⟶ R) :
    (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ nerve (Cᵒᵖ ⥤ Type u) :=
  square_isPushout.desc
    (SSet.yonedaEquiv.symm (ComposableArrows.mk₂ g (pushout.inr f g)))
    (SSet.yonedaEquiv.symm (ComposableArrows.mk₂ f (pushout.inl f g))) (by
      apply SSet.yonedaEquiv.injective
      change (nerve _).δ 1 (ComposableArrows.mk₂ g (pushout.inr f g)) =
        (nerve _).δ 1 (ComposableArrows.mk₂ f (pushout.inl f g))
      simp only [nerve.δ₁_mk₂_eq, pushout.condition])

/-- drafts と同じ全離散埋め込みによる押し出し四角形。
HTT 6.2.2.7、Kerodon 7.5.4.6（Tag 03BB）。定義の展開で元の式に一致する。 -/
def discretePushoutSquare (f : P ⟶ Q) (g : P ⟶ R) :
    (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ PresheafCat C SpaceInfinity.{u} :=
  presheafPushoutNerveSquare f g ≫ (discretePresheafInclusion C).val

private lemma kanDiscretePresheafMap_two (f : P ⟶ Q) (h : Q ⟶ R) :
    (nerveMap (kanDiscretePresheafFunctor C)).app (Opposite.op ⦋2⦌)
        (ComposableArrows.mk₂ f h) =
      ComposableArrows.mk₂ ((kanDiscretePresheafFunctor C).map f)
        ((kanDiscretePresheafFunctor C).map h) := by
  change ComposableArrows.mk₂ f h ⋙ kanDiscretePresheafFunctor C = _
  refine ComposableArrows.ext₂
    (f := ComposableArrows.mk₂ f h ⋙ kanDiscretePresheafFunctor C)
    (g := ComposableArrows.mk₂ ((kanDiscretePresheafFunctor C).map f)
      ((kanDiscretePresheafFunctor C).map h)) rfl rfl rfl ?_ ?_
  all_goals simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  all_goals rfl

/-- 押し出し四角形の第一の三角形は、元の f と左包含の同じ coherent 合成二単体。
HTT 4.2.4.1、Kerodon 7.5.4.6（Tag 03BB）、全二単体の計算則。 -/
lemma discretePushoutSquare_triangle_left (f : P ⟶ Q) (g : P ⟶ R) :
    squareTriangle 1 ≫ discretePushoutSquare f g =
      SSet.yonedaEquiv.symm ((nerveToCoherent (KanDiagramObject Cᵒᵖ)).app
        (Opposite.op ⦋2⦌) (ComposableArrows.mk₂
          ((kanDiscretePresheafFunctor C).map f)
          ((kanDiscretePresheafFunctor C).map (pushout.inl f g)))) ≫
        kanDiagramRealization Cᵒᵖ := by
  change (squareTriangle 1 ≫ presheafPushoutNerveSquare f g) ≫
    (nerveMap (kanDiscretePresheafFunctor C) ≫
      nerveToCoherent (KanDiagramObject Cᵒᵖ) ≫ kanDiagramRealization Cᵒᵖ) = _
  rw [presheafPushoutNerveSquare, square_isPushout.inr_desc]
  rw [← Category.assoc, ← Category.assoc, SSet.yonedaEquiv_symm_comp,
    kanDiscretePresheafMap_two, SSet.yonedaEquiv_symm_comp]

/-- 押し出し四角形の第二の三角形は、元の g と右包含の同じ coherent 合成二単体。
HTT 4.2.4.1、Kerodon 7.5.4.6（Tag 03BB）、全二単体の計算則。 -/
lemma discretePushoutSquare_triangle_right (f : P ⟶ Q) (g : P ⟶ R) :
    squareTriangle 0 ≫ discretePushoutSquare f g =
      SSet.yonedaEquiv.symm ((nerveToCoherent (KanDiagramObject Cᵒᵖ)).app
        (Opposite.op ⦋2⦌) (ComposableArrows.mk₂
          ((kanDiscretePresheafFunctor C).map g)
          ((kanDiscretePresheafFunctor C).map (pushout.inr f g)))) ≫
        kanDiagramRealization Cᵒᵖ := by
  change (squareTriangle 0 ≫ presheafPushoutNerveSquare f g) ≫
    (nerveMap (kanDiscretePresheafFunctor C) ≫
      nerveToCoherent (KanDiagramObject Cᵒᵖ) ≫ kanDiagramRealization Cᵒᵖ) = _
  rw [presheafPushoutNerveSquare, square_isPushout.inl_desc]
  rw [← Category.assoc, ← Category.assoc, SSet.yonedaEquiv_symm_comp,
    kanDiscretePresheafMap_two, SSet.yonedaEquiv_symm_comp]

/-- 元の通常の押し出し余錐の同じ離散表示。HTT 4.2.4.1、S8-3 の全余錐の接続。 -/
def discretePushoutCocone (f : P ⟶ Q) (g : P ⟶ R) :=
  discretePresheafCocone ((pushout.cocone f g).whisker (AsSmall.down : AsSmall.{u} WalkingSpan ⥤ _))

/-- 単射を一脚とする元の押し出し余錐の離散表示は余極限。
HTT 6.2.2.7、Kerodon 7.5.4.6（Tag 03BB）。四角形との照合は別に行う。 -/
lemma discretePushoutCocone_isColimit (f : P ⟶ Q) (g : P ⟶ R) [Mono f] :
    IsColimitCone (discretePushoutCocone f g) := by
  have : Mono (((AsSmall.down : AsSmall.{u} WalkingSpan ⥤ _) ⋙ span f g).map
      (AsSmall.up.map WalkingSpan.Hom.fst)) := inferInstanceAs (Mono f)
  exact discretePresheafCocone_isColimit_of_span_mono _
    ((pushout.isColimit f g).whiskerEquivalence AsSmall.equiv.symm)

end SerrePositivity.InfinityCategories.Sheaves
