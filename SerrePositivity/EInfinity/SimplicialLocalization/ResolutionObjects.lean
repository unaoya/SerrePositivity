module

public import SerrePositivity.EInfinity.SimplicialLocalization.LocalizedFreeResolution

/-!
# 局所化した自由解像の固定対象の表示

概要：Dwyer–Kan の次数ごとの局所化の対象を元の相対圏の対象で表示する。
方針：augmentation の対象写像の全単射性と全単体作用素への自然性を使う。
規約：対象の表示の単体作用素との両立を証明して保持する。
使われ方：固定対象の Hom を単体集合へ束ねる。
-/

@[expose] public section

noncomputable section

universe u

namespace SerrePositivity.EInfinity.SimplicialLocalization

open CategoryTheory Opposite
open SerrePositivity.HomotopyFunctionComplex

/-- 概要：自由相対圏の余単位は対象上で全単射（Dwyer–Kan）。
方針：列の圏は元の対象と同じ対象を持つことを使う。
規約：元の相対圏を変更しない。
使われ方：全反復自由解像の対象の表示。 -/
lemma freeRelativeCounit_obj_bijective (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) :
    Function.Bijective (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.freeRelativeCounit.app C).functor.obj :=
  ⟨fun _ _ h => h, fun X => ⟨X, rfl⟩⟩

/-- 概要：反復自由解像の augmentation は対象上で全単射（Dwyer–Kan）。
方針：余単位の全単射性を反復と逐次合成で使う。
規約：元の汎用 comonad 解像の augmentation を保持する。
使われ方：通常の単体圏上の全次数の対象の同定。 -/
lemma freeComonadAugmentation_obj_bijective (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (n : ℕ) :
    Function.Bijective
      (ComonadResolutionOperators.augmentation _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.freeRelativeComonad C n).functor.obj := by
  induction n with
  | zero => exact Function.bijective_id
  | succ n ih =>
    exact ih.comp (freeRelativeCounit_obj_bijective
      (ComonadResolutionOperators.power _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.freeRelativeComonad C n))

/-- 概要：全自由単体的解像の augmentation は対象上で全単射（Dwyer–Kan）。
方針：元の汎用 augmentation の各次数の式を使う。
規約：任意の単体次数で成立する。
使われ方：次数ごとの局所化へ元の対象を移す。 -/
lemma freeResolutionAugmentation_obj_bijective (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u})
    (n : SimplexCategoryᵒᵖ) :
    Function.Bijective ((freeResolutionAugmentationNatTrans C).app n).functor.obj :=
  freeComonadAugmentation_obj_bijective C (n.unop.len + 1)

/-- 概要：構成的な局所化は相対関手の対象上の全単射性を保つ（Dwyer–Kan）。
方針：局所化の構成の対象の標準同値を相対関手の両側で合成する。
規約：元の局所化の対象を変更しない。
使われ方：局所化した自由次数の固定対象の表示。 -/
lemma strictLocalizationMap_obj_bijective {C D : Type u} [Category.{u} C] [Category.{u} D]
    {W : MorphismProperty C} {V : MorphismProperty D} (F : LocalizerMorphism W V)
    (hF : Function.Bijective F.functor.obj) :
    Function.Bijective (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.strictLocalizationMap F).obj := by
  change Function.Bijective (fun X =>
    (Localization.Construction.objEquiv V) (F.functor.obj
      ((Localization.Construction.objEquiv W).symm X)))
  exact (Localization.Construction.objEquiv V).bijective.comp
    (hF.comp (Localization.Construction.objEquiv W).symm.bijective)

/-- 概要：局所化した全自由解像の augmentation は対象上で全単射（Dwyer–Kan）。
方針：元の自由解像の全単射性と構成的な局所化による保存を使う。
規約：任意の単体次数で同じ augmentation を使う。
使われ方：対象表示の逆と全作用素との両立。 -/
lemma localizedFreeResolutionAugmentation_obj_bijective (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u})
    (n : SimplexCategoryᵒᵖ) :
    Function.Bijective ((localizedFreeResolutionAugmentation C).app n).toFunctor.obj := by
  exact strictLocalizationMap_obj_bijective
    ((freeResolutionAugmentationNatTrans C).app n)
    (freeResolutionAugmentation_obj_bijective C n)

/-- 概要：各局所化次数の対象と元の普通の局所化の対象の標準同値（Dwyer–Kan）。
方針：同じ augmentation の全単射な対象写像を同値に束ねる。
規約：順写像は元の augmentation の対象写像そのもの。
使われ方：固定した元の対象で各 Hom を表示する。 -/
def localizedFreeResolutionObjectEquiv (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (n : SimplexCategoryᵒᵖ) :
    (localizedFreeResolution C).obj n ≃ C.weakEquivalences.Localization :=
  Equiv.ofBijective ((localizedFreeResolutionAugmentation C).app n).toFunctor.obj
    (localizedFreeResolutionAugmentation_obj_bijective C n)

/-- 概要：元の対象を各局所化次数の同じ対象として表示（Dwyer–Kan）。
方針：augmentation の対象同値の逆へ元の局所化像を入力する。
規約：表示の全単体作用素との両立は次の式で保証する。
使われ方：固定した両対象の Hom の単体集合。 -/
def localizedFreeResolutionObject (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}) (n : SimplexCategoryᵒᵖ)
    (X : C.category) : (localizedFreeResolution C).obj n :=
  (localizedFreeResolutionObjectEquiv C n).symm (C.weakEquivalences.Q.obj X)

/-- 概要：全単体作用素は元の対象の各次数の表示を保つ（Dwyer–Kan）。
方針：augmentation の自然性と対象写像の単射性を使う。
規約：対象ごとの選択から自然性を仮定しない。
使われ方：固定対象の Hom の作用素と合成の構成。 -/
lemma localizedFreeResolutionObject_naturality (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u})
    {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) (X : C.category) :
    ((localizedFreeResolution C).map θ).toFunctor.obj (localizedFreeResolutionObject C n X) =
      localizedFreeResolutionObject C m X := by
  apply (localizedFreeResolutionObjectEquiv C m).injective
  have h := congrArg Cat.Hom.toFunctor ((localizedFreeResolutionAugmentation C).naturality θ)
  change ((localizedFreeResolution C).map θ).toFunctor ⋙
    ((localizedFreeResolutionAugmentation C).app m).toFunctor =
      ((localizedFreeResolutionAugmentation C).app n).toFunctor ⋙ 𝟭 _ at h
  have h' : ((localizedFreeResolution C).map θ).toFunctor ⋙
      ((localizedFreeResolutionAugmentation C).app m).toFunctor =
        ((localizedFreeResolutionAugmentation C).app n).toFunctor := by
    simpa only [Functor.comp_id] using h
  change ((localizedFreeResolutionAugmentation C).app m).toFunctor.obj
      (((localizedFreeResolution C).map θ).toFunctor.obj (localizedFreeResolutionObject C n X)) =
    (localizedFreeResolutionObjectEquiv C m) (localizedFreeResolutionObject C m X)
  rw [← Functor.comp_obj, h']
  exact (localizedFreeResolutionObjectEquiv C n).apply_symm_apply _ |>.trans
    ((localizedFreeResolutionObjectEquiv C m).apply_symm_apply _).symm

end SerrePositivity.EInfinity.SimplicialLocalization
