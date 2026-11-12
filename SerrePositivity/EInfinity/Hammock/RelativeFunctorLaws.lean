module

public import SerrePositivity.EInfinity.Hammock.RelativeColimitMap

/-!
# 元の相対関手による hammock 写像の恒等・合成則

概要：固定語の関手、全語の自然変換、余極限と reduced hammock の写像は厳密に関手的。
方針：全対象・全縦射で元の関手の法則を使い、nerve と余極限へ移す。
規約：各段階で元の写像と元の対象を保持する。
使われ方：自由相対解像の全単体作用素に沿う hammock の比較図式。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock
open CategoryTheory

variable {C D E : Type u} [Category.{v} C] [Category.{v} D] [Category.{v} E]
  {W : MorphismProperty C} [W.IsMultiplicative] {V : MorphismProperty D} [V.IsMultiplicative]
  {U : MorphismProperty E} [U.IsMultiplicative]

lemma Zigzag.Relative.functor_id (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (X Y : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.functor (w := w) (X := X) (Y := Y) (LocalizerMorphism.id W) = 𝟭 _ := rfl

lemma Zigzag.Relative.functor_comp (F : LocalizerMorphism W V) (G : LocalizerMorphism V U)
    (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) (X Y : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.functor (w := w) (X := X) (Y := Y) (F.comp G) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.functor F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.functor G := rfl

namespace Relative

lemma graphDiagramMap_id (X Y : C) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphDiagramMap (LocalizerMorphism.id W) X Y = 𝟙 _ := by
  apply NatTrans.ext
  funext w
  change nerveFunctor.map (𝟙 (Cat.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y))) = 𝟙 _
  exact nerveFunctor.map_id _

lemma graphDiagramMap_comp (F : LocalizerMorphism W V) (G : LocalizerMorphism V U) (X Y : C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphDiagramMap (F.comp G) X Y = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphDiagramMap F X Y ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphDiagramMap G (F.functor.obj X) (F.functor.obj Y) := by
  apply NatTrans.ext
  funext w
  change nerveFunctor.map
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.functor (w := w) (X := X) (Y := Y) (F.comp G)).toCatHom =
    nerveFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.functor (w := w) (X := X) (Y := Y) F).toCatHom ≫
      nerveFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.functor (w := w)
        (X := F.functor.obj X) (Y := F.functor.obj Y) G).toCatHom
  rw [← nerveFunctor.map_comp]
  rfl

lemma colimitMap_id (X Y : C) : colimitMap (LocalizerMorphism.id W) X Y = 𝟙 _ := by
  unfold colimitMap
  rw [graphDiagramMap_id]
  exact CategoryTheory.Limits.colim.map_id _

lemma colimitMap_comp (F : LocalizerMorphism W V) (G : LocalizerMorphism V U) (X Y : C) :
    colimitMap (F.comp G) X Y = colimitMap F X Y ≫
      colimitMap G (F.functor.obj X) (F.functor.obj Y) := by
  unfold colimitMap
  rw [graphDiagramMap_comp]
  exact CategoryTheory.Limits.colim.map_comp _ _

lemma reducedMap_id (X Y : C) : reducedMap (LocalizerMorphism.id W) X Y = 𝟙 _ := by
  change (reducedColimitIso W X Y).inv ≫ colimitMap (LocalizerMorphism.id W) X Y ≫
    (reducedColimitIso W X Y).hom = 𝟙 _
  rw [colimitMap_id, Category.id_comp, Iso.inv_hom_id]

lemma reducedMap_comp (F : LocalizerMorphism W V) (G : LocalizerMorphism V U) (X Y : C) :
    reducedMap (F.comp G) X Y = reducedMap F X Y ≫
      reducedMap G (F.functor.obj X) (F.functor.obj Y) := by
  simp only [reducedMap, colimitMap_comp, Category.assoc, Iso.hom_inv_id_assoc]
  rfl

end Relative
end SerrePositivity.EInfinity.Hammock
