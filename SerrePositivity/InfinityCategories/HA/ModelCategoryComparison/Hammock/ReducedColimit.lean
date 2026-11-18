module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.NormalFormTransition
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ReducedSimplicialSet

/-!
# 元の全語の余極限と縮約 hammock の実同型

概要：元の有限縮約による正規化は全語の余錐を定め、元の標準射と互いに逆になる。
方針：全遷移での正規形の不変性と同じ元の余極限の普遍性を使う。
規約：同型の逆射は元の縮約済み代表の同じ標準射であり、全単体で照合する。
使われ方：Dwyer–Kan §5.5 の元の余極限による縮約 hammock の表示。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock
open _root_.CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative]
  (X Y : C)

/-- 元の固定語の全単体から縮約済みの一意な代表への射。 -/
def graphNormalization (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W w X Y ⟶ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.reducedSimplicialSet W X Y where
  app n := ↾fun τ => ⟨_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.normalForm W X Y n ⟨w, τ⟩, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.normalForm_reduced W X Y n ⟨w, τ⟩⟩
  naturality n m α := by
    apply ConcreteCategory.hom_ext
    intro τ
    apply Subtype.ext
    exact (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.normalForm_map_normalForm W X Y n α ⟨w, τ⟩).symm

lemma graphNormalization_naturality {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f : a ⟶ b) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W X Y).map f ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.graphNormalization W X Y b = _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.graphNormalization W X Y a := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro τ
  apply Subtype.ext
  exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.normalForm_transition W X Y n f τ

lemma graphNormalization_augmentation (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.graphNormalization W X Y w ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.reducedAugmentation W X Y = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W X Y w := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro τ
  exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.normalForm_value W X Y n ⟨w, τ⟩

/-- 元の全語の余極限から元の縮約済み代表への正規化。 -/
def colimitNormalization : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W X Y ⟶ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.reducedSimplicialSet W X Y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraphDesc W X Y (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.graphNormalization W X Y)
    (fun f => _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.graphNormalization_naturality W X Y f)

lemma graphInclusion_colimitNormalization (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W X Y w ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.colimitNormalization W X Y = _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.graphNormalization W X Y w :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion_desc W X Y _ _ w

lemma colimitNormalization_augmentation :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.colimitNormalization W X Y ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.reducedAugmentation W X Y = 𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W X Y) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph_hom_ext W X Y
  intro w
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.graphInclusion_colimitNormalization, Category.comp_id]
  exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.graphNormalization_augmentation W X Y w

lemma augmentation_colimitNormalization :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.reducedAugmentation W X Y ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.colimitNormalization W X Y = 𝟙 (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.reducedSimplicialSet W X Y) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro r
  apply Subtype.ext
  have he := congrArg (fun η : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W r.val.1 X Y ⟶ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.reducedSimplicialSet W X Y =>
    (η.app n r.val.2).val) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.graphInclusion_colimitNormalization W X Y r.val.1)
  change ((_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.colimitNormalization W X Y).app n
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W X Y r.val.1).app n r.val.2)).val = _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.normalForm W X Y n r.val at he
  exact he.trans (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.normalForm_eq_self W X Y n r.property)

lemma rawAugmentation_colimitNormalization :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawSimplicialSet.augmentation W X Y ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.colimitNormalization W X Y = _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.normalization W X Y := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro r
  exact congrArg (fun η : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W r.1 X Y ⟶ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.reducedSimplicialSet W X Y => η.app n r.2)
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.graphInclusion_colimitNormalization W X Y r.1)

/-- Dwyer–Kan §5.5 の、元の余極限と縮約 hammock の単体集合としての実同型。 -/
def reducedColimitIso : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W X Y ≅ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.reducedSimplicialSet W X Y where
  hom := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.colimitNormalization W X Y
  inv := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.reducedAugmentation W X Y
  hom_inv_id := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.colimitNormalization_augmentation W X Y
  inv_hom_id := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.augmentation_colimitNormalization W X Y

lemma reducedColimitIso_hom_fac (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W X Y w ≫ (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.reducedColimitIso W X Y).hom = _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.graphNormalization W X Y w :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.graphInclusion_colimitNormalization W X Y w

lemma reducedColimitIso_inv : (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.reducedColimitIso W X Y).inv = _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.reducedAugmentation W X Y := rfl

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock
