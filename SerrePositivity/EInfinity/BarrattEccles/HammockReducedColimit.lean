module

public import SerrePositivity.EInfinity.BarrattEccles.HammockNormalization
public import SerrePositivity.EInfinity.Hammock.ReducedColimit

/-!
# 任意の可換環上の元の余極限と縮約 hammock の実同型

概要：全語の遷移に対する正規形の不変性と、同じ元の余極限からの実同型を提供する。
方針：元の標準射を保持する全語の余錐と両逆を、実際の E 代数に代入する。
規約：モデル構造は局所的に選ぶ。三列の標準射の弱同値性は後続。
使われ方：元の Map^h と縮約 hammock の高次比較。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory HomotopicalAlgebra

namespace SerrePositivity.EInfinity.BarrattEccles
variable (A : Type u) [CommRing A] (X Y : (operad A).Algebra)

lemma algebraHammockNormalForm_transition {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f : a ⟶ b)
    {n : SimplexCategoryᵒᵖ} (τ : (algebraHammockGraph A a X Y).obj n) :
    algebraHammockNormalForm A X Y ⟨b, (algebraHammockGraphMap A f X Y).app n τ⟩ =
      algebraHammockNormalForm A X Y ⟨a, τ⟩ := by
  let := modelCategory A
  exact Hammock.normalForm_transition (weakEquivalences (operad A).Algebra) X Y n f τ

/-- 元の固定語の全単体からの正規化。 -/
def algebraHammockGraphNormalization (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) :
    algebraHammockGraph A w X Y ⟶ algebraHammockReducedSimplicialSet A X Y := by
  let := modelCategory A
  exact Hammock.graphNormalization (weakEquivalences (operad A).Algebra) X Y w

lemma algebraHammockGraphNormalization_naturality {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} (f : a ⟶ b) :
    algebraHammockGraphMap A f X Y ≫ algebraHammockGraphNormalization A X Y b =
      algebraHammockGraphNormalization A X Y a := by
  let := modelCategory A
  exact Hammock.graphNormalization_naturality (weakEquivalences (operad A).Algebra) X Y f

lemma algebraHammockGraphNormalization_augmentation (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) :
    algebraHammockGraphNormalization A X Y w ≫ algebraHammockReducedAugmentation A X Y =
      algebraHammockGraphInclusion A w X Y := by
  let := modelCategory A
  exact Hammock.graphNormalization_augmentation (weakEquivalences (operad A).Algebra) X Y w

/-- 全語の元の余極限から、元の縮約済み代表への正規化。 -/
def algebraHammockColimitNormalization :
    algebraHammockColimitGraph A X Y ⟶ algebraHammockReducedSimplicialSet A X Y := by
  let := modelCategory A
  exact Hammock.colimitNormalization (weakEquivalences (operad A).Algebra) X Y

lemma algebraHammockGraphInclusion_colimitNormalization (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) :
    algebraHammockGraphInclusion A w X Y ≫ algebraHammockColimitNormalization A X Y =
      algebraHammockGraphNormalization A X Y w := by
  let := modelCategory A
  exact Hammock.graphInclusion_colimitNormalization (weakEquivalences (operad A).Algebra) X Y w

/-- 元の全語の余極限と、元の縮約済み hammock の単体集合としての実同型。 -/
def algebraHammockReducedColimitIso :
    algebraHammockColimitGraph A X Y ≅ algebraHammockReducedSimplicialSet A X Y := by
  let := modelCategory A
  exact Hammock.reducedColimitIso (weakEquivalences (operad A).Algebra) X Y

lemma algebraHammockReducedColimitIso_hom_fac (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) :
    algebraHammockGraphInclusion A w X Y ≫ (algebraHammockReducedColimitIso A X Y).hom =
      algebraHammockGraphNormalization A X Y w := by
  let := modelCategory A
  exact Hammock.reducedColimitIso_hom_fac (weakEquivalences (operad A).Algebra) X Y w

lemma algebraHammockReducedColimitIso_inv :
    (algebraHammockReducedColimitIso A X Y).inv = algebraHammockReducedAugmentation A X Y := rfl

lemma algebraHammockRawAugmentation_colimitNormalization :
    algebraHammockRawAugmentation A X Y ≫ algebraHammockColimitNormalization A X Y =
      algebraHammockNormalization A X Y := by
  let := modelCategory A
  exact Hammock.rawAugmentation_colimitNormalization (weakEquivalences (operad A).Algebra) X Y

end SerrePositivity.EInfinity.BarrattEccles
