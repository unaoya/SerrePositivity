module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.CoherentLiftRelative
public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.RelativeChoiceBoundary

/-!
# 中断した任意モデル源への一般化：CoherentLiftFaces

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Higher comparison fillers from prescribed compatible composition faces。

## 方針（定義・証明）
全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0066][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0066
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Higher comparison fillers from prescribed compatible composition faces

Individual face comparisons, agreeing on their actual intersections, are
glued and filled. The filler retains every prescribed face and fixes all
strict lift vertices throughout its higher parameter. No unprovided whole
boundary map is required as an input.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.CoherentLiftRelative
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

include hcof hfib in
lemma post_fill_faces (X Y W : ResolutionObject C) (f : X.base ⟶ Y.base) (g : Y ⟶ W) (n : ℕ)
    (a : ∀ k, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.BoundaryGluing.facet n k).toSSet ⟶ postChoiceSpace X Y W f g)
    (ha : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.BoundaryGluing.Compatible a) :
    ∃ e : SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ⟶ postChoiceSpace X Y W f g,
      (∀ k, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.BoundaryGluing.facet n k).ι ≫ e = a k) ∧
      vertexInclusion X Y f ▷ SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ≫
          RelativeChoiceSpace.family (vertexInclusion X Y f) (postBoundary X Y W f g) e =
        vertices X Y f ◁ (SSet.stdSimplex.isTerminalObj₀.from _ ≫
          RelativeChoiceSpace.pointUnitIso.hom) ≫ (ρ_ _).hom ≫ postBoundary X Y W f g :=
  RelativeChoiceSpace.fill_faces hcof hfib _ _ (ResolutionLiftSpace.projection X W (f ≫ g.base))
    (ResolutionLiftSpace.projection_trivialFibration hcof X W (f ≫ g.base)) n a ha

include hcof hfib in
lemma pre_fill_faces (X Y W : ResolutionObject C) (f : X ⟶ Y) (g : Y.base ⟶ W.base) (n : ℕ)
    (a : ∀ k, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.BoundaryGluing.facet n k).toSSet ⟶ preChoiceSpace X Y W f g)
    (ha : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.BoundaryGluing.Compatible a) :
    ∃ e : SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ⟶ preChoiceSpace X Y W f g,
      (∀ k, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.BoundaryGluing.facet n k).ι ≫ e = a k) ∧
      vertexInclusion Y W g ▷ SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ≫
          RelativeChoiceSpace.family (vertexInclusion Y W g) (preBoundary X Y W f g) e =
        vertices Y W g ◁ (SSet.stdSimplex.isTerminalObj₀.from _ ≫
          RelativeChoiceSpace.pointUnitIso.hom) ≫ (ρ_ _).hom ≫ preBoundary X Y W f g :=
  RelativeChoiceSpace.fill_faces hcof hfib _ _ (ResolutionLiftSpace.projection X W (f.base ≫ g))
    (ResolutionLiftSpace.projection_trivialFibration hcof X W (f.base ≫ g)) n a ha

end SerrePositivity.HomotopyFunctionComplex.CoherentLiftRelative
