module

public import SerrePositivity.HomotopicalAlgebra.Rectification.CategoryTheory.AnchoredChainTransport
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.AllFactorizationComparison
public import SerrePositivity.HomotopicalAlgebra.Simplicial.LargeParameterHomotopy

/-!
# 中断した任意モデル源への一般化：AllFactorizationPost

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：One postcomposition homotopy on all factorization chains。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0053][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0053
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# One postcomposition homotopy on all factorization chains

Both maps are the actual existing families: the new global family along
the transported chain, and the old global family followed by strict
postcomposition. A single large-parameter homotopy compares them.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra
open SerrePositivity.SimplicialModel
open SerrePositivity.HomotopyFunctionComplex.CoherentLiftRelative

namespace SerrePositivity.HomotopyFunctionComplex.AllFactorizationPost
variable {C : Type u} [Category.{v} C] [ModelCategory C] [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  {X Y V W : ResolutionObject C} (f : X.base ⟶ Y.base) (g : Y ⟶ V) (b : V ⟶ W)

abbrev choiceSpace : SSet.{v} := postChoiceSpace X Y W f (g ≫ b)

abbrev direct : AnchoredChain.simplicial g ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{u} (choiceSpace f g b) :=
  AnchoredChain.mapFunctor (ArrowFactorization.postTo g b (g ≫ b) rfl) ≫
    AllFactorizationComparison.chainComparison hcof hfib f (g ≫ b)

abbrev transported : AnchoredChain.simplicial g ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{u} (choiceSpace f g b) :=
  AllFactorizationComparison.chainComparison hcof hfib f g ≫
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map (CoherentLiftPostComposition.firstMap hcof X Y V W f g b)

include hcof hfib in
lemma fillers : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.BoundaryFillers (choiceSpace f g b) :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.relativeFillers hcof hfib (vertexInclusion X Y f)
    (postBoundary X Y W f (g ≫ b))
    (ResolutionLiftSpace.projection X W (f ≫ (g ≫ b).base))
    (ResolutionLiftSpace.projection_trivialFibration hcof X W (f ≫ (g ≫ b).base))

def homotopy : SSet.Homotopy (direct hcof hfib f g b) (transported hcof hfib f g b) :=
  LargeParameterHomotopy.homotopy (fillers hcof hfib f g b)
    (direct hcof hfib f g b) (transported hcof hfib f g b)

/-- Finite values of the global homotopy remain in the original Hom universe. -/
def simplex {n : ℕ} (c : AnchoredChain g n)
    (t : (SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 1)).obj
      (Opposite.op (SimplexCategory.mk n))) :
    SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ⟶ choiceSpace f g b :=
  SSet.yonedaEquiv.symm
    ((((homotopy hcof hfib f g b).h).app (Opposite.op (SimplexCategory.mk n)) (c, t)).down)

lemma simplex_fixed_boundary {n : ℕ} (c : AnchoredChain g n)
    (t : (SSet.stdSimplex.{max u v}.obj (SimplexCategory.mk 1)).obj
      (Opposite.op (SimplexCategory.mk n))) :
    vertexInclusion X Y f ▷ SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ≫
      RelativeChoiceSpace.family (vertexInclusion X Y f) (postBoundary X Y W f (g ≫ b))
        (simplex hcof hfib f g b c t) =
      vertices X Y f ◁ (SSet.stdSimplex.isTerminalObj₀.from _ ≫
        RelativeChoiceSpace.pointUnitIso.hom) ≫ (ρ_ _).hom ≫ postBoundary X Y W f (g ≫ b) :=
  RelativeChoiceSpace.family_fixed_boundary _ _ _

end SerrePositivity.HomotopyFunctionComplex.AllFactorizationPost
