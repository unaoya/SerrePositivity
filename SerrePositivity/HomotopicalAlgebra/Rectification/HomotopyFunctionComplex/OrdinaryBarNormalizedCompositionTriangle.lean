module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarCompositionReindex
public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.NormalizedComparisonTriangle

/-!
# 中断した任意モデル源への一般化：OrdinaryBarNormalizedCompositionTriangle

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Native composition triangles now admit a strictly parameter-natural choice。

## 方針（定義・証明）
全hornを用いたKan空間の高次ホモトピーの整合化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0202][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0202
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Native composition triangles now admit a strictly parameter-natural choice

The normalized horn operation is chosen in the original small internal
Hom, independently of T. The selected whole triangle and its comparison
edge therefore reindex strictly with all native inputs. Previous chosen
triangles are compared while fixing their two specified whole edges.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalClosed
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarRelativeHomDescent
open OrdinaryBarFreeResolutionSeed OrdinaryBarRetractSystem
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (P : SSet.{max u v}) {T : SSet.{v}} {X Y Z : D C}
  (j : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ P)
  (f : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ OrdinaryBarFixedWordResolution.hom C X Y)
  (g : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ OrdinaryBarFixedWordResolution.hom C Y Z)
  (c : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ choices hcof hfib P X Y)
  (d : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ choices hcof hfib P Y Z)
  (e : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ choices hcof hfib P X Z)

local notation "F" => nativeRestrictionComparison hcof hfib P j
  (lift f g ≫ OrdinaryBarFixedWordResolution.composition C X Y Z) e
local notation "G" => compositionComparison hcof hfib P j f g c d
local notation "K" => CategoryTheory.Functor.obj (ihom (small hcof hfib X)) (small hcof hfib Z)
local notation "hK" => SimplexParameterHom.native_kan (small hcof hfib X) (small hcof hfib Z)
  (OrdinaryBarSmallReference.value_kan hcof hfib Z)

abbrev normalizedCompositionTriangle := NormalizedComparisonTriangle.build F G hK

abbrev normalizedNativeCompositionComparison :=
  KanComparisonTriangle.comparison F G (normalizedCompositionTriangle hcof hfib P j f g c d e)

variable {U : SSet.{v}} (i : U ⟶ T)

lemma normalizedCompositionTriangle_reindex :
    (normalizedCompositionTriangle hcof hfib P (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ j)
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ f) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ g)
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ c) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ d) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ e)).triangle =
    (normalizedCompositionTriangle hcof hfib P j f g c d e).triangle ≫ (pre i).app K := by
  have hb := ComparisonTriangleTransport.hornMap_post F G
    (nativeRestrictionComparison hcof hfib P (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ j)
      (lift (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ f) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ g) ≫
        OrdinaryBarFixedWordResolution.composition C X Y Z) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ e))
    (compositionComparison hcof hfib P (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ j) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ f)
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ g) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ c) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ d))
    ((pre i).app K) (compositeComparison_reindex hcof hfib P j f g e i)
    (inputComparison_reindex hcof hfib P j f g c d i)
  change NaturalHornFilling.fill K 2 (NormalizedTriangleHorn.section_ K 2 hK) _ = _
  rw [← hb]
  exact NaturalHornFilling.fill_reindex K 2 (NormalizedTriangleHorn.section_ K 2 hK)
    (KanComparisonTriangle.hornMap F G) i

lemma normalizedNativeCompositionComparison_reindex :
    (normalizedNativeCompositionComparison hcof hfib P (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ j)
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ f) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ g)
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ c) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ d) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ e)).h =
    i ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫
      (normalizedNativeCompositionComparison hcof hfib P j f g c d e).h := by
  change uncurry (SSet.stdSimplex.δ (2 : Fin 3) ≫
    (normalizedCompositionTriangle hcof hfib P (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ j)
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ f) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ g)
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ c) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ d) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ e)).triangle) = _
  rw [normalizedCompositionTriangle_reindex, ← Category.assoc]
  exact uncurry_pre_app K
    (SSet.stdSimplex.δ (2 : Fin 3) ≫
      (normalizedCompositionTriangle hcof hfib P j f g c d e).triangle) i

def normalizeCompositionTriangleComparison : RelativeChoiceSpace.FixedBoundaryHomotopy
    (SSet.horn 2 2).ι (KanComparisonTriangle.hornMap F G)
    (compositionTriangle hcof hfib P j f g c d e).triangle
    (normalizedCompositionTriangle hcof hfib P j f g c d e).triangle :=
  NormalizedComparisonTriangle.compare F G hK (compositionTriangle hcof hfib P j f g c d e)

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarRelativeHomDescent
