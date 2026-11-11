module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarRelativeCompositionTriangle
public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.ComparisonTriangleChoices

/-!
# 中断した任意モデル源への一般化：OrdinaryBarCompositionChoices

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：All native composition triangles form a small relative extension space。

## 方針（定義・証明）
自明fibrationのファイバーと相対延長による選択の比較に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0149][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0149
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# All native composition triangles form a small relative extension space

The earlier selected triangle is a point of this space. Whole parameter
boundaries of triangles extend while the two original comparison edges
stay fixed throughout the extension.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
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

abbrev compositionChoices : SSet.{v} := ComparisonTriangleChoices.obj
  (nativeRestrictionComparison hcof hfib P j
    (lift f g ≫ OrdinaryBarFixedWordResolution.composition C X Y Z) e)
  (compositionComparison hcof hfib P j f g c d)

lemma compositionChoices_boundary_rlp : SSet.modelCategoryQuillen.I.rlp
    (terminal.from (compositionChoices hcof hfib P j f g c d e)) :=
  ComparisonTriangleChoices.boundary_rlp _ _
    (SimplexParameterHom.native_kan _ _ (OrdinaryBarSmallReference.value_kan hcof hfib Z))

lemma compositionChoices_kan : SSet.modelCategoryQuillen.J.rlp
    (terminal.from (compositionChoices hcof hfib P j f g c d e)) :=
  ComparisonTriangleChoices.kan _ _
    (SimplexParameterHom.native_kan _ _ (OrdinaryBarSmallReference.value_kan hcof hfib Z))

def selectedCompositionPoint : SSet.stdSimplex.obj (SimplexCategory.mk 0) ⟶
    compositionChoices hcof hfib P j f g c d e :=
  ComparisonTriangleChoices.ofData _ _ (compositionTriangle hcof hfib P j f g c d e)

def compositionChoiceFamily {L : SSet.{v}}
    (q : L ⟶ compositionChoices hcof hfib P j f g c d e) :
    T ⊗ (SSet.stdSimplex.obj (SimplexCategory.mk 2) ⊗ L) ⟶
      (ihom (small hcof hfib X)).obj (small hcof hfib Z) :=
  uncurry (ComparisonTriangleChoices.family _ _ q)

lemma compositionChoiceFamily_zero {L : SSet.{v}}
    (q : L ⟶ compositionChoices hcof hfib P j f g c d e) :
    T ◁ (SSet.stdSimplex.δ (0 : Fin 3) ▷ L) ≫
      compositionChoiceFamily hcof hfib P j f g c d e q =
    T ◁ fst (SSet.stdSimplex.obj (SimplexCategory.mk 1)) L ≫
      (compositionComparison hcof hfib P j f g c d).h := by
  rw [compositionChoiceFamily, ← uncurry_natural_left, ComparisonTriangleChoices.family_zero,
    uncurry_natural_left, uncurry_curry]

lemma compositionChoiceFamily_one {L : SSet.{v}}
    (q : L ⟶ compositionChoices hcof hfib P j f g c d e) :
    T ◁ (SSet.stdSimplex.δ (1 : Fin 3) ▷ L) ≫
      compositionChoiceFamily hcof hfib P j f g c d e q =
    T ◁ fst (SSet.stdSimplex.obj (SimplexCategory.mk 1)) L ≫
      (nativeRestrictionComparison hcof hfib P j
        (lift f g ≫ OrdinaryBarFixedWordResolution.composition C X Y Z) e).h := by
  rw [compositionChoiceFamily, ← uncurry_natural_left, ComparisonTriangleChoices.family_one,
    uncurry_natural_left, uncurry_curry]

lemma compositionChoiceFamily_selected :
    compositionChoiceFamily hcof hfib P j f g c d e
      (selectedCompositionPoint hcof hfib P j f g c d e) =
    T ◁ (SSet.stdSimplex.obj (SimplexCategory.mk 2) ◁ RelativeChoiceSpace.pointUnitIso.hom ≫
      (ρ_ (SSet.stdSimplex.obj (SimplexCategory.mk 2))).hom) ≫
        compositionTriangleFamily hcof hfib P j f g c d e := by
  rw [compositionChoiceFamily, selectedCompositionPoint, ComparisonTriangleChoices.ofData_family,
    ← Category.assoc, uncurry_natural_left]

lemma compositionChoices_relative_extension {U V : SSet.{v}} (i : U ⟶ V) [Mono i]
    (q : U ⟶ compositionChoices hcof hfib P j f g c d e) :
    ∃ r : V ⟶ compositionChoices hcof hfib P j f g c d e, i ≫ r = q ∧
      T ◁ (SSet.stdSimplex.obj (SimplexCategory.mk 2) ◁ i) ≫
        compositionChoiceFamily hcof hfib P j f g c d e r =
          compositionChoiceFamily hcof hfib P j f g c d e q := by
  obtain ⟨r, hr, hfamily⟩ := ComparisonTriangleChoices.relative_extension _ _
    (SimplexParameterHom.native_kan _ _ (OrdinaryBarSmallReference.value_kan hcof hfib Z)) i q
  refine ⟨r, hr, ?_⟩
  rw [compositionChoiceFamily, ← uncurry_natural_left, hfamily]
  rfl

abbrev compositionTriangleData := KanComparisonTriangle.Data
  (nativeRestrictionComparison hcof hfib P j
    (lift f g ≫ OrdinaryBarFixedWordResolution.composition C X Y Z) e)
  (compositionComparison hcof hfib P j f g c d)

abbrev comparisonOfCompositionTriangles
    (a b : compositionTriangleData hcof hfib P j f g c d e) :=
  ComparisonTriangleChoices.fixedBoundaryComparison _ _
    (SimplexParameterHom.native_kan _ _ (OrdinaryBarSmallReference.value_kan hcof hfib Z)) a b

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarRelativeHomDescent
