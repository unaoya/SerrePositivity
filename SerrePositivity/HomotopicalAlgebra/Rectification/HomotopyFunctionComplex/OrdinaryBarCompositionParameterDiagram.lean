module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarCompositionReindexLaws
public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.ComparisonTriangleParameterDiagram

/-!
# 中断した任意モデル源への一般化：OrdinaryBarCompositionParameterDiagram

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：The strict small restriction diagram of actual native composition triangles。

## 方針（定義・証明）
bar型の鎖パラメータと整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0150][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0150
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# The strict small restriction diagram of actual native composition triangles

A root triangle supplies one natural point, and whole root choice families
supply natural families. This is a parameter diagram, not yet the RMap
bifunctor on the original model category.
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

abbrev compositionParameterDiagram : (Over T)ᵒᵖ ⥤ SSet.{v} :=
  ComparisonTriangleParameterDiagram.diagram
    (nativeRestrictionComparison hcof hfib P j
      (lift f g ≫ OrdinaryBarFixedWordResolution.composition C X Y Z) e)
    (compositionComparison hcof hfib P j f g c d)

abbrev compositionParameterPoint :
    (Functor.const (Over T)ᵒᵖ).obj (SSet.stdSimplex.obj (SimplexCategory.mk 0)) ⟶
      compositionParameterDiagram hcof hfib P j f g c d e :=
  ComparisonTriangleParameterDiagram.point _ _ (compositionTriangle hcof hfib P j f g c d e)

abbrev compositionParameterFamily {L : SSet.{v}}
    (q : L ⟶ compositionChoices hcof hfib P j f g c d e) :=
  ComparisonTriangleParameterDiagram.family
    (nativeRestrictionComparison hcof hfib P j
      (lift f g ≫ OrdinaryBarFixedWordResolution.composition C X Y Z) e)
    (compositionComparison hcof hfib P j f g c d) q

lemma compositionParameterPoint_family : compositionParameterPoint hcof hfib P j f g c d e =
    compositionParameterFamily hcof hfib P j f g c d e
      (selectedCompositionPoint hcof hfib P j f g c d e) := rfl

lemma compositionParameterPoint_naturality {σ τ : (Over T)ᵒᵖ} (φ : σ ⟶ τ) :
    (compositionParameterPoint hcof hfib P j f g c d e).app σ ≫
      (compositionParameterDiagram hcof hfib P j f g c d e).map φ =
        (compositionParameterPoint hcof hfib P j f g c d e).app τ :=
  ((compositionParameterPoint hcof hfib P j f g c d e).naturality φ).symm.trans
    (Category.id_comp _)

def compositionParameterObjectIso (σ : (Over T)ᵒᵖ) :
    (compositionParameterDiagram hcof hfib P j f g c d e).obj σ ≅
    compositionChoices hcof hfib P (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map σ.unop.hom ≫ j)
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map σ.unop.hom ≫ f) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map σ.unop.hom ≫ g)
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map σ.unop.hom ≫ c) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map σ.unop.hom ≫ d)
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map σ.unop.hom ≫ e) :=
  eqToIso (congrArg (fun b => RelativeChoiceSpace.obj (SSet.horn 2 2).ι b)
    (ComparisonTriangleTransport.hornMap_post _ _ _ _ ((pre σ.unop.hom).app _)
      (compositeComparison_reindex hcof hfib P j f g e σ.unop.hom)
      (inputComparison_reindex hcof hfib P j f g c d σ.unop.hom)))

lemma compositionParameterObject_boundary_rlp (σ : (Over T)ᵒᵖ) : SSet.modelCategoryQuillen.I.rlp
    (terminal.from ((compositionParameterDiagram hcof hfib P j f g c d e).obj σ)) :=
  ComparisonTriangleParameterDiagram.object_boundary_rlp _ _
    (SimplexParameterHom.native_kan _ _ (OrdinaryBarSmallReference.value_kan hcof hfib Z)) σ

abbrev compositionParameterEvaluation {L : SSet.{v}}
    (q : L ⟶ compositionChoices hcof hfib P j f g c d e) (σ : (Over T)ᵒᵖ) :=
  ComparisonTriangleParameterDiagram.evaluated
    (nativeRestrictionComparison hcof hfib P j
      (lift f g ≫ OrdinaryBarFixedWordResolution.composition C X Y Z) e)
    (compositionComparison hcof hfib P j f g c d) q σ

lemma compositionParameterEvaluation_restriction {L : SSet.{v}}
    (q : L ⟶ compositionChoices hcof hfib P j f g c d e) (σ : (Over T)ᵒᵖ) :
    compositionParameterEvaluation hcof hfib P j f g c d e q σ =
      σ.unop.hom ▷ (SSet.stdSimplex.obj (SimplexCategory.mk 2) ⊗ L) ≫
        compositionChoiceFamily hcof hfib P j f g c d e q :=
  ComparisonTriangleParameterDiagram.evaluated_restriction _ _ _ _

lemma compositionParameterFamily_extension {U V : SSet.{v}} (i : U ⟶ V) [Mono i]
    (q : U ⟶ compositionChoices hcof hfib P j f g c d e) :
    ∃ r : V ⟶ compositionChoices hcof hfib P j f g c d e, i ≫ r = q ∧
      (Functor.const (Over T)ᵒᵖ).map i ≫ compositionParameterFamily hcof hfib P j f g c d e r =
        compositionParameterFamily hcof hfib P j f g c d e q :=
  ComparisonTriangleParameterDiagram.family_relative_extension _ _
    (SimplexParameterHom.native_kan _ _ (OrdinaryBarSmallReference.value_kan hcof hfib Z)) i q

abbrev compositionParameterPointOf (a : compositionTriangleData hcof hfib P j f g c d e) :=
  ComparisonTriangleParameterDiagram.point
    (nativeRestrictionComparison hcof hfib P j
      (lift f g ≫ OrdinaryBarFixedWordResolution.composition C X Y Z) e)
    (compositionComparison hcof hfib P j f g c d) a

abbrev compositionParameterPointInterval
    (a b : compositionTriangleData hcof hfib P j f g c d e) :=
  ComparisonTriangleParameterDiagram.pointInterval
    (nativeRestrictionComparison hcof hfib P j
      (lift f g ≫ OrdinaryBarFixedWordResolution.composition C X Y Z) e)
    (compositionComparison hcof hfib P j f g c d)
    (SimplexParameterHom.native_kan _ _ (OrdinaryBarSmallReference.value_kan hcof hfib Z)) a b

lemma compositionParameterPointInterval_zero
    (a b : compositionTriangleData hcof hfib P j f g c d e) :
    (Functor.const (Over T)ᵒᵖ).map (SSet.stdSimplex.δ (1 : Fin 2)) ≫
      compositionParameterPointInterval hcof hfib P j f g c d e a b =
        compositionParameterPointOf hcof hfib P j f g c d e a :=
  ComparisonTriangleParameterDiagram.pointInterval_zero _ _ _ _ _

lemma compositionParameterPointInterval_one
    (a b : compositionTriangleData hcof hfib P j f g c d e) :
    (Functor.const (Over T)ᵒᵖ).map (SSet.stdSimplex.δ (0 : Fin 2)) ≫
      compositionParameterPointInterval hcof hfib P j f g c d e a b =
        compositionParameterPointOf hcof hfib P j f g c d e b :=
  ComparisonTriangleParameterDiagram.pointInterval_one _ _ _ _ _

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarRelativeHomDescent
