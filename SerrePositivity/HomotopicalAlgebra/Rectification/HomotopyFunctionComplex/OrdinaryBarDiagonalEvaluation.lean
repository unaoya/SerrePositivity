module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarFixedWordEvaluation
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarFixedWordResolution

/-!
# 中断した任意モデル源への一般化：OrdinaryBarDiagonalEvaluation

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Actual diagonal word families evaluated on the native small bar values。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0157][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0157
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Actual diagonal word families evaluated on the native small bar values
-/

@[expose] public section
universe v u r
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarDiagonalEvaluation
open FreeGeneratorCategories OrdinaryBarFreeResolutionSeed
open OrdinaryBarRetractSystem OrdinaryBarFixedSource

abbrev parameters (P : SSet.{r}) (n : SimplexCategoryᵒᵖ) :=
  OrdinaryBarFreeResolutionAction.parameters P n

def generic (n : SimplexCategoryᵒᵖ) :
    (SSet.stdSimplex.obj n.unop).obj n := SSet.stdSimplex.objEquiv.symm (𝟙 n.unop)

def point {P : SSet.{r}} (n : SimplexCategoryᵒᵖ) (x : P.obj n) : (parameters P n).obj n :=
  (x, generic n)

lemma point_naturality {P : SSet.{r}} {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) (x : P.obj n) :
    (parameters P n).map θ (point n x) =
      (P ◁ SSet.stdSimplex.map θ.unop).app m (point m (P.map θ x)) := by
  rfl

variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (P : SSet.{max u v}) {T : SSet.{v}} (j : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ P)

abbrev evaluation (n : SimplexCategoryᵒᵖ) (x : P.obj n) :=
  (OrdinaryBarWordPresentation.realization (C := C) hcof hfib P n.unop.len n (point n x)).functor

lemma evaluation_naturality {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m) (z : P.obj n)
    (X Y : D C) (f : (OrdinaryBarFixedWordResolution.hom C X Y).obj n)
    (x : (lifted hcof hfib X).obj n) :
    (lifted hcof hfib Y).map θ ((evaluation hcof hfib P n z).map f x) =
      (evaluation hcof hfib P m (P.map θ z)).map
        ((OrdinaryBarFixedWordResolution.hom C X Y).map θ f)
        ((lifted hcof hfib X).map θ x) := by
  have hr := congr($(OrdinaryBarFixedWordResolution.map_functor_reverse C θ).map f)
  have he := congr($(OrdinaryBarFixedWordEvaluation.evaluation_map (C := C) hcof hfib P θ m
    (point m (P.map θ z))).map
      ((WordPresentationDiagram.smallHom.{u, max u v, max u v}
        (degree (D C) (n.unop.len + 1)) X Y).map θ f))
  have hh := WordPresentationNaturality.small_naturality
    (OrdinaryBarFreeAmbientFamilies.fixedAction (C := C) hcof hfib P n.unop.len)
    (lifted (C := C) hcof hfib) (section_ (C := C) hcof hfib)
    (projection (C := C) hcof hfib) (section_fac (C := C) hcof hfib)
    (contraction (C := C) hcof hfib) (contraction_over (C := C) hcof hfib)
    (contraction_on_section (C := C) hcof hfib) θ (point n z) X Y f x
  rw [point_naturality] at hh
  change _ = (evaluation hcof hfib P m (P.map θ z)).map
    (((OrdinaryBarFixedWordResolution.diagram C).map θ).toFunctor.map f)
    ((lifted hcof hfib X).map θ x)
  rw [hr]
  exact hh.trans (types_congr_hom he ((lifted hcof hfib X).map θ x)).symm

def family {X Y : D C}
    (f : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ OrdinaryBarFixedWordResolution.hom C X Y) :
    small hcof hfib X ⊗ T ⟶ small hcof hfib Y where
  app n := ↾fun x =>
    (evaluation hcof hfib P n (j.app n (ULift.up x.2))
      |>.map (f.app n (ULift.up x.2)) (ULift.up x.1)).down
  naturality {n m} θ := by
    apply ConcreteCategory.hom_ext
    intro x
    have hj := types_congr_hom (j.naturality θ) (ULift.up x.2)
    change j.app m (ULift.up (T.map θ x.2)) = P.map θ (j.app n (ULift.up x.2)) at hj
    have hf := types_congr_hom (f.naturality θ) (ULift.up x.2)
    change f.app m (ULift.up (T.map θ x.2)) =
      ((OrdinaryBarFixedWordResolution.diagram C).map θ).toFunctor.map
        (f.app n (ULift.up x.2)) at hf
    have hh := evaluation_naturality hcof hfib P θ (j.app n (ULift.up x.2))
      X Y (f.app n (ULift.up x.2)) (ULift.up x.1)
    change (evaluation hcof hfib P m (j.app m (ULift.up (T.map θ x.2))) |>.map
      (f.app m (ULift.up (T.map θ x.2)))
      (ULift.up ((small hcof hfib X).map θ x.1))).down = _
    rw [hj, hf]
    exact congrArg ULift.down hh.symm

lemma family_substitute {U : SSet.{v}} (i : U ⟶ T) {X Y : D C}
    (f : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ OrdinaryBarFixedWordResolution.hom C X Y) :
    family hcof hfib P (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ j) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ f) =
      ParameterComposition.substitute i (family hcof hfib P j f) := by
  ext n x
  rfl

lemma family_identity (X : D C) :
    family hcof hfib P j
      (SSet.stdSimplex.isTerminalObj₀.from _ ≫ OrdinaryBarFixedWordResolution.identity C X) =
      fst (small hcof hfib X) T := by
  ext n x
  change (evaluation hcof hfib P n (j.app n (ULift.up x.2)) |>.map
    (𝟙 ((RetractWords.quotient (degree (D C) (n.unop.len + 1))
      (WordSegment.degree.{max u v} n)).obj (.small X))) (ULift.up x.1)).down = x.1
  rw [CategoryTheory.Functor.map_id]
  rfl

lemma family_comp {X Y Z : D C}
    (f : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ OrdinaryBarFixedWordResolution.hom C X Y)
    (g : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ OrdinaryBarFixedWordResolution.hom C Y Z) :
    ParameterComposition.comp (family hcof hfib P j f) (family hcof hfib P j g) =
      family hcof hfib P j (lift f g ≫ OrdinaryBarFixedWordResolution.composition C X Y Z) := by
  ext n x
  change _ = (evaluation hcof hfib P n (j.app n (ULift.up x.2)) |>.map
    (f.app n (ULift.up x.2) ≫ g.app n (ULift.up x.2)) (ULift.up x.1)).down
  rw [CategoryTheory.Functor.map_comp]
  rfl

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarDiagonalEvaluation
