module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarWordPresentation
public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.WordPresentationAction

/-!
# 中断した任意モデル源への一般化：OrdinaryBarWordAction

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Simplicial word-arrow families act on the native small ordinary bar values。

## 方針（定義・証明）
自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0237][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0237
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Simplicial word-arrow families act on the native small ordinary bar values

Every actual presented arrow is allowed. The small parameter, values, and
resulting family remain in the original Hom universe. Only the auxiliary
word Hom and simplex parameter may live in the larger universe.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarWordAction
open FreeGeneratorCategories OrdinaryBarFreeResolutionSeed OrdinaryBarChoiceBoundaryGluing
open OrdinaryBarRetractSystem
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (P : SSet.{max u v}) (n : ℕ)

abbrev hom (X Y : degree (D C) (n + 1)) :=
  WordPresentationDiagram.smallHom.{u, max u v, max u v} (degree (D C) (n + 1)) X Y

variable {T : SSet.{v}} (j : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ parameters P n)

def family {X Y : degree (D C) (n + 1)}
    (f : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ hom (C := C) n X Y) :
    small hcof hfib X ⊗ T ⟶ small hcof hfib Y where
  app k := ↾fun x =>
    ((OrdinaryBarWordPresentation.realization (C := C) hcof hfib P n k
      (j.app k (ULift.up x.2))).functor.map
      (f.app k (ULift.up x.2)) (ULift.up x.1)).down
  naturality {k l} θ := by
    apply ConcreteCategory.hom_ext
    intro x
    have hj := types_congr_hom (j.naturality θ) (ULift.up x.2)
    have hf := types_congr_hom (f.naturality θ) (ULift.up x.2)
    change j.app l (ULift.up (T.map θ x.2)) =
      (parameters P n).map θ (j.app k (ULift.up x.2)) at hj
    change f.app l (ULift.up (T.map θ x.2)) =
      (hom (C := C) n X Y).map θ (f.app k (ULift.up x.2)) at hf
    have hh := WordPresentationNaturality.small_naturality
      (OrdinaryBarFreeAmbientFamilies.fixedAction (C := C) hcof hfib P n)
      (lifted (C := C) hcof hfib) (section_ (C := C) hcof hfib)
      (projection (C := C) hcof hfib) (section_fac (C := C) hcof hfib)
      (contraction (C := C) hcof hfib) (contraction_over (C := C) hcof hfib)
      (contraction_on_section (C := C) hcof hfib) θ (j.app k (ULift.up x.2)) X Y
      (f.app k (ULift.up x.2)) (ULift.up x.1)
    change ((OrdinaryBarWordPresentation.realization (C := C) hcof hfib P n l
      (j.app l (ULift.up (T.map θ x.2)))).functor.map
        (f.app l (ULift.up (T.map θ x.2)))
        (ULift.up ((small hcof hfib X).map θ x.1))).down = _
    rw [hj, hf]
    exact congrArg ULift.down hh.symm

lemma family_substitute {U : SSet.{v}} (i : U ⟶ T) {X Y : degree (D C) (n + 1)}
    (f : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ hom (C := C) n X Y) :
    family hcof hfib P n (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ j) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ f) =
      ParameterComposition.substitute i (family hcof hfib P n j f) := by
  ext k x
  rfl

lemma family_identity (X : degree (D C) (n + 1)) :
    family hcof hfib P n j
      (SSet.stdSimplex.isTerminalObj₀.from _ ≫ WordPresentationDiagram.identity _ X) =
      fst (small hcof hfib X) T := by
  ext k x
  change ((OrdinaryBarWordPresentation.realization (C := C) hcof hfib P n k
    (j.app k (ULift.up x.2))).functor.map
      (𝟙 ((RetractWords.quotient (degree (D C) (n + 1))
        (WordSegment.degree.{max u v} k)).obj (.small X))) (ULift.up x.1)).down = x.1
  rw [CategoryTheory.Functor.map_id]
  rfl

lemma family_comp {X Y Z : degree (D C) (n + 1)}
    (f : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ hom (C := C) n X Y)
    (g : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ hom (C := C) n Y Z) :
    ParameterComposition.comp (family hcof hfib P n j f) (family hcof hfib P n j g) =
      family hcof hfib P n j (lift f g ≫ WordPresentationDiagram.composition _ X Y Z) := by
  ext k x
  change _ = ((OrdinaryBarWordPresentation.realization (C := C) hcof hfib P n k
    (j.app k (ULift.up x.2))).functor.map
      (f.app k (ULift.up x.2) ≫ g.app k (ULift.up x.2)) (ULift.up x.1)).down
  rw [CategoryTheory.Functor.map_comp]
  rfl

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarWordAction
