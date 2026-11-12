module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarClosedHomDescent
public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.RestrictionDescentChoices

/-!
# 中断した任意モデル源への一般化：OrdinaryBarRelativeHomDescent

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Relative descent choices for the actual whole word action。

## 方針（定義・証明）
整合図式の値変更による厳密化と宇宙縮小の問題に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0211][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0211
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Relative descent choices for the actual whole word action

The same global comparison interval supplies every parameter family.
Prescribed boundaries extend strictly in this choice space. Native
parameter evaluations still land in the original small internal Hom.
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
open OrdinaryBarDiagonalHomAugmentation
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
  (P : SSet.{max u v})

abbrev parameterAugmentation (X Y : D C) := P ◁ smallAugmentation C X Y

omit [HomotopicalAlgebra.ModelCategory C] [HomotopicalAlgebra.ModelCategory SSet.{v}] in
lemma parameterAugmentation_isIso (X Y : D C) :
    IsIso (AnodyneHomotopy.anodyneQ.map (parameterAugmentation P X Y)) :=
  AnodyneHomotopy.whiskerLeft_anodyneQ_isIso _
    (OrdinaryBarSourceContraction.small_augmentation_isIso C X Y) P

abbrev choices (X Y : D C) : SSet.{max u v} :=
  RestrictionDescentChoices.obj (parameterAugmentation P X Y)
    (OrdinaryBarDiagonalClosedAction.mapping hcof hfib P X Y)

lemma choices_boundary_rlp (X Y : D C) : SSet.modelCategoryQuillen.I.rlp
    (terminal.from (choices hcof hfib P X Y)) :=
  RestrictionDescentChoices.boundary_rlp _ _

lemma choices_kan (X Y : D C) : SSet.modelCategoryQuillen.J.rlp
    (terminal.from (choices hcof hfib P X Y)) :=
  RestrictionDescentChoices.kan _ _

def family {T : SSet.{max u v}} {X Y : D C} (c : T ⟶ choices hcof hfib P X Y) :
    (P ⊗ baseHom C X Y) ⊗ T ⟶
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} ((ihom (small hcof hfib X)).obj (small hcof hfib Y)) :=
  RestrictionDescentChoices.family (parameterAugmentation P X Y)
    (parameterAugmentation_isIso P X Y) (OrdinaryBarClosedHomDescent.target_kan hcof hfib X Y)
    (OrdinaryBarDiagonalClosedAction.mapping hcof hfib P X Y) c

lemma family_naturality {T U : SSet.{max u v}} {X Y : D C}
    (c : T ⟶ choices hcof hfib P X Y) (j : U ⟶ T) :
    family hcof hfib P (j ≫ c) = (P ⊗ baseHom C X Y) ◁ j ≫ family hcof hfib P c :=
  RestrictionDescentChoices.family_naturality _ _ _ _ _ _

abbrev comparison {T : SSet.{max u v}} {X Y : D C}
    (c : T ⟶ choices hcof hfib P X Y) :=
  RestrictionDescentChoices.parameterComparison (parameterAugmentation P X Y)
    (parameterAugmentation_isIso P X Y) (OrdinaryBarClosedHomDescent.target_kan hcof hfib X Y)
    (OrdinaryBarDiagonalClosedAction.mapping hcof hfib P X Y) c

abbrev familyComparison {T : SSet.{max u v}} {X Y : D C}
    (c : T ⟶ choices hcof hfib P X Y) :=
  RestrictionDescentChoices.familyComparison (parameterAugmentation P X Y)
    (parameterAugmentation_isIso P X Y) (OrdinaryBarClosedHomDescent.target_kan hcof hfib X Y)
    (OrdinaryBarDiagonalClosedAction.mapping hcof hfib P X Y) c

lemma comparison_naturality {T U : SSet.{max u v}} {X Y : D C}
    (c : T ⟶ choices hcof hfib P X Y) (j : U ⟶ T) :
    (comparison hcof hfib P (j ≫ c)).h =
      j ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫ (comparison hcof hfib P c).h :=
  RestrictionDescentChoices.parameterComparison_naturality _ _ _ _ _ _

lemma relative_extension {U V : SSet.{max u v}} {X Y : D C} (j : U ⟶ V) [Mono j]
    (c : U ⟶ choices hcof hfib P X Y) : ∃ e : V ⟶ choices hcof hfib P X Y,
      j ≫ e = c ∧ (P ⊗ baseHom C X Y) ◁ j ≫ family hcof hfib P e = family hcof hfib P c ∧
        j ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫
          (comparison hcof hfib P e).h = (comparison hcof hfib P c).h :=
  RestrictionDescentChoices.relative_extension _ _ _ _ _ _

def nativeFamily {T : SSet.{v}} {X Y : D C} (j : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ P)
    (f : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ baseHom C X Y)
    (c : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ choices hcof hfib P X Y) :
    T ⟶ (ihom (small hcof hfib X)).obj (small hcof hfib Y) :=
  _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.lower (lift (lift j f) (𝟙 _) ≫ family hcof hfib P c)

lemma nativeFamily_substitute {T U : SSet.{v}} {X Y : D C}
    (j : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ P)
    (f : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ baseHom C X Y)
    (c : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} T ⟶ choices hcof hfib P X Y) (i : U ⟶ T) :
    nativeFamily hcof hfib P (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ j) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ f)
        (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ c) = i ≫ nativeFamily hcof hfib P j f c := by
  apply (SSet.uliftFunctor.{max u v, v}).map_injective
  change lift (lift (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ j) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ f)) (𝟙 _) ≫
      family hcof hfib P (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ c) =
    _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ lift (lift j f) (𝟙 _) ≫ family hcof hfib P c
  rw [family_naturality, ← Category.assoc, lift_whiskerLeft]
  rw [Category.id_comp, ← Category.assoc, comp_lift, comp_lift, Category.comp_id]

lemma native_relative_extension {U V : SSet.{v}} {X Y : D C} (i : U ⟶ V) [Mono i]
    (j : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} V ⟶ P)
    (f : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} V ⟶ baseHom C X Y)
    (c : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} U ⟶ choices hcof hfib P X Y) :
    ∃ e : _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} V ⟶ choices hcof hfib P X Y,
      _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ e = c ∧ i ≫ nativeFamily hcof hfib P j f e =
        nativeFamily hcof hfib P (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ j) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i ≫ f) c := by
  have : Mono (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map.{max u v} i) := UniverseLift.mono_map i
  obtain ⟨e, he, _, _⟩ := relative_extension hcof hfib P (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.map i) c
  refine ⟨e, he, ?_⟩
  rw [← nativeFamily_substitute, he]

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarRelativeHomDescent
