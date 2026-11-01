module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarChoiceComposition
public import SerrePositivity.HomotopicalAlgebra.Simplicial.ParameterCategory

/-!
# 中断した任意モデル源への一般化：OrdinaryBarChoiceCategory

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Actual categories of whole parameterized lifts of the original Kan bar action。

## 方針（定義・証明）
自明fibrationのファイバーと相対延長による選択の比較に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0140][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0140
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Actual categories of whole parameterized lifts of the original Kan bar action

A morphism retains its original base arrow and its entire relative extension
family. Projection and ambient evaluation are strict functors. No strict
section of the projection is assumed or constructed here.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarChoiceCategory
open OrdinaryBarRetractSystem
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

structure Object
    (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
    (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)
    (T : SSet.{max u v}) where
  base : Cᵒᵖ × C

structure Hom {T : SSet.{max u v}} (X Y : Object (C := C) hcof hfib T) where
  base : X.base ⟶ Y.base
  extension : T ⟶ choices hcof hfib base

lemma hom_ext {T : SSet.{max u v}} {X Y : Object (C := C) hcof hfib T} (f g : Hom hcof hfib X Y)
    (hb : f.base = g.base)
    (he : RelativeChoiceSpace.family _ _ f.extension =
      RelativeChoiceSpace.family _ _ g.extension) : f = g := by
  cases f with | mk f s =>
    cases g with | mk g t =>
      dsimp only at hb he
      subst g
      have hst := RelativeChoiceSpace.family_injective _ _ he
      subst t
      rfl

instance (T : SSet.{max u v}) : Category.{max u v} (Object (C := C) hcof hfib T) where
  Hom X Y := Hom hcof hfib X Y
  id X := ⟨𝟙 X.base, OrdinaryBarChoiceComposition.identity hcof hfib X.base T⟩
  comp f g := ⟨f.base ≫ g.base,
    OrdinaryBarChoiceComposition.compose hcof hfib f.base g.base f.extension g.extension⟩
  id_comp f := hom_ext hcof hfib _ _ (Category.id_comp f.base)
    (OrdinaryBarChoiceComposition.left_unit_family hcof hfib f.base f.extension)
  comp_id f := hom_ext hcof hfib _ _ (Category.comp_id f.base)
    (OrdinaryBarChoiceComposition.right_unit_family hcof hfib f.base f.extension)
  assoc f g h := hom_ext hcof hfib _ _ (Category.assoc f.base g.base h.base)
    (OrdinaryBarChoiceComposition.associativity_family hcof hfib f.base g.base h.base
      f.extension g.extension h.extension)

def projection (T : SSet.{max u v}) : Object (C := C) hcof hfib T ⥤ Cᵒᵖ × C where
  obj X := X.base
  map f := f.base

def evaluation (T : SSet.{max u v}) : Object (C := C) hcof hfib T ⥤ ParameterCategory.Object T where
  obj X := ⟨ambient hcof hfib X.base⟩
  map f := RelativeChoiceSpace.family _ _ f.extension
  map_id X := OrdinaryBarChoiceComposition.identity_family hcof hfib X.base T
  map_comp f g := OrdinaryBarChoiceComposition.compose_family hcof hfib
    f.base g.base f.extension g.extension

def reindex {T U : SSet.{max u v}} (j : U ⟶ T) :
    Object (C := C) hcof hfib T ⥤ Object (C := C) hcof hfib U where
  obj X := ⟨X.base⟩
  map f := ⟨f.base, j ≫ f.extension⟩
  map_id X := by
    apply hom_ext hcof hfib
    · rfl
    · change RelativeChoiceSpace.family _ _
        (j ≫ OrdinaryBarChoiceComposition.identity hcof hfib X.base T) =
          RelativeChoiceSpace.family _ _ (OrdinaryBarChoiceComposition.identity hcof hfib X.base U)
      rw [RelativeChoiceSpace.family_naturality,
        OrdinaryBarChoiceComposition.identity_family, OrdinaryBarChoiceComposition.identity_family]
      ext n x
      rfl
  map_comp f g := by
    apply hom_ext hcof hfib
    · rfl
    · change RelativeChoiceSpace.family _ _
        (j ≫ OrdinaryBarChoiceComposition.compose hcof hfib f.base g.base f.extension g.extension) =
          RelativeChoiceSpace.family _ _
            (OrdinaryBarChoiceComposition.compose hcof hfib f.base g.base
              (j ≫ f.extension) (j ≫ g.extension))
      rw [RelativeChoiceSpace.family_naturality, OrdinaryBarChoiceComposition.compose_family,
        OrdinaryBarChoiceComposition.compose_family, RelativeChoiceSpace.family_naturality,
        RelativeChoiceSpace.family_naturality]
      exact ParameterComposition.substitute_comp j _ _

lemma reindex_projection {T U : SSet.{max u v}} (j : U ⟶ T) :
    reindex (C := C) hcof hfib j ⋙ projection hcof hfib U = projection hcof hfib T := rfl

lemma reindex_evaluation {T U : SSet.{max u v}} (j : U ⟶ T) :
    reindex (C := C) hcof hfib j ⋙ evaluation hcof hfib U =
      evaluation hcof hfib T ⋙ ParameterCategory.reindex j := by
  apply CategoryTheory.Functor.ext (fun _ => rfl)

lemma reindex_id (T : SSet.{max u v}) :
    reindex (C := C) hcof hfib (𝟙 T) = 𝟭 (Object (C := C) hcof hfib T) := by
  apply CategoryTheory.Functor.ext (fun _ => rfl)

lemma reindex_comp {T U V : SSet.{max u v}} (j : U ⟶ T) (k : V ⟶ U) :
    reindex (C := C) hcof hfib (k ≫ j) = reindex hcof hfib j ⋙ reindex hcof hfib k := by
  apply CategoryTheory.Functor.ext (fun _ => rfl)

lemma reindex_map_surjective {T U : SSet.{max u v}} (j : U ⟶ T) [Mono j]
    (X Y : Object (C := C) hcof hfib T)
    (f : (reindex hcof hfib j).obj X ⟶ (reindex hcof hfib j).obj Y) :
    ∃ g : X ⟶ Y, (reindex hcof hfib j).map g = f := by
  obtain ⟨e, he⟩ := LocalizedRelativeChoice.parameter_extension _
    (unit_localized_isIso hcof hfib X.base) (ambient_kan hcof hfib Y.base)
    (boundary hcof hfib f.base) j f.extension
  refine ⟨⟨f.base, e⟩, ?_⟩
  apply hom_ext hcof hfib
  · rfl
  · exact congrArg (RelativeChoiceSpace.family _ _) he

lemma projection_full (T : SSet.{max u v}) :
    (projection (C := C) hcof hfib T).Full where
  map_surjective f :=
    ⟨⟨f, SSet.stdSimplex.isTerminalObj₀.from T ≫ actionPoint hcof hfib f⟩, rfl⟩

lemma reindex_full {T U : SSet.{max u v}} (j : U ⟶ T) [Mono j] :
    (reindex (C := C) hcof hfib j).Full where
  map_surjective {X Y} f := reindex_map_surjective hcof hfib j X Y f

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarChoiceCategory
