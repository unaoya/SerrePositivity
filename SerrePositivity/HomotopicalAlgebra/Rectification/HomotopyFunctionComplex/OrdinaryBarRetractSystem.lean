module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarSmallSubcomplex
public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryKanBarMappingClasses
public import SerrePositivity.HomotopicalAlgebra.Simplicial.MonoLocalizedFactorization
public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.LocalizedRelativeChoice
public import SerrePositivity.HomotopicalAlgebra.Simplicial.UniverseLiftParameterHom
public import SerrePositivity.HomotopicalAlgebra.Simplicial.MonoRightLiftingRelativeHomotopy

/-!
# 中断した任意モデル源への一般化：OrdinaryBarRetractSystem

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Strict objectwise retracts and all-dimensional relative arrow choices。

## 方針（定義・証明）
frameによる導来写像空間と整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0214][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0214
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Strict objectwise retracts and all-dimensional relative arrow choices

Each Kan bar value is enlarged through a mono equivalence to a strict
retract presentation over its small reference. This is a family of
objects, not a functorial choice of enlargements on the base. Relative
arrow families retain every prescribed parameter and transfer to the
lift of an actual small mapping space.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory CategoryTheory.MonoidalClosed
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarRetractSystem
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

abbrev small (b : Cᵒᵖ × C) := OrdinaryBarSmallReference.value hcof hfib b
abbrev lifted (b : Cᵒᵖ × C) := _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} (small hcof hfib b)
abbrev ambient (b : Cᵒᵖ × C) :=
  MonoLocalizedFactorization.middle (OrdinaryBarSmallSubcomplex.toSmall hcof hfib b)

abbrev unit (b : Cᵒᵖ × C) : OrdinaryKanBarMappingClasses.functor.obj b ⟶ ambient hcof hfib b :=
  MonoLocalizedFactorization.left (OrdinaryBarSmallSubcomplex.toSmall hcof hfib b)

abbrev projection (b : Cᵒᵖ × C) : ambient hcof hfib b ⟶ lifted hcof hfib b :=
  MonoLocalizedFactorization.right (OrdinaryBarSmallSubcomplex.toSmall hcof hfib b)

instance unit_mono (b : Cᵒᵖ × C) : Mono (unit hcof hfib b) := inferInstance

lemma unit_localized_isIso (b : Cᵒᵖ × C) :
    IsIso (AnodyneHomotopy.anodyneQ.map (unit hcof hfib b)) :=
  (MonoLocalizedFactorization.left_localized_isIso_iff _).mpr
    (OrdinaryBarSmallSubcomplex.toSmall_isIso hcof hfib b)

lemma projection_mono_rlp (b : Cᵒᵖ × C) :
    (MorphismProperty.monomorphisms SSet.{max u v}).rlp (projection hcof hfib b) :=
  MonoLocalizedFactorization.right_all_mono_rlp _

lemma ambient_kan (b : Cᵒᵖ × C) :
    SSet.modelCategoryQuillen.J.rlp (terminal.from (ambient hcof hfib b)) := by
  have hp : SSet.modelCategoryQuillen.J.rlp (projection hcof hfib b) := by
    intro A B j hj
    exact projection_mono_rlp hcof hfib b j (SSet.modelCategoryQuillen.J_le_monomorphisms j hj)
  have h := SSet.modelCategoryQuillen.J.rlp.comp_mem _ _ hp
    (UniverseLift.horn_terminal_map.{max u v, v} (OrdinaryBarSmallReference.value_kan hcof hfib b))
  have he : projection hcof hfib b ≫ terminal.from (lifted hcof hfib b) =
      terminal.from (ambient hcof hfib b) := terminal.hom_ext _ _
  rwa [he] at h

def section_ (b : Cᵒᵖ × C) : lifted hcof hfib b ⟶ ambient hcof hfib b :=
  (MonoRightLiftingContraction.exists_section _ (projection_mono_rlp hcof hfib b)).choose

lemma section_fac (b : Cᵒᵖ × C) : section_ hcof hfib b ≫ projection hcof hfib b = 𝟙 _ :=
  (MonoRightLiftingContraction.exists_section _ (projection_mono_rlp hcof hfib b)).choose_spec

def contraction (b : Cᵒᵖ × C) : SSet.Homotopy (𝟙 (ambient hcof hfib b))
    (projection hcof hfib b ≫ section_ hcof hfib b) :=
  (MonoRightLiftingRelativeHomotopy.exists_strong_contraction _ (projection_mono_rlp hcof hfib b)
    _ (section_fac hcof hfib b)).choose

lemma contraction_over (b : Cᵒᵖ × C) :
    (contraction hcof hfib b).h ≫ projection hcof hfib b =
      fst (ambient hcof hfib b) (SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫
        projection hcof hfib b :=
  (MonoRightLiftingRelativeHomotopy.exists_strong_contraction _ (projection_mono_rlp hcof hfib b)
    _ (section_fac hcof hfib b)).choose_spec.1

lemma contraction_on_section (b : Cᵒᵖ × C) :
    section_ hcof hfib b ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫
        (contraction hcof hfib b).h =
      fst (lifted hcof hfib b) (SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫
        section_ hcof hfib b :=
  (MonoRightLiftingRelativeHomotopy.exists_strong_contraction _ (projection_mono_rlp hcof hfib b)
    _ (section_fac hcof hfib b)).choose_spec.2

lemma contraction_pre_section (b : Cᵒᵖ × C) {T : SSet.{max u v}}
    (a : T ⟶ lifted hcof hfib b) :
    (a ≫ section_ hcof hfib b) ▷ SSet.stdSimplex.obj (SimplexCategory.mk 1) ≫
        (contraction hcof hfib b).h =
      fst T (SSet.stdSimplex.obj (SimplexCategory.mk 1)) ≫ a ≫ section_ hcof hfib b := by
  rw [comp_whiskerRight, Category.assoc, contraction_on_section, whiskerRight_fst_assoc]

def boundary {b c : Cᵒᵖ × C} (f : b ⟶ c) :=
  OrdinaryKanBarMappingClasses.functor.map f ≫ unit hcof hfib c

abbrev choices {b c : Cᵒᵖ × C} (f : b ⟶ c) : SSet.{max u v} :=
  RelativeChoiceSpace.obj (unit hcof hfib b) (boundary hcof hfib f)

lemma choices_mono_rlp {b c : Cᵒᵖ × C} (f : b ⟶ c) :
    (MorphismProperty.monomorphisms SSet.{max u v}).rlp
      (terminal.from (choices hcof hfib f)) :=
  LocalizedRelativeChoice.terminal_mono_rlp _ (unit_localized_isIso hcof hfib b)
    (ambient_kan hcof hfib c) _

def action {b c : Cᵒᵖ × C} (f : b ⟶ c) : ambient hcof hfib b ⟶ ambient hcof hfib c :=
  LocalizedRelativeChoice.extension _ (unit_localized_isIso hcof hfib b)
    (ambient_kan hcof hfib c) (boundary hcof hfib f)

lemma action_fac {b c : Cᵒᵖ × C} (f : b ⟶ c) :
    unit hcof hfib b ≫ action hcof hfib f = boundary hcof hfib f :=
  LocalizedRelativeChoice.extension_fac _ (unit_localized_isIso hcof hfib b)
    (ambient_kan hcof hfib c) _

def actionPoint {b c : Cᵒᵖ × C} (f : b ⟶ c) :
    SSet.stdSimplex.obj (SimplexCategory.mk 0) ⟶ choices hcof hfib f :=
  RelativeChoiceSpace.ofExtension _ _ (action hcof hfib f) (action_fac hcof hfib f)

def identityPoint (b : Cᵒᵖ × C) :
    SSet.stdSimplex.obj (SimplexCategory.mk 0) ⟶ choices hcof hfib (𝟙 b) :=
  RelativeChoiceSpace.ofExtension _ _ (𝟙 _) (by
    simp only [Category.comp_id, boundary, OrdinaryKanBarMappingClasses.functor.map_id,
      Category.id_comp])

lemma composite_fac {b c d : Cᵒᵖ × C} (f : b ⟶ c) (g : c ⟶ d) :
    unit hcof hfib b ≫ (action hcof hfib f ≫ action hcof hfib g) =
      boundary hcof hfib (f ≫ g) := by
  rw [← Category.assoc, action_fac]
  change (_ ≫ unit hcof hfib c) ≫ action hcof hfib g = _
  rw [Category.assoc, action_fac]
  change _ ≫ (_ ≫ unit hcof hfib d) = _
  rw [← Category.assoc, ← OrdinaryKanBarMappingClasses.functor.map_comp]
  rfl

def compositePoint {b c d : Cᵒᵖ × C} (f : b ⟶ c) (g : c ⟶ d) :
    SSet.stdSimplex.obj (SimplexCategory.mk 0) ⟶ choices hcof hfib (f ≫ g) :=
  RelativeChoiceSpace.ofExtension _ _ (action hcof hfib f ≫ action hcof hfib g)
    (composite_fac hcof hfib f g)

def transferFamily {b c : Cᵒᵖ × C} (f : b ⟶ c) {T : SSet.{max u v}}
    (s : T ⟶ choices hcof hfib f) : lifted hcof hfib b ⊗ T ⟶ lifted hcof hfib c :=
  section_ hcof hfib b ▷ T ≫ RelativeChoiceSpace.family _ _ s ≫ projection hcof hfib c

lemma transfer_identityPoint (b : Cᵒᵖ × C) :
    transferFamily hcof hfib (𝟙 b) (identityPoint hcof hfib b) =
      fst (lifted hcof hfib b) (SSet.stdSimplex.obj (SimplexCategory.mk 0)) := by
  have he : RelativeChoiceSpace.family (unit hcof hfib b) (boundary hcof hfib (𝟙 b))
      (identityPoint hcof hfib b) =
        fst (ambient hcof hfib b) (SSet.stdSimplex.obj (SimplexCategory.mk 0)) := by
    rw [identityPoint, RelativeChoiceSpace.family_ofExtension]
    ext n x
    rfl
  rw [transferFamily, he]
  ext n x
  exact types_congr_hom (congr_app (section_fac hcof hfib b) n) x.1

def arrowLifted {b c : Cᵒᵖ × C} (f : b ⟶ c) : lifted hcof hfib b ⟶ lifted hcof hfib c :=
  section_ hcof hfib b ≫ action hcof hfib f ≫ projection hcof hfib c

def compositionHomotopy {b c d : Cᵒᵖ × C} (f : b ⟶ c) (g : c ⟶ d) :
    SSet.Homotopy
      (section_ hcof hfib b ≫ action hcof hfib f ≫ action hcof hfib g ≫ projection hcof hfib d)
      (arrowLifted hcof hfib f ≫ arrowLifted hcof hfib g) := by
  have H := HomotopyClasses.postHomotopy (action hcof hfib g ≫ projection hcof hfib d)
    (HomotopyClasses.preHomotopy (section_ hcof hfib b ≫ action hcof hfib f)
      (contraction hcof hfib c))
  simpa only [arrowLifted, Category.assoc, Category.id_comp, Category.comp_id] using H

def smallArrow {b c : Cᵒᵖ × C} (f : b ⟶ c) : small hcof hfib b ⟶ small hcof hfib c :=
  _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.lower (arrowLifted hcof hfib f)

def smallCompositionHomotopy {b c d : Cᵒᵖ × C} (f : b ⟶ c) (g : c ⟶ d) :
    SSet.Homotopy
      (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.lower (section_ hcof hfib b ≫ action hcof hfib f ≫
        action hcof hfib g ≫ projection hcof hfib d))
      (smallArrow hcof hfib f ≫ smallArrow hcof hfib g) :=
  UniverseLift.lowerHomotopy.{max u v, v} (compositionHomotopy hcof hfib f g)

lemma transferFamily_naturality {b c : Cᵒᵖ × C} (f : b ⟶ c) {T U : SSet.{max u v}}
    (s : T ⟶ choices hcof hfib f) (j : U ⟶ T) :
    transferFamily hcof hfib f (j ≫ s) = lifted hcof hfib b ◁ j ≫ transferFamily hcof hfib f s := by
  rw [transferFamily, transferFamily, RelativeChoiceSpace.family_naturality]
  simp only [← Category.assoc, whisker_exchange]

def transferred {b c : Cᵒᵖ × C} (f : b ⟶ c) {T : SSet.{max u v}}
    (s : T ⟶ choices hcof hfib f) :
    T ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} ((ihom (small hcof hfib b)).obj (small hcof hfib c)) :=
  curry (transferFamily hcof hfib f s) ≫
    (UniverseLiftParameterHom.closedIso (small hcof hfib b) (small hcof hfib c)).inv

lemma transferred_naturality {b c : Cᵒᵖ × C} (f : b ⟶ c) {T U : SSet.{max u v}}
    (s : T ⟶ choices hcof hfib f) (j : U ⟶ T) :
    transferred hcof hfib f (j ≫ s) = j ≫ transferred hcof hfib f s := by
  rw [transferred, transferFamily_naturality, curry_natural_left, Category.assoc]
  rfl

lemma parameter_extension {b c : Cᵒᵖ × C} (f : b ⟶ c) {T U : SSet.{max u v}}
    (j : T ⟶ U) [Mono j] (s : T ⟶ choices hcof hfib f) :
    ∃ t : U ⟶ choices hcof hfib f, j ≫ t = s ∧
      j ≫ transferred hcof hfib f t = transferred hcof hfib f s := by
  obtain ⟨t, ht⟩ := LocalizedRelativeChoice.parameter_extension _
    (unit_localized_isIso hcof hfib b) (ambient_kan hcof hfib c) (boundary hcof hfib f) j s
  exact ⟨t, ht, (transferred_naturality hcof hfib f t j).symm.trans
    (congrArg (transferred hcof hfib f) ht)⟩

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarRetractSystem
