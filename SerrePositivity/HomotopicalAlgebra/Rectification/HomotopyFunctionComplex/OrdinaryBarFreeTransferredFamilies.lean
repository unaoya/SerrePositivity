module

public import SerrePositivity.HomotopicalAlgebra.Rectification.HomotopyFunctionComplex.OrdinaryBarFreeAmbientFamilies

/-!
# 中断した任意モデル源への一般化：OrdinaryBarFreeTransferredFamilies

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Transfer the actual coherent ambient families to the small object models。

## 方針（定義・証明）
自由単体的分解・Dwyer–Kan型の生成射による整合化に対応する技法。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0190][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0190
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Transfer the actual coherent ambient families to the small object models

The maps retain the entire parameter and all face and degeneracy equations.
They take values in the lift of the actual small internal Hom. Composition
of transferred maps requires the contraction homotopies; it is not asserted
strict merely because ambient composition is strict.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open CategoryTheory.CartesianMonoidalCategory
open SerrePositivity.SimplicialModel

namespace SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeTransferredFamilies
open FreeGeneratorCategories FreeGeneratorFaces OrdinaryBarFreeResolutionSeed
open OrdinaryBarChoiceBoundaryGluing OrdinaryBarFreeResolutionDegeneracyValues
open OrdinaryBarRetractSystem
variable {C : Type u} [Category.{v} C] [HomotopicalAlgebra.ModelCategory C]
  [HomotopicalAlgebra.ModelCategory SSet.{v}]
  (hcof : HomotopicalAlgebra.cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : HomotopicalAlgebra.fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

/-- Transfer an arbitrary whole ambient family using the actual section and projection. -/
def ofFamily {X Y : D C} {T : SSet.{max u v}} (a : ambient hcof hfib X ⊗ T ⟶ ambient hcof hfib Y) :
    lifted hcof hfib X ⊗ T ⟶ lifted hcof hfib Y :=
  section_ hcof hfib X ▷ T ≫ a ≫ projection hcof hfib Y

lemma ofFamily_substitute {X Y : D C} {T U : SSet.{max u v}} (j : U ⟶ T)
    (a : ambient hcof hfib X ⊗ T ⟶ ambient hcof hfib Y) :
    ofFamily hcof hfib (ParameterComposition.substitute j a) =
      lifted hcof hfib X ◁ j ≫ ofFamily hcof hfib a := by
  simp only [ofFamily, ParameterComposition.substitute, ← Category.assoc, whisker_exchange]

lemma ofFamily_id (X : D C) (T : SSet.{max u v}) :
    ofFamily hcof hfib (ParameterComposition.const T (𝟙 (ambient hcof hfib X))) =
      fst (lifted hcof hfib X) T := by
  rw [ofFamily, ParameterComposition.const, Category.comp_id, ← Category.assoc,
    whiskerRight_fst, Category.assoc, section_fac, Category.comp_id]

def ofFamilyClosed {X Y : D C} {T : SSet.{max u v}}
    (a : ambient hcof hfib X ⊗ T ⟶ ambient hcof hfib Y) :
    T ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v} ((ihom (small hcof hfib X)).obj (small hcof hfib Y)) :=
  curry (ofFamily hcof hfib a) ≫
    (UniverseLiftParameterHom.closedIso (small hcof hfib X) (small hcof hfib Y)).inv

lemma ofFamilyClosed_substitute {X Y : D C} {T U : SSet.{max u v}} (j : U ⟶ T)
    (a : ambient hcof hfib X ⊗ T ⟶ ambient hcof hfib Y) :
    ofFamilyClosed hcof hfib (ParameterComposition.substitute j a) =
      j ≫ ofFamilyClosed hcof hfib a := by
  rw [ofFamilyClosed, ofFamily_substitute, curry_natural_left, ofFamilyClosed, Category.assoc]

variable (P : SSet.{max u v})

def family (n : ℕ) {X Y : D C} (f : FreeGeneratorDegeneracies.hom (n + 1) X Y) :
    lifted hcof hfib X ⊗ parameters P n ⟶ lifted hcof hfib Y :=
  ofFamily hcof hfib (OrdinaryBarFreeAmbientFamilies.family hcof hfib P n f)

lemma family_id (n : ℕ) (X : D C) :
    family hcof hfib P n (FreeGeneratorCategories.identity (D C) (n + 1) X) =
      fst (lifted hcof hfib X) (parameters P n) := by
  rw [family, OrdinaryBarFreeAmbientFamilies.family_id, ofFamily_id]

lemma family_face (n : ℕ) (i : Fin (n + 2)) {X Y : degree (D C) (n + 2)} (f : X ⟶ Y) :
    family hcof hfib P n ((fixedFace (D C) (n + 1) i).map f) =
      lifted hcof hfib X ◁ (P ◁ SSet.stdSimplex.δ i) ≫ family hcof hfib P (n + 1) f := by
  rw [family, family, ← OrdinaryBarFreeAmbientFamilies.family_face, ofFamily_substitute]
  rfl

lemma family_degeneracy (n : ℕ) (i : Fin (n + 1)) {X Y : degree (D C) (n + 1)} (f : X ⟶ Y) :
    family hcof hfib P (n + 1) ((degeneracyFunctor (D C) n i).map f) =
      lifted hcof hfib X ◁ (P ◁ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.sigma n i) ≫ family hcof hfib P n f := by
  rw [family, family, OrdinaryBarFreeAmbientFamilies.family_degeneracy, ofFamily_substitute]
  rfl

/-- A whole family valued in the universe lift of the small native internal Hom. -/
def transferred (n : ℕ) {X Y : D C} (f : FreeGeneratorDegeneracies.hom (n + 1) X Y) :
    parameters P n ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.UniverseLiftFillers.obj.{max u v}
      ((ihom (small hcof hfib X)).obj (small hcof hfib Y)) :=
  ofFamilyClosed hcof hfib (OrdinaryBarFreeAmbientFamilies.family hcof hfib P n f)

lemma transferred_face (n : ℕ) (i : Fin (n + 2)) {X Y : degree (D C) (n + 2)} (f : X ⟶ Y) :
    transferred hcof hfib P n ((fixedFace (D C) (n + 1) i).map f) =
      P ◁ SSet.stdSimplex.δ i ≫ transferred hcof hfib P (n + 1) f := by
  rw [transferred, transferred, ← OrdinaryBarFreeAmbientFamilies.family_face,
    ofFamilyClosed_substitute]

lemma transferred_degeneracy (n : ℕ) (i : Fin (n + 1))
    {X Y : degree (D C) (n + 1)} (f : X ⟶ Y) :
    transferred hcof hfib P (n + 1) ((degeneracyFunctor (D C) n i).map f) =
      P ◁ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.sigma n i ≫ transferred hcof hfib P n f := by
  rw [transferred, transferred, OrdinaryBarFreeAmbientFamilies.family_degeneracy,
    ofFamilyClosed_substitute]

end SerrePositivity.HomotopyFunctionComplex.OrdinaryBarFreeTransferredFamilies
