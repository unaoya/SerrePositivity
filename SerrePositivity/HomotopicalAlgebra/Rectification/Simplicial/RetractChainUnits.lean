module

public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.RetractChainFamily

/-!
# 中断した任意モデル源への一般化：RetractChainUnits

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Endpoint unit laws and absorbing contraction parameters for retract chains。

## 方針（定義・証明）
bar型の鎖パラメータと整合図式の厳密化に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0548][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0548
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Endpoint unit laws and absorbing contraction parameters for retract chains

The hypotheses are the actual over-projection and fixed-section equations
of a strong contraction. No semigroup law for the original interval action
is assumed. Interior unit elimination with two general parameters is separate.
-/

@[expose] public section
universe v u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory

namespace SerrePositivity.SimplicialModel.RetractChainUnits
open RetractChainFamily
variable {ι : Type u} (E K : ι → SSet.{v}) (s : ∀ i, K i ⟶ E i) (p : ∀ i, E i ⟶ K i)
  (H : ∀ i, SSet.Homotopy (𝟙 (E i)) (p i ≫ s i))
  (hP : ∀ i, (H i).h ≫ p i = fst (E i) _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.interval ≫ p i)
  (hS : ∀ i, s i ▷ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.interval ≫ (H i).h = fst (K i) _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.interval ≫ s i)

include hP in
lemma contraction_over (i : ι) {T : SSet.{v}} (t : T ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.interval) :
    contraction E K s p H i t ≫ p i = fst (E i) T ≫ p i := by
  rw [contraction, Category.assoc, hP, whiskerLeft_fst_assoc]

include hS in
lemma contraction_section (i : ι) {T : SSet.{v}} (t : T ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.interval) :
    s i ▷ T ≫ contraction E K s p H i t = fst (K i) T ≫ s i := by
  rw [contraction, ← Category.assoc, ← whisker_exchange, Category.assoc, hS,
    whiskerLeft_fst_assoc]

include hP in
lemma contraction_comp_projection (i : ι) {T : SSet.{v}} (t : T ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.interval) :
    ParameterComposition.comp (contraction E K s p H i t) (ParameterComposition.const T (p i)) =
      ParameterComposition.const T (p i) := by
  rw [ParameterComposition.comp_const, contraction_over E K s p H hP]
  rfl

include hS in
lemma section_comp_contraction (i : ι) {T : SSet.{v}} (t : T ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.interval) :
    ParameterComposition.comp (ParameterComposition.const T (s i)) (contraction E K s p H i t) =
      ParameterComposition.const T (s i) := by
  rw [ParameterComposition.const_comp_family, contraction_section E K s p H hS]
  rfl

include hP in
lemma contraction_one_right (i : ι) {T : SSet.{v}} (t : T ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.interval) :
    ParameterComposition.comp (contraction E K s p H i t) (contraction E K s p H i (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.one T)) =
      contraction E K s p H i (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.one T) := by
  rw [contraction_one, ← ParameterComposition.const_comp,
    ← ParameterComposition.assoc, contraction_comp_projection E K s p H hP,
    ParameterComposition.const_comp]

include hS in
lemma contraction_one_left (i : ι) {T : SSet.{v}} (t : T ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.interval) :
    ParameterComposition.comp (contraction E K s p H i (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.one T)) (contraction E K s p H i t) =
      contraction E K s p H i (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.one T) := by
  rw [contraction_one, ← ParameterComposition.const_comp, ParameterComposition.assoc,
    section_comp_contraction E K s p H hS, ParameterComposition.const_comp]

include hP in
lemma trailing_identity {T : SSet.{v}} {a b : ι} (q : Chain E T a b) (t : T ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.interval) :
    transfer E K s p H (q.familySnoc (ParameterComposition.const T (𝟙 (E b))) t) =
      transfer E K s p H q := by
  rw [transfer_last_family_parameter E K s p H hP, ParameterComposition.id_comp]
  rfl

include hS in
lemma leading_identity {T : SSet.{v}} {a b : ι} (q : Chain E T a b) (t : T ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.interval) :
    transfer E K s p H
      (((Chain.nil : Chain E T a a).familySnoc
        (ParameterComposition.const T (𝟙 (E a))) t).append q) =
      transfer E K s p H q := by
  simp only [transfer, evaluate_append, evaluate, ParameterComposition.id_comp,
    ParameterComposition.assoc]
  rw [← ParameterComposition.assoc, section_comp_contraction E K s p H hS]

lemma interior_identity_after_zero {T : SSet.{v}} {a b c d : ι}
    (q : Chain E T a b) (f : E b ⊗ T ⟶ E c) (t : T ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.interval) (r : Chain E T c d) :
    transfer E K s p H
      (((q.familySnoc f (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.zero T)).familySnoc (ParameterComposition.const T (𝟙 (E c))) t).append r) =
      transfer E K s p H ((q.familySnoc f t).append r) := by
  simpa only [ParameterComposition.comp_id] using
    zero_family_face E K s p H q f (ParameterComposition.const T (𝟙 (E c))) t r

lemma interior_identity_at_zero {T : SSet.{v}} {a b c d : ι}
    (q : Chain E T a b) (g : E b ⊗ T ⟶ E c) (t : T ⟶ _root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.interval) (r : Chain E T c d) :
    transfer E K s p H
      (((q.familySnoc (ParameterComposition.const T (𝟙 (E b))) (_root_.SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.zero T)).familySnoc g t).append r) =
      transfer E K s p H ((q.familySnoc g t).append r) := by
  simpa only [ParameterComposition.id_comp] using
    zero_family_face E K s p H q (ParameterComposition.const T (𝟙 (E b))) g t r

end SerrePositivity.SimplicialModel.RetractChainUnits
