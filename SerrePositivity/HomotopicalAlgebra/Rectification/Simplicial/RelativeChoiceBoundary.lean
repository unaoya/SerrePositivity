module
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.FixedBoundaryExtensions

public import SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.BoundaryGluing
public import SerrePositivity.HomotopicalAlgebra.Rectification.Simplicial.RelativeChoiceSpace

/-!
# 中断した任意モデル源への一般化：RelativeChoiceBoundary

## 概要
任意モデル源への一般化（中断、計画書§396）の一部である（分類B）。
対象：Filling prescribed compatible faces while retaining a fixed boundary。

## 方針（定義・証明）
自明fibrationのファイバーと相対延長による選択の比較に対応する足場。
下の技術注記に、元の具体的な構成と比較の範囲を保存する。

## 規約と注意
全hornを用いるKan複体の議論と、内側hornによる∞圏の議論を区別する。
既知の厳密化定理や単体的局所化との同定を証明したとは主張しない。

## 使われ方
stage 4の完成部分L・E・Sからの利用はない。
再開時は[計画書 §396][plan]と[棚卸し m0535][inventory]を参照する。

[inventory]: ../../../../formalization-plans/archive/k-theory-generalization-inventory.md#m0535
[plan]: ../../../../formalization-plans/archive/k-theory-v1.md#396-任意モデル源への一般化中断2026-10-17
-/

/- 旧モジュールの技術注記（構成と注意を保存）
# Filling prescribed compatible faces while retaining a fixed boundary

Face maps into the actual relative choice space are glued, then filled.
Every prescribed face is retained, and evaluating the filler keeps the
original V-boundary fixed throughout the entire higher simplex.
-/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra

namespace SerrePositivity.SimplicialModel.RelativeChoiceSpace
variable [ModelCategory SSet.{v}]
  (hcof : cofibrations SSet.{v} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{v} = SSet.modelCategoryQuillen.J.{v}.rlp)

include hcof hfib in
lemma fill_faces {V T P : SSet.{v}} (i : V ⟶ T) [Mono i] (b : V ⟶ P)
    (p : P ⟶ SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0))
    (hp : trivialFibrations SSet.{v} p) (n : ℕ)
    (f : ∀ k, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.BoundaryGluing.facet n k).toSSet ⟶ obj i b) (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.BoundaryGluing.Compatible f) :
    ∃ e : SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ⟶ obj i b,
      (∀ k, (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.BoundaryGluing.facet n k).ι ≫ e = f k) ∧
      i ▷ SSet.stdSimplex.{v}.obj (SimplexCategory.mk n) ≫ family i b e =
        V ◁ (SSet.stdSimplex.isTerminalObj₀.from _ ≫ pointUnitIso.hom) ≫ (ρ_ V).hom ≫ b := by
  obtain ⟨e, he⟩ := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.extension hcof hfib i b p hp (SSet.boundary.{v} n).ι
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.BoundaryGluing.BoundaryGluing.desc f hf)
  refine ⟨e, fun k => ?_, family_fixed_boundary i b e⟩
  have hk : SSet.boundary.faceι k ≫ (SSet.boundary.{v} n).ι = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.BoundaryGluing.facet n k).ι := rfl
  rw [← hk, Category.assoc, he]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.BoundaryGluing.BoundaryGluing.desc_fac f hf k

include hcof hfib in
/-- Fill given standard faces satisfying the ordinary simplicial face identities. -/
lemma fill_standard_faces {V T P : SSet.{v}} (i : V ⟶ T) [Mono i] (b : V ⟶ P)
    (p : P ⟶ SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0))
    (hp : trivialFibrations SSet.{v} p) (n : ℕ)
    (f : Fin (n + 3) → (SSet.stdSimplex.{v}.obj (SimplexCategory.mk (n + 1)) ⟶ obj i b))
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.BoundaryGluing.StandardCompatible f) :
    ∃ e : SSet.stdSimplex.{v}.obj (SimplexCategory.mk (n + 2)) ⟶ obj i b,
      (∀ k, SSet.stdSimplex.δ k ≫ e = f k) ∧
      i ▷ SSet.stdSimplex.{v}.obj (SimplexCategory.mk (n + 2)) ≫ family i b e =
        V ◁ (SSet.stdSimplex.isTerminalObj₀.from _ ≫ pointUnitIso.hom) ≫ (ρ_ V).hom ≫ b := by
  obtain ⟨e, he⟩ := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.extension hcof hfib i b p hp (SSet.boundary.{v} (n + 2)).ι
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.BoundaryGluing.standardDesc f hf)
  refine ⟨e, fun k => ?_, family_fixed_boundary i b e⟩
  rw [← SSet.boundary.ι_ι k, Category.assoc, he]
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.SimplicialSets.BoundaryGluing.standardDesc_fac f hf k

end SerrePositivity.SimplicialModel.RelativeChoiceSpace
