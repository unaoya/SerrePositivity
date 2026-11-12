module

public import SerrePositivity.EInfinity.Hammock.AllMarkedEmbedding
public import SerrePositivity.EInfinity.Hammock.UnmarkedNonemptyImage

/-!
# 指定部分圏の元の hammock の像と元の空文字列

概要：実際の包含の像が既存の非指定文字列評価の空の fiber と正確に一致する。
方針：元の全行の指定性と全列の空性を照合し、元の各次数の共同全射性を使う。
規約：元の包含・標準射・元の colimitValue を使う。
使われ方：空文字列部分との同型と反復切断の終端。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.AllMarked
open CategoryTheory

variable {C : Type u} [Category.{u} C] (W : MorphismProperty C) {X Y : Paths C}

lemma holds_value_iff {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {n : SimplexCategoryᵒᵖ} (τ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths w X Y).obj n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Holds W τ ↔ value W (τ.obj 0) = [] := by
  classical
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.holds_iff, ← value_ne_nil_iff, not_not]

lemma value_graphMap {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {n : SimplexCategoryᵒᵖ}
    (τ : (nativeGraph W X Y w).obj n) : value W (((graphMap W X Y w).app n τ).obj 0) = [] :=
  (holds_value_iff W _).1 (graphMap_holds W τ)

lemma inclusion_range (X Y : Paths C) (n : SimplexCategoryᵒᵖ)
    (x : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W.paths X Y).obj n) :
    (∃ z, (inclusion W X Y).app n z = x) ↔ (colimitValue W X Y).app n x = [] := by
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨w, τ, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimit_point_surjective
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram (⊤ : MorphismProperty (WideSubcategory W.paths)) ⟨X⟩ ⟨Y⟩) n z
    have hi := congrArg (fun k => k.app n τ) (nativeInclusion_inclusion W X Y w)
    exact ((congrArg ((colimitValue W X Y).app n) hi).trans
      (FirstFactor.colimitValue_inclusion W X Y w ((graphMap W X Y w).app n τ))).trans
        (value_graphMap W τ)
  · intro hx
    obtain ⟨w, τ, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimit_point_surjective (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W.paths X Y) n x
    have hτ : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Holds W τ := (holds_value_iff W τ).2
      ((FirstFactor.colimitValue_inclusion W X Y w τ).symm.trans hx)
    refine ⟨(nativeInclusion W X Y w).app n (lift W τ hτ), ?_⟩
    exact congrArg (fun k => k.app n (lift W τ hτ)) (nativeInclusion_inclusion W X Y w)

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.AllMarked
