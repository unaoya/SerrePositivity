module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColimitPoints
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Unit
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagExt

/-!
# 一対象で薄い元の圏の行と全単体の一意性

概要：対象が一意で薄い圏では同じ端点の行と全射列が一意となる。
方針：元の全頂点と全成分を異種等式で照合する。
規約：空語を含む任意の語を使う。
使われ方：有限木の根だけの基底の実際の hammock。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SubsingletonCategoryRows
open CategoryTheory

variable {C : Type u} [Category.{v} C] [Subsingleton C] [Quiver.IsThin C]
  {W : MorphismProperty C} {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : C}

lemma arrow_heq {A B A' B' : C} (f : A ⟶ B) (g : A' ⟶ B') : HEq f g := by
  have hA : A = A' := Subsingleton.elim _ _
  have hB : B = B' := Subsingleton.elim _ _
  subst A'
  subst B'
  exact heq_of_eq (Subsingleton.elim _ _)

lemma row_eq (S T : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y) : S = T :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagExt.object_ext S T (fun _ => Subsingleton.elim _ _) (fun _ => arrow_heq _ _)

lemma vertical_heq {S T S' T' : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y}
    (f : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Hom S T) (g : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Hom S' T') : HEq f g :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagExt.hom_hext (row_eq S S') (row_eq T T') f g (fun _ => arrow_heq _ _)

lemma simplex_eq [W.IsMultiplicative] (n : SimplexCategoryᵒᵖ)
    (σ τ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W w X Y).obj n) : σ = τ := by
  apply CategoryTheory.Functor.hext (fun j => row_eq (σ.obj j) (τ.obj j))
  intro i j f
  exact vertical_heq (σ.map f) (τ.map f)

lemma colimit_point_eq_unit [W.IsMultiplicative] (X : C) (n : SimplexCategoryᵒᵖ)
    (p : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W X X).obj n) : p = (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitUnit W X).app n PUnit.unit := by
  obtain ⟨w, σ, hp⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimit_point_surjective (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W X X) n p
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W X X w).app n σ = p at hp
  rw [← hp]
  have h := congrArg (fun k => k.app n ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphUnit W X).app n PUnit.unit))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion_naturality W X X (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.fromEmpty w))
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W X X w).app n
    (((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W X X).map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.fromEmpty w)).app n
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphUnit W X).app n PUnit.unit)) = (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitUnit W X).app n PUnit.unit at h
  exact (congrArg ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W X X w).app n) (simplex_eq n _ _)).trans h

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SubsingletonCategoryRows
