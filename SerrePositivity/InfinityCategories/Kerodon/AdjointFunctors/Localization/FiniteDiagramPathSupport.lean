module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.PathVertices
public import Mathlib.CategoryTheory.PathCategory.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Finset.Union

/-!
# 元の有限図式の全射列の有限支持

概要：有限な対象と射を持つ図式の全射列に現れる元の頂点を集める。
方針：全射の pathVertices の有限和を使い、対象は恒等射から回収する。
規約：射列の内部頂点と長さ零の射も含める。
使われ方：元の有限 hammock grid の全列と全縦射の支持。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v w w'
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory
attribute [local instance] Classical.propDecidable

variable {Q : Type u} [Quiver.{v} Q] {I : Type w} [Category.{w'} I]
  [Fintype I] [∀ i j : I, Fintype (i ⟶ j)]

def diagramPathSupport (F : I ⥤ Paths Q) : Finset Q :=
  Finset.univ.biUnion fun i => Finset.univ.biUnion fun j =>
    Finset.univ.biUnion fun f : i ⟶ j => @_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pathVertices Q _ _ _ (F.map f)

lemma diagramPathSupport_arrow (F : I ⥤ Paths Q) {i j : I} (f : i ⟶ j) :
    @_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pathVertices Q _ _ _ (F.map f) ⊆ diagramPathSupport F := by
  intro x hx
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _,
    Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _,
      Finset.mem_biUnion.mpr ⟨f, Finset.mem_univ _, hx⟩⟩⟩

lemma diagramPathSupport_vertex (F : I ⥤ Paths Q) (i : I) :
    (show Q from F.obj i) ∈ diagramPathSupport F :=
  diagramPathSupport_arrow F (𝟙 i) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pathVertices_source (F.map (𝟙 i)))

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
