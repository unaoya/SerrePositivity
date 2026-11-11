module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteDiagramPathSupport

/-!
# 元の行と有限 hammock grid の全射列の支持

概要：元の横列・全縦射に現れる生成辺の全頂点を集める。
方針：行の全頂点と横射列、頂点ごとの元の有限図式の支持の有限和を使う。
規約：空語と長さ零の射列の頂点も落とさない。
使われ方：元の全 grid を同じ有限部分木へ持ち上げる。

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

variable {Q : Type u} [Quiver.{v} Q] {a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : Paths Q}
  {W : MorphismProperty (Paths Q)}

def zigzagPathSupport (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X Y) : Finset Q :=
  (Finset.univ.biUnion fun j => {(show Q from S.vertex j)}) ∪
    (Finset.univ.biUnion fun k => @_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pathVertices Q _ _ _ (S.arrow k))

lemma zigzagPathSupport_vertex (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X Y) (j : Fin (a.length + 1)) :
    (show Q from S.vertex j) ∈ zigzagPathSupport S :=
  Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _,
    Finset.mem_singleton_self _⟩)

lemma zigzagPathSupport_arrow (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X Y) (k : Fin a.length) :
    @_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pathVertices Q _ _ _ (S.arrow k) ⊆ zigzagPathSupport S := by
  intro x hx
  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, hx⟩)

variable [W.IsMultiplicative] {I : Type w} [Category.{w'} I]
  [Fintype I] [∀ i j : I, Fintype (i ⟶ j)]

def gridPathSupport (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X Y) : Finset Q :=
  (Finset.univ.biUnion fun i => zigzagPathSupport (F.obj i)) ∪
    (Finset.univ.biUnion fun j => _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagramPathSupport (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.evaluation j))

lemma gridPathSupport_vertex (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X Y) (i : I) (j : Fin (a.length + 1)) :
    (show Q from (F.obj i).vertex j) ∈ gridPathSupport F :=
  Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _,
    zigzagPathSupport_vertex (F.obj i) j⟩)

lemma gridPathSupport_horizontal (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X Y) (i : I) (k : Fin a.length) :
    @_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pathVertices Q _ _ _ ((F.obj i).arrow k) ⊆ gridPathSupport F := by
  intro x hx
  exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _,
    zigzagPathSupport_arrow (F.obj i) k hx⟩)

lemma gridPathSupport_vertical (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W a X Y) {i i' : I} (f : i ⟶ i')
    (j : Fin (a.length + 1)) :
    @_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.pathVertices Q _ _ _ ((F.map f).app j) ⊆ gridPathSupport F := by
  intro x hx
  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _,
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.diagramPathSupport_arrow (F ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.evaluation j) f hx⟩)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
