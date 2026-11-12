module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.QuiverTreeHeight
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver

/-!
# 根だけを含む有限部分木の元の自由圏

概要：全頂点が根なら元の生成辺は無く、自由圏の対象と射は一意となる。
方針：証明済みの元の木の no_loop と射列の帰納を使う。
規約：元の quiver を局所的に有限頂点部分型へ制限する。
使われ方：有限木の hammock の可縮性の基底。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {Q : Type u} [Quiver.{v} Q] (T : WideSubquiver (Quiver.Symmetrify Q))
  [Quiver.Arborescence T] {S : Finset Q}
  (hroot : ∀ x ∈ S, (show T from x) = Quiver.root T)

include hroot in
lemma rootVertexSubsingleton : Subsingleton (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S) :=
  ⟨fun x y => Subtype.ext ((hroot x.val x.property).trans (hroot y.val y.property).symm)⟩

include hroot in
lemma rootPathsSubsingleton : Subsingleton (Paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S)) := by
  refine ⟨fun x y => ?_⟩
  change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S at x y
  exact (rootVertexSubsingleton T hroot).elim x y

variable [Quiver.IsThin (Quiver.FreeGroupoid Q)]

include hroot in
lemma root_no_arrow : letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
    ∀ {x y : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S}, (x ⟶ y) → False := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
  rintro ⟨x, hx⟩ ⟨y, hy⟩ f
  change x ⟶ y at f
  have hxy : x = y := (hroot x hx).trans (hroot y hy).symm
  subst y
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.no_loop T f

include hroot in
lemma root_path_eq_nil : letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
    ∀ (x : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S) (p : Quiver.Path x x), p = Quiver.Path.nil := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
  intro x p
  cases p with
  | nil => rfl
  | cons p f => exact (root_no_arrow T hroot f).elim

include hroot in
lemma rootPathsThin : letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
    Quiver.IsThin (Paths (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S)) := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver S
  intro x y
  have he : x = y := (rootPathsSubsingleton T hroot).elim x y
  subst y
  refine ⟨fun p q => ?_⟩
  exact (root_path_eq_nil T hroot x p).trans (root_path_eq_nil T hroot x q).symm

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
