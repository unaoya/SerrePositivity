module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.QuiverTreeRetractVertex

/-!
# 元の生成辺を葉の除去後の自由圏へ送る

概要：葉に接する元の生成辺を恒等射へ、残りの辺を同じ生成辺へ送る。
方針：両端の回収式に沿って元の射を移送する。
規約：葉に接しない元の辺を別の射列で置き換えない。
使われ方：葉を親へ送る元の自由圏の関手。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

attribute [local instance] Classical.propDecidable

variable {Q : Type u} [Quiver.{v} Q] {T : WideSubquiver (Quiver.Symmetrify Q)}
  [Quiver.Arborescence T] {S : Finset Q} (D : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeafDeletion T S)

def LeafDeletion.retractArrow (x y : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S) (f : x.val ⟶ y.val) :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver (S.erase D.leaf)
    (Paths.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex (S.erase D.leaf))).obj (D.retractVertex x) ⟶
      (Paths.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex (S.erase D.leaf))).obj (D.retractVertex y) := by
  letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver (S.erase D.leaf)
  by_cases h : x.val = D.leaf ∨ y.val = D.leaf
  · exact eqToHom (congrArg (Paths.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex (S.erase D.leaf))).obj
      (D.incident_retract_eq x y f h))
  · have hx := (not_or.mp h).1
    have hy := (not_or.mp h).2
    let x' : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex (S.erase D.leaf) :=
      ⟨x.val, Finset.mem_erase.mpr ⟨hx, x.property⟩⟩
    let y' : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex (S.erase D.leaf) :=
      ⟨y.val, Finset.mem_erase.mpr ⟨hy, y.property⟩⟩
    let g : x' ⟶ y' := f
    exact eqToHom (congrArg (Paths.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex (S.erase D.leaf))).obj
        (D.retractVertex_of_ne x hx)) ≫
      (Paths.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex (S.erase D.leaf))).map g ≫
        eqToHom (congrArg (Paths.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex (S.erase D.leaf))).obj
          (D.retractVertex_of_ne y hy).symm)

lemma LeafDeletion.retractArrow_incident (x y : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex S) (f : x.val ⟶ y.val)
    (h : x.val = D.leaf ∨ y.val = D.leaf) :
    letI := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver (S.erase D.leaf)
    D.retractArrow x y f = eqToHom
      (congrArg (Paths.of (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.Vertex (S.erase D.leaf))).obj
        (D.incident_retract_eq x y f h)) := by
  let := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FiniteQuiver.quiver (S.erase D.leaf)
  exact dite_eq_left h

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
