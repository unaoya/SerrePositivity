module
public import SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrameHomotopy

public import SerrePositivity.KST.LocalizingInvariants.HomotopyPathFamily
public import SerrePositivity.KST.LocalizingInvariants.SquareFramePathExtension

/-!
概要：四辺の指定ホモトピーを、元の円柱を保つ境界 path の全族へ貼る。
方針：可逆な成分を持つ各円柱を可逆 path の圏へ入れ、角での厳密な一致を使う。
規約：全四辺の輸送を保持する。使われ方：BF 合成二脚への正方形全体の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.LocalizingInvariants

namespace SquareFrameHomotopy
attribute [local instance] SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrameHomotopy.instMonoSSetEquivalencePathι
variable {X : SSet.{u}} {f g : _root_.SerrePositivity.InfinityCategories.Core.Quasicategory.SquareFrame X} (H : _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrameHomotopy f g)

def pathFrame : _root_.SerrePositivity.InfinityCategories.Core.Quasicategory.SquareFrame (equivalencePath X) where
  _root_.SerrePositivity.InfinityCategories.Core.Quasicategory.SquareFrame.bottom := homotopyPathFamily H.bottom H.bottom_invertible
  _root_.SerrePositivity.InfinityCategories.Core.Quasicategory.SquareFrame.top := homotopyPathFamily H.top H.top_invertible
  _root_.SerrePositivity.InfinityCategories.Core.Quasicategory.SquareFrame.left := homotopyPathFamily H.left H.left_invertible
  _root_.SerrePositivity.InfinityCategories.Core.Quasicategory.SquareFrame.right := homotopyPathFamily H.right H.right_invertible
  _root_.SerrePositivity.InfinityCategories.Core.Quasicategory.SquareFrame.lower_left := by
    apply (cancel_mono (equivalencePathι X)).1
    simp only [Category.assoc, homotopyPathFamily_inclusion]
    exact ofHomotopy_restriction_eq _ _ _ _ H.lower_left
  _root_.SerrePositivity.InfinityCategories.Core.Quasicategory.SquareFrame.lower_right := by
    apply (cancel_mono (equivalencePathι X)).1
    simp only [Category.assoc, homotopyPathFamily_inclusion]
    exact ofHomotopy_restriction_eq _ _ _ _ H.lower_right
  _root_.SerrePositivity.InfinityCategories.Core.Quasicategory.SquareFrame.upper_left := by
    apply (cancel_mono (equivalencePathι X)).1
    simp only [Category.assoc, homotopyPathFamily_inclusion]
    exact ofHomotopy_restriction_eq _ _ _ _ H.upper_left
  _root_.SerrePositivity.InfinityCategories.Core.Quasicategory.SquareFrame.upper_right := by
    apply (cancel_mono (equivalencePathι X)).1
    simp only [Category.assoc, homotopyPathFamily_inclusion]
    exact ofHomotopy_restriction_eq _ _ _ _ H.upper_right

lemma pathFrame_source : H.pathFrame.postcomp (equivalencePathEndpoint X 0) = f := by
  apply _root_.SerrePositivity.InfinityCategories.Core.Quasicategory.SquareFrame.ext
  · exact homotopyPathFamily_source H.bottom H.bottom_invertible
  · exact homotopyPathFamily_source H.top H.top_invertible
  · exact homotopyPathFamily_source H.left H.left_invertible
  · exact homotopyPathFamily_source H.right H.right_invertible

lemma pathFrame_target : H.pathFrame.postcomp (equivalencePathEndpoint X 1) = g := by
  apply _root_.SerrePositivity.InfinityCategories.Core.Quasicategory.SquareFrame.ext
  · exact homotopyPathFamily_target H.bottom H.bottom_invertible
  · exact homotopyPathFamily_target H.top H.top_invertible
  · exact homotopyPathFamily_target H.left H.left_invertible
  · exact homotopyPathFamily_target H.right H.right_invertible

variable [Quasicategory X] (Q : (Δ[1] ⊗ Δ[1] : SSet.{u}) ⟶ X) (hf : f = _root_.SerrePositivity.InfinityCategories.F1B.Quasicategory.SquareFrame.ofSquare Q)

def extension : _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrame.PathExtension H.pathFrame Q :=
  _root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrame.pathExtension _ _ (H.pathFrame_source.trans hf)

lemma extension_target_boundary : _root_.SerrePositivity.InfinityCategories.Core.Quasicategory.SquareFrame.boundaryι ≫ (H.extension Q hf).target =
    g.diagram := by
  rw [_root_.SerrePositivity.InfinityCategories.Stable.Quasicategory.SquareFrame.PathExtension.target_boundary, pathFrame_target]

end SquareFrameHomotopy
end SerrePositivity.KST.LocalizingInvariants
