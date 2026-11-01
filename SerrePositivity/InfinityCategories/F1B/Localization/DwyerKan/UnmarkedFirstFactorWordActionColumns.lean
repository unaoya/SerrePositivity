module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.UnmarkedPrefixWordActionInner
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.UnmarkedResidualWordActionInner
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.UnmarkedPrefixWordActionOuter
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.UnmarkedResidualWordActionOuter

/-!
# 元の最小列で切断した因子の全横列と語の作用

概要：内部接続列と外側の全列を合わせ、元の因子の全横列を回収する。
方針：連結語の列の左右の場合分けを使う。
規約：元の全行・全方向・同じ切断端点を保持する。
使われ方：全因子図式と同じ hammock 余極限の標準射の比較。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactorAction
open CategoryTheory Word.CutFactor

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {a b : Word} {X Y : Paths C} {n : SimplexCategoryᵒᵖ}
  (f : a ⟶ b) (τ : (graph W.paths a X Y).obj n) (h : ∃ i, column W (τ.obj 0) i ≠ [])
  (hT : column W ((τ ⋙ WordAction.functor f).obj 0)
    (f.orderHom (AttachedPrefix.index W τ h)) ≠ []) (d : Fin (n.unop.len + 1))

include hT in
lemma prefix_columns (k : Fin (prefixWord b (f.orderHom (AttachedPrefix.index W τ h))).length) :
    HEq ((WordAction.obj
      (prefixMap f (AttachedPrefix.index W τ h) (firstColumn_forward W (τ.obj 0) h))
      ((AttachedPrefix.diagram W τ h).obj d)).arrow k)
      (((Attachments.prefixDiagram W (τ ⋙ WordAction.functor f)
        (f.orderHom (AttachedPrefix.index W τ h)) hT).obj d).arrow k) := by
  cases k using Fin.addCases with
  | left k =>
    exact Attachments.prefix_outer_arrow W f τ (AttachedPrefix.index W τ h)
      (AttachedPrefix.nonempty W τ h) (firstColumn_forward W (τ.obj 0) h) hT d k
  | right k =>
    change Fin 1 at k
    have hk : k = (0 : Fin 1) := Subsingleton.elim _ _
    subst k
    exact prefix_inner_action_arrow W f τ h hT d

include hT in
lemma residual_columns (k : Fin (residualWord b (f.orderHom (AttachedPrefix.index W τ h))).length) :
    HEq ((WordAction.obj
      (residualMap f (AttachedPrefix.index W τ h) (firstColumn_forward W (τ.obj 0) h))
      ((Attachments.residualDiagram W τ (AttachedPrefix.index W τ h)
        (AttachedPrefix.nonempty W τ h)).obj d)).arrow k)
      (((Attachments.residualDiagram W (τ ⋙ WordAction.functor f)
        (f.orderHom (AttachedPrefix.index W τ h)) hT).obj d).arrow k) := by
  cases k using Fin.addCases with
  | left k =>
    change Fin 1 at k
    have hk : k = (0 : Fin 1) := Subsingleton.elim _ _
    subst k
    exact residual_inner_action_arrow W f τ h hT d
  | right k =>
    exact Attachments.residual_outer_arrow W f τ (AttachedPrefix.index W τ h)
      (AttachedPrefix.nonempty W τ h) (firstColumn_forward W (τ.obj 0) h) hT d k

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactorAction
