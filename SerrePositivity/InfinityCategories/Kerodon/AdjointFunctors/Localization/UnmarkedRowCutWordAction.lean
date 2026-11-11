module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFirstFactorWordActionVertices
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFirstFiberCuts
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFixedCutGeneratorTransport

/-!
# 元の全行の切断の前後の射列と語の圧縮

概要：圧縮後の全行の切断を元の生成矢へ移し、元の接頭射・残りを回収する。
方針：元の生成矢の一致・最小列以前の全行の指定性・固定切断の比較を使う。
規約：元の各行と全射列を保持し、後置区間の指定性を仮定しない。
使われ方：prefix 最終列と残り最初列の比較。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)
  {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : Paths C} {n : SimplexCategoryᵒᵖ}
  (f : a ⟶ b) (τ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W.paths a X Y).obj n)
  (h : ∃ i, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W (τ.obj 0) i ≠ [])
  (hT : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W ((τ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor f).obj 0)
    (f.orderHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn W (τ.obj 0) h)) ≠ [])

include hT in
lemma row_cut_left (d : Fin (n.unop.len + 1)) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fixedRowCut W (τ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor f)
      (f.orderHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn W (τ.obj 0) h)) hT d).left
      (Quiver.Path.comp
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordActionCutComparison.prefixMap W f (τ.obj d) (f.orderHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn W (τ.obj 0) h))
          (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn W (τ.obj 0) h) rfl
          ((f.direction_eq _).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn_forward W (τ.obj 0) h)))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fixedRowCut W τ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn W (τ.obj 0) h)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn_nonempty W (τ.obj 0) h) d).left) := by
  let Q := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fixedRowCut W (τ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor f)
    (f.orderHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn W (τ.obj 0) h)) hT d
  let Q' := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFixedCutGeneratorTransport.changeGenerator W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.generator_eq W f τ h hT) Q
  have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordActionCutComparison.cut_left W f (τ.obj d)
    (f.orderHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn W (τ.obj 0) h)) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn W (τ.obj 0) h)
    rfl ((f.direction_eq _).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn_forward W (τ.obj 0) h))
    (fun k _ hk => _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.before_firstColumn_row_mem W τ h d k hk)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fixedRowCut W τ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn W (τ.obj 0) h) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn_nonempty W (τ.obj 0) h) d) Q'
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFixedCutGeneratorTransport.changeGenerator_left W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.generator_eq W f τ h hT) Q).symm.trans hc

include hT in
lemma row_cut_right (d : Fin (n.unop.len + 1)) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fixedRowCut W (τ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor f)
      (f.orderHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn W (τ.obj 0) h)) hT d).right
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fixedRowCut W τ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn W (τ.obj 0) h)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn_nonempty W (τ.obj 0) h) d).right.comp
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordActionCutComparison.residual W f (τ.obj d) (f.orderHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn W (τ.obj 0) h))
          (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn W (τ.obj 0) h) rfl
          ((f.direction_eq _).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn_forward W (τ.obj 0) h)))) := by
  let Q := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fixedRowCut W (τ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor f)
    (f.orderHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn W (τ.obj 0) h)) hT d
  let Q' := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFixedCutGeneratorTransport.changeGenerator W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.generator_eq W f τ h hT) Q
  have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordActionCutComparison.cut_right W f (τ.obj d)
    (f.orderHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn W (τ.obj 0) h)) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn W (τ.obj 0) h)
    rfl ((f.direction_eq _).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn_forward W (τ.obj 0) h))
    (fun k _ hk => _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.before_firstColumn_row_mem W τ h d k hk)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fixedRowCut W τ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn W (τ.obj 0) h) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn_nonempty W (τ.obj 0) h) d) Q'
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFixedCutGeneratorTransport.changeGenerator_right W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.generator_eq W f τ h hT) Q).symm.trans hc

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
