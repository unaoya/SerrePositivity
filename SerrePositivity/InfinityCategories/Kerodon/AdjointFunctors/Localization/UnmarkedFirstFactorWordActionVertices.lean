module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFactorWordActionVertices
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedFirstGeneratorImage

/-!
# 最小非指定列の切断因子の全頂点・全縦射と語の制限射

概要：内部切断端点を含む prefix・残りの全頂点と全縦射を元の語の作用へ照合する。
方針：前後の cut の公式と同じ元の生成矢の端点・恒等縦射の回収を合成する。
規約：全体の端点と内部切断端点を含む。横の列の比較は別工程。
使われ方：切断因子の全図式と同じ hammock 余極限の像の比較。

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


variable (hT : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedGeneratorColumns.column W (((τ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor f)).obj 0) (f.orderHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn W (τ.obj 0)
  h)) ≠ [])

include hT

lemma generator_eq : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowGenerator W (τ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor f) (f.orderHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn W (τ.obj
  0) h)) hT = _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowGenerator W τ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn W (τ.obj 0) h) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn_nonempty W (τ.obj 0) h) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstFiber_generator W f (τ.obj 0) h (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowFirstCut W τ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn W (τ.obj 0) h)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn_nonempty W (τ.obj 0) h) 0)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.rowFirstCut W (τ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor f) (f.orderHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn W (τ.obj 0) h)) hT 0)

lemma prefix_vertices (d : Fin (n.unop.len + 1))
    (k : Fin ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.prefixWord b (f.orderHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn W (τ.obj 0) h))).length + 1)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordCutFactorMaps.prefixMap f (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn W (τ.obj 0) h) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn_forward W (τ.obj 0) h))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.prefixDiagram W τ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn W (τ.obj 0) h) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn_nonempty W (τ.obj
      0) h)).obj d)).vertex k =
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.prefixDiagram W (τ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor f) (f.orderHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn W (τ.obj
        0) h)) hT).obj d).vertex k := by
  cases k using Fin.lastCases with
  | last =>
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordCutFactorMaps.prefixMap f (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn W (τ.obj 0) h) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn_forward W (τ.obj
      0) h))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.prefixDiagram W τ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn W (τ.obj 0) h) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn_nonempty W (τ.obj
        0) h)).obj d)).last.trans
      ((congrArg (fun g : Quiver.Total C => (show Paths C from g.left))
        (generator_eq W f τ h hT)).symm.trans
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.prefixDiagram W (τ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor f) (f.orderHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn W
          (τ.obj 0) h)) hT).obj d).last.symm)
  | cast k =>
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.prefix_action_vertex W f τ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn W (τ.obj 0) h)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn_nonempty W (τ.obj 0) h) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn_forward W (τ.obj 0) h) hT d k

lemma residual_vertices (d : Fin (n.unop.len + 1))
    (k : Fin ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residualWord b (f.orderHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn W (τ.obj 0) h))).length + 1)) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordCutFactorMaps.residualMap f (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn W (τ.obj 0) h) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn_forward W (τ.obj 0) h))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.residualDiagram W τ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn W (τ.obj 0) h) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn_nonempty W
        (τ.obj 0) h)).obj d)).vertex k =
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.residualDiagram W (τ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor f) (f.orderHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn W
        (τ.obj 0) h)) hT).obj d).vertex k := by
  change Fin (1 + ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.after b (f.orderHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn W (τ.obj 0) h))).length +
    1)) at k
  cases k using Fin.addCases with
  | left k =>
    have hk : k = (0 : Fin 1) := Subsingleton.elim _ _
    subst k
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordCutFactorMaps.residualMap f (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn W (τ.obj 0) h) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn_forward W
      (τ.obj 0) h))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.residualDiagram W τ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn W (τ.obj 0) h) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn_nonempty W
        (τ.obj 0) h)).obj d)).first.trans
      ((congrArg (fun g : Quiver.Total C => (show Paths C from g.right))
        (generator_eq W f τ h hT)).symm.trans
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.residualDiagram W (τ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor f) (f.orderHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn W
          (τ.obj 0) h)) hT).obj d).first.symm)
  | right k =>
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residual_action_vertex W f τ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn W (τ.obj 0) h)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn_nonempty W (τ.obj 0) h) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn_forward W (τ.obj 0) h) hT d k

lemma prefix_apps {d e : Fin (n.unop.len + 1)} (g : d ⟶ e)
    (k : Fin ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.prefixWord b (f.orderHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn W (τ.obj 0) h))).length + 1)) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.movingMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordCutFactorMaps.prefixMap f (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn W (τ.obj 0) h) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn_forward W
      (τ.obj 0) h))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.prefixDiagram W τ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn W (τ.obj 0) h) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn_nonempty W (τ.obj
        0) h)).map g)).app k)
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.prefixDiagram W (τ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor f) (f.orderHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn W (τ.obj
        0) h)) hT).map g).app k) := by
  cases k using Fin.lastCases with
  | last =>
    have ho := (congrArg (fun g : Quiver.Total C => (show Paths C from g.left))
      (generator_eq W f τ h hT)).symm
    exact ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.wordAction (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordCutFactorMaps.prefixMap f (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn W (τ.obj 0) h)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn_forward W (τ.obj 0) h))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.prefixDiagram W τ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn W (τ.obj 0) h) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn_nonempty W (τ.obj
        0) h))).last g).trans
      (((eqToHom_heq_id_dom _ _ ho).symm.trans (eqToHom_heq_id_cod _ _ ho)).trans
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.prefixDiagram W (τ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor f) (f.orderHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn W
          (τ.obj 0) h)) hT).last g).symm)
  | cast k =>
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.prefix_action_app W f τ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn W (τ.obj 0) h)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn_nonempty W (τ.obj 0) h) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn_forward W (τ.obj 0) h) hT g k

lemma residual_apps {d e : Fin (n.unop.len + 1)} (g : d ⟶ e)
    (k : Fin ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residualWord b (f.orderHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn W (τ.obj 0) h))).length + 1)) :
    HEq ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.movingMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordCutFactorMaps.residualMap f (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn W (τ.obj 0) h) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn_forward W
      (τ.obj 0) h))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.residualDiagram W τ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn W (τ.obj 0) h) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn_nonempty W
        (τ.obj 0) h)).map g)).app k)
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.residualDiagram W (τ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor f) (f.orderHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn W
        (τ.obj 0) h)) hT).map g).app k) := by
  change Fin (1 + ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordColumnSplit.after b (f.orderHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn W (τ.obj 0) h))).length +
    1)) at k
  cases k using Fin.addCases with
  | left k =>
    have hk : k = (0 : Fin 1) := Subsingleton.elim _ _
    subst k
    have ho := (congrArg (fun g : Quiver.Total C => (show Paths C from g.right))
      (generator_eq W f τ h hT)).symm
    exact ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.wordAction (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordCutFactorMaps.residualMap f (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn W (τ.obj 0) h)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn_forward W (τ.obj 0) h))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.residualDiagram W τ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn W (τ.obj 0) h) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn_nonempty W (τ.obj
        0) h))).first g).trans
      (((eqToHom_heq_id_dom _ _ ho).symm.trans (eqToHom_heq_id_cod _ _ ho)).trans
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.UnmarkedCutAttachmentDiagrams.residualDiagram W (τ ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor f) (f.orderHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn W
          (τ.obj 0) h)) hT).first g).symm)
  | right k =>
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.residual_action_app W f τ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn W (τ.obj 0) h) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn_nonempty
      W (τ.obj 0) h) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.firstColumn_forward W (τ.obj 0) h) hT g k

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
