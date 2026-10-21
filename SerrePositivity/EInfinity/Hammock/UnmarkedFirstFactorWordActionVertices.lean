module

public import SerrePositivity.EInfinity.Hammock.UnmarkedFactorWordActionVertices
public import SerrePositivity.EInfinity.Hammock.UnmarkedFirstGeneratorImage

/-!
# 最小非指定列の切断因子の全頂点・全縦射と語の制限射

概要：内部切断端点を含む prefix・残りの全頂点と全縦射を元の語の作用へ照合する。
方針：前後の cut の公式と同じ元の生成矢の端点・恒等縦射の回収を合成する。
規約：全体の端点と内部切断端点を含む。横の列の比較は別工程。
使われ方：切断因子の全図式と同じ hammock 余極限の像の比較。
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
  (f : a ⟶ b) (τ : (graph W.paths a X Y).obj n)
  (h : ∃ i, column W (τ.obj 0) i ≠ [])


variable (hT : column W (((τ ⋙ WordAction.functor f)).obj 0) (f.orderHom (firstColumn W (τ.obj 0)
  h)) ≠ [])

include hT

lemma generator_eq : rowGenerator W (τ ⋙ WordAction.functor f) (f.orderHom (firstColumn W (τ.obj
  0) h)) hT = rowGenerator W τ (firstColumn W (τ.obj 0) h) (firstColumn_nonempty W (τ.obj 0) h) :=
  firstFiber_generator W f (τ.obj 0) h (rowFirstCut W τ (firstColumn W (τ.obj 0) h)
    (firstColumn_nonempty W (τ.obj 0) h) 0)
    (rowFirstCut W (τ ⋙ WordAction.functor f) (f.orderHom (firstColumn W (τ.obj 0) h)) hT 0)

lemma prefix_vertices (d : Fin (n.unop.len + 1))
    (k : Fin ((prefixWord b (f.orderHom (firstColumn W (τ.obj 0) h))).length + 1)) :
    (WordAction.obj (prefixMap f (firstColumn W (τ.obj 0) h) (firstColumn_forward W (τ.obj 0) h))
      ((Attachments.prefixDiagram W τ (firstColumn W (τ.obj 0) h) (firstColumn_nonempty W (τ.obj
      0) h)).obj d)).vertex k =
      ((Attachments.prefixDiagram W (τ ⋙ WordAction.functor f) (f.orderHom (firstColumn W (τ.obj
        0) h)) hT).obj d).vertex k := by
  cases k using Fin.lastCases with
  | last =>
    exact (WordAction.obj (prefixMap f (firstColumn W (τ.obj 0) h) (firstColumn_forward W (τ.obj
      0) h))
      ((Attachments.prefixDiagram W τ (firstColumn W (τ.obj 0) h) (firstColumn_nonempty W (τ.obj
        0) h)).obj d)).last.trans
      ((congrArg (fun g : Quiver.Total C => (show Paths C from g.left))
        (generator_eq W f τ h hT)).symm.trans
        ((Attachments.prefixDiagram W (τ ⋙ WordAction.functor f) (f.orderHom (firstColumn W
          (τ.obj 0) h)) hT).obj d).last.symm)
  | cast k =>
    exact Attachments.prefix_action_vertex W f τ (firstColumn W (τ.obj 0) h)
      (firstColumn_nonempty W (τ.obj 0) h) (firstColumn_forward W (τ.obj 0) h) hT d k

lemma residual_vertices (d : Fin (n.unop.len + 1))
    (k : Fin ((residualWord b (f.orderHom (firstColumn W (τ.obj 0) h))).length + 1)) :
    (WordAction.obj (residualMap f (firstColumn W (τ.obj 0) h) (firstColumn_forward W (τ.obj 0) h))
      ((Attachments.residualDiagram W τ (firstColumn W (τ.obj 0) h) (firstColumn_nonempty W
        (τ.obj 0) h)).obj d)).vertex k =
      ((Attachments.residualDiagram W (τ ⋙ WordAction.functor f) (f.orderHom (firstColumn W
        (τ.obj 0) h)) hT).obj d).vertex k := by
  change Fin (1 + ((Word.ColumnSplit.after b (f.orderHom (firstColumn W (τ.obj 0) h))).length +
    1)) at k
  cases k using Fin.addCases with
  | left k =>
    have hk : k = (0 : Fin 1) := Subsingleton.elim _ _
    subst k
    exact (WordAction.obj (residualMap f (firstColumn W (τ.obj 0) h) (firstColumn_forward W
      (τ.obj 0) h))
      ((Attachments.residualDiagram W τ (firstColumn W (τ.obj 0) h) (firstColumn_nonempty W
        (τ.obj 0) h)).obj d)).first.trans
      ((congrArg (fun g : Quiver.Total C => (show Paths C from g.right))
        (generator_eq W f τ h hT)).symm.trans
        ((Attachments.residualDiagram W (τ ⋙ WordAction.functor f) (f.orderHom (firstColumn W
          (τ.obj 0) h)) hT).obj d).first.symm)
  | right k =>
    exact Attachments.residual_action_vertex W f τ (firstColumn W (τ.obj 0) h)
      (firstColumn_nonempty W (τ.obj 0) h) (firstColumn_forward W (τ.obj 0) h) hT d k

lemma prefix_apps {d e : Fin (n.unop.len + 1)} (g : d ⟶ e)
    (k : Fin ((prefixWord b (f.orderHom (firstColumn W (τ.obj 0) h))).length + 1)) :
    HEq ((WordAction.movingMap (prefixMap f (firstColumn W (τ.obj 0) h) (firstColumn_forward W
      (τ.obj 0) h))
      ((Attachments.prefixDiagram W τ (firstColumn W (τ.obj 0) h) (firstColumn_nonempty W (τ.obj
        0) h)).map g)).app k)
      (((Attachments.prefixDiagram W (τ ⋙ WordAction.functor f) (f.orderHom (firstColumn W (τ.obj
        0) h)) hT).map g).app k) := by
  cases k using Fin.lastCases with
  | last =>
    have ho := (congrArg (fun g : Quiver.Total C => (show Paths C from g.left))
      (generator_eq W f τ h hT)).symm
    exact ((Zigzag.MovingDiagram.wordAction (prefixMap f (firstColumn W (τ.obj 0) h)
      (firstColumn_forward W (τ.obj 0) h))
      (Attachments.prefixDiagram W τ (firstColumn W (τ.obj 0) h) (firstColumn_nonempty W (τ.obj
        0) h))).last g).trans
      (((eqToHom_heq_id_dom _ _ ho).symm.trans (eqToHom_heq_id_cod _ _ ho)).trans
        ((Attachments.prefixDiagram W (τ ⋙ WordAction.functor f) (f.orderHom (firstColumn W
          (τ.obj 0) h)) hT).last g).symm)
  | cast k =>
    exact Attachments.prefix_action_app W f τ (firstColumn W (τ.obj 0) h)
      (firstColumn_nonempty W (τ.obj 0) h) (firstColumn_forward W (τ.obj 0) h) hT g k

lemma residual_apps {d e : Fin (n.unop.len + 1)} (g : d ⟶ e)
    (k : Fin ((residualWord b (f.orderHom (firstColumn W (τ.obj 0) h))).length + 1)) :
    HEq ((WordAction.movingMap (residualMap f (firstColumn W (τ.obj 0) h) (firstColumn_forward W
      (τ.obj 0) h))
      ((Attachments.residualDiagram W τ (firstColumn W (τ.obj 0) h) (firstColumn_nonempty W
        (τ.obj 0) h)).map g)).app k)
      (((Attachments.residualDiagram W (τ ⋙ WordAction.functor f) (f.orderHom (firstColumn W
        (τ.obj 0) h)) hT).map g).app k) := by
  change Fin (1 + ((Word.ColumnSplit.after b (f.orderHom (firstColumn W (τ.obj 0) h))).length +
    1)) at k
  cases k using Fin.addCases with
  | left k =>
    have hk : k = (0 : Fin 1) := Subsingleton.elim _ _
    subst k
    have ho := (congrArg (fun g : Quiver.Total C => (show Paths C from g.right))
      (generator_eq W f τ h hT)).symm
    exact ((Zigzag.MovingDiagram.wordAction (residualMap f (firstColumn W (τ.obj 0) h)
      (firstColumn_forward W (τ.obj 0) h))
      (Attachments.residualDiagram W τ (firstColumn W (τ.obj 0) h) (firstColumn_nonempty W (τ.obj
        0) h))).first g).trans
      (((eqToHom_heq_id_dom _ _ ho).symm.trans (eqToHom_heq_id_cod _ _ ho)).trans
        ((Attachments.residualDiagram W (τ ⋙ WordAction.functor f) (f.orderHom (firstColumn W
          (τ.obj 0) h)) hT).first g).symm)
  | right k =>
    exact Attachments.residual_action_app W f τ (firstColumn W (τ.obj 0) h) (firstColumn_nonempty
      W (τ.obj 0) h) (firstColumn_forward W (τ.obj 0) h) hT g k

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactorAction
