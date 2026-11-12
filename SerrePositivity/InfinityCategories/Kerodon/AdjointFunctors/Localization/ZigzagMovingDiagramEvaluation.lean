module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagram
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingHomSquareTransport
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagColumnDiagram

/-!
# 動く端点を持つ図式の評価と列

概要：各頂点の評価関手、各列の自然変換、端点関手との自然同型を構成する。
方針：元の全縦射と位置の移送を用い、両端では元の HEq を回収する。
規約：端点関手の射も元の弱同値であることを証明する。
使われ方：任意の前後の語の中の局所ブロックから MovingFamily を抽出する。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v u' v'
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagramEvaluation
open CategoryTheory

variable {D : Type u'} [Category.{v'} D] {C : Type u} [Category.{v} C]
  {W : MorphismProperty C} [W.IsMultiplicative] {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {A B : D ⥤ C}
  (F : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram D C W w A B)

def evaluation (i : Fin (w.length + 1)) : D ⥤ C where
  obj d := (F.obj d).vertex i
  map f := (F.map f).app i
  map_id d := congrArg (fun g => g.app i) (F.map_id d)
  map_comp f g := congrArg (fun h => h.app i) (F.map_comp f g)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagramEvaluation (evaluation)


def columnDiagram (j : Fin w.length) (l r : Fin (w.length + 1))
    (hl : l = w.source j) (hr : w.target j = r) : F.evaluation l ⟶ F.evaluation r where
  app d := eqToHom (congrArg (F.obj d).vertex hl) ≫ (F.obj d).arrow j ≫
    eqToHom (congrArg (F.obj d).vertex hr)
  naturality _ _ f := ((F.map f).square_transport j l r hl hr).symm

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagramEvaluation (columnDiagram)


lemma columnDiagram_mem (j : Fin w.length) (l r : Fin (w.length + 1))
    (hl : l = w.source j) (hr : w.target j = r) (hj : w.direction j = .backward)
    (d : D) : W ((F.columnDiagram j l r hl hr).app d) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.transport_mem _ _ _).2 ((F.obj d).backward_mem j hj)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagramEvaluation (columnDiagram_mem)


def firstEvaluationIso : F.evaluation 0 ≅ A :=
  NatIso.ofComponents (fun d => eqToIso (F.obj d).first) (by
    intro d d' f
    have h := (conj_eqToHom_iff_heq _ _ (F.obj d).first (F.obj d').first).2 (F.first f)
    change (F.map f).app 0 ≫ eqToHom (F.obj d').first =
      eqToHom (F.obj d).first ≫ A.map f
    rw [h]
    simp)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagramEvaluation (firstEvaluationIso)


def lastEvaluationIso : F.evaluation (Fin.last w.length) ≅ B :=
  NatIso.ofComponents (fun d => eqToIso (F.obj d).last) (by
    intro d d' f
    have h := (conj_eqToHom_iff_heq _ _ (F.obj d).last (F.obj d').last).2 (F.last f)
    change (F.map f).app (Fin.last w.length) ≫ eqToHom (F.obj d').last =
      eqToHom (F.obj d).last ≫ B.map f
    rw [h]
    simp)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagramEvaluation (lastEvaluationIso)


include F in
lemma endpoint_left_mem {d d' : D} (f : d ⟶ d') : W (A.map f) := by
  have h := (conj_eqToHom_iff_heq _ _ (F.obj d).first (F.obj d').first).2 (F.first f)
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.transport_mem (F.obj d).first (F.obj d').first.symm (A.map f)).1
  rw [← h]
  exact (F.map f).app_mem 0

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagramEvaluation (endpoint_left_mem)


include F in
lemma endpoint_right_mem {d d' : D} (f : d ⟶ d') : W (B.map f) := by
  have h := (conj_eqToHom_iff_heq _ _ (F.obj d).last (F.obj d').last).2 (F.last f)
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.transport_mem (F.obj d).last (F.obj d').last.symm (B.map f)).1
  rw [← h]
  exact (F.map f).app_mem (Fin.last w.length)

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingDiagram export _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagramEvaluation (endpoint_right_mem)


end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingDiagramEvaluation
