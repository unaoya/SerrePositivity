module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordCons
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagExt
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory

/-!
# 先頭列の境界を動かした元の zigzag

概要：先頭が forward の元の語の始点に前合成する対象を構成する。
方針：始点だけを指定対象にし、残りの全頂点・全列を同じ端点移送で保持する。
規約：全 backward 列の元の指定条件と同じ終点を保持する。
使われ方：DK9.3・10.3の元の先頭の向きによる反変係数。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory
namespace Zigzag.FirstBoundary
variable {C : Type u} [Category.{u} C] {W : MorphismProperty C} {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X X' Y : C}

def vertex {d : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction} (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons d w) X Y) (X' : C) :
    Fin ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons d w).length + 1) → C :=
  Fin.cases X' (fun i => S.vertex i.succ)

lemma vertex_source_succ {d : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction} (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons d w) X Y)
    (X' : C) (i : Fin w.length) :
    vertex S X' ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons d w).source i.succ) = S.vertex ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons d w).source i.succ) := by
  dsimp only [vertex, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.source, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons]
  simp only [Fin.cases_succ]
  cases h : w.direction i <;> simp only [Fin.castSucc_succ, Fin.cases_succ]

lemma vertex_target_succ {d : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction} (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons d w) X Y)
    (X' : C) (i : Fin w.length) :
    vertex S X' ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons d w).target i.succ) = S.vertex ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons d w).target i.succ) := by
  dsimp only [vertex, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.target, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons]
  simp only [Fin.cases_succ]
  cases h : w.direction i <;> simp only [Fin.castSucc_succ, Fin.cases_succ]

def tailArrow {d : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction} (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons d w) X Y) (X' : C) (i : Fin w.length) :
    vertex S X' ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons d w).source i.succ) ⟶ vertex S X' ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons d w).target i.succ) :=
  eqToHom (vertex_source_succ S X' i) ≫ S.arrow i.succ ≫ eqToHom (vertex_target_succ S X' i).symm

def forwardArrow (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .forward w) X Y) (f : X' ⟶ X) :
    ∀ i, vertex S X' ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .forward w).source i) ⟶
      vertex S X' ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .forward w).target i) :=
  Fin.cases (f ≫ eqToHom S.first.symm ≫ S.arrow (0 : Fin (w.length + 1)))
    (tailArrow S X')

def forward (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .forward w) X Y) (f : X' ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .forward w) X' Y where
  vertex := vertex S X'
  first := rfl
  last := S.last
  arrow := forwardArrow S f
  backward_mem i hi := by
    cases i using Fin.cases with
    | zero => simp [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons] at hi
    | succ i =>
      change W (tailArrow S X' i)
      exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.DirectionCategory.transport_mem _ _ _).2 (S.backward_mem i.succ hi)
end Zigzag.FirstBoundary
end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
