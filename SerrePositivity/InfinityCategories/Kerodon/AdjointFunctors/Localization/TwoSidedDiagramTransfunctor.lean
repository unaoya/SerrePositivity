module

-- functorFrom の公開型に含まれる内部の端点移送の証明も読み込む。
import all Mathlib.CategoryTheory.Grothendieck
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedDiagram
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TransfunctorObjectDiagram
/-!
# 元の二方向図式からの係数 transfunctor の回収

概要：底と両係数が動く元の図式から Grothendieck 圏上の係数関手を構成する。
方針：元の全作用素と同じ端点移送を使い、既存の関手則へ回収する。
規約：元の全単体を保持し、弱同値性を入力にしない。
使われ方：DK10.6(ii)の固定頂点列ごとの Hom 因子分解。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedDiagramTransfunctor
open CategoryTheory Opposite

def baseFunctor : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedDiagram.Data.{u} ⥤ Cat.{u, u} where
  obj A := A.base
  map f := f.base.toCatHom
  map_id _ := rfl
  map_comp _ _ := rfl

lemma left_heq {A B : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedDiagram.Data.{u}} {f g : A ⟶ B} (h : f = g) : HEq f.left g.left := by
  cases h
  rfl
lemma right_heq {A B : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedDiagram.Data.{u}} {f g : A ⟶ B} (h : f = g) : HEq f.right g.right := by
  cases h
  rfl

variable {I : Type*} [Category* I] (D : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedDiagram.Data.{u})
def rightTransfunctor : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Transfunctor.Covariant (D ⋙ baseFunctor) :=
  Grothendieck.functorFrom (fun n => (D.obj n).right) (fun θ => (D.map θ).right)
    (fun n => by
      apply eq_of_heq
      exact (right_heq (D.map_id n)).trans (eqToHom_heq_id_dom _ _ _).symm)
    (fun _ _ _ θ φ => by
      apply eq_of_heq
      exact (right_heq (D.map_comp θ φ)).trans (comp_eqToHom_heq _ _).symm)

def leftTransfunctor : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Transfunctor.Covariant (D ⋙ baseFunctor ⋙ Cat.opFunctor) :=
  Grothendieck.functorFrom (fun n => (D.obj n).left) (fun θ => (D.map θ).left)
    (fun n => by
      apply eq_of_heq
      exact (left_heq (D.map_id n)).trans (eqToHom_heq_id_dom _ _ _).symm)
    (fun _ _ _ θ φ => by
      apply eq_of_heq
      exact (left_heq (D.map_comp θ φ)).trans (comp_eqToHom_heq _ _).symm)
end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedDiagramTransfunctor
