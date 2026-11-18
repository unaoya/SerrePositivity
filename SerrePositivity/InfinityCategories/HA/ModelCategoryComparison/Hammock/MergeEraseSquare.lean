module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.PunctureSimplex
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordMerge
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordSurjectionDescent

/-!
# 元の合成と外側の削除の可換四角形からの局所合流

概要：面と退化の元の可換四角形から、各側一段の混合縮約の合流を得る。
方針：短い語の二列の色と残りの包含の色を、元の全射から回収する。
規約：元の全単体の像を回収してから基本削除を適用する。
使われ方：削除列が合成する二列の外側にある場合。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock
open _root_.CategoryTheory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative]
  (X Y : C) {n : SimplexCategoryᵒᵖ}

lemma merge_erase_join_of_square {k : ℕ} (d : Fin (k + 3) → _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction)
    (p : Fin (k + 2)) (hp : d p.castSucc = d p.succ) (j : Fin (k + 3))
    (q : Fin (k + 1)) (r : Fin (k + 2))
    (hc : ∀ x, p.predAbove (j.succAbove x) = r.succAbove (q.predAbove x))
    (τ : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W (⟨k + 3, d⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) X Y).obj n)
    (hτ : ∀ t, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.IdentityColumn (τ.obj t) j) :
    ∃ s : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock W X Y n,
      Relation.ReflGen (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Reduction W X Y n)
        ⟨_, ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W X Y).map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.mergeMap d p hp)).app n τ⟩ s ∧
      Relation.ReflGen (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Reduction W X Y n)
        ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.erase (⟨k + 3, d⟩ : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) j, _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.eraseSimplex W X Y j τ hτ⟩ s := by
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.punctureInclusion d j
  let f := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.mergeMap d p hp
  let u := e ≫ f
  have hq : (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.puncture d j).direction q.castSucc =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.puncture d j).direction q.succ := by
    have he : u.orderHom q.castSucc = u.orderHom q.succ := by
      change p.predAbove (j.succAbove q.castSucc) = p.predAbove (j.succAbove q.succ)
      rw [hc, hc, Fin.predAbove_castSucc_self, Fin.predAbove_succ_self]
    exact (u.direction_eq q.castSucc).symm.trans
      ((congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.mergeTarget d p).direction he).trans (u.direction_eq q.succ))
  let f' := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.mergeMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.puncture d j).direction q hq
  let h := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.descendSurjection f'
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.mergeMap_surjective (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.puncture d j).direction q hq) u
    (Fin.succAboveOrderEmb r).toOrderHom (fun x => (hc x).symm)
  have hh : Function.Injective h.orderHom := Fin.succAbove_right_injective
  have hr : Set.range h.orderHom = {r}ᶜ := Fin.range_succAbove r
  have hword : f' ≫ h = e ≫ f := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.descendSurjection_fac _ _ _ _ _
  let σ := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.punctureSimplex W X Y d j τ hτ
  let ρ := ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W X Y).map f').app n σ
  let s : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RawHammock W X Y n := ⟨_, ρ⟩
  have hfac : ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W X Y).map h).app n ρ =
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W X Y).map f).app n τ := by
    have he := congrArg (fun z => ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W X Y).map z).app n σ) hword
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp] at he
    change ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W X Y).map h).app n
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W X Y).map f').app n σ) =
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W X Y).map f).app n (((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W X Y).map e).app n σ) at he
    rw [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.punctureSimplex_fac] at he
    exact he
  refine ⟨s, Relation.ReflGen.single ?_, Relation.ReflGen.single ?_⟩
  · exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.erase_reduction_of_embedding W X Y h hh r hr ρ _ hfac
  · have he := _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.punctureSimplex_raw_eq W X Y d j τ hτ
    rw [← he]
    exact _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Reduction.merge _ q hq σ

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock
