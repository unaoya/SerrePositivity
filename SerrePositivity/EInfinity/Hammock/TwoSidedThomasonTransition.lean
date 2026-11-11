module

public import SerrePositivity.EInfinity.Hammock.TwoSidedThomasonWeak
public import SerrePositivity.EInfinity.Hammock.TwoSidedThomasonBaseChange
public import SerrePositivity.EInfinity.Hammock.TwoSidedThomasonNaturality

/-!
# 底と両係数を同時に変える元の二方向比較

概要：底の関手と両係数の射を組み合わせ、元の全圏と bar の同じ比較を得る。
方針：元の係数射・底の変更と DK9.5 の厳密な自然性を合成する。
規約：この比較自身の弱同値性は元の bar 比較自身の弱同値性と同値。
使われ方：DK10.1–10.6の transfunctor の全作用素。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.TwoSidedThomason
open CategoryTheory Opposite SerrePositivity.InfinityCategories
variable {V W : Type u} [Category.{u} V] [Category.{u} W] (H : V ⥤ W)
  {F : Vᵒᵖ ⥤ Cat.{u, u}} {G : V ⥤ Cat.{u, u}}
  {F' : Wᵒᵖ ⥤ Cat.{u, u}} {G' : W ⥤ Cat.{u, u}}
  (α : F ⟶ H.op ⋙ F') (β : G ⟶ H ⋙ G')

def transitionTotal : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.total F G ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.total F' G' :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieckFunctoriality.coefficientMap α β ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieckFunctoriality.baseChange H F' G'

def transitionBar : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedBar.space (F ⋙ nerveFunctor) (G ⋙ nerveFunctor) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedBar.space (F' ⋙ nerveFunctor) (G' ⋙ nerveFunctor) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedBar.map (Functor.whiskerRight α nerveFunctor) (Functor.whiskerRight β nerveFunctor) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedBarBaseChange.baseChange H (F' ⋙ nerveFunctor) (G' ⋙ nerveFunctor)

lemma map_transition :
    map F G ≫ nerveMap (transitionTotal H α β) = transitionBar H α β ≫ map F' G' := by
  change map F G ≫ nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieckFunctoriality.coefficientMap α β) ≫
    nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieckFunctoriality.baseChange H F' G') = _
  rw [← Category.assoc, map_naturality α β, Category.assoc, map_baseChange H F' G']
  rfl

lemma transition_weak_iff :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (nerveMap (transitionTotal H α β)) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (transitionBar H α β) := by
  constructor
  · intro h
    have hc := (map_isWeakHomotopyEquivalence F G).comp h
    rw [map_transition H α β] at hc
    exact (map_isWeakHomotopyEquivalence F' G').cancel_right hc
  · intro h
    have hc := h.comp (map_isWeakHomotopyEquivalence F' G')
    rw [← map_transition H α β] at hc
    exact (map_isWeakHomotopyEquivalence F G).cancel_left hc

end SerrePositivity.EInfinity.Hammock.TwoSidedThomason
