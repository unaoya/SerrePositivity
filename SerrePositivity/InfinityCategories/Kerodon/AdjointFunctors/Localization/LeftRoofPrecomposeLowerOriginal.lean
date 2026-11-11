module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoofPrecomposeLowerInsertion
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoofPrecomposeDiagram

/-!
# 始域比較の下行を元の前合成へ回収する全図式

概要：下行は元の始域射と roof の連結へ恒等列を挿入した同じ全図式。
方針：元の cut と連結の全縦射の回収を使う。
規約：元の射と全対象・全作用素を保持する。
使われ方：下行の nerve ホモトピーと元の前合成の照合。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v uI vI
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory
variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative]
  {I : Type uI} [Category.{vI} I] {X' X Y : C}
  (A : I ⥤ C) (p : A ⟶ (Functor.const I).obj X) (hp : ∀ i, W (p.app i))
  (f : X' ⟶ X) (σ : A ⟶ (Functor.const I).obj Y)
  (hA : ∀ {i j} (a : i ⟶ j), W (A.map a))

lemma lowerDiagram_insert :
    ((Functor.const I).obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj (W := W) f)).prod'
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.diagram W A p hp σ hA) ⋙
      _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendFunctor.functor ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.functor _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoofPrecomposeWords.lowerInsert =
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lowerDiagram W A p hp f σ hA := by
  have ho (i : I) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAction.obj _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoofPrecomposeWords.lowerInsert
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj f) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.obj W (p.app i) (hp i) (σ.app i))) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoofPrecomposeObjects.lower W (p.app i) (hp i) f (σ.app i) := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.lowerInsert_obj W _ _ _ _
  apply CategoryTheory.Functor.hext ho
  intro i j a
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagExt.hom_hext (ho i) (ho j)
  intro k
  change HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertical.app (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj (W := W) f))
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.diagram W A p hp σ hA).map a) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoofPrecomposeWords.lowerInsert.cut k)) _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoofPrecomposeWords.lowerInsert_cut]
  fin_cases k
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertical.app_left_heq (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj (W := W) f))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.diagram W A p hp σ hA).map a) (0 : Fin 2)
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertical.app_left_heq (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj (W := W) f))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.diagram W A p hp σ hA).map a) (0 : Fin 2)
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertical.app_left_heq (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj (W := W) f))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.diagram W A p hp σ hA).map a) (1 : Fin 2)
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertical.app_right_heq (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj (W := W) f))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.diagram W A p hp σ hA).map a) (1 : Fin 3)
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendVertical.app_right_heq (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ForwardZigzag.obj (W := W) f))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoof.diagram W A p hp σ hA).map a) (2 : Fin 3)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
