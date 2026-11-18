module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Transfunctor
public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagramBar

/-!
# transfunctor の元の単体的二方向 Grothendieck 図式

概要：元の底の図式と両 transfunctor から全圏・bar・比較の全作用素を構成する。
方針：元の fiber と遷移自然変換を二方向図式の圏へ束ね、その元の関手を適用する。
規約：恒等・合成の端点移送を吸収し、元の全射をそのまま保持する。
使われ方：DK10.1–10.2の構成と10.6(i)の対角比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Transfunctor
open _root_.CategoryTheory _root_.Opposite
private lemma natTrans_hext {C D : Type*} [Category* C] [Category* D]
    {F F' G G' : C ⥤ D} (hF : F = F') (hG : G = G')
    (α : F ⟶ G) (β : F' ⟶ G') (ha : ∀ X, HEq (α.app X) (β.app X)) : HEq α β := by
  cases hF
  cases hG
  apply heq_of_eq
  ext X
  exact eq_of_heq (ha X)

variable {I : Type v} [Category I] (B : I ⥤ Cat.{u, u})
  (L : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Transfunctor.Covariant (B ⋙ Cat.opFunctor)) (R : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Transfunctor.Covariant B)

def twoSidedDiagram : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedDiagram.Data.{u} where
  obj i := ⟨B.obj i, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Transfunctor.fiber L i, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Transfunctor.fiber R i⟩
  map θ := ⟨(B.map θ).toFunctor, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Transfunctor.transition L θ, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Transfunctor.transition R θ⟩
  map_id i := by
    refine _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedDiagram.hom_ext _ _ ?_ ?_ ?_
    · exact congrArg Cat.Hom.toFunctor (B.map_id i)
    · change HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Transfunctor.transition L (𝟙 i)) (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Transfunctor.fiber L i))
      refine _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Transfunctor.natTrans_hext rfl ?_ _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Transfunctor.transition_id_app L i)
      rw [(B ⋙ Cat.opFunctor).map_id]
      rfl
    · change HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Transfunctor.transition R (𝟙 i)) (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Transfunctor.fiber R i))
      refine _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Transfunctor.natTrans_hext rfl ?_ _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Transfunctor.transition_id_app R i)
      rw [B.map_id]
      rfl
  map_comp θ φ := by
    refine _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedDiagram.hom_ext _ _ ?_ ?_ ?_
    · exact congrArg Cat.Hom.toFunctor (B.map_comp θ φ)
    · change HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Transfunctor.transition L (θ ≫ φ))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Transfunctor.transition L θ ≫ Functor.whiskerLeft ((B ⋙ Cat.opFunctor).map θ).toFunctor
          (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Transfunctor.transition L φ))
      refine _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Transfunctor.natTrans_hext rfl ?_ _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Transfunctor.transition_comp_app L θ φ)
      rw [(B ⋙ Cat.opFunctor).map_comp]
      rfl
    · change HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Transfunctor.transition R (θ ≫ φ))
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Transfunctor.transition R θ ≫ Functor.whiskerLeft (B.map θ).toFunctor (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Transfunctor.transition R φ))
      refine _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Transfunctor.natTrans_hext rfl ?_ _ _ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Transfunctor.transition_comp_app R θ φ)
      rw [B.map_comp]
      rfl

def totalDiagram : I ⥤ Cat.{u, u} :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Transfunctor.twoSidedDiagram B L R ⋙ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.totalFunctor

def barDiagram : I ⥤ SSet.{u} :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Transfunctor.twoSidedDiagram B L R ⋙ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.barFunctor

def comparison : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Transfunctor.barDiagram B L R ⟶ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Transfunctor.totalDiagram B L R ⋙ nerveFunctor :=
  Functor.whiskerLeft (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Transfunctor.twoSidedDiagram B L R) _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedDiagram.thomasonMap

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.Transfunctor
