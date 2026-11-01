module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.Transfunctor
public import SerrePositivity.EInfinity.Hammock.TwoSidedDiagramBar

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
namespace SerrePositivity.EInfinity.Hammock.Transfunctor
open CategoryTheory Opposite
private lemma natTrans_hext {C D : Type*} [Category* C] [Category* D]
    {F F' G G' : C ⥤ D} (hF : F = F') (hG : G = G')
    (α : F ⟶ G) (β : F' ⟶ G') (ha : ∀ X, HEq (α.app X) (β.app X)) : HEq α β := by
  cases hF
  cases hG
  apply heq_of_eq
  ext X
  exact eq_of_heq (ha X)

variable {I : Type v} [Category I] (B : I ⥤ Cat.{u, u})
  (L : Covariant (B ⋙ Cat.opFunctor)) (R : Covariant B)

def twoSidedDiagram : I ⥤ TwoSidedDiagram.Data.{u} where
  obj i := ⟨B.obj i, fiber L i, fiber R i⟩
  map θ := ⟨(B.map θ).toFunctor, transition L θ, transition R θ⟩
  map_id i := by
    refine TwoSidedDiagram.hom_ext _ _ ?_ ?_ ?_
    · exact congrArg Cat.Hom.toFunctor (B.map_id i)
    · change HEq (transition L (𝟙 i)) (𝟙 (fiber L i))
      refine natTrans_hext rfl ?_ _ _ (transition_id_app L i)
      rw [(B ⋙ Cat.opFunctor).map_id]
      rfl
    · change HEq (transition R (𝟙 i)) (𝟙 (fiber R i))
      refine natTrans_hext rfl ?_ _ _ (transition_id_app R i)
      rw [B.map_id]
      rfl
  map_comp θ φ := by
    refine TwoSidedDiagram.hom_ext _ _ ?_ ?_ ?_
    · exact congrArg Cat.Hom.toFunctor (B.map_comp θ φ)
    · change HEq (transition L (θ ≫ φ))
        (transition L θ ≫ Functor.whiskerLeft ((B ⋙ Cat.opFunctor).map θ).toFunctor
          (transition L φ))
      refine natTrans_hext rfl ?_ _ _ (transition_comp_app L θ φ)
      rw [(B ⋙ Cat.opFunctor).map_comp]
      rfl
    · change HEq (transition R (θ ≫ φ))
        (transition R θ ≫ Functor.whiskerLeft (B.map θ).toFunctor (transition R φ))
      refine natTrans_hext rfl ?_ _ _ (transition_comp_app R θ φ)
      rw [B.map_comp]
      rfl

def totalDiagram : I ⥤ Cat.{u, u} :=
  twoSidedDiagram B L R ⋙ TwoSidedDiagram.totalFunctor

def barDiagram : I ⥤ SSet.{u} :=
  twoSidedDiagram B L R ⋙ TwoSidedDiagram.barFunctor

def comparison : barDiagram B L R ⟶ totalDiagram B L R ⋙ nerveFunctor :=
  Functor.whiskerLeft (twoSidedDiagram B L R) TwoSidedDiagram.thomasonMap

end SerrePositivity.EInfinity.Hammock.Transfunctor
