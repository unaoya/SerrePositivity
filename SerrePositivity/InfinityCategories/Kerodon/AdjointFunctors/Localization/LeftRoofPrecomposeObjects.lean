module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoofPrecomposeWords

/-!
# 元の augmentation 正方形による二つの四列

概要：元の始域比較の二行と、弱同値の縦射を持つ同じ正方形を構成する。
方針：元の augmentation を縦成分に使う。
規約：任意の元の始域射と中間射を保持する。
使われ方：source frame 比較の始域自然性のホモトピー。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoofPrecomposeObjects
open CategoryTheory
variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative]
  {X' X U' U Y : C} (p' : U' ⟶ X') (hp' : W p') (p : U ⟶ X) (hp : W p)
  (α : U' ⟶ U) (f : X' ⟶ X) (σ : U ⟶ Y)

def upper : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoofPrecomposeWords.word X' Y where
  vertex := ![X', U', U, U, Y]
  first := rfl
  last := rfl
  arrow := Fin.cases p' (Fin.cases α (Fin.cases (𝟙 U) (Fin.cases σ (fun i => Fin.elim0 i))))
  backward_mem i hi := by
    fin_cases i
    · exact hp'
    · cases hi
    · exact W.id_mem U
    · cases hi

def lower : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoofPrecomposeWords.word X' Y where
  vertex := ![X', X', X, U, Y]
  first := rfl
  last := rfl
  arrow := Fin.cases (𝟙 X') (Fin.cases f (Fin.cases p (Fin.cases σ (fun i => Fin.elim0 i))))
  backward_mem i hi := by
    fin_cases i
    · exact W.id_mem X'
    · cases hi
    · exact hp
    · cases hi

def component (h : α ≫ p = p' ≫ f) : upper W p' hp' α σ ⟶ lower W p hp f σ where
  app := Fin.cases (𝟙 X') (Fin.cases p' (Fin.cases p
    (Fin.cases (𝟙 U) (Fin.cases (𝟙 Y) (fun i => Fin.elim0 i)))))
  app_mem i := by
    fin_cases i
    · exact W.id_mem X'
    · exact hp'
    · exact hp
    · exact W.id_mem U
    · exact W.id_mem Y
  first := rfl
  last := rfl
  comm i := by
    fin_cases i
    · rfl
    · exact h
    · rfl
    · exact (Category.comp_id _).trans (Category.id_comp _).symm

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.LeftRoofPrecomposeObjects
