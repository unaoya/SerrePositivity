module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedBar
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ThomasonSimplex

/-!
# 任意の右集合ラベルを持つ反変対角比較の左成分

概要：既存の二方向比較の左射と単位・合成の計算を任意の右集合ラベルへ一般化する。
方針：元の左ラベルの対角と同じ端点移送を使う。
規約：元の左射の式と計算を保ち、二方向比較もこの一般の計算を再利用する。
使われ方：DK9.5の右ラベル次数を固定した左比較。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.ContravariantThomason
open CategoryTheory Opposite
variable {W : Type u} [Category.{u} W]
  (F : Wᵒᵖ ⥤ Cat.{u, u}) (S : W ⥤ Type u)

abbrev labels (n : ℕ) := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedElements.Element (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.Thomason.values F n) S

variable {n : ℕ} (e : ComposableArrows (labels F S n) n)

def leftArrow {i j : Fin (n + 1)} (h : i ⟶ j) :
    (e.obj i).left.obj i ⟶ (F.map (e.map h).base.op).toFunctor.obj ((e.obj j).left.obj j) :=
  (e.obj i).left.map h ≫ eqToHom (congrArg (fun q => q.obj j) (e.map h).left.symm)


lemma leftArrow_id_heq (i : Fin (n + 1)) :
    HEq (leftArrow F S e (𝟙 i)) (𝟙 ((e.obj i).left.obj i)) := by
  unfold leftArrow
  simp only [comp_eqToHom_heq_iff]
  exact heq_of_eq ((e.obj i).left.map_id i)


lemma leftArrow_comp_heq {i j k : Fin (n + 1)} (h : i ⟶ j) (l : j ⟶ k) :
    HEq (leftArrow F S e (h ≫ l))
      (leftArrow F S e h ≫ (F.map (e.map h).base.op).toFunctor.map (leftArrow F S e l)) := by
  have hn := eqToHom_naturality
    (fun q : ComposableArrows (F.obj (op (e.obj i).base)) n => q.map l) (e.map h).left.symm
  change (e.obj i).left.map l ≫ eqToHom _ =
    eqToHom _ ≫ (F.map (e.map h).base.op).toFunctor.map ((e.obj j).left.map l) at hn
  unfold leftArrow
  simp only [Functor.map_comp, eqToHom_map, Category.assoc]
  rw [← reassoc_of% hn]
  simp only [eqToHom_trans, ← Category.assoc, comp_eqToHom_heq_iff, heq_comp_eqToHom_iff]
  rfl


end SerrePositivity.EInfinity.Hammock.ContravariantThomason
