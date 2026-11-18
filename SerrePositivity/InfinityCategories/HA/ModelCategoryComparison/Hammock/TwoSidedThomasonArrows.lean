module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ContravariantThomasonArrows
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieckHomComponents
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedBar
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.ThomasonSimplex

/-!
# 元の二方向 bar の対角頂点と比較射の左右の成分

概要：元の両ラベルの対角を評価し、元の全圏の射の左右の成分を構成する。
方針：左のラベル等式は逆向き、右のラベル等式は順向きに端点を移送する。
規約：元の底の射と元の左右のラベルを保持する。
使われ方：DK9.5の元の nerve 比較の各単体。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedThomason
open _root_.CategoryTheory _root_.Opposite


variable {W : Type u} [Category.{u} W]
  (F : Wᵒᵖ ⥤ Cat.{u, u}) (G : W ⥤ Cat.{u, u})

abbrev labels (n : ℕ) := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedElements.Element
  (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.Thomason.values F n) (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.Thomason.values G n)

variable {n : ℕ} (e : ComposableArrows (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedThomason.labels F G n) n)

def vertex (i : Fin (n + 1)) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.total F G :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.mk F G (e.obj i).base ((e.obj i).left.obj i) ((e.obj i).right.obj i)

def leftArrow {i j : Fin (n + 1)} (h : i ⟶ j) :
    (e.obj i).left.obj i ⟶ (F.map (e.map h).base.op).toFunctor.obj ((e.obj j).left.obj j) :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ContravariantThomason.leftArrow F (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.Thomason.values G n) e h

def rightArrow {i j : Fin (n + 1)} (h : i ⟶ j) :
    (G.map (e.map h).base).toFunctor.obj ((e.obj i).right.obj i) ⟶ (e.obj j).right.obj j :=
  eqToHom (congrArg (fun q => q.obj i) (e.map h).right) ≫ (e.obj j).right.map h

def arrow {i j : Fin (n + 1)} (h : i ⟶ j) : _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedThomason.vertex F G e i ⟶ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedThomason.vertex F G e j :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.homMk (e.map h).base (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedThomason.leftArrow F G e h) (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedThomason.rightArrow F G e h)

lemma leftArrow_id_heq (i : Fin (n + 1)) :
    HEq (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedThomason.leftArrow F G e (𝟙 i)) (𝟙 ((e.obj i).left.obj i)) :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ContravariantThomason.leftArrow_id_heq F (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.Thomason.values G n) e i

lemma rightArrow_id_heq (i : Fin (n + 1)) :
    HEq (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedThomason.rightArrow F G e (𝟙 i)) (𝟙 ((e.obj i).right.obj i)) := by
  unfold _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedThomason.rightArrow
  simp only [eqToHom_comp_heq_iff]
  exact heq_of_eq ((e.obj i).right.map_id i)

lemma leftArrow_comp_heq {i j k : Fin (n + 1)} (h : i ⟶ j) (l : j ⟶ k) :
    HEq (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedThomason.leftArrow F G e (h ≫ l))
      (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedThomason.leftArrow F G e h ≫ (F.map (e.map h).base.op).toFunctor.map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedThomason.leftArrow F G e l)) :=
  _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.ContravariantThomason.leftArrow_comp_heq F (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.Thomason.values G n) e h l

lemma rightArrow_comp_heq {i j k : Fin (n + 1)} (h : i ⟶ j) (l : j ⟶ k) :
    HEq (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedThomason.rightArrow F G e (h ≫ l))
      ((G.map (e.map l).base).toFunctor.map (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedThomason.rightArrow F G e h) ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedThomason.rightArrow F G e l) := by
  have hn := eqToHom_naturality
    (fun q : ComposableArrows (G.obj (e.obj k).base) n => q.map h) (e.map l).right
  change (G.map (e.map l).base).toFunctor.map ((e.obj j).right.map h) ≫ eqToHom _ =
    eqToHom _ ≫ (e.obj k).right.map h at hn
  unfold _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedThomason.rightArrow
  simp only [Functor.map_comp, eqToHom_map, Category.assoc]
  rw [reassoc_of% hn]
  simp only [eqToHom_trans_assoc, eqToHom_comp_heq_iff, heq_eqToHom_comp_iff]
  rfl

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.TwoSidedThomason
