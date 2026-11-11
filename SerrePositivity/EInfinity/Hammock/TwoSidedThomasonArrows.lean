module

public import SerrePositivity.EInfinity.Hammock.ContravariantThomasonArrows
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieckHomComponents
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedBar
public import SerrePositivity.EInfinity.FrameHom.ThomasonSimplex

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
namespace SerrePositivity.EInfinity.Hammock.TwoSidedThomason
open CategoryTheory Opposite


variable {W : Type u} [Category.{u} W]
  (F : Wᵒᵖ ⥤ Cat.{u, u}) (G : W ⥤ Cat.{u, u})

abbrev labels (n : ℕ) := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedElements.Element
  (FrameHom.Thomason.values F n) (FrameHom.Thomason.values G n)

variable {n : ℕ} (e : ComposableArrows (labels F G n) n)

def vertex (i : Fin (n + 1)) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.total F G :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.mk F G (e.obj i).base ((e.obj i).left.obj i) ((e.obj i).right.obj i)

def leftArrow {i j : Fin (n + 1)} (h : i ⟶ j) :
    (e.obj i).left.obj i ⟶ (F.map (e.map h).base.op).toFunctor.obj ((e.obj j).left.obj j) :=
  ContravariantThomason.leftArrow F (FrameHom.Thomason.values G n) e h

def rightArrow {i j : Fin (n + 1)} (h : i ⟶ j) :
    (G.map (e.map h).base).toFunctor.obj ((e.obj i).right.obj i) ⟶ (e.obj j).right.obj j :=
  eqToHom (congrArg (fun q => q.obj i) (e.map h).right) ≫ (e.obj j).right.map h

def arrow {i j : Fin (n + 1)} (h : i ⟶ j) : vertex F G e i ⟶ vertex F G e j :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedGrothendieck.homMk (e.map h).base (leftArrow F G e h) (rightArrow F G e h)

lemma leftArrow_id_heq (i : Fin (n + 1)) :
    HEq (leftArrow F G e (𝟙 i)) (𝟙 ((e.obj i).left.obj i)) :=
  ContravariantThomason.leftArrow_id_heq F (FrameHom.Thomason.values G n) e i

lemma rightArrow_id_heq (i : Fin (n + 1)) :
    HEq (rightArrow F G e (𝟙 i)) (𝟙 ((e.obj i).right.obj i)) := by
  unfold rightArrow
  simp only [eqToHom_comp_heq_iff]
  exact heq_of_eq ((e.obj i).right.map_id i)

lemma leftArrow_comp_heq {i j k : Fin (n + 1)} (h : i ⟶ j) (l : j ⟶ k) :
    HEq (leftArrow F G e (h ≫ l))
      (leftArrow F G e h ≫ (F.map (e.map h).base.op).toFunctor.map (leftArrow F G e l)) :=
  ContravariantThomason.leftArrow_comp_heq F (FrameHom.Thomason.values G n) e h l

lemma rightArrow_comp_heq {i j k : Fin (n + 1)} (h : i ⟶ j) (l : j ⟶ k) :
    HEq (rightArrow F G e (h ≫ l))
      ((G.map (e.map l).base).toFunctor.map (rightArrow F G e h) ≫ rightArrow F G e l) := by
  have hn := eqToHom_naturality
    (fun q : ComposableArrows (G.obj (e.obj k).base) n => q.map h) (e.map l).right
  change (G.map (e.map l).base).toFunctor.map ((e.obj j).right.map h) ≫ eqToHom _ =
    eqToHom _ ≫ (e.obj k).right.map h at hn
  unfold rightArrow
  simp only [Functor.map_comp, eqToHom_map, Category.assoc]
  rw [reassoc_of% hn]
  simp only [eqToHom_trans_assoc, eqToHom_comp_heq_iff, heq_eqToHom_comp_iff]
  rfl

end SerrePositivity.EInfinity.Hammock.TwoSidedThomason
