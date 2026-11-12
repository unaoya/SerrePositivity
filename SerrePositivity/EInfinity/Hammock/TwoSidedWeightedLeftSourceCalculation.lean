module

public import SerrePositivity.EInfinity.Hammock.TwoSidedWeightedLeftSourceIso
public import SerrePositivity.EInfinity.FrameHom.ThomasonNerveMap

/-!
# 元の重み付き始域同型と一方向比較の単体ごとの照合

概要：始域同型を通した元の一方向比較を、元の重み付き対角射列へ回収する。
方針：一回の反転で両射列を照合してから、既存の二重反転の恒等式を使う。
規約：元の全射列・底・両ラベルと端点移送を保持する。
使われ方：元の重み付き左比較自身の弱同値性。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.TwoSidedWeightedLeftSource
open CategoryTheory Opposite
open SerrePositivity.KST.ProExcision

variable {W : Type u} [Category.{u} W] (F : Wᵒᵖ ⥤ Cat.{u, u}) (S : W ⥤ Type u)

def reverseLabels (n : ℕ) : FrameHom.Thomason.values F n ⟶
    FrameHom.Thomason.values (F ⋙ Cat.opFunctor) n where
  app w := ↾fun a => nerveOppositeSimplex a
  naturality w w' h := by apply ConcreteCategory.hom_ext; intro a; rfl

def barSimplex {n : ℕ} (e : ComposableArrows (ContravariantThomason.labels F S n) n) :
    ComposableArrows
      (FrameHom.Thomason.values (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedMixedLabel.pulledDiagram F S) n).Elements n :=
  oppositeNerveSimplex (e ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedElements.map (reverseLabels F n) (𝟙 S) ⋙
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.toOpposite (FrameHom.Thomason.values (F ⋙ Cat.opFunctor) n) S)

lemma spaceIso_hom_app (n : ℕ) (e : ComposableArrows (ContravariantThomason.labels F S n) n) :
    (spaceIso F S).hom.app (op (SimplexCategory.mk n)) e =
      SSet.opObjEquiv.symm (barSimplex F S e) := rfl

lemma simplex_transport {n : ℕ} (e : ComposableArrows (ContravariantThomason.labels F S n) n) :
    FrameHom.Thomason.simplex (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedMixedLabel.pulledDiagram F S) (barSimplex F S e) =
      oppositeNerveSimplex
        (TwoSidedWeightedLeft.simplex F S e ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedMixedLabel.fromMixed F S) := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro i j h
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  refine Grothendieck.ext _ _ rfl ?_
  dsimp only [FrameHom.Thomason.simplex, barSimplex, reverseLabels,
    oppositeNerveSimplex, nerveOppositeSimplex, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.toOpposite,
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.baseElementMap, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedMixedLabel.fromMixed, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedMixedLabel.fromMixedMap,
    TwoSidedWeightedLeft.simplex, ContravariantThomason.simplex,
    ContravariantThomason.arrow, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ContravariantGrothendieckComponents.homMk, ContravariantThomason.leftArrow,
    Functor.comp_map, Functor.comp_obj, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedElements.map]
  dsimp
  simp only [eqToHom_op, Category.id_comp]

end SerrePositivity.EInfinity.Hammock.TwoSidedWeightedLeftSource
