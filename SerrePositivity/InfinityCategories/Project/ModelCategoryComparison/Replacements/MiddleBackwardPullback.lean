module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Replacements.ForwardPathBoundaryComparisons

/-!
# 中央の backward 列を左ブロック全体の pullback で置換する

概要：元の X,Y を固定した全体の zigzag と、元の zigzag への縦弱同値を構成する。
方針：中央の弱同値 c≫p に対し、左ブロックを自明 fibration p で置換する。
規約：外側の元の backward 射も保持する。左右の forward 長は零でもよい。
使われ方：中央の列を自明 cofibration にする関手的置換の対象と counit 成分。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C] {n m : ℕ} {X Y : C}

abbrev word (n m : ℕ) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.leftBoundaryWord n) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward)) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightBoundaryWord m)

def obj (L : ComposableArrows C n) (R : ComposableArrows C m)
    (a : L.obj 0 ⟶ X) (ha : weakEquivalences C a)
    (u : R.obj 0 ⟶ L.obj (Fin.last n)) (hu : weakEquivalences C u)
    (b : Y ⟶ R.obj (Fin.last m)) (hb : weakEquivalences C b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (weakEquivalences C) (word n m) X Y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.leftBoundaryBlock L a ha) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzag.obj u hu))
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightBoundaryBlock R b hb)

lemma middle_weak (s : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TerminalReplacement C n) (hs : trivialFibrations C s.hom)
    (R : ComposableArrows C m) (u : R.obj 0 ⟶ s.right.obj (Fin.last n))
    (hu : weakEquivalences C u) (c : R.obj 0 ⟶ s.left) (h : c ≫ s.hom = u) :
    weakEquivalences C c := by
  apply (weakEquivalences C).of_postcomp _ s.hom hs.2
  exact h.symm ▸ hu

def pullbackObj (s : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TerminalReplacement C n) (hs : trivialFibrations C s.hom)
    (R : ComposableArrows C m) (a : s.right.obj 0 ⟶ X) (ha : weakEquivalences C a)
    (u : R.obj 0 ⟶ s.right.obj (Fin.last n)) (hu : weakEquivalences C u)
    (c : R.obj 0 ⟶ s.left) (h : c ≫ s.hom = u)
    (b : Y ⟶ R.obj (Fin.last m)) (hb : weakEquivalences C b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (weakEquivalences C) (word n m) X Y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.pullbackLeftBoundary s hs a ha)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzag.obj c (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.middle_weak s hs R u hu c h)))
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightBoundaryBlock R b hb)

def pullbackProjection (s : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TerminalReplacement C n) (hs : trivialFibrations C s.hom)
    (R : ComposableArrows C m) (a : s.right.obj 0 ⟶ X) (ha : weakEquivalences C a)
    (u : R.obj 0 ⟶ s.right.obj (Fin.last n)) (hu : weakEquivalences C u)
    (c : R.obj 0 ⟶ s.left) (h : c ≫ s.hom = u)
    (b : Y ⟶ R.obj (Fin.last m)) (hb : weakEquivalences C b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Hom (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.pullbackObj s hs R a ha u hu c h b hb) (obj s.right R a ha u hu b hb) := by
  let f := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.pullbackLeftBoundaryProjection s hs a ha
  let g := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzag.movingHom (middle_weak s hs R u hu c h) hu s.hom (𝟙 (R.obj 0))
    hs.2 ((weakEquivalences C).id_mem _) (h.trans (Category.id_comp u).symm)
  have hj : HEq (f.app (Fin.last (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.leftBoundaryWord n).length)) (g.app 0) :=
    _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.pullbackLeftBoundaryProjection_last s hs a ha
  let fg := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendMorphisms.map f g hj
  let k := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.id (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightBoundaryBlock R b hb)
  have hj' : HEq (fg.app (Fin.last (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.leftBoundaryWord n)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward)).length)) (k.app 0) := by
    apply HEq.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendVertical.app_right_heq f g hj (Fin.last 1))
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.id_first (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightBoundaryBlock R b hb)).symm
  have hf : fg.app 0 = eqToHom
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.pullbackLeftBoundary s hs a ha)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzag.obj c (middle_weak s hs R u hu c h))).first.trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.leftBoundaryBlock s.right a ha)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzag.obj u hu)).first.symm) := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.first_of_heq_id fg
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendVertical.app_left_heq f g 0).trans
      (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.pullbackLeftBoundaryProjection_first s hs a ha)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fixedMap fg k hj' hf
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.last_of_heq_id k (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.id_last _))

end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback
