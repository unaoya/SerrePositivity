module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Replacements.MiddleBackwardPullback

/-!
# 中央の自明 cofibration を右ブロック全体の pushout で置換する

概要：元の X,Y を固定し、中央を指定中間対象の恒等列にした実際の zigzag を構成。
方針：右ブロックの包含と中央の正方形を貼り、元の全体からの縦弱同値を作る。
規約：同じ語・同じ左右の外側の射を使う。長さ零も含む。
使われ方：中央の恒等列の包含に向かう unit の成分。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C] {n m : ℕ} {X Y : C}

def pushoutInput (L : ComposableArrows C n) (R : ComposableArrows C m)
    (c : R.obj 0 ⟶ L.obj (Fin.last n)) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InitialReplacement C m :=
  ⟨R, L.obj (Fin.last n), c⟩

def pushoutObj (L : ComposableArrows C n) (R : ComposableArrows C m)
    (a : L.obj 0 ⟶ X) (ha : weakEquivalences C a)
    (c : R.obj 0 ⟶ L.obj (Fin.last n)) (hc : trivialCofibrations C c)
    (b : Y ⟶ R.obj (Fin.last m)) (hb : weakEquivalences C b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (weakEquivalences C) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.word n m) X Y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.leftBoundaryBlock L a ha)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzag.obj (𝟙 (L.obj (Fin.last n))) ((weakEquivalences C).id_mem _)))
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.pushoutRightBoundary (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.pushoutInput L R c) hc b hb)

def pushoutInclusion (L : ComposableArrows C n) (R : ComposableArrows C m)
    (a : L.obj 0 ⟶ X) (ha : weakEquivalences C a)
    (c : R.obj 0 ⟶ L.obj (Fin.last n)) (hc : trivialCofibrations C c)
    (b : Y ⟶ R.obj (Fin.last m)) (hb : weakEquivalences C b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag.Hom (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.MiddleBackwardPullback.obj L R a ha c hc.2 b hb) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.pushoutObj L R a ha c hc b hb) := by
  let f := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.id (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.leftBoundaryBlock L a ha)
  let g := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzag.movingHom hc.2 ((weakEquivalences C).id_mem _)
    (𝟙 (L.obj (Fin.last n))) c ((weakEquivalences C).id_mem _) hc.2 rfl
  have hj : HEq (f.app (Fin.last (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.leftBoundaryWord n).length)) (g.app 0) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.id_last (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.leftBoundaryBlock L a ha)
  let fg := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendMorphisms.map f g hj
  let k := _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.pushoutRightBoundaryInclusion (pushoutInput L R c) hc b hb
  have hj' : HEq (fg.app (Fin.last (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.leftBoundaryWord n)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward)).length)) (k.app 0) := by
    apply HEq.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendVertical.app_right_heq f g hj (Fin.last 1))
    exact (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.pushoutRightBoundaryInclusion_first (pushoutInput L R c) hc b hb).symm
  have hf : fg.app 0 = eqToHom
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.leftBoundaryBlock L a ha) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzag.obj c hc.2)).first.trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.leftBoundaryBlock L a ha)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzag.obj (𝟙 (L.obj (Fin.last n)))
          ((weakEquivalences C).id_mem _))).first.symm) := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.first_of_heq_id fg
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendVertical.app_left_heq f g 0).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.id_first _)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fixedMap fg k hj' hf
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom.last_of_heq_id k
      (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.pushoutRightBoundaryInclusion_last (pushoutInput L R c) hc b hb))

end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
