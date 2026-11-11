module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ForwardPathZigzag
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzag
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendFixed

/-!
# 元の外側の backward 列を保持する forward ブロックの置換

概要：左への pullback と右への pushout を、元の外側の弱同値へ合成する。
方針：正規化した射列の全縦射を一列の backward の正方形と貼り合わせる。
規約：外側の X または Y は固定し、内側の指定置換対象は動いてよい。
使われ方：中央の backward 列の分解を元の全体の zigzag に組み込む。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C] {n : ℕ}

abbrev leftBoundaryWord (n : ℕ) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.forwardWord n)
abbrev rightBoundaryWord (n : ℕ) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.forwardWord n) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward)

def leftBoundaryBlock (F : ComposableArrows C n) {X : C} (e : F.obj 0 ⟶ X)
    (he : weakEquivalences C e) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (weakEquivalences C) (leftBoundaryWord n) X (F.obj (Fin.last n)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzag.obj e he) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.zigzag F rfl rfl)

def rightBoundaryBlock (F : ComposableArrows C n) {Y : C} (e : Y ⟶ F.obj (Fin.last n))
    (he : weakEquivalences C e) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (weakEquivalences C) (rightBoundaryWord n) (F.obj 0) Y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.zigzag F rfl rfl) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzag.obj e he)

def pullbackLeftBoundary (s : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TerminalReplacement C n) (hs : trivialFibrations C s.hom)
    {X : C} (e : s.right.obj 0 ⟶ X) (he : weakEquivalences C e) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (weakEquivalences C) (leftBoundaryWord n) X s.left :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzag.obj ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.normalizedPullbackProjection s).app 0 ≫ e)
      ((weakEquivalences C).comp_mem _ _
        (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.normalizedPullbackProjection_trivialFibration s hs 0).2 he))
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.normalizedPullbackZigzag s)

def pullbackLeftBoundaryProjection (s : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TerminalReplacement C n)
    (hs : trivialFibrations C s.hom) {X : C} (e : s.right.obj 0 ⟶ X)
    (he : weakEquivalences C e) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom (pullbackLeftBoundary s hs e he) (leftBoundaryBlock s.right e he) := by
  let f := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzag.movingHom
    ((weakEquivalences C).comp_mem _ _
      (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.normalizedPullbackProjection_trivialFibration s hs 0).2 he) he
    (𝟙 X) ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.normalizedPullbackProjection s).app 0) ((weakEquivalences C).id_mem X)
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.normalizedPullbackProjection_trivialFibration s hs 0).2 (Category.comp_id _)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendMorphisms.map f (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.normalizedPullbackProjectionMoving s hs) HEq.rfl

def pushoutRightBoundary (s : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InitialReplacement C n) (hs : trivialCofibrations C s.hom)
    {Y : C} (e : Y ⟶ s.left.obj (Fin.last n)) (he : weakEquivalences C e) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (weakEquivalences C) (rightBoundaryWord n) s.right Y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagAppendObjects.obj (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.normalizedPushoutZigzag s)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzag.obj (e ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.normalizedPushoutInclusion s).app (Fin.last n))
      ((weakEquivalences C).comp_mem _ _ he
        (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.normalizedPushoutInclusion_trivialCofibration s hs (Fin.last n)).2))

def pushoutRightBoundaryInclusion (s : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InitialReplacement C n)
    (hs : trivialCofibrations C s.hom) {Y : C} (e : Y ⟶ s.left.obj (Fin.last n))
    (he : weakEquivalences C e) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom (rightBoundaryBlock s.left e he) (pushoutRightBoundary s hs e he) := by
  let g := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzag.movingHom he
    ((weakEquivalences C).comp_mem _ _ he
      (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.normalizedPushoutInclusion_trivialCofibration s hs (Fin.last n)).2)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.normalizedPushoutInclusion s).app (Fin.last n)) (𝟙 Y)
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.normalizedPushoutInclusion_trivialCofibration s hs (Fin.last n)).2
    ((weakEquivalences C).id_mem Y) (Category.id_comp _).symm
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendMorphisms.map (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.normalizedPushoutInclusionMoving s hs) g HEq.rfl

lemma pullbackLeftBoundaryProjection_first (s : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TerminalReplacement C n)
    (hs : trivialFibrations C s.hom) {X : C} (e : s.right.obj 0 ⟶ X)
    (he : weakEquivalences C e) :
    HEq ((pullbackLeftBoundaryProjection s hs e he).app 0) (𝟙 X) := by
  dsimp only [pullbackLeftBoundaryProjection, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendMorphisms.map]
  apply HEq.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendVertical.app_left_heq _
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.normalizedPullbackProjectionMoving s hs) 0)
  rfl

lemma pullbackLeftBoundaryProjection_last (s : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TerminalReplacement C n)
    (hs : trivialFibrations C s.hom) {X : C} (e : s.right.obj 0 ⟶ X)
    (he : weakEquivalences C e) :
    HEq ((pullbackLeftBoundaryProjection s hs e he).app (Fin.last (leftBoundaryWord n).length))
      s.hom := by
  dsimp only [pullbackLeftBoundaryProjection, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendMorphisms.map]
  apply HEq.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendVertical.app_right_heq _
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.normalizedPullbackProjectionMoving s hs) HEq.rfl (Fin.last n))
  change HEq ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.normalizedPullbackProjection s).app (Fin.last n)) s.hom
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.normalizedPullbackProjection_last]
  simp only [eqToHom_comp_heq_iff]
  rfl

lemma pushoutRightBoundaryInclusion_first (s : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InitialReplacement C n)
    (hs : trivialCofibrations C s.hom) {Y : C} (e : Y ⟶ s.left.obj (Fin.last n))
    (he : weakEquivalences C e) :
    HEq ((pushoutRightBoundaryInclusion s hs e he).app 0) s.hom := by
  dsimp only [pushoutRightBoundaryInclusion, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendMorphisms.map]
  apply HEq.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendVertical.app_left_heq
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.normalizedPushoutInclusionMoving s hs) _ 0)
  exact heq_of_eq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.normalizedPushoutInclusion_zero s)

lemma pushoutRightBoundaryInclusion_last (s : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InitialReplacement C n)
    (hs : trivialCofibrations C s.hom) {Y : C} (e : Y ⟶ s.left.obj (Fin.last n))
    (he : weakEquivalences C e) :
    HEq ((pushoutRightBoundaryInclusion s hs e he).app
      (Fin.last (rightBoundaryWord n).length)) (𝟙 Y) := by
  dsimp only [pushoutRightBoundaryInclusion, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendMorphisms.map]
  apply HEq.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendVertical.app_right_heq (b := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward)
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.normalizedPushoutInclusionMoving s hs) _ HEq.rfl (Fin.last 1))
  rfl

end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
