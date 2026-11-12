module

public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.ForwardPathBoundaryBlocks
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendLaws

/-!
# 外側の backward 列を持つ置換ブロックの全縦比較

概要：forward ブロックと内外の端点を同時に動かす全縦弱同値を構成する。
方針：元の射影・包含の自然性から外側の一列の正方形を作り、全成分を貼る。
規約：外側の端点の射も動いてよい。proper 性や cofibrancy は不要。
使われ方：中央の backward の関手的分解による元の zigzag の置換。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C] {n : ℕ}

def leftBoundaryComparison {F G : ComposableArrows C n} (η : F ⟶ G)
    (hη : ∀ i, weakEquivalences C (η.app i)) {X X' : C}
    (e : F.obj 0 ⟶ X) (e' : G.obj 0 ⟶ X')
    (he : weakEquivalences C e) (he' : weakEquivalences C e')
    (x : X ⟶ X') (hx : weakEquivalences C x) (h : e ≫ x = η.app 0 ≫ e') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.leftBoundaryBlock F e he) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.leftBoundaryBlock G e' he') :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendMorphisms.map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzag.movingHom he he' x (η.app 0) hx (hη 0) h)
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.movingHom η hη rfl rfl rfl rfl) HEq.rfl

def rightBoundaryComparison {F G : ComposableArrows C n} (η : F ⟶ G)
    (hη : ∀ i, weakEquivalences C (η.app i)) {Y Y' : C}
    (e : Y ⟶ F.obj (Fin.last n)) (e' : Y' ⟶ G.obj (Fin.last n))
    (he : weakEquivalences C e) (he' : weakEquivalences C e')
    (y : Y ⟶ Y') (hy : weakEquivalences C y) (h : e ≫ η.app (Fin.last n) = y ≫ e') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightBoundaryBlock F e he) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.rightBoundaryBlock G e' he') :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendMorphisms.map (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.movingHom η hη rfl rfl rfl rfl)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzag.movingHom he he' (η.app (Fin.last n)) y (hη _) hy h) HEq.rfl

def pullbackLeftBoundaryComparison {s t : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TerminalReplacement C n} (m : s ⟶ t)
    (hs : trivialFibrations C s.hom) (ht : trivialFibrations C t.hom)
    (hm : ∀ i, weakEquivalences C (m.right.app i)) {X X' : C}
    (e : s.right.obj 0 ⟶ X) (e' : t.right.obj 0 ⟶ X')
    (he : weakEquivalences C e) (he' : weakEquivalences C e')
    (x : X ⟶ X') (hx : weakEquivalences C x) (h : e ≫ x = m.right.app 0 ≫ e') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.pullbackLeftBoundary s hs e he) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.pullbackLeftBoundary t ht e' he') := by
  have hw : ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.normalizedPullbackProjection s).app 0 ≫ e) ≫ x =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.normalizedPullbackComparison m).app 0 ≫ ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.normalizedPullbackProjection t).app 0 ≫ e') := by
    have hn := congr_app (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.normalizedPullbackProjection_naturality m) 0
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.normalizedPullbackComparison m).app 0 ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.normalizedPullbackProjection t).app 0 =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.normalizedPullbackProjection s).app 0 ≫ m.right.app 0 at hn
    rw [Category.assoc, h, ← Category.assoc, ← hn, Category.assoc]
  let f := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzag.movingHom
    ((weakEquivalences C).comp_mem _ _
      (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.normalizedPullbackProjection_trivialFibration s hs 0).2 he)
    ((weakEquivalences C).comp_mem _ _
      (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.normalizedPullbackProjection_trivialFibration t ht 0).2 he')
    x ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.normalizedPullbackComparison m).app 0) hx
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.normalizedPullbackComparison_weakEquivalence m hs ht hm 0) hw
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendMorphisms.map f (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.normalizedPullbackComparisonMoving m hs ht hm) HEq.rfl

def pushoutRightBoundaryComparison {s t : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InitialReplacement C n} (m : s ⟶ t)
    (hs : trivialCofibrations C s.hom) (ht : trivialCofibrations C t.hom)
    (hm : ∀ i, weakEquivalences C (m.left.app i)) {Y Y' : C}
    (e : Y ⟶ s.left.obj (Fin.last n)) (e' : Y' ⟶ t.left.obj (Fin.last n))
    (he : weakEquivalences C e) (he' : weakEquivalences C e')
    (y : Y ⟶ Y') (hy : weakEquivalences C y) (h : e ≫ m.left.app (Fin.last n) = y ≫ e') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.pushoutRightBoundary s hs e he) (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.pushoutRightBoundary t ht e' he') := by
  have hw : (e ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.normalizedPushoutInclusion s).app (Fin.last n)) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.normalizedPushoutComparison m).app (Fin.last n) =
        y ≫ (e' ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.normalizedPushoutInclusion t).app (Fin.last n)) := by
    have hn := congr_app (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.normalizedPushoutInclusion_naturality m) (Fin.last n)
    change m.left.app (Fin.last n) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.normalizedPushoutInclusion t).app (Fin.last n) =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.normalizedPushoutInclusion s).app (Fin.last n) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.normalizedPushoutComparison m).app (Fin.last n) at hn
    rw [Category.assoc, ← hn, ← Category.assoc, h, Category.assoc]
  let g := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzag.movingHom
    ((weakEquivalences C).comp_mem _ _ he
      (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.normalizedPushoutInclusion_trivialCofibration s hs (Fin.last n)).2)
    ((weakEquivalences C).comp_mem _ _ he'
      (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.normalizedPushoutInclusion_trivialCofibration t ht (Fin.last n)).2)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.normalizedPushoutComparison m).app (Fin.last n)) y
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.normalizedPushoutComparison_weakEquivalence m hs ht hm _) hy hw
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingAppendMorphisms.map (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.normalizedPushoutComparisonMoving m hs ht hm) g HEq.rfl

end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
