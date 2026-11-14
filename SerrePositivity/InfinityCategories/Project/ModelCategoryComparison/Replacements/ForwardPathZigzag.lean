module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagMovingHom
public import SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.Replacements.ForwardPathNormalizeModel

/-!
# 正規化した forward 射列の実際の zigzag への代入

概要：任意長の forward 射列を、指定端点と全縦射を持つ zigzag にする。
方針：元の隣接射と自然変換の成分を使い、端点の等式だけを記録する。
規約：局所端点は動いてよい。自明な置換から得る全縦弱同値を保持する。
使われ方：左右のブロックを元の外側の backward 列と貼り合わせる。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} {n : ℕ}

abbrev forwardWord (n : ℕ) : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word := ⟨n, fun _ => .forward⟩

def zigzag (F : ComposableArrows C n) {X Y : C}
    (h0 : F.obj 0 = X) (hl : F.obj (Fin.last n) = Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W (forwardWord n) X Y where
  vertex := F.obj
  first := h0
  last := hl
  arrow i := F.map (homOfLE (Fin.castSucc_le_succ i))
  backward_mem _ h := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Direction.noConfusion h

def movingHom {F G : ComposableArrows C n} (η : F ⟶ G)
    (hη : ∀ i, W (η.app i)) {X Y X' Y' : C}
    (h0 : F.obj 0 = X) (hl : F.obj (Fin.last n) = Y)
    (h0' : G.obj 0 = X') (hl' : G.obj (Fin.last n) = Y') :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom (zigzag (W := W) F h0 hl) (zigzag G h0' hl') where
  app := η.app
  app_mem := hη
  comm i := η.naturality (homOfLE (Fin.castSucc_le_succ i))

section Model
variable [ModelCategory C]

def normalizedPullbackZigzag (s : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TerminalReplacement C n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (weakEquivalences C) (forwardWord n) ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.normalizedPullbackPath s).obj 0) s.left :=
  zigzag _ rfl (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.normalizedPullbackObj_last s)

def normalizedPushoutZigzag (s : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InitialReplacement C n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag (weakEquivalences C) (forwardWord n) s.right
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.normalizedPushoutPath s).obj (Fin.last n)) := zigzag _ rfl rfl

def normalizedPullbackProjectionMoving (s : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TerminalReplacement C n)
    (hs : trivialFibrations C s.hom) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom (normalizedPullbackZigzag s) (zigzag s.right rfl rfl) :=
  movingHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.normalizedPullbackProjection s)
    (fun i => (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.normalizedPullbackProjection_trivialFibration s hs i).2) _ _ _ _

def normalizedPushoutInclusionMoving (s : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InitialReplacement C n)
    (hs : trivialCofibrations C s.hom) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom (zigzag s.left rfl rfl) (normalizedPushoutZigzag s) :=
  movingHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.normalizedPushoutInclusion s)
    (fun i => (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.normalizedPushoutInclusion_trivialCofibration s hs i).2) _ _ _ _

def normalizedPullbackComparisonMoving {s t : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TerminalReplacement C n} (m : s ⟶ t)
    (hs : trivialFibrations C s.hom) (ht : trivialFibrations C t.hom)
    (hm : ∀ i, weakEquivalences C (m.right.app i)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom (normalizedPullbackZigzag s) (normalizedPullbackZigzag t) :=
  movingHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.normalizedPullbackComparison m)
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.normalizedPullbackComparison_weakEquivalence m hs ht hm) _ _ _ _

def normalizedPushoutComparisonMoving {s t : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.InitialReplacement C n} (m : s ⟶ t)
    (hs : trivialCofibrations C s.hom) (ht : trivialCofibrations C t.hom)
    (hm : ∀ i, weakEquivalences C (m.left.app i)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.MovingHom (normalizedPushoutZigzag s) (normalizedPushoutZigzag t) :=
  movingHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.normalizedPushoutComparison m)
    (_root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison.normalizedPushoutComparison_weakEquivalence m hs ht hm) _ _ _ _

end Model
end SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
