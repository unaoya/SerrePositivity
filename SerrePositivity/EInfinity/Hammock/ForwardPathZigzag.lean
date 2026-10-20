module

public import SerrePositivity.EInfinity.Hammock.ZigzagMovingHom
public import SerrePositivity.EInfinity.Hammock.ForwardPathNormalizeModel

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
namespace SerrePositivity.EInfinity.Hammock.ForwardPath
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] {W : MorphismProperty C} {n : ℕ}

abbrev forwardWord (n : ℕ) : Word := ⟨n, fun _ => .forward⟩

def zigzag (F : ComposableArrows C n) {X Y : C}
    (h0 : F.obj 0 = X) (hl : F.obj (Fin.last n) = Y) :
    Zigzag W (forwardWord n) X Y where
  vertex := F.obj
  first := h0
  last := hl
  arrow i := F.map (homOfLE (Fin.castSucc_le_succ i))
  backward_mem _ h := Direction.noConfusion h

def movingHom {F G : ComposableArrows C n} (η : F ⟶ G)
    (hη : ∀ i, W (η.app i)) {X Y X' Y' : C}
    (h0 : F.obj 0 = X) (hl : F.obj (Fin.last n) = Y)
    (h0' : G.obj 0 = X') (hl' : G.obj (Fin.last n) = Y') :
    Zigzag.MovingHom (zigzag (W := W) F h0 hl) (zigzag G h0' hl') where
  app := η.app
  app_mem := hη
  comm i := η.naturality (homOfLE (Fin.castSucc_le_succ i))

section Model
variable [ModelCategory C]

def normalizedPullbackZigzag (s : TerminalReplacement C n) :
    Zigzag (weakEquivalences C) (forwardWord n) ((normalizedPullbackPath s).obj 0) s.left :=
  zigzag _ rfl (normalizedPullbackObj_last s)

def normalizedPushoutZigzag (s : InitialReplacement C n) :
    Zigzag (weakEquivalences C) (forwardWord n) s.right
      ((normalizedPushoutPath s).obj (Fin.last n)) := zigzag _ rfl rfl

def normalizedPullbackProjectionMoving (s : TerminalReplacement C n)
    (hs : trivialFibrations C s.hom) :
    Zigzag.MovingHom (normalizedPullbackZigzag s) (zigzag s.right rfl rfl) :=
  movingHom (normalizedPullbackProjection s)
    (fun i => (normalizedPullbackProjection_trivialFibration s hs i).2) _ _ _ _

def normalizedPushoutInclusionMoving (s : InitialReplacement C n)
    (hs : trivialCofibrations C s.hom) :
    Zigzag.MovingHom (zigzag s.left rfl rfl) (normalizedPushoutZigzag s) :=
  movingHom (normalizedPushoutInclusion s)
    (fun i => (normalizedPushoutInclusion_trivialCofibration s hs i).2) _ _ _ _

def normalizedPullbackComparisonMoving {s t : TerminalReplacement C n} (m : s ⟶ t)
    (hs : trivialFibrations C s.hom) (ht : trivialFibrations C t.hom)
    (hm : ∀ i, weakEquivalences C (m.right.app i)) :
    Zigzag.MovingHom (normalizedPullbackZigzag s) (normalizedPullbackZigzag t) :=
  movingHom (normalizedPullbackComparison m)
    (normalizedPullbackComparison_weakEquivalence m hs ht hm) _ _ _ _

def normalizedPushoutComparisonMoving {s t : InitialReplacement C n} (m : s ⟶ t)
    (hs : trivialCofibrations C s.hom) (ht : trivialCofibrations C t.hom)
    (hm : ∀ i, weakEquivalences C (m.left.app i)) :
    Zigzag.MovingHom (normalizedPushoutZigzag s) (normalizedPushoutZigzag t) :=
  movingHom (normalizedPushoutComparison m)
    (normalizedPushoutComparison_weakEquivalence m hs ht hm) _ _ _ _

end Model
end SerrePositivity.EInfinity.Hammock.ForwardPath
