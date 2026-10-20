module

public import SerrePositivity.EInfinity.Hammock.ForwardPathZigzag
public import SerrePositivity.EInfinity.Hammock.BackwardZigzag
public import SerrePositivity.EInfinity.Hammock.ZigzagMovingAppendFixed

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
namespace SerrePositivity.EInfinity.Hammock.ForwardPath
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C] {n : ℕ}

abbrev leftBoundaryWord (n : ℕ) : Word := Word.append (Word.single .backward) (forwardWord n)
abbrev rightBoundaryWord (n : ℕ) : Word := Word.append (forwardWord n) (Word.single .backward)

def leftBoundaryBlock (F : ComposableArrows C n) {X : C} (e : F.obj 0 ⟶ X)
    (he : weakEquivalences C e) :
    Zigzag (weakEquivalences C) (leftBoundaryWord n) X (F.obj (Fin.last n)) :=
  ZigzagAppend.obj (BackwardZigzag.obj e he) (zigzag F rfl rfl)

def rightBoundaryBlock (F : ComposableArrows C n) {Y : C} (e : Y ⟶ F.obj (Fin.last n))
    (he : weakEquivalences C e) :
    Zigzag (weakEquivalences C) (rightBoundaryWord n) (F.obj 0) Y :=
  ZigzagAppend.obj (zigzag F rfl rfl) (BackwardZigzag.obj e he)

def pullbackLeftBoundary (s : TerminalReplacement C n) (hs : trivialFibrations C s.hom)
    {X : C} (e : s.right.obj 0 ⟶ X) (he : weakEquivalences C e) :
    Zigzag (weakEquivalences C) (leftBoundaryWord n) X s.left :=
  ZigzagAppend.obj
    (BackwardZigzag.obj ((normalizedPullbackProjection s).app 0 ≫ e)
      ((weakEquivalences C).comp_mem _ _
        (normalizedPullbackProjection_trivialFibration s hs 0).2 he))
    (normalizedPullbackZigzag s)

def pullbackLeftBoundaryProjection (s : TerminalReplacement C n)
    (hs : trivialFibrations C s.hom) {X : C} (e : s.right.obj 0 ⟶ X)
    (he : weakEquivalences C e) :
    Zigzag.MovingHom (pullbackLeftBoundary s hs e he) (leftBoundaryBlock s.right e he) := by
  let f := BackwardZigzag.movingHom
    ((weakEquivalences C).comp_mem _ _
      (normalizedPullbackProjection_trivialFibration s hs 0).2 he) he
    (𝟙 X) ((normalizedPullbackProjection s).app 0) ((weakEquivalences C).id_mem X)
    (normalizedPullbackProjection_trivialFibration s hs 0).2 (Category.comp_id _)
  exact ZigzagAppend.Moving.map f (normalizedPullbackProjectionMoving s hs) HEq.rfl

def pushoutRightBoundary (s : InitialReplacement C n) (hs : trivialCofibrations C s.hom)
    {Y : C} (e : Y ⟶ s.left.obj (Fin.last n)) (he : weakEquivalences C e) :
    Zigzag (weakEquivalences C) (rightBoundaryWord n) s.right Y :=
  ZigzagAppend.obj (normalizedPushoutZigzag s)
    (BackwardZigzag.obj (e ≫ (normalizedPushoutInclusion s).app (Fin.last n))
      ((weakEquivalences C).comp_mem _ _ he
        (normalizedPushoutInclusion_trivialCofibration s hs (Fin.last n)).2))

def pushoutRightBoundaryInclusion (s : InitialReplacement C n)
    (hs : trivialCofibrations C s.hom) {Y : C} (e : Y ⟶ s.left.obj (Fin.last n))
    (he : weakEquivalences C e) :
    Zigzag.MovingHom (rightBoundaryBlock s.left e he) (pushoutRightBoundary s hs e he) := by
  let g := BackwardZigzag.movingHom he
    ((weakEquivalences C).comp_mem _ _ he
      (normalizedPushoutInclusion_trivialCofibration s hs (Fin.last n)).2)
    ((normalizedPushoutInclusion s).app (Fin.last n)) (𝟙 Y)
    (normalizedPushoutInclusion_trivialCofibration s hs (Fin.last n)).2
    ((weakEquivalences C).id_mem Y) (Category.id_comp _).symm
  exact ZigzagAppend.Moving.map (normalizedPushoutInclusionMoving s hs) g HEq.rfl

lemma pullbackLeftBoundaryProjection_first (s : TerminalReplacement C n)
    (hs : trivialFibrations C s.hom) {X : C} (e : s.right.obj 0 ⟶ X)
    (he : weakEquivalences C e) :
    HEq ((pullbackLeftBoundaryProjection s hs e he).app 0) (𝟙 X) := by
  dsimp only [pullbackLeftBoundaryProjection, ZigzagAppend.Moving.map]
  apply HEq.trans (ZigzagAppend.Moving.app_left_heq _
    (normalizedPullbackProjectionMoving s hs) 0)
  rfl

lemma pullbackLeftBoundaryProjection_last (s : TerminalReplacement C n)
    (hs : trivialFibrations C s.hom) {X : C} (e : s.right.obj 0 ⟶ X)
    (he : weakEquivalences C e) :
    HEq ((pullbackLeftBoundaryProjection s hs e he).app (Fin.last (leftBoundaryWord n).length))
      s.hom := by
  dsimp only [pullbackLeftBoundaryProjection, ZigzagAppend.Moving.map]
  apply HEq.trans (ZigzagAppend.Moving.app_right_heq _
    (normalizedPullbackProjectionMoving s hs) HEq.rfl (Fin.last n))
  change HEq ((normalizedPullbackProjection s).app (Fin.last n)) s.hom
  rw [normalizedPullbackProjection_last]
  simp only [eqToHom_comp_heq_iff]
  rfl

lemma pushoutRightBoundaryInclusion_first (s : InitialReplacement C n)
    (hs : trivialCofibrations C s.hom) {Y : C} (e : Y ⟶ s.left.obj (Fin.last n))
    (he : weakEquivalences C e) :
    HEq ((pushoutRightBoundaryInclusion s hs e he).app 0) s.hom := by
  dsimp only [pushoutRightBoundaryInclusion, ZigzagAppend.Moving.map]
  apply HEq.trans (ZigzagAppend.Moving.app_left_heq
    (normalizedPushoutInclusionMoving s hs) _ 0)
  exact heq_of_eq (normalizedPushoutInclusion_zero s)

lemma pushoutRightBoundaryInclusion_last (s : InitialReplacement C n)
    (hs : trivialCofibrations C s.hom) {Y : C} (e : Y ⟶ s.left.obj (Fin.last n))
    (he : weakEquivalences C e) :
    HEq ((pushoutRightBoundaryInclusion s hs e he).app
      (Fin.last (rightBoundaryWord n).length)) (𝟙 Y) := by
  dsimp only [pushoutRightBoundaryInclusion, ZigzagAppend.Moving.map]
  apply HEq.trans (ZigzagAppend.Moving.app_right_heq (b := Word.single .backward)
    (normalizedPushoutInclusionMoving s hs) _ HEq.rfl (Fin.last 1))
  rfl

end SerrePositivity.EInfinity.Hammock.ForwardPath
