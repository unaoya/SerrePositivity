module

public import SerrePositivity.EInfinity.Hammock.MiddleBackwardIdentityInsertion
public import Mathlib.CategoryTheory.EssentialImage

/-!
# 元の右置換が中央恒等列の挿入の本質像に入ること

概要：元の右置換対象から恒等列だけを省き、元の挿入の実際の前像を構成する。
方針：左右の同じブロックを貼り、insertBetween の WordAction の厳密な対象同定を使う。
規約：本質像への所属を入力仮定にしない。
使われ方：全忠実な元の挿入を通して右置換関手を持ち上げる。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.MiddleBackward.IdentityInsertion
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra ForwardPath

variable {C : Type u} [Category.{v} C] [ModelCategory C] {n m : ℕ} {X Y : C}

def preimageObj (S : TrivialCofibration.Objects
    (C := C) (n := n) (m := m) (X := X) (Y := Y)) :
    Zigzag (weakEquivalences C) (sourceWord n m) X Y :=
  ZigzagAppend.obj
    (leftBoundaryBlock (TrivialCofibration.sourceFamily.left.obj S)
      (TrivialCofibration.sourceFamily.a.app S) (TrivialCofibration.sourceFamily.a_mem S))
    (pushoutRightBoundary (TrivialCofibration.sourceFamily.pushoutInputs.obj S)
      (TrivialCofibration.sourceFamily_middle_trivial S)
      (TrivialCofibration.sourceFamily.b.app S) (TrivialCofibration.sourceFamily.b_mem S))

lemma originalFunctor_obj_preimage (S : TrivialCofibration.Objects
    (C := C) (n := n) (m := m) (X := X) (Y := Y)) :
    originalFunctor.obj (preimageObj S) = TrivialCofibration.rightReplacement.obj S := by
  dsimp only [originalFunctor, preimageObj, WordAction.functor]
  change WordAction.obj (Word.insertBetween (leftBoundaryWord n) (rightBoundaryWord m) .backward)
    (ZigzagAppend.obj _ _) = _
  rw [InsertBetween.action_obj_eq]
  rfl

lemma rightReplacement_essImage (S : TrivialCofibration.Objects
    (C := C) (n := n) (m := m) (X := X) (Y := Y)) :
    (originalFunctor (C := C) (n := n) (m := m) (X := X) (Y := Y)).essImage
      (TrivialCofibration.rightReplacement.obj S) :=
  ⟨preimageObj S, ⟨eqToIso (originalFunctor_obj_preimage S)⟩⟩

def rightReplacement : TrivialCofibration.Objects
    (C := C) (n := n) (m := m) (X := X) (Y := Y) ⥤
      Zigzag (weakEquivalences C) (sourceWord n m) X Y :=
  Functor.essImage.liftFunctor TrivialCofibration.rightReplacement originalFunctor
    rightReplacement_essImage

def rightReplacementCompIso : rightReplacement (C := C) (n := n) (m := m) (X := X) (Y := Y) ⋙
    originalFunctor ≅ TrivialCofibration.rightReplacement :=
  Functor.essImage.liftFunctorCompIso TrivialCofibration.rightReplacement originalFunctor
    rightReplacement_essImage

end SerrePositivity.EInfinity.Hammock.MiddleBackward.IdentityInsertion
