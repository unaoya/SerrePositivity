module

public import SerrePositivity.EInfinity.Hammock.MiddleBackwardContextErasure
public import SerrePositivity.EInfinity.Hammock.IdentityPreimageRecovery
public import Mathlib.CategoryTheory.EssentialImage

/-!
# 元の削除語の挿入の本質像への右置換の持ち上げ

概要：元の右置換の各対象の実際の前像を構成し、右置換関手を持ち上げる。
方針：元の中央恒等列と既存の対象の像の特徴付けを使う。
規約：未知の本質像所属を入力にしない。元の eraseInclusion を使う。
使われ方：元の unit を第二の包含の比較へ戻す。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.MiddleBackward.Context.Erasure
open CategoryTheory HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (a b : Word) (n m : ℕ) (X Y : C)

lemma rightReplacement_identityOutside (S : TrivialCofibration.Objects a b n m X Y) :
    IdentityOutside (wordMap a b n m) ((TrivialCofibration.rightReplacement a b n m X Y).obj S) :=
  (identityOutside_erase_iff _ (middleColumn a b n m)).2
    (TrivialCofibration.rightReplacement_identity a b n m X Y S)

def preimageObj (S : TrivialCofibration.Objects a b n m X Y) :
    Zigzag (weakEquivalences C) (sourceWord a b n m) X Y :=
  IdentityPreimage.obj (wordMap a b n m) (Word.eraseInclusion_injective _ _)
    ((TrivialCofibration.rightReplacement a b n m X Y).obj S)
    (rightReplacement_identityOutside a b n m X Y S)

lemma originalFunctor_obj_preimage (S : TrivialCofibration.Objects a b n m X Y) :
    (originalFunctor a b n m X Y).obj (preimageObj a b n m X Y S) =
      (TrivialCofibration.rightReplacement a b n m X Y).obj S :=
  IdentityPreimage.obj_image (wordMap a b n m) (Word.eraseInclusion_injective _ _) _
    (rightReplacement_identityOutside a b n m X Y S)

lemma rightReplacement_essImage (S : TrivialCofibration.Objects a b n m X Y) :
    (originalFunctor a b n m X Y).essImage
      ((TrivialCofibration.rightReplacement a b n m X Y).obj S) :=
  ⟨preimageObj a b n m X Y S, ⟨eqToIso (originalFunctor_obj_preimage a b n m X Y S)⟩⟩

def rightReplacement : TrivialCofibration.Objects a b n m X Y ⥤
    Zigzag (weakEquivalences C) (sourceWord a b n m) X Y :=
  Functor.essImage.liftFunctor (TrivialCofibration.rightReplacement a b n m X Y)
    (originalFunctor a b n m X Y) (rightReplacement_essImage a b n m X Y)

def rightReplacementCompIso : rightReplacement a b n m X Y ⋙ originalFunctor a b n m X Y ≅
    TrivialCofibration.rightReplacement a b n m X Y :=
  Functor.essImage.liftFunctorCompIso (TrivialCofibration.rightReplacement a b n m X Y)
    (originalFunctor a b n m X Y) (rightReplacement_essImage a b n m X Y)

end SerrePositivity.EInfinity.Hammock.MiddleBackward.Context.Erasure
