module

public import SerrePositivity.InfinityCategories.ModelBridge.MiddleBackwardContextColumn
public import SerrePositivity.InfinityCategories.ModelBridge.MiddleBackwardTrivialCofibration

/-!
# 任意の前後の語を持つ中央列の全部分圏の比較

概要：元の全体の中央列が自明 cofibration である全部分圏への包含は弱同値。
方針：元の全体へ貼った左置換と元の恒等図式への counit を使う。
規約：同じ指定関手的分解を使用し、単体集合のモデル構造は仮定しない。
使われ方：任意の前後の語の中の backward 挿入の第一工程。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.MiddleBackward.Context.TrivialCofibration
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.SimplicialModel

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (a b : Word) (n m : ℕ) (X Y : C)

def property : ObjectProperty (Zigzag (weakEquivalences C) (wholeWord a b n m) X Y) :=
  fun S => trivialCofibrations C (S.arrow (middleColumn a b n m))

abbrev Objects := (property a b n m X Y).FullSubcategory

abbrev inclusion : Objects a b n m X Y ⥤
    Zigzag (weakEquivalences C) (wholeWord a b n m) X Y := (property a b n m X Y).ι

variable (cof : MorphismProperty.FunctorialFactorizationData
  (cofibrations C) (trivialFibrations C))

def replacement : Zigzag (weakEquivalences C) (wholeWord a b n m) X Y ⥤
    Objects a b n m X Y :=
  (property a b n m X Y).lift (pullbackFunctor a b n m X Y cof)
    (pullback_middle_trivial a b n m X Y cof)

def counit : replacement a b n m X Y cof ⋙ inclusion a b n m X Y ⟶
    𝟭 (Zigzag (weakEquivalences C) (wholeWord a b n m) X Y) :=
  pullbackOriginalCounit a b n m X Y cof

include cof in
lemma inclusion_localized_isIso : IsIso (AnodyneHomotopy.anodyneQ.map
    (nerveMap (inclusion a b n m X Y))) :=
  FrameHom.FullyFaithfulNerveRetraction.of_counit (inclusion a b n m X Y)
    (replacement a b n m X Y cof) (counit a b n m X Y cof)

include cof in
lemma inclusion_isWeakHomotopyEquivalence :
    SerrePositivity.InfinityCategories.IsWeakHomotopyEquivalence
      (nerveMap (inclusion a b n m X Y)) :=
  FrameHom.AnodyneWeakDetection.isWeakHomotopyEquivalence _
    (inclusion_localized_isIso a b n m X Y cof)

end SerrePositivity.EInfinity.Hammock.MiddleBackward.Context.TrivialCofibration
