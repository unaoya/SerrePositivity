module

public import SerrePositivity.EInfinity.Hammock.MiddleBackwardRightEssentialImage
public import SerrePositivity.EInfinity.Hammock.Diagram

/-!
# 元の中央 backward 恒等列の挿入の nerve 比較

概要：右置換の元の unit を全忠実な挿入に戻し、第二の包含の nerve を反転する。
方針：構成済みの前像による本質像の持ち上げを使い、第一の包含と合成する。
規約：元の WordAction と元の graphDiagram の同じ射を結論にする。
使われ方：forward ブロックの間の backward 一列挿入の弱同値性。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.MiddleBackward.IdentityInsertion
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.SimplicialModel SerrePositivity.InfinityCategories

variable {C : Type u} [Category.{v} C] [ModelCategory C] {n m : ℕ} {X Y : C}

def underlyingUnit : TrivialCofibration.inclusion
    (C := C) (n := n) (m := m) (X := X) (Y := Y) ⟶ rightReplacement ⋙ originalFunctor :=
  TrivialCofibration.rightUnit ≫ rightReplacementCompIso.inv

def unit : 𝟭 (TrivialCofibration.Objects (C := C) (n := n) (m := m) (X := X) (Y := Y)) ⟶
    rightReplacement ⋙ functor where
  app S := ObjectProperty.homMk (underlyingUnit.app S)
  naturality _ _ f := by
    apply ObjectProperty.hom_ext
    exact underlyingUnit.naturality f

lemma functor_localized_isIso :
    IsIso (AnodyneHomotopy.anodyneQ.map
      (nerveMap (functor (C := C) (n := n) (m := m) (X := X) (Y := Y)))) :=
  FrameHom.FullyFaithfulNerveRetraction.of_unit functor rightReplacement unit

lemma functor_isWeakHomotopyEquivalence :
    IsWeakHomotopyEquivalence
      (nerveMap (functor (C := C) (n := n) (m := m) (X := X) (Y := Y))) :=
  FrameHom.AnodyneWeakDetection.isWeakHomotopyEquivalence _ functor_localized_isIso

lemma originalFunctor_localized_isIso
    (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C)) :
    IsIso (AnodyneHomotopy.anodyneQ.map
      (nerveMap (originalFunctor (C := C) (n := n) (m := m) (X := X) (Y := Y)))) := by
  let Q := AnodyneHomotopy.anodyneQ.{max u v}
  have hI := TrivialCofibration.inclusion_localized_isIso (n := n) (m := m) (X := X) (Y := Y) cof
  have hJ := functor_localized_isIso (C := C) (n := n) (m := m) (X := X) (Y := Y)
  have h : IsIso (Q.map (nerveMap (functor (C := C) (n := n) (m := m) (X := X) (Y := Y))) ≫
      Q.map (nerveMap TrivialCofibration.inclusion)) := by infer_instance
  have he : Q.map (nerveMap (functor (C := C) (n := n) (m := m) (X := X) (Y := Y))) ≫
      Q.map (nerveMap TrivialCofibration.inclusion) = Q.map (nerveMap originalFunctor) := by
    rw [← Q.map_comp]
    rfl
  exact he ▸ h

lemma originalFunctor_isWeakHomotopyEquivalence
    (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C)) :
    IsWeakHomotopyEquivalence
      (nerveMap (originalFunctor (C := C) (n := n) (m := m) (X := X) (Y := Y))) :=
  FrameHom.AnodyneWeakDetection.isWeakHomotopyEquivalence _ (originalFunctor_localized_isIso cof)

lemma graphMap_isWeakHomotopyEquivalence
    (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C)) :
    IsWeakHomotopyEquivalence
      ((graphDiagram (weakEquivalences C) X Y).map (wordMap n m)) :=
  originalFunctor_isWeakHomotopyEquivalence cof

end SerrePositivity.EInfinity.Hammock.MiddleBackward.IdentityInsertion
