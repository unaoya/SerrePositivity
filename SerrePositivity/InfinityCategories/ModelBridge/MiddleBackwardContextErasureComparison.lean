module

public import SerrePositivity.InfinityCategories.ModelBridge.MiddleBackwardContextEssentialImage
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.Diagram

/-!
# 任意の前後の語を保つ元の中央 backward 挿入の弱同値性

概要：元の eraseInclusion の graph 写像自体が弱ホモトピー同値となる。
方針：右置換の unit を全忠実な第二の包含へ持ち上げ、第一の包含と合成する。
規約：元の全体の語・中央列・削除語・挿入写像を保持する。
使われ方：padding された任意の語の backward 一列挿入の比較。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.MiddleBackward.Context.Erasure
open CategoryTheory HomotopicalAlgebra
open SerrePositivity.SimplicialModel SerrePositivity.InfinityCategories

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  (a b : Word) (n m : ℕ) (X Y : C)

def underlyingUnit : TrivialCofibration.inclusion a b n m X Y ⟶
    rightReplacement a b n m X Y ⋙ originalFunctor a b n m X Y :=
  TrivialCofibration.rightUnit a b n m X Y ≫ (rightReplacementCompIso a b n m X Y).inv

def unit : 𝟭 (TrivialCofibration.Objects a b n m X Y) ⟶
    rightReplacement a b n m X Y ⋙ functor a b n m X Y where
  app S := ObjectProperty.homMk ((underlyingUnit a b n m X Y).app S)
  naturality _ _ f := by
    apply ObjectProperty.hom_ext
    exact (underlyingUnit a b n m X Y).naturality f

lemma functor_localized_isIso :
    IsIso (AnodyneHomotopy.anodyneQ.map (nerveMap (functor a b n m X Y))) :=
  FrameHom.FullyFaithfulNerveRetraction.of_unit (functor a b n m X Y)
    (rightReplacement a b n m X Y) (unit a b n m X Y)

lemma functor_isWeakHomotopyEquivalence :
    IsWeakHomotopyEquivalence (nerveMap (functor a b n m X Y)) :=
  FrameHom.AnodyneWeakDetection.isWeakHomotopyEquivalence _
    (functor_localized_isIso a b n m X Y)

variable (cof : MorphismProperty.FunctorialFactorizationData
  (cofibrations C) (trivialFibrations C))

include cof in
lemma originalFunctor_localized_isIso :
    IsIso (AnodyneHomotopy.anodyneQ.map (nerveMap (originalFunctor a b n m X Y))) := by
  let Q := AnodyneHomotopy.anodyneQ.{max u v}
  have hI := TrivialCofibration.inclusion_localized_isIso a b n m X Y cof
  have hJ := functor_localized_isIso a b n m X Y
  have h : IsIso (Q.map (nerveMap (functor a b n m X Y)) ≫
      Q.map (nerveMap (TrivialCofibration.inclusion a b n m X Y))) := by infer_instance
  have he : Q.map (nerveMap (functor a b n m X Y)) ≫
      Q.map (nerveMap (TrivialCofibration.inclusion a b n m X Y)) =
        Q.map (nerveMap (originalFunctor a b n m X Y)) := by
    rw [← Q.map_comp]
    rfl
  exact he ▸ h

include cof in
lemma originalFunctor_isWeakHomotopyEquivalence :
    IsWeakHomotopyEquivalence (nerveMap (originalFunctor a b n m X Y)) :=
  FrameHom.AnodyneWeakDetection.isWeakHomotopyEquivalence _
    (originalFunctor_localized_isIso a b n m X Y cof)

include cof in
lemma graphMap_isWeakHomotopyEquivalence :
    IsWeakHomotopyEquivalence ((graphDiagram (weakEquivalences C) X Y).map
      (Word.eraseInclusion (wholeWord a b n m) (middleColumn a b n m))) :=
  originalFunctor_isWeakHomotopyEquivalence a b n m X Y cof

end SerrePositivity.EInfinity.Hammock.MiddleBackward.Context.Erasure
