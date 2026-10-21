module

public import SerrePositivity.EInfinity.Hammock.MiddleBackwardFamilyFactorizationInput

/-!
# 中央の列を自明 cofibration にする図式全体の置換

概要：同じ関手的分解の第一因子を中央の脚とする新しい全体の zigzag 関手。
方針：左の射列を同時 pullback し、自然な射影と正規化した端点を使う。
規約：元の X,Y と右ブロックを保持する。proper 性・cofibrancy は不要。
使われ方：中央の自明 cofibration の充満部分圏への関手的置換。
-/

@[expose] public section
universe u v u' v'
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.MiddleBackward.Family
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra ForwardPath

variable {D : Type u'} [Category.{v'} D] {C : Type u} [Category.{v} C] [ModelCategory C]
  {n m : ℕ} {X Y : C} (F : Family D C n m X Y)
  (cof : MorphismProperty.FunctorialFactorizationData (cofibrations C) (trivialFibrations C))

def pullbackMiddle :
    F.right ⋙ pathEvaluation C m 0 ⟶ F.pullbackLeft cof ⋙ pathEvaluation C n (Fin.last n) where
  app d := Factorization.first cof (F.middle.app d) ≫
    eqToHom (normalizedPullbackObj_last ((F.pullbackInputs cof).obj d)).symm
  naturality d d' f := by
    change (F.right.map f).app 0 ≫
        (Factorization.first cof (F.middle.app d') ≫ eqToHom
          (normalizedPullbackObj_last ((F.pullbackInputs cof).obj d')).symm) =
      (Factorization.first cof (F.middle.app d) ≫ eqToHom
        (normalizedPullbackObj_last ((F.pullbackInputs cof).obj d)).symm) ≫
          (normalizedPullbackComparison ((F.pullbackInputs cof).map f)).app (Fin.last n)
    rw [normalizedPullbackComparison_last]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
    have h := cof.i.naturality (F.middleArrow.map f)
    change (F.right.map f).app 0 ≫ Factorization.first cof (F.middle.app d') =
      Factorization.first cof (F.middle.app d) ≫ cof.Z.map (F.middleArrow.map f) at h
    rw [← Category.assoc, h, Category.assoc]
    rfl

def pullbackOuterLeft : F.pullbackLeft cof ⋙ pathEvaluation C n 0 ⟶ (Functor.const D).obj X :=
  Functor.whiskerRight (F.pullbackLeftProjection cof) (pathEvaluation C n 0) ≫ F.a

lemma pullbackMiddle_trivialCofibration (d : D) :
    trivialCofibrations C ((F.pullbackMiddle cof).app d) :=
  (trivialCofibrations C).comp_mem _ _
    (Factorization.first_trivialCofibration cof (F.middle.app d) (F.middle_mem d))
    ((trivialCofibrations C).of_isIso _)

def pullbackFamily : Family D C n m X Y where
  left := F.pullbackLeft cof
  right := F.right
  a := F.pullbackOuterLeft cof
  middle := F.pullbackMiddle cof
  b := F.b
  a_mem d := (weakEquivalences C).comp_mem _ _
    (F.pullbackLeftProjection_trivialFibration cof d 0).2 (F.a_mem d)
  middle_mem d := (F.pullbackMiddle_trivialCofibration cof d).2
  b_mem := F.b_mem
  left_mem := F.pullbackLeft_map_weak cof
  right_mem := F.right_mem

def pullbackFunctor : D ⥤ Zigzag (weakEquivalences C) (word n m) X Y :=
  (F.pullbackFamily cof).zigzagFunctor

end SerrePositivity.EInfinity.Hammock.MiddleBackward.Family
