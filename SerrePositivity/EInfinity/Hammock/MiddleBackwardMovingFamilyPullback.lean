module

public import SerrePositivity.EInfinity.Hammock.MiddleBackwardMovingFamilyFactorizationInput

/-!
# 中央の列を自明 cofibration にする図式全体の置換

概要：同じ関手的分解の第一因子を中央の脚とする新しい動く端点の zigzag 図式。
方針：左の射列を同時 pullback し、自然な射影と正規化した端点を使う。
規約：元の端点関手 A,B と右ブロックを保持する。proper 性・cofibrancy は不要。
使われ方：中央の自明 cofibration の充満部分圏への関手的置換。
-/

@[expose] public section
universe u v u' v'
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.EInfinity.Hammock.MiddleBackward.MovingFamily
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra ForwardPath

variable {D : Type u'} [Category.{v'} D] {C : Type u} [Category.{v} C] [ModelCategory C]
  {n m : ℕ} {A B : D ⥤ C} (F : MovingFamily D C n m A B)
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

def pullbackOuterLeft : F.pullbackLeft cof ⋙ pathEvaluation C n 0 ⟶ A :=
  Functor.whiskerRight (F.pullbackLeftProjection cof) (pathEvaluation C n 0) ≫ F.a

lemma pullbackMiddle_trivialCofibration (d : D) :
    trivialCofibrations C ((F.pullbackMiddle cof).app d) :=
  (trivialCofibrations C).comp_mem _ _
    (Factorization.first_trivialCofibration cof (F.middle.app d) (F.middle_mem d))
    ((trivialCofibrations C).of_isIso _)

def pullbackFamily : MovingFamily D C n m A B where
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
  endpoint_left_mem := F.endpoint_left_mem
  endpoint_right_mem := F.endpoint_right_mem

def pullbackDiagram : Zigzag.MovingDiagram D C (weakEquivalences C) (word n m) A B :=
  (F.pullbackFamily cof).movingDiagram

end SerrePositivity.EInfinity.Hammock.MiddleBackward.MovingFamily
