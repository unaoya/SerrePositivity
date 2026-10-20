module
public import SerrePositivity.KST.SConstruction.EnrichedTensorActionComposition
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGInputHomCross
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGTensorHom

/-! # 二回の tensor dg 作用の全 Hom 分解
概要：右入力・左入力・ラベルの三重 tensor 上で、二回作用を二段合成へ分解する。
方針：豊穣結合則と任意パラメータの交差式を使い、入力作用の順を揃える。
規約：入力とラベルの全 Hom を保持する。使われ方：合成入力作用との元の等号移送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) (E : Type w) (T : Type z)
  [DGCategory A D] [Small.{u} D] [DGCategory A E] [Small.{u} E]
  [DGCategory A T] [Small.{u} T]

/-- 二回作用は、入力の横合成に対応する二射とラベルの二回作用との元の合成。 -/
lemma presentedPerfectDGTensorIterationHom (F F' : DGFunctor A D E)
    (G G' : DGFunctor A E T) (X Y : PresentedPerfectDGObject A D) :
    (α_ (dgFunctorHom A E T G G') (dgFunctorHom A D E F F')
        (homObject A (PresentedPerfectDGObject A D) X Y)).hom ≫
      (𝟙 (dgFunctorHom A E T G G') ⊗ₘ presentedPerfectDGTensorHom A D E F F' X Y) ≫
        presentedPerfectDGTensorHom A E T G G'
          ((presentedPerfectDGAction A D E F).obj X)
          ((presentedPerfectDGAction A D E F').obj Y) =
      (((β_ (dgFunctorHom A E T G G') (dgFunctorHom A D E F F')).hom ≫
        ((presentedPerfectDGInputHom A D E F F' X ≫ (presentedPerfectDGAction A E T G).map
          ((presentedPerfectDGAction A D E F).obj X)
          ((presentedPerfectDGAction A D E F').obj X)) ⊗ₘ
          presentedPerfectDGInputHom A E T G G' ((presentedPerfectDGAction A D E F').obj X)) ≫
          eComp (Complex A)
            ((presentedPerfectDGAction A E T G).obj ((presentedPerfectDGAction A D E F).obj X))
            ((presentedPerfectDGAction A E T G).obj ((presentedPerfectDGAction A D E F').obj X))
            ((presentedPerfectDGAction A E T G').obj
              ((presentedPerfectDGAction A D E F').obj X))) ⊗ₘ
        ((presentedPerfectDGAction A D E F').map X Y ≫ (presentedPerfectDGAction A E T G').map
          ((presentedPerfectDGAction A D E F').obj X)
          ((presentedPerfectDGAction A D E F').obj Y))) ≫
        eComp (Complex A)
          ((presentedPerfectDGAction A E T G).obj ((presentedPerfectDGAction A D E F).obj X))
          ((presentedPerfectDGAction A E T G').obj ((presentedPerfectDGAction A D E F').obj X))
          ((presentedPerfectDGAction A E T G').obj
            ((presentedPerfectDGAction A D E F').obj Y)) := by
  dsimp only [presentedPerfectDGTensorHom]
  rw [enrichedFunctorTensorAction_composition]
  rw [presentedPerfectDGInputHom_cross]

end SerrePositivity.KST.SConstruction
