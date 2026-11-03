module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGLabelAction
public import SerrePositivity.KST.SConstruction.DGFunctorHorizontalDG
public import SerrePositivity.DifferentialGraded.Functor.DGFunctorParamNaturality
public import SerrePositivity.DifferentialGraded.Category.Tensor

/-! # 入力とラベルを動かす Perf の tensor Hom 作用
概要：元の入力 Hom と元のラベル Hom の tensor から、同じ作用対象間の Hom を作る。
方針：入力作用の後にラベル作用を合成し、全次数自然性で逆順の表示と比較する。
規約：ラベル全体の end を作らない。使われ方：厳密 tensor dg 作用の合成保存。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory HomologicalComplex SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) (E : Type w)
  [DGCategory A D] [Small.{u} D] [DGCategory A E] [Small.{u} E]

/-- 元の入力とラベルの Hom を、同じ二つの作用対象間で合成する chain map。 -/
def presentedPerfectDGTensorHom (F G : DGFunctor A D E)
    (X Y : PresentedPerfectDGObject A D) :
    dgFunctorHom A D E F G ⊗ homObject A (PresentedPerfectDGObject A D) X Y ⟶
      homObject A (PresentedPerfectDGObject A E)
        ((presentedPerfectDGAction A D E F).obj X) ((presentedPerfectDGAction A D E G).obj Y) :=
  (presentedPerfectDGInputHom A D E F G X ⊗ₘ (presentedPerfectDGAction A D E G).map X Y) ≫
    eComp (Complex A) _ _ _

/-- 入力とラベルの順序交換は、元の複体の Koszul braiding を保つ。 -/
lemma presentedPerfectDGTensorHom_other (F G : DGFunctor A D E)
    (X Y : PresentedPerfectDGObject A D) :
    presentedPerfectDGTensorHom A D E F G X Y =
      (β_ (dgFunctorHom A D E F G) (homObject A (PresentedPerfectDGObject A D) X Y)).hom ≫
        ((presentedPerfectDGAction A D E F).map X Y ⊗ₘ presentedPerfectDGInputHom A D E F G Y) ≫
          eComp (Complex A) _ _ _ :=
  (presentedPerfectDGInputHom_naturality A D E F G X Y).symm

/-- tensor Hom 作用の純斉次成分は、同じ入力成分とラベル成分の豊穣合成。 -/
lemma presentedPerfectDGTensorHom_apply {F G : DGFunctor A D E}
    {X Y : PresentedPerfectDGObject A D} {p q n : ℤ}
    (a : GradedHom A F G p) (b : GradedHom A X Y q) (hn : p + q = n) :
    (presentedPerfectDGTensorHom A D E F G X Y).f n
        (ιTensorObj (dgFunctorHom A D E F G)
          (homObject A (PresentedPerfectDGObject A D) X Y) p q n hn (a ⊗ₜ[A] b)) =
      forward A ((presentedPerfectDGInputHom A D E F G X).f p a)
        (((presentedPerfectDGAction A D E G).map X Y).f q b) hn := by
  change (eComp (Complex A) _ _ _).f n
    ((presentedPerfectDGInputHom A D E F G X ⊗ₘ
      (presentedPerfectDGAction A D E G).map X Y).f n _) = _
  rw [tensorMap_apply]
  rfl

end SerrePositivity.KST.SConstruction
