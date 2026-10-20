module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGParameter

/-! # 元の入力 Hom 複体から各ラベルへの高次作用
概要：元の入力関手間の全次数 Hom 複体を、各ラベルの作用間の全 Hom へ送る。
方針：入力 end の普遍自然変換へ任意パラメータ作用を適用する。
規約：巨大な出力関手圏の end は作らない。使われ方：高次入力の単位・合成の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) (E : Type w)
  [DGCategory A D] [Small.{u} D] [DGCategory A E] [Small.{u} E]
  (F G : DGFunctor A D E)

/-- 元の入力関手の Hom end から、同じラベルにおける二作用間の Hom への chain map。 -/
def presentedPerfectDGInputHom (X : PresentedPerfectDGObject A D) :
    dgFunctorHom A D E F G ⟶ homObject A (PresentedPerfectDGObject A E)
      ((presentedPerfectDGAction A D E F).obj X) ((presentedPerfectDGAction A D E G).obj X) :=
  (presentedPerfectDGParameter A D E
    (dgFunctorHomEquiv A D E (dgFunctorHom A D E F G) F G (𝟙 _))).app X

/-- 入力の全 Hom 作用は、全てのラベル間の元の Hom 射について豊穣自然。 -/
lemma presentedPerfectDGInputHom_naturality (X Y : PresentedPerfectDGObject A D) :
    (β_ (dgFunctorHom A D E F G) (homObject A (PresentedPerfectDGObject A D) X Y)).hom ≫
        ((presentedPerfectDGAction A D E F).map X Y ⊗ₘ presentedPerfectDGInputHom A D E F G Y) ≫
          eComp (Complex A) ((presentedPerfectDGAction A D E F).obj X)
            ((presentedPerfectDGAction A D E F).obj Y) ((presentedPerfectDGAction A D E G).obj Y) =
      (presentedPerfectDGInputHom A D E F G X ⊗ₘ (presentedPerfectDGAction A D E G).map X Y) ≫
        eComp (Complex A) ((presentedPerfectDGAction A D E F).obj X)
          ((presentedPerfectDGAction A D E G).obj X) ((presentedPerfectDGAction A D E G).obj Y) :=
  (presentedPerfectDGParameter A D E
    (dgFunctorHomEquiv A D E (dgFunctorHom A D E F G) F G (𝟙 _))).naturality X Y

/-- 全 Hom 作用は、元の実 Perf 延長の普遍パラメータ作用を同じ比較で共役したもの。 -/
lemma presentedPerfectDGInputHom_eq (X : PresentedPerfectDGObject A D) :
    presentedPerfectDGInputHom A D E F G X =
      (perfectDGExtensionParameter A D E
        (dgFunctorHomEquiv A D E (dgFunctorHom A D E F G) F G (𝟙 _))).app
          (presentedPerfectDGValue A D X) ≫
        enrichedClosedIsoConjugation (Complex A)
          (presentedPerfectDGActionIso A D E F X) (presentedPerfectDGActionIso A D E G X) :=
  presentedPerfectDGParameter_app A D E
    (dgFunctorHomEquiv A D E (dgFunctorHom A D E F G) F G (𝟙 _)) X

end SerrePositivity.KST.SConstruction
