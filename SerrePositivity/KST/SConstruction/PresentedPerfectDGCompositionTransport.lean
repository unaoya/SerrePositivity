module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGActionCompositionIso

/-! # ラベル付き作用の元の合成等号の評価移送
概要：二回のラベル作用から合成入力のラベルへの、元の対象等号の移送を固定する。
方針：既存のラベル等号を同じ実 Perf 評価で写し、既存の三重比較の式を回収する。
規約：新しい比較同型を選ばない。使われ方：高次入力横合成の厳密な比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) (E : Type w) (T : Type z)
  [DGCategory A D] [Small.{u} D] [DGCategory A E] [Small.{u} E]
  [DGCategory A T] [Small.{u} T]

/-- 二回の元のラベル作用と合成入力の作用との、同じ対象等号の実評価移送。 -/
def presentedPerfectDGCompositionTransport (F : DGFunctor A D E) (G : DGFunctor A E T)
    (X : PresentedPerfectDGObject A D) :
    ForgetEnrichment.of (Complex A) (presentedPerfectDGValue A T
        (presentedPerfectDGActionObject A E T G (presentedPerfectDGActionObject A D E F X))) ≅
      ForgetEnrichment.of (Complex A) (presentedPerfectDGValue A T
        (presentedPerfectDGActionObject A D T (F.comp G) X)) :=
  eqToIso (congrArg (fun Z => ForgetEnrichment.of (Complex A) (presentedPerfectDGValue A T Z))
    (presentedPerfectDGActionObject_comp A D E T F G X))

/-- 元の二回の評価比較と対象等号移送は、同じ実合成比較を回収する。 -/
lemma presentedPerfectDGAction_composition_transport (F : DGFunctor A D E)
    (G : DGFunctor A E T) (X : PresentedPerfectDGObject A D) :
    (perfectDGExtension A E T G).onClosed.mapIso (presentedPerfectDGActionIso A D E F X) ≪≫
        presentedPerfectDGActionIso A E T G (presentedPerfectDGActionObject A D E F X) ≪≫
        presentedPerfectDGCompositionTransport A D E T F G X =
      perfectDGExtensionCompositionAt A D E T F G (presentedPerfectDGValue A D X) ≪≫
        presentedPerfectDGActionIso A D T (F.comp G) X :=
  presentedPerfectDGAction_compositionIso A D E T F G X

end SerrePositivity.KST.SConstruction
