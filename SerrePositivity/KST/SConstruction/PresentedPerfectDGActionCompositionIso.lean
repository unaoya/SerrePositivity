module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGHomTransport
public import SerrePositivity.KST.SConstruction.PerfectDGExtensionAssociativity

/-! # ラベル付き Perf 作用の合成比較の照合
概要：二回の作用の評価比較とラベル移送を、元の三重実延長比較で照合する。
方針：元の Perf 三重比較を同じ出発代表に適用する。
規約：入力の結合等号移送を保持する。使われ方：全 Hom の作用の厳密合成則。
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
  [DGCategory A T] [Small.{u} T] (F : DGFunctor A D E) (G : DGFunctor A E T)

/-- 二回の評価比較とラベル移送は、元の実 Perf 合成比較を回収する。 -/
lemma presentedPerfectDGAction_compositionIso (X : PresentedPerfectDGObject A D) :
    (perfectDGExtension A E T G).onClosed.mapIso (presentedPerfectDGActionIso A D E F X) ≪≫
        presentedPerfectDGActionIso A E T G (presentedPerfectDGActionObject A D E F X) ≪≫
        eqToIso (congrArg (fun Z => ForgetEnrichment.of (Complex A)
          (presentedPerfectDGValue A T Z)) (presentedPerfectDGActionObject_comp A D E T F G X)) =
      perfectDGExtensionCompositionAt A D E T F G (presentedPerfectDGValue A D X) ≪≫
        presentedPerfectDGActionIso A D T (F.comp G) X := by
  apply Iso.ext
  simp only [Iso.trans_hom, CategoryTheory.Functor.mapIso_hom]
  rw [presentedPerfectDGActionObject_comp_valueIso]
  exact perfectDGExtensionCompositionAt_assoc A X.source D E T X.arrow F G X.seed.val

end SerrePositivity.KST.SConstruction
