module
public import SerrePositivity.KST.SConstruction.PerfectDGExtensionInputHom
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGInputHom
public import SerrePositivity.DifferentialGraded.Functor.DGClosedIsoConjugation

/-! # ラベル付き作用の元の入力 Hom の合成保存
概要：元の入力 Hom の全次数合成は、各ラベルの同じ Hom 合成へ送られる。
方針：実 Perf の入力 Hom の合成保存を、元の閉零比較による共役へ通す。
規約：元の比較・Hom 作用を変更しない。使われ方：各ラベルの厳密 dg 入力作用。
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

/-- 入力 Hom の全次数合成は、各ラベルの作用の同じ合成へ送られる。 -/
lemma presentedPerfectDGInputHom_composition (F G H : DGFunctor A D E)
    (X : PresentedPerfectDGObject A D) :
    dgFunctorComposition A D E F G H ≫ presentedPerfectDGInputHom A D E F H X =
      (presentedPerfectDGInputHom A D E F G X ⊗ₘ presentedPerfectDGInputHom A D E G H X) ≫
        eComp (Complex A) ((presentedPerfectDGAction A D E F).obj X)
          ((presentedPerfectDGAction A D E G).obj X)
          ((presentedPerfectDGAction A D E H).obj X) := by
  change _ = _ ≫ eComp (Complex A)
    (ForgetEnrichment.of (Complex A)
      (presentedPerfectDGValue A E (presentedPerfectDGActionObject A D E F X)))
    (ForgetEnrichment.of (Complex A)
      (presentedPerfectDGValue A E (presentedPerfectDGActionObject A D E G X)))
    (ForgetEnrichment.of (Complex A)
      (presentedPerfectDGValue A E (presentedPerfectDGActionObject A D E H X)))
  have hp := congrArg (fun k => k ≫ enrichedClosedIsoConjugation (Complex A)
    (presentedPerfectDGActionIso A D E F X) (presentedPerfectDGActionIso A D E H X))
      (perfectDGExtensionInputHom_composition A D E F G H (presentedPerfectDGValue A D X))
  have hc := congrArg (fun k =>
    (perfectDGExtensionInputHom A D E F G (presentedPerfectDGValue A D X) ⊗ₘ
      perfectDGExtensionInputHom A D E G H (presentedPerfectDGValue A D X)) ≫ k)
    (enrichedClosedIsoConjugation_comp (Complex A) (presentedPerfectDGActionIso A D E F X)
      (presentedPerfectDGActionIso A D E G X) (presentedPerfectDGActionIso A D E H X))
  simp only [Category.assoc] at hp hc
  simpa only [perfectDGExtensionInputHom, presentedPerfectDGInputHom_eq,
    Category.assoc, tensorHom_comp_tensorHom_assoc] using hp.trans hc.symm

end SerrePositivity.KST.SConstruction
