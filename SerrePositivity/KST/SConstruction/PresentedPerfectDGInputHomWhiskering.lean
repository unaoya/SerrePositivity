module
public import SerrePositivity.KST.SConstruction.PerfectDGExtensionInputHomWhiskering
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGCompositionTransport
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGInputHom
public import SerrePositivity.KST.SConstruction.DGFunctorHomConjugation

/-! # ラベル付き入力 Hom の元の前後合成
概要：元の入力 Hom の前後合成を、既存のラベル等号移送を保って厳密に照合する。
方針：実 Perf の式と全次数同型自然性を、同じ三重比較の共役へ通す。
規約：元の入力 Hom・実比較・対象等号を保つ。使われ方：ラベル付き高次入力の横合成。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) (E : Type w)
  [DGCategory A D] [Small.{u} D] [DGCategory A E] [Small.{u} E]

/-- 元のラベル付き入力 Hom は、同じ実 Perf の入力 Hom の比較共役。 -/
lemma presentedPerfectDGInputHom_eq_perfect (F F' : DGFunctor A D E)
    (X : PresentedPerfectDGObject A D) :
    presentedPerfectDGInputHom A D E F F' X =
      perfectDGExtensionInputHom A D E F F' (presentedPerfectDGValue A D X) ≫
        enrichedClosedIsoConjugation (Complex A)
          (presentedPerfectDGActionIso A D E F X) (presentedPerfectDGActionIso A D E F' X) :=
  presentedPerfectDGInputHom_eq A D E F F' X

variable (T : Type z) [DGCategory A T] [Small.{u} T]

/-- 元の後合成は、同じラベル合成等号の移送を保って全入力 Hom 上で回収される。 -/
lemma presentedPerfectDGInputHom_post (F F' : DGFunctor A D E) (G : DGFunctor A E T)
    (X : PresentedPerfectDGObject A D) :
    (presentedPerfectDGInputHom A D E F F' X ≫ (presentedPerfectDGAction A E T G).map
        ((presentedPerfectDGAction A D E F).obj X) ((presentedPerfectDGAction A D E F').obj X)) ≫
        enrichedClosedIsoConjugation (Complex A)
          (presentedPerfectDGCompositionTransport A D E T F G X)
          (presentedPerfectDGCompositionTransport A D E T F' G X) =
      dgFunctorHomPost A D E T G F F' ≫
        presentedPerfectDGInputHom A D T (F.comp G) (F'.comp G) X := by
  let MX := presentedPerfectDGValue A D X
  let EX := presentedPerfectDGActionObject A D E F X
  let EY := presentedPerfectDGActionObject A D E F' X
  let aX := presentedPerfectDGActionIso A D E F X
  let aY := presentedPerfectDGActionIso A D E F' X
  let bX := presentedPerfectDGActionIso A E T G EX
  let bY := presentedPerfectDGActionIso A E T G EY
  let tX := presentedPerfectDGCompositionTransport A D E T F G X
  let tY := presentedPerfectDGCompositionTransport A D E T F' G X
  let aXY := perfectDGExtensionInputHom A D E F F' MX
  have hm := dgFunctorHom_conjugation A (perfectDGExtension A E T G) aX aY
  have hm' := congrArg (fun k => aXY ≫ k ≫
    enrichedClosedIsoConjugation (Complex A) bX bY ≫
      enrichedClosedIsoConjugation (Complex A) tX tY) hm
  have hn := perfectDGExtensionInputHom_post A D E T G MX (F := F) (F' := F')
  have hn' := congrArg (fun k => k ≫ enrichedClosedIsoConjugation (Complex A)
    (presentedPerfectDGActionIso A D T (F.comp G) X)
    (presentedPerfectDGActionIso A D T (F'.comp G) X)) hn
  simp only [Category.assoc] at hm' hn'
  calc
    _ = aXY ≫ (perfectDGExtension A E T G).map
          ((perfectDGExtension A D E F).obj MX) ((perfectDGExtension A D E F').obj MX) ≫
        enrichedClosedIsoConjugation (Complex A)
          ((perfectDGExtension A E T G).onClosed.mapIso aX)
          ((perfectDGExtension A E T G).onClosed.mapIso aY) ≫
        enrichedClosedIsoConjugation (Complex A) bX bY ≫
        enrichedClosedIsoConjugation (Complex A) tX tY := by
      simpa only [presentedPerfectDGInputHom_eq_perfect, presentedPerfectDGAction_map,
        presentedPerfectDGAction_obj, ForgetEnrichment.to_of,
        MX, EX, EY, aX, aY, bX, bY, tX, tY, aXY, Category.assoc] using hm'
    _ = _ := by
      rw [enrichedClosedIsoConjugation_trans, enrichedClosedIsoConjugation_trans]
      rw [presentedPerfectDGAction_composition_transport,
        presentedPerfectDGAction_composition_transport]
      rw [← enrichedClosedIsoConjugation_trans]
      simpa only [presentedPerfectDGInputHom_eq_perfect, Category.assoc] using hn'

/-- 元の前合成は、同じラベル合成等号の移送を保って全入力 Hom 上で回収される。 -/
lemma presentedPerfectDGInputHom_pre (F : DGFunctor A D E) (G G' : DGFunctor A E T)
    (X : PresentedPerfectDGObject A D) :
    presentedPerfectDGInputHom A E T G G' ((presentedPerfectDGAction A D E F).obj X) ≫
        enrichedClosedIsoConjugation (Complex A)
          (presentedPerfectDGCompositionTransport A D E T F G X)
          (presentedPerfectDGCompositionTransport A D E T F G' X) =
      dgFunctorHomPre A E T D F G G' ≫
        presentedPerfectDGInputHom A D T (F.comp G) (F.comp G') X := by
  let MX := presentedPerfectDGValue A D X
  let EX := presentedPerfectDGActionObject A D E F X
  let aX := presentedPerfectDGActionIso A D E F X
  let bX := presentedPerfectDGActionIso A E T G EX
  let bY := presentedPerfectDGActionIso A E T G' EX
  let tX := presentedPerfectDGCompositionTransport A D E T F G X
  let tY := presentedPerfectDGCompositionTransport A D E T F G' X
  have hm := perfectDGExtensionInputHom_conjugation A E T G G' aX
  have hm' := congrArg (fun k => k ≫ enrichedClosedIsoConjugation (Complex A) bX bY ≫
    enrichedClosedIsoConjugation (Complex A) tX tY) hm
  have hn := perfectDGExtensionInputHom_pre A D E T F MX (G := G) (G' := G')
  have hn' := congrArg (fun k => k ≫ enrichedClosedIsoConjugation (Complex A)
    (presentedPerfectDGActionIso A D T (F.comp G) X)
    (presentedPerfectDGActionIso A D T (F.comp G') X)) hn
  simp only [Category.assoc] at hm' hn'
  calc
    _ = perfectDGExtensionInputHom A E T G G' ((perfectDGExtension A D E F).obj MX) ≫
        enrichedClosedIsoConjugation (Complex A)
          ((perfectDGExtension A E T G).onClosed.mapIso aX)
          ((perfectDGExtension A E T G').onClosed.mapIso aX) ≫
        enrichedClosedIsoConjugation (Complex A) bX bY ≫
        enrichedClosedIsoConjugation (Complex A) tX tY := by
      simpa only [presentedPerfectDGInputHom_eq_perfect, presentedPerfectDGAction_obj,
        ForgetEnrichment.to_of, MX, EX, aX, bX, bY, tX, tY, Category.assoc] using hm'.symm
    _ = _ := by
      rw [enrichedClosedIsoConjugation_trans, enrichedClosedIsoConjugation_trans]
      rw [presentedPerfectDGAction_composition_transport,
        presentedPerfectDGAction_composition_transport]
      rw [← enrichedClosedIsoConjugation_trans]
      simpa only [presentedPerfectDGInputHom_eq_perfect, Category.assoc] using hn'

end SerrePositivity.KST.SConstruction
