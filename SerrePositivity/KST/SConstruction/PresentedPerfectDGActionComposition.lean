module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGActionCompositionIso
public import SerrePositivity.KST.SConstruction.DGFunctorHomConjugation
public import SerrePositivity.KST.SConstruction.PerfectDGExtensionConjugation

/-! # ラベル付き Perf の dg 作用の厳密な合成法則
概要：二回の dg 作用は、元の合成入力による作用と全 Hom 複体上で等しい。
方針：実延長の Hom 作用と共役を交換し、元の三重比較と全 Hom 自然性で相殺する。
規約：異なる出発圏を持つ二つのラベル間の Hom も含む。使われ方：厳密な Perf 作用。
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

/-- 二回の作用の Hom は、元のラベル移送後に合成入力の Hom 作用と等しい。 -/
lemma presentedPerfectDGAction_comp_map (X Y : PresentedPerfectDGObject A D) :
    ((presentedPerfectDGAction A D E F).comp (presentedPerfectDGAction A E T G)).map X Y ≫
        enrichedClosedIsoConjugation (Complex A)
          (eqToIso (congrArg (fun Z => ForgetEnrichment.of (Complex A)
            (presentedPerfectDGValue A T Z)) (presentedPerfectDGActionObject_comp A D E T F G X)))
          (eqToIso (congrArg (fun Z => ForgetEnrichment.of (Complex A)
            (presentedPerfectDGValue A T Z)) (presentedPerfectDGActionObject_comp A D E T F G Y))) =
      (presentedPerfectDGAction A D T (F.comp G)).map X Y := by
  let MX := presentedPerfectDGValue A D X
  let MY := presentedPerfectDGValue A D Y
  let EX := presentedPerfectDGActionObject A D E F X
  let EY := presentedPerfectDGActionObject A D E F Y
  let aX := presentedPerfectDGActionIso A D E F X
  let aY := presentedPerfectDGActionIso A D E F Y
  let bX := presentedPerfectDGActionIso A E T G EX
  let bY := presentedPerfectDGActionIso A E T G EY
  let tX := eqToIso (congrArg (fun Z => ForgetEnrichment.of (Complex A)
    (presentedPerfectDGValue A T Z)) (presentedPerfectDGActionObject_comp A D E T F G X))
  let tY := eqToIso (congrArg (fun Z => ForgetEnrichment.of (Complex A)
    (presentedPerfectDGValue A T Z)) (presentedPerfectDGActionObject_comp A D E T F G Y))
  let aXY := (perfectDGExtension A D E F).map MX MY
  have hm := dgFunctorHom_conjugation A (perfectDGExtension A E T G) aX aY
  have hm' := congrArg (fun k => aXY ≫ k ≫
    enrichedClosedIsoConjugation (Complex A) bX bY ≫
      enrichedClosedIsoConjugation (Complex A) tX tY) hm
  have hn := perfectDGExtensionCompositionAt_conjugation A D E T F G MX MY
  have hn' := congrArg (fun k => k ≫ enrichedClosedIsoConjugation (Complex A)
    (presentedPerfectDGActionIso A D T (F.comp G) X)
    (presentedPerfectDGActionIso A D T (F.comp G) Y)) hn
  simp only [Category.assoc] at hm' hn'
  calc
    _ = aXY ≫ (perfectDGExtension A E T G).map
          ((perfectDGExtension A D E F).obj MX) ((perfectDGExtension A D E F).obj MY) ≫
        enrichedClosedIsoConjugation (Complex A)
          ((perfectDGExtension A E T G).onClosed.mapIso aX)
          ((perfectDGExtension A E T G).onClosed.mapIso aY) ≫
        enrichedClosedIsoConjugation (Complex A) bX bY ≫
        enrichedClosedIsoConjugation (Complex A) tX tY := by
      simpa only [EnrichedFunctor.comp_map, presentedPerfectDGAction_map,
        presentedPerfectDGAction_obj, ForgetEnrichment.to_of,
        MX, MY, EX, EY, aX, aY, bX, bY, tX, tY, aXY, Category.assoc] using hm'
    _ = _ := by
      rw [enrichedClosedIsoConjugation_trans, enrichedClosedIsoConjugation_trans]
      rw [presentedPerfectDGAction_compositionIso, presentedPerfectDGAction_compositionIso]
      rw [← enrichedClosedIsoConjugation_trans]
      simpa only [presentedPerfectDGAction_map, Category.assoc] using hn'

/-- 元の入力の合成は、ラベル付き模型の dg 関手の合成へ厳密に送られる。 -/
lemma presentedPerfectDGAction_comp :
    (presentedPerfectDGAction A D E F).comp (presentedPerfectDGAction A E T G) =
      presentedPerfectDGAction A D T (F.comp G) := by
  apply presentedPerfectDGFunctor_ext A T (presentedPerfectDGActionObject_comp A D E T F G)
  exact presentedPerfectDGAction_comp_map A D E T F G

end SerrePositivity.KST.SConstruction
