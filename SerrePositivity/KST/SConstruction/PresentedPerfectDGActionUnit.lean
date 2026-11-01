module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGHomTransport
public import SerrePositivity.DifferentialGraded.SharedFunctoriality.DGConjugationNaturality
public import SerrePositivity.KST.SConstruction.PerfectDGExtensionRightUnit

/-! # ラベル付き Perf の dg 作用の厳密な単位法則
概要：恒等 dg 入力による作用は、全 Hom 複体を含めて恒等 dg 関手と等しい。
方針：元の右単位比較と全 Hom 自然性から、共役とラベル等号の移送を消す。
規約：対象の等号だけで関手の等号を結論しない。使われ方：厳密豊穣 Perf 作用。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 恒等作用の比較とラベル移送は、評価値の元の実 Perf 単位同型そのもの。 -/
lemma presentedPerfectDGAction_unitIso (X : PresentedPerfectDGObject A D) :
    presentedPerfectDGActionIso A D D (DGFunctor.id D) X ≪≫
        eqToIso (congrArg (fun Z => ForgetEnrichment.of (Complex A)
          (presentedPerfectDGValue A D Z)) (presentedPerfectDGActionObject_id A D X)) =
      perfectDGExtensionIdentityAt A D (presentedPerfectDGValue A D X) := by
  apply Iso.ext
  rw [Iso.trans_hom, presentedPerfectDGActionObject_id_valueIso]
  exact perfectDGExtensionCompositionAt_comp_id A X.source D X.arrow X.seed.val

/-- 恒等入力の元の Hom 作用は、ラベルの等号移送後に全次数で恒等。 -/
lemma presentedPerfectDGAction_id_map (X Y : PresentedPerfectDGObject A D) :
    (presentedPerfectDGAction A D D (DGFunctor.id D)).map X Y ≫
        enrichedClosedIsoConjugation (Complex A)
          (eqToIso (congrArg (fun Z => ForgetEnrichment.of (Complex A)
            (presentedPerfectDGValue A D Z)) (presentedPerfectDGActionObject_id A D X)))
          (eqToIso (congrArg (fun Z => ForgetEnrichment.of (Complex A)
            (presentedPerfectDGValue A D Z)) (presentedPerfectDGActionObject_id A D Y))) =
      𝟙 (homObject A (PresentedPerfectDGObject A D) X Y) := by
  rw [presentedPerfectDGAction_map, Category.assoc, enrichedClosedIsoConjugation_trans,
    presentedPerfectDGAction_unitIso, presentedPerfectDGAction_unitIso]
  refine enrichedConjugation_of_naturality (Complex A)
    (perfectDGExtensionIdentityAt A D (presentedPerfectDGValue A D X))
    (perfectDGExtensionIdentityAt A D (presentedPerfectDGValue A D Y))
    ((perfectDGExtension A D D (DGFunctor.id D)).map
      (presentedPerfectDGValue A D X) (presentedPerfectDGValue A D Y)) (𝟙 _) ?_
  simpa only [Category.id_comp] using perfectDGExtensionIdentityAt_naturality A D
    (presentedPerfectDGValue A D X) (presentedPerfectDGValue A D Y)

/-- 恒等 dg 入力の作用は、元の恒等 dg 関手と厳密に等しい。 -/
lemma presentedPerfectDGAction_id :
    presentedPerfectDGAction A D D (DGFunctor.id D) =
      DGFunctor.id (PresentedPerfectDGObject A D) := by
  apply presentedPerfectDGFunctor_ext A D (presentedPerfectDGActionObject_id A D)
  exact presentedPerfectDGAction_id_map A D

end SerrePositivity.KST.SConstruction
