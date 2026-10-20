module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGAction
public import SerrePositivity.KST.SConstruction.PerfectDGExtensionTriangle

/-! # ラベル作用の恒等・合成と評価移送
概要：元の厳密 dg 関手の等号から、ラベルの恒等・合成の等号を得る。
方針：同じ出発圏と代表を固定した構成子に入力の等号を作用させる。
規約：Hom 作用の厳密保存は別工程。使われ方：dg 作用の関手法則の入力移送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

omit [Small.{u} D] in
/-- 恒等 dg 入力の対象作用は、元のラベルそのものを回収する。 -/
lemma presentedPerfectDGActionObject_id (X : PresentedPerfectDGObject A D) :
    presentedPerfectDGActionObject A D D (DGFunctor.id D) X = X := by
  have h := congrArg (fun K : DGFunctor A X.source D =>
    ({ source := X.source, enrichment := X.enrichment, seed := X.seed, arrow := K } :
      PresentedPerfectDGObject A D)) (strictDGFunctor_comp_id X.arrow)
  exact h

/-- 恒等ラベルの等号を評価すると、元の実延長の右単位入力移送を回収する。 -/
lemma presentedPerfectDGActionObject_id_valueIso (X : PresentedPerfectDGObject A D) :
    eqToIso (congrArg (fun Y => ForgetEnrichment.of (Complex A)
      (presentedPerfectDGValue A D Y)) (presentedPerfectDGActionObject_id A D X)) =
      perfectDGExtensionInputIso A X.source D
        (strictDGFunctor_comp_id X.arrow) X.seed.val := rfl

variable (E : Type w) (T : Type z)
  [DGCategory A E] [Small.{u} E] [DGCategory A T] [Small.{u} T]
  (F : DGFunctor A D E) (G : DGFunctor A E T)

omit [Small.{u} D] [Small.{u} E] [Small.{u} T] in
/-- 二つの入力を順に作用させたラベルは、元の合成入力のラベルと等しい。 -/
lemma presentedPerfectDGActionObject_comp (X : PresentedPerfectDGObject A D) :
    presentedPerfectDGActionObject A E T G (presentedPerfectDGActionObject A D E F X) =
      presentedPerfectDGActionObject A D T (F.comp G) X := by
  exact congrArg (fun K : DGFunctor A X.source T =>
    ({ source := X.source, enrichment := X.enrichment, seed := X.seed, arrow := K } :
      PresentedPerfectDGObject A T)) (strictDGFunctor_comp_assoc X.arrow F G)

omit [Small.{u} D] [Small.{u} E] in
/-- ラベルの合成等号を評価した移送は、元の実 Perf 延長の入力移送である。 -/
lemma presentedPerfectDGActionObject_comp_valueIso (X : PresentedPerfectDGObject A D) :
    eqToIso (congrArg (fun Y => ForgetEnrichment.of (Complex A)
      (presentedPerfectDGValue A T Y))
        (presentedPerfectDGActionObject_comp A D E T F G X)) =
      perfectDGExtensionInputIso A X.source T
        (strictDGFunctor_comp_assoc X.arrow F G) X.seed.val := rfl

end SerrePositivity.KST.SConstruction
