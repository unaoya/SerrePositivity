module
public import SerrePositivity.KST.SConstruction.PresentedPerfectDGLabelCoherence
public import SerrePositivity.KST.SConstruction.DGClosedIsoConjugationLaws

/-! # ラベルの等号による全 Hom 移送
概要：ラベルの等号移送を、評価対象の実閉零同型による共役として計算する。
方針：等号帰納で元の全 Hom の恒等作用へ帰着する。
規約：入力等号の証明を捨てず、比較対象を保持する。使われ方：dg 作用の厳密法則。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 評価値の全 Hom は、ラベルの等号に沿う移送を実同型の共役として回収する。 -/
lemma presentedPerfectDGHom_transport
    {X X' Y Y' : PresentedPerfectDGObject A D} (hx : X = X') (hy : Y = Y') :
    eqToHom (congrArg₂ (homObject A (PresentedPerfectDGObject A D)) hx hy) =
      enrichedClosedIsoConjugation (Complex A)
        (eqToIso (congrArg (fun Z => ForgetEnrichment.of (Complex A)
          (presentedPerfectDGValue A D Z)) hx))
        (eqToIso (congrArg (fun Z => ForgetEnrichment.of (Complex A)
          (presentedPerfectDGValue A D Z)) hy)) := by
  cases hx
  cases hy
  simp only [eqToHom_refl, eqToIso_refl]
  exact (enrichedClosedIsoConjugation_refl (Complex A)
    (ForgetEnrichment.of (Complex A) (presentedPerfectDGValue A D X))
    (ForgetEnrichment.of (Complex A) (presentedPerfectDGValue A D Y))).symm

variable {I : Type w} [DGCategory A I]

/-- ラベル付き模型への二つの dg 関手は、全 Hom の評価共役で比較できる。 -/
lemma presentedPerfectDGFunctor_ext
    {F G : DGFunctor A I (PresentedPerfectDGObject A D)}
    (h : ∀ X, F.obj X = G.obj X)
    (hm : ∀ X Y, F.map X Y ≫ enrichedClosedIsoConjugation (Complex A)
        (eqToIso (congrArg (fun Z => ForgetEnrichment.of (Complex A)
          (presentedPerfectDGValue A D Z)) (h X)))
        (eqToIso (congrArg (fun Z => ForgetEnrichment.of (Complex A)
          (presentedPerfectDGValue A D Z)) (h Y))) = G.map X Y) : F = G := by
  apply EnrichedFunctor.ext (Complex A) h
  intro X Y
  rw [presentedPerfectDGHom_transport A D (h X) (h Y)]
  exact hm X Y

end SerrePositivity.KST.SConstruction
