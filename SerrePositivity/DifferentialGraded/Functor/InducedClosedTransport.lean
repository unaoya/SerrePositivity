module
public import SerrePositivity.DifferentialGraded.Functor.InducedClosedConjugate
public import SerrePositivity.DifferentialGraded.Functor.DGClosedIsoConjugationLaws
/-!
概要：任意ラベル族の等号移送を、評価値の閉同型による全 Hom 共役として表す。
方針：等号帰納と一般の共役恒等則を使い、元の豊穣関手の外延性へ接続する。
規約：任意の評価族に適用する。K-S 固有の提示対象宣言を import しない。
使われ方：小さい出発提示模型の全次数における厳密恒等・合成の検証。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w t
namespace SerrePositivity.DifferentialGraded
open CategoryTheory SerrePositivity.KST.SConstruction
variable (A : Type u) [CommRing A] {C : Type v} [DGCategory A C]
  {I : Type w} (value : I → C)

lemma inducedDGHom_eqToHom {X X' Y Y' : I} (hx : X = X') (hy : Y = Y') :
    letI := inducedDGCategory A value
    eqToHom (congrArg₂ (homObject A I) hx hy) =
      enrichedClosedIsoConjugation (Complex A)
        (eqToIso (congrArg (fun x => ForgetEnrichment.of (Complex A) (value x)) hx))
        (eqToIso (congrArg (fun x => ForgetEnrichment.of (Complex A) (value x)) hy)) := by
  subst X'
  subst Y'
  exact (enrichedClosedIsoConjugation_refl (Complex A)
    (ForgetEnrichment.of (Complex A) (value X))
    (ForgetEnrichment.of (Complex A) (value Y))).symm

lemma inducedDGFunctor_ext_of_closed_conjugation {J : Type t} [DGCategory A J] :
    letI := inducedDGCategory A value
    ∀ {F G : DGFunctor A J I} (h : ∀ x, F.obj x = G.obj x),
      (∀ x y, F.map x y ≫ enrichedClosedIsoConjugation (Complex A)
        (eqToIso (congrArg (fun z => ForgetEnrichment.of (Complex A) (value z)) (h x)))
        (eqToIso (congrArg (fun z => ForgetEnrichment.of (Complex A) (value z)) (h y))) =
          G.map x y) → F = G := by
  let := inducedDGCategory A value
  intro F G h hm
  apply EnrichedFunctor.ext (Complex A) h
  intro x y
  exact (congrArg (fun k => F.map x y ≫ k)
    (inducedDGHom_eqToHom A value (h x) (h y))).trans (hm x y)

end SerrePositivity.DifferentialGraded
