module
public import SerrePositivity.InfinityCategories.Derived.DGRestrictionGradedLift
public import SerrePositivity.InfinityCategories.Derived.DGModuleYonedaPrecomposition
public import SerrePositivity.DifferentialGraded.Functor.QuasiIsoHomology

/-! # 制限代表への斉次持ち上げと元の閉射による前合成

概要：像の斉次元の持ち上げを元の閉射で前合成し、再び像の Hom へ評価する。
方針：全 Hom Yoneda の逆写像の前合成公式を、制限代表の作用の公式で展開する。
規約：像の斉次元と前合成する閉射を固定。使われ方：商の全次数の分数比較。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories
open CategoryTheory DifferentialGraded DGNerve Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (F : DGFunctor A D E)

omit [Small.{u} E] in
/-- 制限代表の持ち上げを前合成して評価すると、像での指定された斉次合成になる。 -/
lemma dgRestrictionGradedLift_precompose_evaluation {q x y : D} (n : ℤ)
    (c : GradedHom A (F.obj x) (F.obj y) n)
    (s : ForgetEnrichment.of (Complex A) q ⟶ ForgetEnrichment.of (Complex A) x) :
    (dgYonedaIso A q (restrictModule A D E F.op (representable A (F.obj y)))).hom.f n
      (compose A (D := RightModule A D) (dgRestrictionGradedLift A D E F n c)
        (closedHomEquiv A (RightModule A D) _ _ ((dgYoneda A D).onClosed.map s)).val
        (zero_add n)) =
      compose A c ((F.map q x).f 0 (closedHomEquiv A D _ _ s).val) (zero_add n) := by
  have hs := congrArg Subtype.val ((dgYoneda A D).closedHomEquiv_map s)
  change (closedHomEquiv A (RightModule A D) _ _ ((dgYoneda A D).onClosed.map s)).val =
    (yonedaHom A D q x).f 0 (closedHomEquiv A D _ _ s).val at hs
  rw [hs]
  unfold dgRestrictionGradedLift
  rw [dgYonedaInverse_precompose_evaluation]
  change (((representableMap A (F.obj y) (op (F.obj x)) (op (F.obj q))).f 0
    ((F.map q x).f 0 (closedHomEquiv A D _ _ s).val)).v n n (add_zero n)) c = _
  rw [representableMap_apply, forward_eq_signed_compose]
  simp only [Int.zero_mul, Int.negOnePow_zero, one_smul]

end SerrePositivity.InfinityCategories
