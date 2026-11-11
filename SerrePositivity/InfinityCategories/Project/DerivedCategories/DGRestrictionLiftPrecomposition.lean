module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGRestrictionGradedLift
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGModuleYonedaPrecomposition
public import SerrePositivity.DifferentialGraded.Functor.QuasiEquivalence

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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded Opposite
variable (A : Type u) [CommRing A] (D : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory A D] [Small.{u} D]
  (E : Type w) [_root_.SerrePositivity.DifferentialGraded.DGCategory A E] [Small.{u} E] (F : _root_.SerrePositivity.DifferentialGraded.DGFunctor A D E)

omit [Small.{u} E] in
/-- 制限代表の持ち上げを前合成して評価すると、像での指定された斉次合成になる。 -/
lemma dgRestrictionGradedLift_precompose_evaluation {q x y : D} (n : ℤ)
    (c : _root_.SerrePositivity.DifferentialGraded.GradedHom A (F.obj x) (F.obj y) n)
    (s : ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) q ⟶ ForgetEnrichment.of (_root_.SerrePositivity.DifferentialGraded.Complex A) x) :
    (_root_.SerrePositivity.DifferentialGraded.dgYonedaIso A q (_root_.SerrePositivity.DifferentialGraded.restrictModule A D E F.op (_root_.SerrePositivity.DifferentialGraded.representable A (F.obj y)))).hom.f n
      (compose A (D := RightModule A D) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRestrictionGradedLift A D E F n c)
        (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv A (_root_.SerrePositivity.DifferentialGraded.RightModule A D) _ _ ((_root_.SerrePositivity.DifferentialGraded.dgYoneda A D).onClosed.map s)).val
        (zero_add n)) =
      _root_.SerrePositivity.DifferentialGraded.compose A c ((F.map q x).f 0 (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv A D _ _ s).val) (zero_add n) := by
  have hs := congrArg Subtype.val ((_root_.SerrePositivity.DifferentialGraded.dgYoneda A D).closedHomEquiv_map s)
  change (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv A (_root_.SerrePositivity.DifferentialGraded.RightModule A D) _ _ ((_root_.SerrePositivity.DifferentialGraded.dgYoneda A D).onClosed.map s)).val =
    (_root_.SerrePositivity.DifferentialGraded.yonedaHom A D q x).f 0 (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv A D _ _ s).val at hs
  rw [hs]
  unfold _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgRestrictionGradedLift
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgYonedaInverse_precompose_evaluation]
  change (((_root_.SerrePositivity.DifferentialGraded.representableMap A (F.obj y) (op (F.obj x)) (op (F.obj q))).f 0
    ((F.map q x).f 0 (_root_.SerrePositivity.DifferentialGraded.closedHomEquiv A D _ _ s).val)).v n n (add_zero n)) c = _
  rw [_root_.SerrePositivity.DifferentialGraded.representableMap_apply, _root_.SerrePositivity.DifferentialGraded.forward_eq_signed_compose]
  simp only [Int.zero_mul, Int.negOnePow_zero, one_smul]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
