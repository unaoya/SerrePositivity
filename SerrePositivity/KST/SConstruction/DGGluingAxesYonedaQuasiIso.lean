module
public import SerrePositivity.KST.SConstruction.DGGluingAxesYonedaEvaluation
public import SerrePositivity.DifferentialGraded.Module.Hom.HomotopyAndOperations

/-! # 元の二軸 Yoneda 円錐比較の実準同型性
概要：元の右軸射の代表加群円錐から同じ左軸代表への比較は、各対象で準同型となる。
方針：同じ Yoneda 射の評価を元の後合成に戻し、実 Hom 短完全列の円錐比較を使う。
規約：元の比較射と左軸射を保持。使われ方：実二軸列の cofiber 性と商の生成性。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  (D : Type w) [DGCategory R D] [Small.{u} D] (M : Bimodule R C D)
  (zc : C) (hc : IsZero (ForgetEnrichment.of (Complex R) zc))
  (zd : D) (hd : IsZero (ForgetEnrichment.of (Complex R) zd))
  (X : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)

/-- 同じ元の Yoneda 円錐比較は、各実試験対象で準同型となる。 -/
lemma dgGluingAxesYonedaConeComparison_eval_quasiIso (T : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) :
    QuasiIso ((moduleEvaluation R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M) T).map
      (dgGluingAxesYonedaConeComparison R C D M zc hc zd hd X)) := by
  rw [dgGluingAxesYonedaConeComparison_eval]
  change QuasiIso (CochainComplex.mappingCone.descShortComplex
    (dgGluingAxesYonedaEvaluationShortComplex R C D M zc hc zd hd T X))
  exact CochainComplex.mappingCone.quasiIso_descShortComplex
    (dgGluingAxesYonedaEvaluationShortComplex_shortExact R C D M zc hc zd hd T X)

/-- 同じ元の Yoneda 円錐比較は、実 dg 加群の対象別準同型である。 -/
lemma dgGluingAxesYonedaConeComparison_moduleQuasiIso :
    moduleQuasiIso R (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingObject R C D M)
      (dgGluingAxesYonedaConeComparison R C D M zc hc zd hd X) :=
  dgGluingAxesYonedaConeComparison_eval_quasiIso R C D M zc hc zd hd X

end SerrePositivity.KST.SConstruction
