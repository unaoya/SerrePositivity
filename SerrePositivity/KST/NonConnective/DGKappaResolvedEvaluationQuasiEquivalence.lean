module
public import SerrePositivity.KST.NonConnective.DGKappaResolvedEvaluationPerfect

/-!
概要：同じ実小核の評価を、元の全 perfect dg 加群への厳密 dg 準同値にする。
方針：評価列の射影性・perfect 性で値域を制限し、P による回収を H⁰ の本質的全射性へ戻す。
規約：明示 I・P に条件付き。元の全 Hom 作用を保持し、Perf 完備化の比較とは区別する。
使われ方：K-7 c5 の P の全関手比較を、元の実評価 dg 関手と照合するための実準同値。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (D : Type (max (u + 1) v))
  [DGCategory R D] [Small.{u} D] {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)
  (P : DGKappaPerfectInput R D I)

/-- I・P に条件付きで、同じ実評価の値域だけを元の全 perfect dg 加群へ制限する。 -/
def dgKappaResolvedPerfectEvaluation :
    DGFunctor R (dgKappaResolvedKernelKInput R D I) (PerfectDGModule R D) :=
  ((DGCategoryCellResolution.augmentation R (DGKappaCone R D I)).comp
    ((dgFullSubcategoryInclusion R (ModuleCategory R D) I.objects).comp
      (dgConeModuleForget R D))).restrict _ _ (fun x hx =>
    ⟨dgKappaResolvedEvaluationBimodule_column_projective R D I ⟨x, hx⟩,
      dgKappaResolvedEvaluationBimodule_column_perfect R D I P ⟨x, hx⟩⟩)

/-- I・P に条件付きで、元の同じ全 Hom 作用は各複体で準同型。 -/
theorem dgKappaResolvedPerfectEvaluation_homQuasiIso :
    HomQuasiIso (dgKappaResolvedPerfectEvaluation R D I P) :=
  dgKappaResolvedEvaluationBimodule_homQuasiIso R D I

/-- I・P に条件付きで、同じ実評価関手は元の全 perfect dg 加群を H⁰ で回収する。 -/
theorem dgKappaResolvedPerfectEvaluation_essSurj :
    (dgKappaResolvedPerfectEvaluation R D I P).onHomotopy.EssSurj := by
  constructor
  intro Y
  let N : PerfectDGModule R D := ForgetEnrichment.to (Complex R) Y.as
  obtain ⟨x, ⟨e⟩⟩ := dgKappaResolvedEvaluationBimodule_covers R D I P N
  let XH := (toHomotopy R (dgKappaResolvedKernelKInput R D I)).obj
    (ForgetEnrichment.of (Complex R) x)
  let F := perfectDGModuleToDerived R D Set.univ
  have h : F.obj ((dgKappaResolvedPerfectEvaluation R D I P).onHomotopy.obj XH) ≅
      F.obj Y :=
    (moduleToHomotopyDerivedIso R D).app
      (ForgetEnrichment.of (Complex R) ((dgKappaResolvedPerfectEvaluation R D I P).obj x).val) ≪≫
    e ≪≫ ((moduleToHomotopyDerivedIso R D).app (ForgetEnrichment.of (Complex R) N.val)).symm
  exact ⟨XH, ⟨F.preimageIso h⟩⟩

/-- I・P に条件付きで、元の同じ評価 dg 関手は実準同値。 -/
theorem dgKappaResolvedPerfectEvaluation_quasiEquivalence :
    QuasiEquivalence (dgKappaResolvedPerfectEvaluation R D I P) :=
  ⟨dgKappaResolvedPerfectEvaluation_homQuasiIso R D I P,
    dgKappaResolvedPerfectEvaluation_essSurj R D I P⟩

/-- I・P に条件付きで、同じ実評価から得る元の native Perf との全写像空間の同値。 -/
def dgKappaResolvedPerfectEvaluationNerveEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.dgNerve R (dgKappaResolvedKernelKInput R D I))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgModulePerfectInfinityCategory R D) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgQuasiEquivalenceNerveEquivalence (dgKappaResolvedPerfectEvaluation R D I P)
    (dgKappaResolvedPerfectEvaluation_quasiEquivalence R D I P)

end SerrePositivity.KST.NonConnective
