module
public import SerrePositivity.KST.NonConnective.DGKappaResolvedPerfectComparison
public import SerrePositivity.DifferentialGraded.Morita.Adjunction.Construction

/-!
概要：D-9 の同じ実小核から、元の D 加群への実評価双加群を作る。
方針：元の核包含・同じ平坦増大・実加群包含を合成し、I の射影性と増大の Hom 準同型を使う。
規約：明示 I に条件付き。評価核の生成性や Perf 同値の存在はまだ結論しない。
使われ方：K-7 c5 の Perf・P 照合における、同じ実評価核の Morita 三条件の検証。
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

/-- 同じ実小核の各対象を、元の cone の同じ実加群へ評価する双加群。 -/
def dgKappaResolvedEvaluationBimodule : Bimodule R D (dgKappaResolvedKernelKInput R D I) :=
  ((dgKappaResolvedKernelInputMap R D I).down.comp
    (DGCategoryCellResolution.augmentation R (DGKappaCone R D I))).comp
      ((dgFullSubcategoryInclusion R (ModuleCategory R D) I.objects).comp
        (dgConeModuleForget R D))

/-- 同じ実評価核の列は、明示 I が選んだ同じ射影的加群である。 -/
theorem dgKappaResolvedEvaluationBimodule_column_projective
    (x : dgKappaResolvedKernelKInput R D I) :
    moduleHomotopicallyProjective R D (ForgetEnrichment.of (Complex R)
      ((dgKappaResolvedEvaluationBimodule R D I).rightAt x)) :=
  I.projective _ ((DGCategoryCellResolution.augmentation R (DGKappaCone R D I)).obj x.val).property

/-- 同じ実評価核の全 Hom 作用は、元の平坦増大の準同型そのもの。 -/
theorem dgKappaResolvedEvaluationBimodule_homQuasiIso :
    HomQuasiIso (dgKappaResolvedEvaluationBimodule R D I) := by
  intro x y
  change QuasiIso ((𝟙 _) ≫
    (DGCategoryCellResolution.augmentation R (DGKappaCone R D I)).map x.val y.val ≫
      ((𝟙 _) ≫ 𝟙 _))
  simp only [Category.id_comp, Category.comp_id]
  exact DGCategoryCellResolution.augmentation_homQuasiIso R (DGKappaCone R D I) x.val y.val

/-- 同じ射影的列により、実評価核は D 正本の導来 Hom 比較の準同型条件を満たす。 -/
theorem dgKappaResolvedEvaluationBimodule_fullHomQuasiIso :
    Morita.criterionPerfFullHomQuasiIso R (dgKappaResolvedKernelKInput R D I) D
      (dgKappaResolvedEvaluationBimodule R D I) := by
  intro x y
  rw [Morita.criterionPerfHomComparison_projective_iff R
    (dgKappaResolvedKernelKInput R D I) D (dgKappaResolvedEvaluationBimodule R D I) x y
      (dgKappaResolvedEvaluationBimodule_column_projective R D I x)]
  exact dgKappaResolvedEvaluationBimodule_homQuasiIso R D I x y

end SerrePositivity.KST.NonConnective
