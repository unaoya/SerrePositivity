module
public import SerrePositivity.DifferentialGraded.Morita.CriterionPerfTriangulated
public import SerrePositivity.DifferentialGraded.Derived.ProjectivePrecomposition
public import SerrePositivity.DifferentialGraded.Perfect.RepresentableHomology

/-! # Kernel の左作用から導来全 Hom への比較

源の列だけを射影置換する。標的の列は置換する必要がなく、列自体の射影性も
仮定しない。比較は全次数の複体射であり、次数零の Hom 集合ではない。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.Morita
open CategoryTheory HomologicalComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
  (E : Type w) [DGCategory A E] [Small.{u} E] (P : Bimodule A E D)

/-- 列を通常の dg 加群の圏の対象として読む。 -/
abbrev criterionPerfColumn (d : D) : ModuleCategory A E :=
  ForgetEnrichment.of (Complex A) (P.rightAt d)

/-- 左作用の後で、源の列の増強により前合成した実際の複体射。 -/
def criterionPerfHomComparison (d d' : D)
    (R : ModuleProjectiveResolution A E (criterionPerfColumn A D E P d)) :
    homObject A D d d' ⟶
      homObject A (RightModule A E) R.obj (criterionPerfColumn A D E P d') :=
  P.toFunctor.map d d' ≫ eHomWhiskerRight (Complex A) R.π
    (criterionPerfColumn A D E P d')

/-- 標準解像度を使った、全 Hom 複体の擬同型条件。 -/
def criterionPerfFullHomQuasiIso : Prop :=
  ∀ d d' : D, QuasiIso (criterionPerfHomComparison A D E P d d'
    (moduleCanonicalProjectiveResolution A E (criterionPerfColumn A D E P d)))

/-- 比較の終域の次数零ホモロジーは、実際の導来圏の列間の射を計算する。 -/
def criterionPerfColumnDerivedHomEquiv (d d' : D)
    (R : ModuleProjectiveResolution A E (criterionPerfColumn A D E P d)) :
    ((moduleToDerived A E).obj (criterionPerfColumn A D E P d) ⟶
        (moduleToDerived A E).obj (criterionPerfColumn A D E P d')) ≃
      (homObject A (RightModule A E) R.obj (criterionPerfColumn A D E P d')).homology 0 := by
  letI := moduleToDerived_inverts A E R.π R.quasiIso
  exact (Iso.homCongr (asIso ((moduleToDerived A E).map R.π)).symm (Iso.refl _)).trans
    (moduleProjectiveDerivedHomologyEquiv A E R.projective _)

/-- 異なる解像度の比較は全 Hom 複体上でホモトピー可換。 -/
def criterionPerfHomComparison_resolution_homotopy (d d' : D)
    (R S : ModuleProjectiveResolution A E (criterionPerfColumn A D E P d)) :
    Homotopy
      (criterionPerfHomComparison A D E P d d' S ≫
        eHomWhiskerRight (Complex A) (R.comparison S) (criterionPerfColumn A D E P d'))
      (criterionPerfHomComparison A D E P d d' R) := by
  have h : Nonempty (ModuleHomotopy A E (R.comparison S ≫ S.π) R.π) := by
    apply (moduleToHomotopy_map_eq_iff A E _ _).1
    rw [CategoryTheory.Functor.map_comp]
    exact R.comparison_fac S
  simpa only [criterionPerfHomComparison, Category.assoc, eHomWhiskerRight_comp] using
    (moduleHomPrecomposeHomotopy A E h.some (criterionPerfColumn A D E P d')).compLeft
      (P.toFunctor.map d d')

/-- 全次数の擬同型条件は、源の列の射影解像度の選択に依存しない。 -/
lemma criterionPerfHomComparison_resolution_iff (d d' : D)
    (R S : ModuleProjectiveResolution A E (criterionPerfColumn A D E P d)) :
    QuasiIso (criterionPerfHomComparison A D E P d d' R) ↔
      QuasiIso (criterionPerfHomComparison A D E P d d' S) := by
  let s := eHomWhiskerRight (Complex A) (R.comparison S) (criterionPerfColumn A D E P d')
  have : QuasiIso s := moduleHomotopicallyProjective_precompose_quasiIso A E
    R.projective S.projective (R.comparison S) (R.comparison_quasiIso S) _
  have h : QuasiIso (criterionPerfHomComparison A D E P d d' S ≫ s) ↔
      QuasiIso (criterionPerfHomComparison A D E P d d' R) := by
    simp only [quasiIso_iff, quasiIsoAt_iff_isIso_homologyMap]
    exact forall_congr' (fun n => by
      rw [(criterionPerfHomComparison_resolution_homotopy A D E P d d' R S).homologyMap_eq n])
  exact h.symm.trans (quasiIso_iff_comp_right _ s)

lemma criterionPerfFullHomQuasiIso_iff (R : ∀ d : D,
    ModuleProjectiveResolution A E (criterionPerfColumn A D E P d)) :
    criterionPerfFullHomQuasiIso A D E P ↔
      ∀ d d' : D, QuasiIso (criterionPerfHomComparison A D E P d d' (R d)) := by
  apply forall₂_congr
  intro d d'
  exact criterionPerfHomComparison_resolution_iff A D E P d d' _ _

/-- 列が既に射影的な場合に限り、通常の左作用との比較へ簡約できる。 -/
lemma criterionPerfHomComparison_projective_iff (d d' : D)
    (h : moduleHomotopicallyProjective A E (criterionPerfColumn A D E P d)) :
    QuasiIso (criterionPerfHomComparison A D E P d d'
      (moduleCanonicalProjectiveResolution A E (criterionPerfColumn A D E P d))) ↔
      QuasiIso (P.toFunctor.map d d') := by
  rw [criterionPerfHomComparison_resolution_iff A D E P d d' _
    (moduleIdentityProjectiveResolution A E (criterionPerfColumn A D E P d) h)]
  simp only [criterionPerfHomComparison, moduleIdentityProjectiveResolution,
    eHomWhiskerRight_id]
  change QuasiIso (P.toFunctor.map d d' ≫ 𝟙 _) ↔ _
  rw [Category.comp_id]

end SerrePositivity.DifferentialGraded.Morita
