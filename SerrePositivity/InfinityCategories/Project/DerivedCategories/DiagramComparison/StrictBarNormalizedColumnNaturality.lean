module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictBarNormalizedFunctor
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.PointShiftInNaturality
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.NativeColumns

/-!
概要：退化ラベルも含む元の正規化列と、元の strict 自然変換の整合性を示す。
方針：同じ直和の包含と正規化射影の自然性を合成する。
規約：列を独立に選ばず、元の符号付き shift 包含へ接続する。
使われ方：3b-3 R6、元の native 余錐の高次成分の自然性。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits SSet Opposite HomologicalComplex CochainComplex HomComplex
open SerrePositivity.DifferentialGraded
open SerrePositivity.InfinityCategories.Project.DerivedCategories
open SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar
open SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.SimplicialRealization
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
variable (A : Type u) [CommRing A] (J : Type) [SmallCategory J]

/-- 元の全ラベルの包含を同じ正規化射影へ送った列。退化ラベルでは零。 -/
def strictBarNormalizedColumn (F : J ⥤ ModuleCategory A PUnit.{1})
    (s : dgCoherentBarIndex ((SSet.uliftFunctor.{u, 0}).obj (nerve J))) :=
  Sigma.ι (dgCoherentBarFamily A PUnit.{1} (smallStrictBarDiagram A F)) s ≫
    dgCoherentBarNormalizedProjection A PUnit.{1} (smallStrictBarDiagram A F)

/-- 元の正規化列は、元の同じシフトした先頭成分に自然である。 -/
@[reassoc]
lemma strictBarNormalizedColumn_naturality {F G : J ⥤ ModuleCategory A PUnit.{1}}
    (η : F ⟶ G) (s : dgCoherentBarIndex ((SSet.uliftFunctor.{u, 0}).obj (nerve J))) :
    strictBarNormalizedColumn A J F s ≫ strictBarNormalizedGradedMap A J η =
      (moduleShiftFunctor A PUnit.{1} (s.1 : ℤ)).map (η.app (s.2.down.obj 0)) ≫
        strictBarNormalizedColumn A J G s := by
  unfold strictBarNormalizedColumn
  rw [Category.assoc, ← strictBarGradedMap_projection, ← Category.assoc,
    strictBarGradedMap_ι, Category.assoc]

/-- 元の符号付き正規化包含は、同じ閉零の正規化列への後合成である。 -/
lemma strictBarNormalizedShiftedInclusion_eq (F : J ⥤ ModuleCategory A PUnit.{1})
    (s : dgCoherentBarIndex ((SSet.uliftFunctor.{u, 0}).obj (nerve J))) :
    dgCoherentBarNormalizedShiftedInclusion A PUnit.{1} (smallStrictBarDiagram A F) s =
      (s.1 : ℤ).negOnePow •
        (eHomWhiskerLeft (Complex A)
          (ForgetEnrichment.of (Complex A)
            (dgCoherentBarSource A PUnit.{1} (smallStrictBarDiagram A F) s))
          (strictBarNormalizedColumn A J F s)).f (-(s.1 : ℤ))
            (moduleShiftInElement A PUnit.{1} (s.1 : ℤ)
              (dgCoherentBarSource A PUnit.{1} (smallStrictBarDiagram A F) s)) := by
  have h := congrArg (fun f => f.f (-(s.1 : ℤ))
      (moduleShiftInElement A PUnit.{1} (s.1 : ℤ)
        (dgCoherentBarSource A PUnit.{1} (smallStrictBarDiagram A F) s)))
    (eHomWhiskerLeft_comp (Complex A)
      (ForgetEnrichment.of (Complex A)
        (dgCoherentBarSource A PUnit.{1} (smallStrictBarDiagram A F) s))
      (Sigma.ι (dgCoherentBarFamily A PUnit.{1} (smallStrictBarDiagram A F)) s)
      (dgCoherentBarNormalizedProjection A PUnit.{1} (smallStrictBarDiagram A F)))
  unfold dgCoherentBarNormalizedShiftedInclusion dgCoherentBarShiftedInclusion
  simp only [Units.smul_def, map_zsmul]
  exact congrArg (fun z => (↑((s.1 : ℤ).negOnePow) : ℤ) • z) h.symm


end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
