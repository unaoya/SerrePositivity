module

public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison.StrictBarNormalizedColumnNaturality

/-!
概要：元の native 余錐列の全次数の値を、同じ shift 包含と正規化列へ戻す。
方針：元の MC 標的への rebase が成分を保つことと、元の包含の合成式を使う。
規約：native 列と全ての退化ラベルを保持する。
使われ方：3b-3 R6、指定余錐の全 HA 成分の自然性への入力。
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

/-- 元の native 列の全内部次数の値は、同じ符号付き shift 包含と同じ正規化列の合成。 -/
lemma strictBarNativeColumn_point (F : J ⥤ ModuleCategory A PUnit.{1})
    (s : dgCoherentBarIndex ((SSet.uliftFunctor.{u, 0}).obj (nerve J)))
    (q r : ℤ) (hqr : q + -(s.1 : ℤ) = r) :
    (((moduleHomπ A PUnit.{1}
      (dgCoherentBarSource A PUnit.{1} (smallStrictBarDiagram A F) s)
      (dgCoherentBarNormalizedModuleUnconditional A PUnit.{1} (smallStrictBarDiagram A F))
      PUnit.unit).f (-(s.1 : ℤ))
        (dgCoherentBarNativeColumn A PUnit.{1} (smallStrictBarDiagram A F)
          (dgCoherentBarMaurerCartan_unconditional A PUnit.{1} (smallStrictBarDiagram A F)) s)).v q r hqr) =
      (s.1 : ℤ).negOnePow •
        ((((moduleHomπ A PUnit.{1}
          (dgCoherentBarSource A PUnit.{1} (smallStrictBarDiagram A F) s)
          (shiftModule (s.1 : ℤ)
            (dgCoherentBarSource A PUnit.{1} (smallStrictBarDiagram A F) s))
          PUnit.unit).f (-(s.1 : ℤ))
            (moduleShiftInElement A PUnit.{1} (s.1 : ℤ)
              (dgCoherentBarSource A PUnit.{1} (smallStrictBarDiagram A F) s))).v q r hqr) ≫
          ((moduleEvaluation A PUnit.{1} PUnit.unit).map (strictBarNormalizedColumn A J F s)).f r) := by
  rw [dgCoherentBarNativeColumn, dgCoherentBarNormalizedTargetRebase_π,
    strictBarNormalizedShiftedInclusion_eq]
  simp only [Units.smul_def, map_zsmul]
  have he := moduleHomWhiskerLeft_apply_π A PUnit.{1}
    (T := ForgetEnrichment.of (Complex A)
      (dgCoherentBarSource A PUnit.{1} (smallStrictBarDiagram A F) s))
    (M := dgCoherentBarFamily A PUnit.{1} (smallStrictBarDiagram A F) s)
    (N := dgCoherentBarNormalizedGraded A PUnit.{1} (smallStrictBarDiagram A F))
    (strictBarNormalizedColumn A J F s) (-(s.1 : ℤ))
    (moduleShiftInElement A PUnit.{1} (s.1 : ℤ)
      (dgCoherentBarSource A PUnit.{1} (smallStrictBarDiagram A F) s)) PUnit.unit
  have hv := congrArg (fun z => z.v q r hqr) he
  simp only [Cochain.comp_zero_cochain_v, Cochain.ofHom_v] at hv
  simpa only [Cochain.smul_v] using!
    congrArg (fun z => (↑((s.1 : ℤ).negOnePow) : ℤ) • z) hv

end SerrePositivity.InfinityCategories.Project.DerivedCategories.DiagramComparison
