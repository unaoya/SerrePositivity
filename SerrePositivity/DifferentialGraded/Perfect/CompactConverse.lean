module
public import SerrePositivity.DifferentialGraded.Perfect.CompactConverseSequentialCone

/-! # compact ⇒ Perf：引用なしの標準解像度による証明

標準解像度の各段、射影余積、cone に対する有限因子分解性と、
可算余極限の cone 表示を組み合わせる。係数環の体性・Hom の平坦性は仮定しない。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Pretriangulated
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

/-- 標準解像度の余極限に対する有限 cell 因子分解性。 -/
lemma moduleFiniteCellFactorTarget_resolutionCandidate (M : ModuleCategory A D) :
    moduleFiniteCellFactorTarget A D Set.univ
      ((moduleToDerived A D).obj (moduleResolutionCandidate A D M)) := by
  let F := moduleResolutionDiagram A D M
  let P := sequentialCoproductFamily.{u} F
  have hp (j : ULift.{u} ℕ) : moduleHomotopicallyProjective A D (P j) :=
    (moduleResolutionSemifreeFiltration A D M).stage_homotopicallyProjective A D (j.down + 1)
  have hP : moduleFiniteCellFactorTarget A D Set.univ ((moduleToDerived A D).obj (∐ P)) :=
    moduleFiniteCellFactorTarget_projectiveCoproduct A D P hp
      (fun j => moduleFiniteCellFactorTarget_resolutionStage A D M j.down)
  have hcone : moduleFiniteCellFactorTarget A D Set.univ
      ((moduleToDerived A D).obj (moduleCone A D (sequentialCoproductMap.{u} F))) :=
    (moduleFiniteCellFactorTarget A D Set.univ).ext_of_isTriangulatedClosed₃ _
      (moduleDerivedConeTriangle_distinguished A D (sequentialCoproductMap.{u} F)) hP hP
  exact (moduleFiniteCellFactorTarget A D Set.univ).prop_of_iso
    (moduleDerivedIso A D (moduleSequentialConeDesc A D F (colimit.cocone F))
      (moduleSequentialConeDesc_quasiIso A D F (colimit.cocone F) (colimit.isColimit F))) hcone

/-- 任意の主導来対象へ compact な始域から向かう射は有限 cell を経由する。 -/
lemma moduleFiniteCellFactorTarget_all (X : DerivedModuleCategory A D) :
    moduleFiniteCellFactorTarget A D Set.univ X := by
  obtain ⟨⟨M⟩⟩ := X
  exact (moduleFiniteCellFactorTarget A D Set.univ).prop_of_iso
    (moduleDerivedIso A D (moduleResolutionCandidateπ A D M)
      (moduleResolutionCandidateπ_quasiIso A D M))
    (moduleFiniteCellFactorTarget_resolutionCandidate A D M)

/-- U13d：u-small 余積に関して compact な対象は perfect。 -/
lemma moduleCompact_perfect {X : DerivedModuleCategory A D} (hX : moduleCompact A D X) :
    modulePerfect A D X :=
  modulePerfectOver_of_compact_factorTarget A D hX (moduleFiniteCellFactorTarget_all A D X)

lemma moduleCompact_iff_perfect (X : DerivedModuleCategory A D) :
    moduleCompact A D X ↔ modulePerfect A D X :=
  ⟨moduleCompact_perfect A D, modulePerfect_compact A D⟩

end SerrePositivity.DifferentialGraded
