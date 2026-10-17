module
public import SerrePositivity.DifferentialGraded.Perfect.CompactConverseResolutionStages
public import SerrePositivity.DifferentialGraded.Perfect.CompactConverseSequentialCone

/-! # 全主導来対象を余積とconeで生成するための判定

既存の標準解像度とtelescope coneの擬同型を用いる。
compact⇒Perfの再証明ではなく、余積閉な三角部分圏への全対象の所属を扱う。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Pretriangulated
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
variable (P : ObjectProperty (DerivedModuleCategory A D))
variable [P.IsTriangulated] [P.IsClosedUnderIsomorphisms]
variable (hcop : ∀ (J : Type u) (F : J → DerivedModuleCategory A D),
  (∀ j, P (F j)) → P (∐ F))
variable (hperf : ∀ X : DerivedModuleCategory A D, modulePerfect A D X → P X)
include hcop

omit [P.IsTriangulated] in
lemma moduleLocalizing_projectiveCoproduct {J : Type w} [Small.{u} J]
    (M : J → ModuleCategory A D) (hM : ∀ j, moduleHomotopicallyProjective A D (M j))
    (hF : ∀ j, P ((moduleToDerived A D).obj (M j))) :
    P ((moduleToDerived A D).obj (∐ M)) := by
  let F := fun j => (moduleToDerived A D).obj (M j)
  have hc : P (∐ F) := by
    let e : Shrink.{u} J ≃ J := (equivShrink J).symm
    exact P.prop_of_iso (Sigma.reindex e F) (hcop _ (F ∘ e) (fun j => hF (e j)))
  exact P.prop_of_iso
    ((colimit.isColimit (Discrete.functor F)).coconePointUniqueUpToIso
      (moduleProjectiveDerivedCofanIsColimit A D M hM)) hc

include hperf

omit [P.IsTriangulated] in
lemma moduleLocalizing_sphereCoproduct {J : Type w} [Small.{u} J]
    (x : J → D) (n : J → ℤ) :
    P ((moduleToDerived A D).obj (∐ fun j => freeSphere A D (x j) (n j))) := by
  apply moduleLocalizing_projectiveCoproduct A D P hcop _
    (fun j => freeSphere_homotopicallyProjective A D (x j) (n j))
  intro j
  apply hperf
  exact modulePerfectOver_of_finiteCell A D
    (moduleFiniteCellOver_freeSphere A D (x j) (Set.mem_univ _) (n j))

lemma moduleLocalizing_resolutionStage (M : ModuleCategory A D) (n : ℕ) :
    P ((moduleToDerived A D).obj (moduleResolutionStage A D M n).left) := by
  induction n with
  | zero =>
    apply P.prop_of_isZero
    apply moduleToDerived_isZero_of_acyclic A D
    intro x i
    let : HasExactColimitsOfShape (Discrete (ModuleDiskCoverIndex A D M)) (ModuleCat.{u} A) :=
      HasExactColimitsOfShape.of_domain_equivalence (ModuleCat.{u} A)
        (Discrete.equivalence (equivShrink.{u} (ModuleDiskCoverIndex A D M)).symm)
    exact (complex_colimit_acyclic A
      (Discrete.functor (moduleDiskCoverFamily A D M) ⋙ moduleEvaluation A D x)
      (fun j => freeDisk_acyclic A D j.as.1 j.as.2.1 x) i).of_iso
        (preservesColimitIso (moduleEvaluation A D x)
          (Discrete.functor (moduleDiskCoverFamily A D M))).symm
  | succ n ih =>
    exact P.ext_of_isTriangulatedClosed₃ _
      (moduleDerivedConeTriangle_distinguished A D
        (moduleKernelCellMap A D (moduleResolutionStage A D M n).hom))
      (moduleLocalizing_sphereCoproduct A D P hcop hperf _ _) ih

lemma moduleLocalizing_resolutionCandidate (M : ModuleCategory A D) :
    P ((moduleToDerived A D).obj (moduleResolutionCandidate A D M)) := by
  let F := moduleResolutionDiagram A D M
  let Q := sequentialCoproductFamily.{u} F
  have hp (j : ULift.{u} ℕ) : moduleHomotopicallyProjective A D (Q j) :=
    (moduleResolutionSemifreeFiltration A D M).stage_homotopicallyProjective A D (j.down + 1)
  have hQ : P ((moduleToDerived A D).obj (∐ Q)) :=
    moduleLocalizing_projectiveCoproduct A D P hcop Q hp
      (fun j => moduleLocalizing_resolutionStage A D P hcop hperf M j.down)
  have hcone : P ((moduleToDerived A D).obj
      (moduleCone A D (sequentialCoproductMap.{u} F))) :=
    P.ext_of_isTriangulatedClosed₃ _
      (moduleDerivedConeTriangle_distinguished A D (sequentialCoproductMap.{u} F)) hQ hQ
  exact P.prop_of_iso
    (moduleDerivedIso A D (moduleSequentialConeDesc A D F (colimit.cocone F))
      (moduleSequentialConeDesc_quasiIso A D F (colimit.cocone F) (colimit.isColimit F))) hcone

/-- perfect対象を含みu-small余積で閉じる三角部分圏は全主導来対象を含む。 -/
lemma moduleLocalizing_all (X : DerivedModuleCategory A D) : P X := by
  obtain ⟨⟨M⟩⟩ := X
  exact P.prop_of_iso
    (moduleDerivedIso A D (moduleResolutionCandidateπ A D M)
      (moduleResolutionCandidateπ_quasiIso A D M))
    (moduleLocalizing_resolutionCandidate A D P hcop hperf M)

end SerrePositivity.DifferentialGraded
