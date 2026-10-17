module
public import SerrePositivity.DifferentialGraded.Perfect.CompactConverse
public import SerrePositivity.DifferentialGraded.Perfect.UniversalProperty

/-! # 代表加群による導来圏の localizing 生成の帰納法

普通の dg 加群の標準解像度を使う。dg 圏の解像度は使わない。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits Pretriangulated
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
section
variable (P : ObjectProperty (DerivedModuleCategory A D)) [P.IsTriangulated]
  [P.IsClosedUnderIsomorphisms]
variable (hcoprod : ∀ (I : Type u) (F : I → DerivedModuleCategory A D),
  (∀ i, P (F i)) → P (∐ F))
include hcoprod

omit [P.IsTriangulated] in
lemma moduleGeneratorInduction_coproduct_small {I : Type w} [Small.{u} I]
    (F : I → DerivedModuleCategory A D) (hF : ∀ i, P (F i)) : P (∐ F) := by
  let e : Shrink.{u} I ≃ I := (equivShrink I).symm
  exact P.prop_of_iso (Sigma.reindex e F) (hcoprod _ (F ∘ e) (fun i => hF (e i)))

omit [P.IsTriangulated] in
lemma moduleGeneratorInduction_projectiveCoproduct {I : Type w} [Small.{u} I]
    (M : I → ModuleCategory A D) (hM : ∀ i, moduleHomotopicallyProjective A D (M i))
    (hF : ∀ i, P ((moduleToDerived A D).obj (M i))) :
    P ((moduleToDerived A D).obj (∐ M)) := by
  let hc := colimit.isColimit (Discrete.functor (fun i => (moduleToDerived A D).obj (M i)))
  exact P.prop_of_iso
    (hc.coconePointUniqueUpToIso (moduleProjectiveDerivedCofanIsColimit A D M hM))
    (moduleGeneratorInduction_coproduct_small A D P hcoprod _ hF)

variable (hgen : ∀ x : D, P ((moduleToDerived A D).obj
  (ForgetEnrichment.of (Complex A) (representable A x))))
include hgen

lemma moduleGeneratorInduction_sphereCoproduct {I : Type w} [Small.{u} I]
    (x : I → D) (n : I → ℤ) :
    P ((moduleToDerived A D).obj (∐ fun i => freeSphere A D (x i) (n i))) := by
  apply moduleGeneratorInduction_projectiveCoproduct A D P hcoprod _
    (fun i => freeSphere_homotopicallyProjective A D (x i) (n i))
  intro i
  apply (derivedFiniteCellOver_le_iff_generators A D P Set.univ).mpr
    (fun x _ => hgen x) _
  exact (moduleFiniteCellOver A D Set.univ).prop_map_obj (moduleToDerived A D)
    (moduleFiniteCellOver_freeSphere A D (x i) (Set.mem_univ _) (n i))

lemma moduleGeneratorInduction_resolutionStage (M : ModuleCategory A D) (n : ℕ) :
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
      (moduleGeneratorInduction_sphereCoproduct A D P hcoprod hgen _ _) ih

lemma moduleGeneratorInduction_resolutionCandidate (M : ModuleCategory A D) :
    P ((moduleToDerived A D).obj (moduleResolutionCandidate A D M)) := by
  let F := moduleResolutionDiagram A D M
  let R := sequentialCoproductFamily.{u} F
  have hp (i : ULift.{u} ℕ) : moduleHomotopicallyProjective A D (R i) :=
    (moduleResolutionSemifreeFiltration A D M).stage_homotopicallyProjective A D (i.down + 1)
  have hR : P ((moduleToDerived A D).obj (∐ R)) :=
    moduleGeneratorInduction_projectiveCoproduct A D P hcoprod R hp
      (fun i => moduleGeneratorInduction_resolutionStage A D P hcoprod hgen M i.down)
  have hcone : P ((moduleToDerived A D).obj
      (moduleCone A D (sequentialCoproductMap.{u} F))) :=
    P.ext_of_isTriangulatedClosed₃ _
      (moduleDerivedConeTriangle_distinguished A D (sequentialCoproductMap.{u} F)) hR hR
  exact P.prop_of_iso
    (moduleDerivedIso A D (moduleSequentialConeDesc A D F (colimit.cocone F))
      (moduleSequentialConeDesc_quasiIso A D F (colimit.cocone F) (colimit.isColimit F))) hcone

/-- 同型・三角形・u-small 余積に閉じて全代表加群を含む性質は、全導来対象で成立。 -/
lemma moduleDerived_generatorInduction (X : DerivedModuleCategory A D) : P X := by
  obtain ⟨⟨M⟩⟩ := X
  exact P.prop_of_iso
    (moduleDerivedIso A D (moduleResolutionCandidateπ A D M)
      (moduleResolutionCandidateπ_quasiIso A D M))
    (moduleGeneratorInduction_resolutionCandidate A D P hcoprod hgen M)

end

/-- 余積と三角形を保つ導来関手の像の性質も、全代表加群上で検証すればよい。 -/
lemma moduleDerived_functor_generatorInduction
    (E : Type w) [DGCategory A E] [Small.{u} E]
    (F : DerivedModuleCategory A D ⥤ DerivedModuleCategory A E)
    [F.CommShift ℤ] [F.IsTriangulated]
    (P : ObjectProperty (DerivedModuleCategory A E)) [P.IsTriangulated]
    [P.IsClosedUnderIsomorphisms]
    (hcoprod : ∀ (I : Type u) (G : I → DerivedModuleCategory A E),
      (∀ i, P (G i)) → P (∐ G))
    (hFcoprod : ∀ I : Type u, PreservesColimitsOfShape (Discrete I) F)
    (hgen : ∀ x : D, P (F.obj ((moduleToDerived A D).obj
      (ForgetEnrichment.of (Complex A) (representable A x)))))
    (X : DerivedModuleCategory A D) : P (F.obj X) := by
  refine moduleDerived_generatorInduction A D (P.inverseImage F) ?_ hgen X
  intro I G hG
  let := hFcoprod I
  exact P.prop_of_iso (PreservesCoproduct.iso F G).symm
    (hcoprod I (fun i => F.obj (G i)) hG)

end SerrePositivity.DifferentialGraded
