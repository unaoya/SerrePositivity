module
public import SerrePositivity.KST.NonConnective.DGKappaResolvedEvaluationKernel
public import SerrePositivity.InfinityCategories.Derived.DGModuleResolvedClassicalComparison

/-!
概要：P の元の全関手比較から、同じ実評価核の列の perfect 性を読む。
方針：同じ実半自由模型での頂点同型を D 正本の H⁰・主導来比較で戻す。
規約：明示 I・P に条件付き。対象別の比較から全入力の自然性は推論しない。
使われ方：K-7 c5 の Perf・P 照合における同じ評価核の列の条件。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.DifferentialGraded SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.NonConnective
variable (R : Type u) [CommRing R] (D : Type (max (u + 1) v))
  [DGCategory R D] [Small.{u} D] {κ : Cardinal.{u}} (I : DGKappaConeInput R D κ)

private def derivedHo : hoFunctor.obj (dgModuleDerivedInfinityCategory R D) ⥤
    DerivedModuleCategory R D :=
  (dgStableHomotopyEquivalence R (SemifreeDGModules R D)).functor ⋙ dgSemifreeModuleToDerived R D

private def coneColumnIso (x : DGKappaCone R D I) :
    (derivedHo R D).obj (SSet.HomotopyCategory.mk
      ((dgKappaConeDerivedComparison R D I).app (Opposite.op ⦋0⦌) (DGNerve.Simplex.vertex x))) ≅
        (moduleToDerived R D).obj x.val := by
  exact (dgModuleResolvedInfinity_classicalIso R (ModuleCategory R D) D
      (dgConeModuleForget R D)).app (SSet.HomotopyCategory.mk (DGNerve.Simplex.vertex x.val)) ≪≫
    (dgModuleOutputResolutionClassicalComparisonIso R (ModuleCategory R D) D
      (dgConeModuleForget R D)).app
        ((dgStableHomotopyEquivalence R (ModuleCategory R D)).functor.obj
          (SSet.HomotopyCategory.mk (DGNerve.Simplex.vertex x.val))) ≪≫
    (moduleToHomotopyDerivedIso R D).app x.val

private def perfectUnderlyingIso :
    FunctorIso (dgPerfectInclusionInfinity R D ≫ dgNerve.map
      (dgFullSubcategoryInclusion R (RightModule R D) (dgModuleSemifreeProperty R D)))
      (dgNerve.map (perfectDGModuleInclusion R D Set.univ)) := by
  let e := (dgSemifreeToProjectiveNerve_isQCatEquivalence R D).choose
  let J := dgFullSubcategoryInclusion R (RightModule R D) (dgModuleProjectiveProperty R D)
  have h := (e.invHomIso.postcomp (dgNerve.map J)).precomp
    (dgNerve.map (dgPerfectToProjective R D))
  simpa only [dgPerfectInclusionInfinity, Category.assoc, ← dgNerve.map_comp,
    Category.comp_id] using! h

private def perfectColumnIso (x : PerfectDGModule R D) :
    (derivedHo R D).obj (SSet.HomotopyCategory.mk
      ((dgPerfectInclusionInfinity R D).app (Opposite.op ⦋0⦌) (DGNerve.Simplex.vertex x))) ≅
      (moduleToDerived R D).obj (ForgetEnrichment.of (Complex R) x.val) := by
  let K := (dgStableHomotopyEquivalence R (RightModule R D)).functor ⋙
    moduleHomotopyToDerivedClosed R D
  have n := dgStableHomotopyEquivalence_naturalityIso R (SemifreeDGModules R D)
    (RightModule R D)
    (dgFullSubcategoryInclusion R (RightModule R D) (dgModuleSemifreeProperty R D))
  have h := (perfectUnderlyingIso R D).toNatIso
  let z : hoFunctor.obj (dgModulePerfectInfinityCategory R D) :=
    SSet.HomotopyCategory.mk (DGNerve.Simplex.vertex x)
  exact (Functor.isoWhiskerRight n (moduleHomotopyToDerivedClosed R D)).symm.app
      ((hoFunctor.map (dgPerfectInclusionInfinity R D)).toFunctor.obj z) ≪≫
    K.mapIso (h.app z) ≪≫
    (moduleToHomotopyDerivedIso R D).app (ForgetEnrichment.of (Complex R) x.val)

/-- I・P に条件付きで、同じ実評価双加群の各列は元の D の perfect 加群。 -/
theorem dgKappaResolvedEvaluationBimodule_column_perfect
    (P : DGKappaPerfectInput R D I) (x : dgKappaResolvedKernelKInput R D I) :
    modulePerfect R D ((moduleToDerived R D).obj (ForgetEnrichment.of (Complex R)
      ((dgKappaResolvedEvaluationBimodule R D I).rightAt x))) := by
  obtain ⟨z, ⟨e⟩⟩ :=
    (dgKappaPerfectResolvedComparison_isQCatEquivalence R D I P).choose.isEssentiallySurjective
      (DGNerve.Simplex.vertex x)
  obtain ⟨N, rfl⟩ := DGNerve.Simplex.vertexEquiv.symm.surjective z
  let G := dgNerve.map (dgKappaResolvedKernelInputMap R D I).down ≫
    dgNerve.map (DGCategoryCellResolution.augmentation R (DGKappaCone R D I)) ≫
      dgKappaConeDerivedComparison R D I
  have e₁ := ((hoFunctor.map G).toFunctor.mapIso e).symm
  have e₂ := (dgKappaPerfectResolvedComparison_inclusion R D I P).toNatIso.app
    (SSet.HomotopyCategory.mk (DGNerve.Simplex.vertex N))
  have e₃ := (derivedHo R D).mapIso (e₁ ≪≫ e₂)
  let M := (DGCategoryCellResolution.augmentation R (DGKappaCone R D I)).obj x.val
  have hG : G.app (Opposite.op ⦋0⦌) (DGNerve.Simplex.vertex x) =
      (dgKappaConeDerivedComparison R D I).app (Opposite.op ⦋0⦌)
        (DGNerve.Simplex.vertex M) := by
    change (dgKappaConeDerivedComparison R D I).app (Opposite.op ⦋0⦌)
      ((dgNerve.map (DGCategoryCellResolution.augmentation R
        (DGKappaCone R D I))).app (Opposite.op ⦋0⦌)
        ((dgNerve.map (dgKappaResolvedKernelInputMap R D I).down).app (Opposite.op ⦋0⦌)
          (DGNerve.Simplex.vertex x))) = _
    rw [dgFunctorNerve_vertex, dgFunctorNerve_vertex]
    rfl
  change (derivedHo R D).obj (SSet.HomotopyCategory.mk
      (G.app (Opposite.op ⦋0⦌) (DGNerve.Simplex.vertex x))) ≅ _ at e₃
  rw [hG] at e₃
  have e₄ := (coneColumnIso R D I M).symm ≪≫ e₃ ≪≫ perfectColumnIso R D N
  exact (modulePerfect R D).prop_of_iso e₄.symm N.property.2

/-- I・P に条件付きで、同じ実評価核の列は元の全 perfect 加群を同型まで回収する。 -/
theorem dgKappaResolvedEvaluationBimodule_covers
    (P : DGKappaPerfectInput R D I) (N : PerfectDGModule R D) :
    ∃ x : dgKappaResolvedKernelKInput R D I, Nonempty
      ((moduleToDerived R D).obj (ForgetEnrichment.of (Complex R)
        ((dgKappaResolvedEvaluationBimodule R D I).rightAt x)) ≅
      (moduleToDerived R D).obj (ForgetEnrichment.of (Complex R) N.val)) := by
  let z := (dgKappaPerfectResolvedComparison R D I P).app
    (Opposite.op ⦋0⦌) (DGNerve.Simplex.vertex N)
  obtain ⟨x, hx⟩ := DGNerve.Simplex.vertexEquiv.symm.surjective z
  let G := dgNerve.map (dgKappaResolvedKernelInputMap R D I).down ≫
    dgNerve.map (DGCategoryCellResolution.augmentation R (DGKappaCone R D I)) ≫
      dgKappaConeDerivedComparison R D I
  have e := (dgKappaPerfectResolvedComparison_inclusion R D I P).toNatIso.app
    (SSet.HomotopyCategory.mk (DGNerve.Simplex.vertex N))
  have e' := eqToIso (congrArg (fun a => SSet.HomotopyCategory.mk
    (G.app (Opposite.op ⦋0⦌) a)) hx) ≪≫ e
  have e'' := (derivedHo R D).mapIso e'
  let M := (DGCategoryCellResolution.augmentation R (DGKappaCone R D I)).obj x.val
  have hG : G.app (Opposite.op ⦋0⦌) (DGNerve.Simplex.vertex x) =
      (dgKappaConeDerivedComparison R D I).app (Opposite.op ⦋0⦌)
        (DGNerve.Simplex.vertex M) := by
    change (dgKappaConeDerivedComparison R D I).app (Opposite.op ⦋0⦌)
      ((dgNerve.map (DGCategoryCellResolution.augmentation R
        (DGKappaCone R D I))).app (Opposite.op ⦋0⦌)
        ((dgNerve.map (dgKappaResolvedKernelInputMap R D I).down).app (Opposite.op ⦋0⦌)
          (DGNerve.Simplex.vertex x))) = _
    rw [dgFunctorNerve_vertex, dgFunctorNerve_vertex]
    rfl
  change (derivedHo R D).obj (SSet.HomotopyCategory.mk
      (G.app (Opposite.op ⦋0⦌) (DGNerve.Simplex.vertex x))) ≅ _ at e''
  rw [hG] at e''
  exact ⟨x, ⟨(coneColumnIso R D I M).symm ≪≫ e'' ≪≫ perfectColumnIso R D N⟩⟩

end SerrePositivity.KST.NonConnective
