module
public import SerrePositivity.DifferentialGraded.Module.DiskCover
public import SerrePositivity.DifferentialGraded.Module.ConeDesc

/-! # kernelの全cycleを添字とするcell付加の一段階 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits HomologicalComplex CochainComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma freeSphereHomEquiv_zero_val (x : D) (n : ℤ) (M : ModuleCategory A D) :
    (freeSphereHomEquiv A D x n M (0 : freeSphere A D x n ⟶ M)).val = 0 := by
  have h := freeSphereHomEquiv_naturality_val A D x n (𝟙 (freeSphere A D x n))
    (0 : freeSphere A D x n ⟶ M)
  rw [Category.id_comp, CategoryTheory.Functor.map_zero, HomologicalComplex.zero_f] at h
  exact h

/-- 全対象・次数のkernel内のcycle。次数nのcellはこの次数n+1のcycleを消す。 -/
def ModuleKernelCellIndex {M N : ModuleCategory A D} (f : M ⟶ N) :=
  Σ x : D, Σ n : ℤ,
    { z : complexCycles A ((moduleEvaluation A D x).obj M) (n + 1) //
      ((moduleEvaluation A D x).map f).f (n + 1) z.val = 0 }

instance moduleKernelCellIndexSmall {M N : ModuleCategory A D} (f : M ⟶ N) :
    Small.{u} (ModuleKernelCellIndex A D f) := by
  unfold ModuleKernelCellIndex
  infer_instance

def moduleKernelCellFamily {M N : ModuleCategory A D} (f : M ⟶ N) :
    ModuleKernelCellIndex A D f → ModuleCategory A D := fun j => freeSphere A D j.1 (j.2.1 + 1)

def moduleKernelCellSource {M N : ModuleCategory A D} (f : M ⟶ N) : ModuleCategory A D :=
  ∐ moduleKernelCellFamily A D f

def moduleKernelCellMap {M N : ModuleCategory A D} (f : M ⟶ N) :
    moduleKernelCellSource A D f ⟶ M :=
  Sigma.desc (fun j : ModuleKernelCellIndex A D f =>
    (freeSphereHomEquiv A D j.1 (j.2.1 + 1) M).symm j.2.2.val)

@[reassoc] lemma moduleKernelCellι_map {M N : ModuleCategory A D} (f : M ⟶ N)
    (j : ModuleKernelCellIndex A D f) :
    Sigma.ι (moduleKernelCellFamily A D f) j ≫ moduleKernelCellMap A D f =
      (freeSphereHomEquiv A D j.1 (j.2.1 + 1) M).symm j.2.2.val :=
  Sigma.ι_comp_desc _ _

lemma moduleKernelCellMap_comp {M N : ModuleCategory A D} (f : M ⟶ N) :
    moduleKernelCellMap A D f ≫ f = 0 := by
  apply Sigma.hom_ext
  intro j
  have hz : (freeSphereHomEquiv A D j.1 (j.2.1 + 1) M).symm j.2.2.val ≫ f = 0 := by
    apply (freeSphereHomEquiv A D j.1 (j.2.1 + 1) N).injective
    apply Subtype.ext
    have hn := freeSphereHomEquiv_naturality_val A D j.1 (j.2.1 + 1)
      ((freeSphereHomEquiv A D j.1 (j.2.1 + 1) M).symm j.2.2.val) f
    have he := congrArg (fun c => ((moduleEvaluation A D j.1).map f).f (j.2.1 + 1) c.val)
      ((freeSphereHomEquiv A D j.1 (j.2.1 + 1) M).apply_symm_apply j.2.2.val)
    exact hn.trans (he.trans (j.2.2.property.trans
      (freeSphereHomEquiv_zero_val A D j.1 (j.2.1 + 1) N).symm))
  calc
    Sigma.ι (moduleKernelCellFamily A D f) j ≫ (moduleKernelCellMap A D f ≫ f) =
        (Sigma.ι (moduleKernelCellFamily A D f) j ≫ moduleKernelCellMap A D f) ≫ f :=
      (Category.assoc _ _ _).symm
    _ = (freeSphereHomEquiv A D j.1 (j.2.1 + 1) M).symm j.2.2.val ≫ f :=
      congrArg (fun k => k ≫ f) (moduleKernelCellι_map A D f j)
    _ = 0 := hz
    _ = Sigma.ι (moduleKernelCellFamily A D f) j ≫ 0 := comp_zero.symm

def moduleKernelCellStep {M N : ModuleCategory A D} (f : M ⟶ N) : ModuleCategory A D :=
  moduleCone A D (moduleKernelCellMap A D f)

def moduleKernelCellStepι {M N : ModuleCategory A D} (f : M ⟶ N) :
    M ⟶ moduleKernelCellStep A D f := moduleConeInr A D (moduleKernelCellMap A D f)

def moduleKernelCellStepπ {M N : ModuleCategory A D} (f : M ⟶ N) :
    moduleKernelCellStep A D f ⟶ N :=
  moduleConeDesc A D (moduleKernelCellMap A D f) f (moduleKernelCellMap_comp A D f)

@[reassoc] lemma moduleKernelCellStep_fac {M N : ModuleCategory A D} (f : M ⟶ N) :
    moduleKernelCellStepι A D f ≫ moduleKernelCellStepπ A D f = f :=
  moduleConeDesc_inr A D _ _ _

lemma moduleKernelCellStepπ_degreewiseSurjective {M N : ModuleCategory A D} (f : M ⟶ N)
    (hf : moduleDegreewiseSurjective A D f) :
    moduleDegreewiseSurjective A D (moduleKernelCellStepπ A D f) := by
  intro x n y
  obtain ⟨t, ht⟩ := hf x n y
  refine ⟨((moduleEvaluation A D x).map (moduleKernelCellStepι A D f)).f n t, ?_⟩
  have h := congrArg (fun k => ((moduleEvaluation A D x).map k).f n t)
    (moduleKernelCellStep_fac A D f)
  rw [CategoryTheory.Functor.map_comp, HomologicalComplex.comp_f] at h
  exact h.trans ht

/-- kernelの各cycleの像を、一段階のcell付加で境界にする。 -/
lemma moduleKernelCellStep_killsInKernel {M N : ModuleCategory A D} (f : M ⟶ N) (x : D) (n : ℤ)
    (z : complexCycles A ((moduleEvaluation A D x).obj M) (n + 1))
    (hz : ((moduleEvaluation A D x).map f).f (n + 1) z.val = 0) :
    ∃ t : ((moduleEvaluation A D x).obj (moduleKernelCellStep A D f)).X n,
      ((moduleEvaluation A D x).obj (moduleKernelCellStep A D f)).d n (n + 1) t =
        ((moduleEvaluation A D x).map (moduleKernelCellStepι A D f)).f (n + 1) z.val ∧
      ((moduleEvaluation A D x).map (moduleKernelCellStepπ A D f)).f n t = 0 := by
  let j : ModuleKernelCellIndex A D f := ⟨x, n, ⟨z, hz⟩⟩
  let a := Sigma.ι (moduleKernelCellFamily A D f) j
  let c := freeSphereHomEquiv A D x (n + 1) (moduleKernelCellSource A D f) a
  have hv : ((moduleEvaluation A D x).map (moduleKernelCellMap A D f)).f (n + 1) c.val = z.val := by
    have h : a ≫ moduleKernelCellMap A D f = (freeSphereHomEquiv A D x (n + 1) M).symm z :=
      moduleKernelCellι_map A D f j
    have he := congrArg (fun k => (freeSphereHomEquiv A D x (n + 1) M k).val) h
    rw [freeSphereHomEquiv_naturality_val, Equiv.apply_symm_apply] at he
    exact he
  simp only [moduleKernelCellStepι, moduleConeInr_eval, moduleKernelCellStepπ, moduleConeDesc_eval]
  change ∃ t : (mappingCone ((moduleEvaluation A D x).map (moduleKernelCellMap A D f))).X n,
    (mappingCone ((moduleEvaluation A D x).map (moduleKernelCellMap A D f))).d n (n + 1) t =
      (mappingCone.inr ((moduleEvaluation A D x).map (moduleKernelCellMap A D f))).f
        (n + 1) z.val ∧ _
  refine ⟨complexConeBoundaryWitness ((moduleEvaluation A D x).map (moduleKernelCellMap A D f)) n c,
    ?_, ?_⟩
  · exact (complexConeBoundaryWitness_d _ n c).trans (congrArg _ hv)
  · exact complexConeBoundaryWitness_desc _ _ _ n c

lemma moduleKernelCellStep_kills {M N : ModuleCategory A D} (f : M ⟶ N) (x : D) (n : ℤ)
    (z : complexCycles A ((moduleEvaluation A D x).obj M) (n + 1))
    (hz : ((moduleEvaluation A D x).map f).f (n + 1) z.val = 0) :
    ∃ t : ((moduleEvaluation A D x).obj (moduleKernelCellStep A D f)).X n,
      ((moduleEvaluation A D x).obj (moduleKernelCellStep A D f)).d n (n + 1) t =
        ((moduleEvaluation A D x).map (moduleKernelCellStepι A D f)).f (n + 1) z.val := by
  obtain ⟨t, ht, _⟩ := moduleKernelCellStep_killsInKernel A D f x n z hz
  exact ⟨t, ht⟩

end SerrePositivity.DifferentialGraded
