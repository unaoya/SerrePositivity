module
public import SerrePositivity.DifferentialGraded.Module.Disk
public import SerrePositivity.DifferentialGraded.Complexes.TensorCoproduct

/-!
概要：セルの部分族の余積を、全セルの余積へ分裂単射で入れる。
方針：添字の包含と零による射影を使い、任意の斉次要素の有限部分族への持上げを得る。
規約：微分を変更するセル付加は扱わず、自由な層の実加群を扱う。
使われ方：D-8 d の小部分セルの各段の単射と有限 support。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers
open CategoryTheory Limits DifferentialGraded

lemma dgKappaSmallCofanElement_rep (R : Type u) [CommRing R]
    {J : Type w} [Small.{u} J] (L : J → ModuleCat.{u} R) (c : Cofan L)
    (hc : IsColimit c) (z : c.pt) :
    ∃ (t : Finset J) (b : ∀ j, L j), ∑ j ∈ t, c.inj j (b j) = z := by
  classical
  let e := equivShrink.{u} J
  have hs := Cofan.isColimitEquivOfEquiv e.symm c hc
  obtain ⟨t, b, hb⟩ := moduleCofan_element_rep R (L ∘ e.symm) _ hs z
  let b' := (Equiv.piCongrLeft' (fun j => ↥(L j)) e).symm b
  refine ⟨t.image e.symm, b', ?_⟩
  rw [Finset.sum_image]
  · simpa only [b', Equiv.piCongrLeft'_symm_apply_apply] using! hb
  · intro i hi j hj h
    exact e.symm.injective h

variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {J : Type w} [Small.{u} J] (L : J → ModuleCategory R D)

def dgKappaSubsetModule (s : Set J) : ModuleCategory R D := ∐ (fun j : s => L j.val)

def dgKappaSubsetModuleInclusion (s : Set J) : dgKappaSubsetModule R D L s ⟶ ∐ L :=
  Sigma.desc (fun j : s => Sigma.ι L j.val)

@[reassoc] lemma dgKappaSubsetModuleInclusion_ι (s : Set J) (j : s) :
    Sigma.ι (fun j : s => L j.val) j ≫ dgKappaSubsetModuleInclusion R D L s =
      Sigma.ι L j.val := Sigma.ι_comp_desc _ _

def dgKappaSubsetModuleRetraction (s : Set J) : ∐ L ⟶ dgKappaSubsetModule R D L s := by
  classical
  exact Sigma.desc (fun j => if h : j ∈ s then
    Sigma.ι (fun j : s => L j.val) ⟨j, h⟩ else 0)

@[reassoc] lemma dgKappaSubsetModule_inclusion_retraction (s : Set J) :
    dgKappaSubsetModuleInclusion R D L s ≫ dgKappaSubsetModuleRetraction R D L s = 𝟙 _ := by
  classical
  apply Sigma.hom_ext
  intro j
  simp only [dgKappaSubsetModuleInclusion_ι_assoc, dgKappaSubsetModuleRetraction,
    Sigma.ι_comp_desc, dif_pos j.property, Category.comp_id]
  exact (Category.comp_id _).symm

lemma dgKappaSubsetModuleInclusion_degreewiseMono (s : Set J) (x : D) (n : ℤ) :
    Mono (((moduleEvaluation R D x).map (dgKappaSubsetModuleInclusion R D L s)).f n) := by
  let E := moduleDegreeEvaluation R D x n
  exact SplitMono.mono
    { retraction := E.map (dgKappaSubsetModuleRetraction R D L s)
      id := by
        have h := congrArg (fun f => ((moduleEvaluation R D x).map f).f n)
          (dgKappaSubsetModule_inclusion_retraction R D L s)
        simpa only [CategoryTheory.Functor.map_comp, HomologicalComplex.comp_f,
          CategoryTheory.Functor.map_id, HomologicalComplex.id_f] using! h }

def dgKappaSubsetModuleMap {s t : Set J} (h : s ⊆ t) :
    dgKappaSubsetModule R D L s ⟶ dgKappaSubsetModule R D L t :=
  Sigma.desc (fun j : s => Sigma.ι (fun j : t => L j.val) ⟨j.val, h j.property⟩)

@[reassoc] lemma dgKappaSubsetModuleMap_inclusion {s t : Set J} (h : s ⊆ t) :
    dgKappaSubsetModuleMap R D L h ≫ dgKappaSubsetModuleInclusion R D L t =
      dgKappaSubsetModuleInclusion R D L s := by
  apply Sigma.hom_ext
  intro j
  simp only [dgKappaSubsetModuleMap, Sigma.ι_comp_desc_assoc,
    dgKappaSubsetModuleInclusion_ι]

lemma dgKappaSubsetModule_finiteElement (x : D) (n : ℤ)
    (z : ((moduleEvaluation R D x).obj (∐ L)).X n) :
    ∃ t : Finset J, ∀ s : Set J, (↑t : Set J) ⊆ s →
      ∃ b : ((moduleEvaluation R D x).obj (dgKappaSubsetModule R D L s)).X n,
        ((moduleEvaluation R D x).map (dgKappaSubsetModuleInclusion R D L s)).f n b = z := by
  classical
  obtain ⟨t, b, hb⟩ := dgKappaSmallCofanElement_rep R
    (fun j => (moduleDegreeEvaluation R D x n).obj (L j)) _
    (moduleCoproductDegreeIsColimit R D L x n) z
  refine ⟨t, fun s hs => ?_⟩
  let a (j : J) (hj : j ∈ t) :=
    ((moduleEvaluation R D x).map (Sigma.ι (fun j : s => L j.val) ⟨j, hs hj⟩)).f n (b j)
  refine ⟨∑ j ∈ t.attach, a j.val j.property, ?_⟩
  rw [map_sum]
  have he : (∑ j ∈ t.attach,
      ((moduleEvaluation R D x).map (dgKappaSubsetModuleInclusion R D L s)).f n
        (a j.val j.property)) = ∑ j ∈ t,
          ((moduleEvaluation R D x).map (Sigma.ι L j)).f n (b j) := by
    rw [← Finset.sum_attach t]
    apply Finset.sum_congr rfl
    intro j hj
    have h := congrArg (fun f => ((moduleEvaluation R D x).map f).f n (b j.val))
      (dgKappaSubsetModuleInclusion_ι R D L s ⟨j.val, hs j.property⟩)
    simpa only [CategoryTheory.Functor.map_comp, HomologicalComplex.comp_f,
      ModuleCat.comp_apply, a] using! h
  exact he.trans (by simpa only [moduleDegreeEvaluation, Functor.comp_map] using! hb)

lemma dgKappaSubsetModule_finiteLabelElement {A : Type u} (label : J → A)
    (x : D) (n : ℤ) (z : ((moduleEvaluation R D x).obj (∐ L)).X n) :
    ∃ t : Finset A, ∀ s : Set A, (↑t : Set A) ⊆ s →
      ∃ b : ((moduleEvaluation R D x).obj
        (dgKappaSubsetModule R D L (label ⁻¹' s))).X n,
        ((moduleEvaluation R D x).map
          (dgKappaSubsetModuleInclusion R D L (label ⁻¹' s))).f n b = z := by
  classical
  obtain ⟨t, ht⟩ := dgKappaSubsetModule_finiteElement R D L x n z
  refine ⟨t.image label, fun s hs => ht (label ⁻¹' s) ?_⟩
  intro j hj
  exact hs (Finset.mem_image.mpr ⟨j, hj, rfl⟩)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.KappaCovers
