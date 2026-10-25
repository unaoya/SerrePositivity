module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.StrictComparison.CoherentFirstHomologyComplex

/-!
概要：内部次元層の cycle を実 bar へ持ち上げ、その境界を一段下で表す。
方針：層包含の内部微分との可換性と theta の次元下降を使う。
規約：元の実微分を使い、cycle の代表元を保持する。
使われ方：連結射と一次 bar 微分の照合。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (G : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))

lemma dgCoherentBarLayerCycleLift_boundary_mem (x : D) (q : ℤ) (n : ℕ)
    (z : (moduleDegreeEvaluation R D x q).obj (dgCoherentBarLayerGraded R D G (n + 1)))
    (hz : ((moduleEvaluation R D x).obj (dgCoherentBarLayerGraded R D G (n + 1))).d
      q (q + 1) z = 0) :
    ((dgCoherentBarNormalizedModuleUnconditional R D G).obj (Opposite.op x)).d q (q + 1)
      ((moduleDegreeEvaluation R D x q).map (dgCoherentBarLayerInclusion R D G (n + 1)) z) ∈
        dgCoherentBarNormalizedDegreeFiltration R D G x (q + 1) n := by
  let a := (moduleDegreeEvaluation R D x q).map (dgCoherentBarLayerInclusion R D G (n + 1)) z
  have ha := dgCoherentBarLayerInclusion_mem_filtration R D G x q (n + 1) z
  have hc := ConcreteCategory.congr_hom
    (((moduleEvaluation R D x).map (dgCoherentBarLayerInclusion R D G (n + 1))).comm
      q (q + 1)) z
  have h0 : ((moduleEvaluation R D x).obj (dgCoherentBarNormalizedGraded R D G)).d
      q (q + 1) a = 0 := by
    simpa only [ModuleCat.comp_apply, hz, map_zero] using! hc
  have hd := congrArg (fun f => f a)
    (dgCoherentBarNormalizedModule_d R D G (dgCoherentBarMaurerCartan_unconditional R D G)
      (Opposite.op x) q)
  change _ = ((moduleEvaluation R D x).obj (dgCoherentBarNormalizedGraded R D G)).d
    q (q + 1) a + _ at hd
  rw [hd, h0, zero_add]
  exact dgCoherentBarNormalizedDegreeFiltration_theta R D G x q (n + 1) a ha

def dgCoherentBarLayerCycleLift (x : D) (q : ℤ) (n : ℕ) :
    ((moduleEvaluation R D x).obj (dgCoherentBarLayerGraded R D G (n + 1))).cycles q ⟶
      (dgCoherentBarNormalizedStageComplex R D G x (n + 1)).X q :=
  ModuleCat.ofHom
    { toFun z := ⟨(moduleDegreeEvaluation R D x q).map
        (dgCoherentBarLayerInclusion R D G (n + 1))
          (((moduleEvaluation R D x).obj (dgCoherentBarLayerGraded R D G (n + 1))).iCycles q z),
        dgCoherentBarLayerInclusion_mem_filtration R D G x q (n + 1) _⟩
      map_add' a b := by apply Subtype.ext; simp only [Submodule.coe_add, map_add]
      map_smul' r a := by
        apply Subtype.ext
        simp only [Submodule.coe_smul, RingHom.id_apply, map_smul] }

def dgCoherentBarLayerCycleBoundary (x : D) (q : ℤ) (n : ℕ) :
    ((moduleEvaluation R D x).obj (dgCoherentBarLayerGraded R D G (n + 1))).cycles q ⟶
      (dgCoherentBarNormalizedStageComplex R D G x n).X (q + 1) :=
  ModuleCat.ofHom (LinearMap.codRestrict
    (dgCoherentBarNormalizedDegreeFiltration R D G x (q + 1) n)
    ((((dgCoherentBarNormalizedModuleUnconditional R D G).obj (Opposite.op x)).d
      q (q + 1)).hom.comp
        ((dgCoherentBarNormalizedDegreeFiltration R D G x q (n + 1)).subtype.comp
          (dgCoherentBarLayerCycleLift R D G x q n).hom))
    (fun z => dgCoherentBarLayerCycleLift_boundary_mem R D G x q n _
          (ConcreteCategory.congr_hom
            (((moduleEvaluation R D x).obj (dgCoherentBarLayerGraded R D G (n + 1))).iCycles_d
              q (q + 1)) z)))

lemma dgCoherentBarLayerCycleLift_toLayer (x : D) (q : ℤ) (n : ℕ) :
    dgCoherentBarLayerCycleLift R D G x q n ≫
      (dgCoherentBarStageToLayer R D G x (n + 1)).f q =
    ((moduleEvaluation R D x).obj (dgCoherentBarLayerGraded R D G (n + 1))).iCycles q := by
  ext z
  change (moduleDegreeEvaluation R D x q).map (dgCoherentBarLayerProjection R D G (n + 1))
    ((moduleDegreeEvaluation R D x q).map (dgCoherentBarLayerInclusion R D G (n + 1)) _) = _
  rw [← ModuleCat.comp_apply, ← Functor.map_comp, dgCoherentBarLayerInclusion_projection,
    CategoryTheory.Functor.map_id, ModuleCat.id_apply]

lemma dgCoherentBarLayerCycleBoundary_stageMap (x : D) (q : ℤ) (n : ℕ) :
    dgCoherentBarLayerCycleBoundary R D G x q n ≫
      (dgCoherentBarNormalizedStageMap R D G x (Nat.le_succ n)).f (q + 1) =
    dgCoherentBarLayerCycleLift R D G x q n ≫
      (dgCoherentBarNormalizedStageComplex R D G x (n + 1)).d q (q + 1) := by
  dsimp only [dgCoherentBarNormalizedStageComplex, dgBarDegreeSubcomplex]
  rw [CochainComplex.of_d]
  ext z
  rfl

end SerrePositivity.InfinityCategories
