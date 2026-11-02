module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.TowerUnit
public import SerrePositivity.CommutativeAlgebra.Koszul.Resolution

/-! # 標準包含で正規化したKoszulのH⁰

零次数環からの包含が誘導する全射とその核を計算し、商との同型を正規化する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
variable (R : Type u) [CommRing R]

/-- 零次数環からKoszulのH⁰への標準写像。 -/
def koszulH0Unit {e : ℕ} (a : Fin e → R) : R →ₗ[R] (koszulComplex a).homology 0 :=
  (HomologicalComplex.homologyMap (koszulComplexInclusion R a) 0).hom.comp
    (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0
      (ModuleCat.of R R)).inv.hom

/-- 一座標増やしたときの標準写像の式。 -/
theorem koszulH0Unit_succ {e : ℕ} (a : Fin (e + 1) → R) :
    koszulH0Unit R a =
      (HomologicalComplex.homologyMap (CochainComplex.mappingCone.inr
        (smulId (a (Fin.last e)) (koszulComplex (Fin.init a)))) 0).hom.comp
          (koszulH0Unit R (Fin.init a)) := by
  simp only [koszulH0Unit, koszulComplexInclusion, HomologicalComplex.homologyMap_comp,
    ModuleCat.hom_comp, LinearMap.comp_assoc]

/-- KoszulのH⁰は、標準包含の像で生成される。 -/
theorem koszulH0Unit_surjective : ∀ {e : ℕ} (a : Fin e → R),
    Function.Surjective (koszulH0Unit R a)
  | 0, a => by
    simp only [koszulH0Unit, koszulComplexInclusion, HomologicalComplex.homologyMap_id,
      ModuleCat.hom_id, LinearMap.id_comp]
    exact (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0
      (ModuleCat.of R R)).toLinearEquiv.symm.surjective
  | e + 1, a => by
    have h1 := koszulComplex_isZero_homology_of_pos (Fin.init a) 1 one_pos
    have h3 := Cone.exact₃ (smulId (a (Fin.last e)) (koszulComplex (Fin.init a))) 0 1 rfl
    have hj := h3.epi_f (h1.eq_zero_of_tgt _)
    rw [koszulH0Unit_succ]
    exact ((ModuleCat.epi_iff_surjective _).mp hj).comp
      (koszulH0Unit_surjective (Fin.init a))

private theorem ker_comp_of_scalar_range
    {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (u : R →ₗ[R] M) (hu : Function.Surjective u) (j : M →ₗ[R] N) (a : R)
    (hj : LinearMap.range (a • LinearMap.id : M →ₗ[R] M) = j.ker) :
    (j.comp u).ker = u.ker ⊔ Submodule.span R {a} := by
  apply le_antisymm
  · intro r hr
    have hur : u r ∈ LinearMap.range (a • LinearMap.id : M →ₗ[R] M) := by
      rw [hj]
      exact hr
    obtain ⟨m, hm⟩ := hur
    obtain ⟨s, hs⟩ := hu m
    have hdiff : r - a * s ∈ u.ker := by
      change u (r - a * s) = 0
      rw [map_sub, show a * s = a • s from rfl, map_smul, hs]
      change u r - a • m = 0
      rw [show a • m = u r from hm, sub_self]
    have hprod : a * s ∈ Submodule.span R {a} := by
      exact Submodule.mem_span_singleton.mpr ⟨s, by simp [smul_eq_mul, mul_comm]⟩
    exact sub_add_cancel r (a * s) ▸ (u.ker ⊔ Submodule.span R {a}).add_mem
      ((show u.ker ≤ u.ker ⊔ Submodule.span R {a} from le_sup_left) hdiff)
      ((show Submodule.span R {a} ≤ u.ker ⊔ Submodule.span R {a} from le_sup_right) hprod)
  · apply sup_le
    · intro r hr
      change j (u r) = 0
      rw [show u r = 0 from hr, map_zero]
    · apply Submodule.span_le.mpr
      intro r hr
      rw [Set.mem_singleton_iff] at hr
      subst r
      change u a ∈ j.ker
      rw [← hj]
      refine ⟨u 1, ?_⟩
      change a • u 1 = u a
      rw [← map_smul, smul_eq_mul, mul_one]

/-- 標準包含からH⁰への写像の核は、列の生成イデアル。 -/
theorem koszulH0Unit_ker : ∀ {e : ℕ} (a : Fin e → R),
    (koszulH0Unit R a).ker = Ideal.span (Set.range a)
  | 0, a => by
    rw [Set.range_eq_empty, Ideal.span_empty]
    apply LinearMap.ker_eq_bot.mpr
    simp only [koszulH0Unit, koszulComplexInclusion, HomologicalComplex.homologyMap_id,
      ModuleCat.hom_id, LinearMap.id_comp]
    exact (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0
      (ModuleCat.of R R)).toLinearEquiv.symm.injective
  | e + 1, a => by
    have h2 := Cone.exact₂ (smulId (a (Fin.last e)) (koszulComplex (Fin.init a))) 0
    have hrk := (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mp h2
    have hmap : HomologicalComplex.homologyMap
        (smulId (a (Fin.last e)) (koszulComplex (Fin.init a))) 0 =
      a (Fin.last e) • 𝟙 ((koszulComplex (Fin.init a)).homology 0) := by
      rw [smulId, homologyMap_smul, HomologicalComplex.homologyMap_id]
    change (HomologicalComplex.homologyMap
      (smulId (a (Fin.last e)) (koszulComplex (Fin.init a))) 0).hom.range =
      (HomologicalComplex.homologyMap (CochainComplex.mappingCone.inr
        (smulId (a (Fin.last e)) (koszulComplex (Fin.init a)))) 0).hom.ker at hrk
    rw [hmap] at hrk
    rw [koszulH0Unit_succ, ker_comp_of_scalar_range R _
      (koszulH0Unit_surjective R (Fin.init a)) _ _ hrk, koszulH0Unit_ker]
    have hrange : Set.range a = insert (a (Fin.last e)) (Set.range (Fin.init a)) := by
      have h := Fin.range_snoc (Fin.init a) (a (Fin.last e))
      rwa [Fin.snoc_init_self] at h
    rw [hrange]
    change _ = Submodule.span R _
    rw [Submodule.span_insert, sup_comm]

/-- 標準包含の像を商の標準元へ送る、正規化されたH⁰の同型。 -/
def koszulCanonicalH0Equiv {e : ℕ} (a : Fin e → R) :
    (koszulComplex a).homology 0 ≃ₗ[R] R ⧸ Ideal.span (Set.range a) :=
  (LinearMap.quotKerEquivOfSurjective (koszulH0Unit R a)
    (koszulH0Unit_surjective R a)).symm.trans
      (Submodule.quotEquivOfEq _ _ (koszulH0Unit_ker R a))

@[simp] theorem koszulCanonicalH0Equiv_unit {e : ℕ} (a : Fin e → R) (r : R) :
    koszulCanonicalH0Equiv R a (koszulH0Unit R a r) = Ideal.Quotient.mk _ r := by
  simp only [koszulCanonicalH0Equiv, LinearEquiv.trans_apply,
    LinearMap.quotKerEquivOfSurjective_symm_apply]
  exact Submodule.quotEquivOfEq_mk _ _ _ r

/-- 座標の倍数によるKoszul写像は標準包含を保つ。 -/
theorem koszulH0Unit_mapOfMul {e : ℕ} (a b c : Fin e → R)
    (h : ∀ i, a i = b i * c i) (r : R) :
    (HomologicalComplex.homologyMap (koszulComplexMapOfMul R a b c h) 0).hom
      (koszulH0Unit R a r) = koszulH0Unit R b r := by
  have hcomp := congrArg (fun f ↦ HomologicalComplex.homologyMap f 0)
    (koszulComplexInclusion_mapOfMul R a b c h)
  rw [HomologicalComplex.homologyMap_comp] at hcomp
  exact LinearMap.congr_fun (congrArg (fun f ↦ f.hom.comp
    (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0
      (ModuleCat.of R R)).inv.hom) hcomp) r

end SerrePositivity.DerivedCompletion
