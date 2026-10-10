module

public import SerrePositivity.CommutativeAlgebra.MinimalGenerators

/-! # Noether 局所環上の極小自由分解

剰余体の基底から作った極小自由被覆を、各核に繰り返し適用する。
Noether 性は核の有限生成性のみに使う。環の正則性や分解の有界性は仮定しない。
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace SerrePositivity.MinimalFreeResolution

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable (M : FGModuleCat.{u} R)

/-- 極小被覆の核を繰り返して得る有限生成の syzygy。 -/
noncomputable def syzygy : ℕ → FGModuleCat.{u} R
  | 0 => M
  | n + 1 => FGModuleCat.of R (LinearMap.ker (MinimalGenerators.π (syzygy n)))

/-- 極小分解の各項。 -/
noncomputable abbrev term (n : ℕ) : ModuleCat.{u} R :=
  MinimalGenerators.cover (syzygy M n)

/-- 各項から syzygy への全射。 -/
noncomputable abbrev π (n : ℕ) : term M n →ₗ[R] syzygy M n :=
  MinimalGenerators.π (syzygy M n)

/-- syzygy を前の自由項の核として埋め込む。 -/
noncomputable def ι (n : ℕ) : syzygy M (n + 1) →ₗ[R] term M n :=
  (LinearMap.ker (π M n)).subtype

lemma ι_injective (n : ℕ) : Function.Injective (ι M n) := Subtype.val_injective

lemma π_surjective (n : ℕ) : Function.Surjective (π M n) :=
  MinimalGenerators.π_surjective _

lemma exact_ι_π (n : ℕ) : Function.Exact (ι M n) (π M n) :=
  LinearMap.exact_subtype_ker_map _

/-- 極小自由分解の隣接する項の微分。 -/
noncomputable def d (n : ℕ) : term M (n + 1) ⟶ term M n :=
  ModuleCat.ofHom ((ι M n).comp (π M (n + 1)))

lemma d_comp_d (n : ℕ) : d M (n + 1) ≫ d M n = 0 := by
  ext x
  change ι M n (π M (n + 1) (ι M (n + 1) (π M (n + 2) x))) = 0
  rw [(exact_ι_π M (n + 1)).apply_apply_eq_zero, map_zero]

/-- 自然数添字の極小自由複体。 -/
noncomputable def complex : ChainComplex (ModuleCat.{u} R) ℕ :=
  ChainComplex.of (term M) (d M) (d_comp_d M)

@[simp] lemma complex_d (n : ℕ) : (complex M).d (n + 1) n = d M n :=
  ChainComplex.of_d _ _ n

lemma exact_d_π : Function.Exact (d M 0).hom (π M 0) := by
  rw [LinearMap.exact_iff]
  change LinearMap.ker (π M 0) = LinearMap.range ((ι M 0).comp (π M 1))
  rw [LinearMap.range_comp_of_range_eq_top _
    (LinearMap.range_eq_top.mpr (π_surjective M 1))]
  exact (LinearMap.exact_iff.mp (exact_ι_π M 0))

lemma exact_d_d (n : ℕ) : Function.Exact (d M (n + 1)).hom (d M n).hom := by
  rw [LinearMap.exact_iff]
  change LinearMap.ker ((ι M n).comp (π M (n + 1))) =
    LinearMap.range ((ι M (n + 1)).comp (π M (n + 2)))
  rw [LinearMap.ker_comp, LinearMap.ker_eq_bot.mpr (ι_injective M n), Submodule.comap_bot,
    LinearMap.range_comp_of_range_eq_top _
      (LinearMap.range_eq_top.mpr (π_surjective M (n + 2)))]
  exact LinearMap.exact_iff.mp (exact_ι_π M (n + 1))

/-- 増大射と完全性を備えた極小射影分解。全ての項は有限自由である。 -/
noncomputable def resolution : ProjectiveResolution M.obj := by
  let g : (complex M).X 0 ⟶ M.obj := ModuleCat.ofHom (π M 0)
  have hg : (complex M).d 1 0 ≫ g = 0 := by
    ext x
    exact (exact_d_π M).apply_apply_eq_zero x
  refine { complex := complex M, projective := ?_, π :=
    (ChainComplex.toSingle₀Equiv (complex M) M.obj).symm ⟨g, hg⟩, quasiIso := ?_ }
  · intro n
    change Projective (term M n)
    infer_instance
  · constructor
    intro n
    cases n with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
      · exact ⟨(ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr (exact_d_π M),
          (ModuleCat.epi_iff_surjective g).mpr (π_surjective M 0)⟩
      all_goals rfl
    | succ n =>
      rw [quasiIsoAt_iff_exactAt' _ _ (ChainComplex.exactAt_succ_single_obj _ _)]
      rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp)]
      apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr
      change Function.Exact ((complex M).d (n + 2) (n + 1)).hom
        ((complex M).d (n + 1) n).hom
      simp only [complex_d]
      exact exact_d_d M n

@[simp] lemma resolution_complex : (resolution M).complex = complex M := rfl

/-- 極小分解を整数添字に延長しても、各項は自由である。 -/
instance extRes_free (q : ℤ) : Module.Free R ((extRes (resolution M)).X q) := by
  by_cases hq : 0 < q
  · have := ModuleCat.subsingleton_of_isZero (extRes_isZero_X (resolution M) q hq)
    exact Module.Free.of_subsingleton _ _
  · have : Module.Free R ((complex M).X (-q).toNat) := by
      change Module.Free R (term M (-q).toNat)
      infer_instance
    exact Module.Free.of_equiv
      ((complex M).extendXIso embUp (i := (-q).toNat) (by simp; omega)).toLinearEquiv.symm

/-- 整数添字に延長した極小分解の各項は有限生成である。分解全体の有界性は不要。 -/
instance extRes_finite (q : ℤ) : Module.Finite R ((extRes (resolution M)).X q) := by
  by_cases hq : 0 < q
  · have := ModuleCat.subsingleton_of_isZero (extRes_isZero_X (resolution M) q hq)
    infer_instance
  · have : Module.Finite R ((complex M).X (-q).toNat) := by
      change Module.Finite R (term M (-q).toNat)
      infer_instance
    exact Module.Finite.equiv
      ((complex M).extendXIso embUp (i := (-q).toNat) (by simp; omega)).toLinearEquiv.symm

/-- 自由分解の全ての微分は、全ての座標で極大イデアルに値をとる。 -/
lemma d_coordinate_mem (n : ℕ) (x : term M (n + 1))
    (i : Fin (MinimalGenerators.rank (syzygy M n))) :
    d M n x i ∈ IsLocalRing.maximalIdeal R := by
  apply MinimalGenerators.ker_coordinate_mem
  exact (exact_ι_π M n).apply_apply_eq_zero (π M (n + 1) x)

end SerrePositivity.MinimalFreeResolution
