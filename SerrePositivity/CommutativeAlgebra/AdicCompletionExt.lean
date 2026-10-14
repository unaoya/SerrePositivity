module

public import Mathlib.RingTheory.AdicCompletion.Completeness

/-! # 完備化から分離加群への線形写像の外延性

元の加群の像での一致を、冪商の代表元と分離性によって完備化全体へ延長する。
-/

@[expose] public section
namespace SerrePositivity

/-- 有限生成イデアルの完備化から分離加群への線形写像は、元の加群の像で決まる。 -/
theorem adicCompletion_linearMap_ext_of_of {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (I : Ideal R) (hI : I.FG) [IsHausdorff I N]
    (f g : AdicCompletion I M →ₗ[R] N)
    (h : f.comp (AdicCompletion.of I M) = g.comp (AdicCompletion.of I M)) : f = g := by
  apply LinearMap.ext
  intro x
  apply (IsHausdorff.eq_iff_smodEq (I := I)).mpr
  intro n
  obtain ⟨a, ha⟩ := (I ^ n • (⊤ : Submodule R M)).mkQ_surjective (AdicCompletion.eval I M n x)
  have hx : x - AdicCompletion.of I M a ∈ I ^ n • (⊤ : Submodule R (AdicCompletion I M)) := by
    rw [AdicCompletion.pow_smul_top_eq_ker_eval hI, LinearMap.mem_ker, map_sub,
      AdicCompletion.eval_of]
    exact sub_eq_zero.mpr ha.symm
  have hm (l : AdicCompletion I M →ₗ[R] N) :
      l x ≡ l (AdicCompletion.of I M a) [SMOD I ^ n • (⊤ : Submodule R N)] := by
    apply SModEq.sub_mem.mpr
    rw [← map_sub]
    have hl : l (x - AdicCompletion.of I M a) ∈
        (I ^ n • (⊤ : Submodule R (AdicCompletion I M))).map l := ⟨_, hx, rfl⟩
    rw [Submodule.map_smul''] at hl
    exact Submodule.smul_mono le_rfl le_top hl
  have he : f (AdicCompletion.of I M a) = g (AdicCompletion.of I M a) := LinearMap.congr_fun h a
  exact (hm f).trans (he ▸ (hm g).symm)

end SerrePositivity
