module

public import SerrePositivity.HomologicalAlgebra.FiniteFreeResolution
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.TensorProduct.Finite

/-!
# 有限自由分解によるトレースの降下

有限自由分解を持つ加群の自己準同型を体へ係数拡大すると、そのトレースは基底環から来る。
分解の各段で自己準同型を持ち上げ、核に誘導される写像のトレースを差し引く。
短完全列のトレース加法性には、体上の分裂と合成の順序を交換するトレース公式を使う。
正則生成列からの有限自由分解を通じて、正則局所環の正規性の証明に用いる。
-/

public section

universe u

namespace SerrePositivity

open LinearMap
open scoped TensorProduct

/-- 有限次元ベクトル空間の短完全列と両立する自己準同型のトレースは加法的。
列を線形に分裂させ、恒等写像を二つの射影の和として計算する。 -/
theorem trace_eq_add_of_exact
    {K U V W : Type u} [Field K]
    [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (i : U →ₗ[K] V) (p : V →ₗ[K] W)
    (hi : Function.Injective i) (hp : Function.Surjective p) (he : Function.Exact i p)
    (a : U →ₗ[K] U) (b : V →ₗ[K] V) (c : W →ₗ[K] W)
    (hab : b.comp i = i.comp a) (hbc : p.comp b = c.comp p) :
    trace K V b = trace K U a + trace K W c := by
  obtain ⟨s, hs⟩ := p.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hp)
  let q : V →ₗ[K] LinearMap.range i :=
    (LinearMap.id - s.comp p).codRestrict _ (by
      intro x
      apply (he (x - s (p x))).mp
      simp only [map_sub]
      exact sub_eq_zero.mpr (congrArg (fun f : W →ₗ[K] W ↦ f (p x)) hs).symm)
  let t : V →ₗ[K] U := (LinearEquiv.ofInjective i hi).symm.toLinearMap.comp q
  have hit : i.comp t = LinearMap.id - s.comp p := by
    ext x
    exact congrArg Subtype.val ((LinearEquiv.ofInjective i hi).apply_symm_apply (q x))
  have hti : t.comp i = LinearMap.id := by
    ext x
    apply hi
    have hh := congrArg (fun f : V →ₗ[K] V ↦ f (i x)) hit
    simpa [he.apply_apply_eq_zero x] using hh
  have hb : b = i.comp (t.comp b) + s.comp (p.comp b) := by
    rw [← LinearMap.comp_assoc, hit, LinearMap.sub_comp, LinearMap.id_comp]
    simp [LinearMap.comp_assoc]
  rw [hb, map_add]
  congr 1
  · rw [trace_comp_comm' (t.comp b) i, LinearMap.comp_assoc, hab,
      ← LinearMap.comp_assoc, hti, LinearMap.id_comp]
  · rw [trace_comp_comm' (p.comp b) s, hbc, LinearMap.comp_assoc, hs, LinearMap.comp_id]

/-- 有限自由加群の短完全列を有限回たどり、最後の核も自由なら、体への係数拡大後の
トレースは基底環から来る。核の自己準同型は射影性による持ち上げから構成する。 -/
theorem trace_baseChange_mem_range_of_free_syzygy
    {R K : Type u} [CommRing R] [Field K] [Algebra R K] [Module.Flat R K]
    (Z F : ℕ → ModuleCat.{u} R)
    (hZ : ∀ j, Module.Finite R (Z j))
    (hF : ∀ j, Module.Finite R (F j)) (hfree : ∀ j, Module.Free R (F j))
    (i : ∀ j, Z (j + 1) →ₗ[R] F j) (p : ∀ j, F j →ₗ[R] Z j)
    (hi : ∀ j, Function.Injective (i j)) (hp : ∀ j, Function.Surjective (p j))
    (he : ∀ j, Function.Exact (i j) (p j))
    (n : ℕ) (hn : Module.Free R (Z n)) (f : Z 0 →ₗ[R] Z 0) :
    trace K (K ⊗[R] Z 0) (f.baseChange K) ∈ Set.range (algebraMap R K) := by
  induction n generalizing Z F with
  | zero =>
    let := hn
    let := hZ 0
    exact ⟨trace R (Z 0) f, (trace_baseChange f K).symm⟩
  | succ n ih =>
    let := hfree 0
    let := hF 0
    let := hZ 0
    let := hZ 1
    obtain ⟨b, hb⟩ := Module.projective_lifting_property (p 0) (f.comp (p 0)) (hp 0)
    let q : Z 1 →ₗ[R] LinearMap.range (i 0) :=
      (b.comp (i 0)).codRestrict _ (by
        intro x
        apply (he 0 (b (i 0 x))).mp
        have h := congrArg (fun g : F 0 →ₗ[R] Z 0 ↦ g (i 0 x)) hb
        simpa [(he 0).apply_apply_eq_zero x] using h)
    let a : Z 1 →ₗ[R] Z 1 := (LinearEquiv.ofInjective (i 0) (hi 0)).symm.toLinearMap.comp q
    have ha : b.comp (i 0) = (i 0).comp a := by
      ext x
      exact (congrArg Subtype.val
        ((LinearEquiv.ofInjective (i 0) (hi 0)).apply_symm_apply (q x))).symm
    obtain ⟨r, hr⟩ := ih (fun j ↦ Z (j + 1)) (fun j ↦ F (j + 1))
      (fun j ↦ hZ (j + 1)) (fun j ↦ hF (j + 1)) (fun j ↦ hfree (j + 1))
      (fun j ↦ i (j + 1)) (fun j ↦ p (j + 1))
      (fun j ↦ hi (j + 1)) (fun j ↦ hp (j + 1)) (fun j ↦ he (j + 1)) hn a
    have ht := trace_eq_add_of_exact ((i 0).baseChange K) ((p 0).baseChange K)
      (Module.Flat.lTensor_preserves_injective_linearMap (M := K) (i 0) (hi 0))
      ((p 0).baseChange_surjective K (hp 0)) (Module.Flat.lTensor_exact K (he 0))
      (a.baseChange K) (b.baseChange K) (f.baseChange K)
      (by simpa only [LinearMap.baseChange_comp] using congrArg (LinearMap.baseChange K) ha)
      (by simpa only [LinearMap.baseChange_comp] using congrArg (LinearMap.baseChange K) hb)
    refine ⟨trace R (F 0) b - r, ?_⟩
    rw [map_sub, hr, ← trace_baseChange b K, ht, add_sub_cancel_left]

/-- 極大イデアルが正則列で生成される局所環では、任意の有限加群の自己準同型について
平坦な体への係数拡大後のトレースが基底環に属する。最終核の自由性は既存の分解構成による。 -/
theorem trace_baseChange_mem_range_of_regular_generators
    {R K : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [Field K] [Algebra R K] [Module.Flat R K]
    (rs : List R) (hreg : RingTheory.Sequence.IsWeaklyRegular R rs)
    (hgen : Ideal.ofList rs = IsLocalRing.maximalIdeal R)
    (M : ModuleCat.{u} R) [Module.Finite R M] (f : M →ₗ[R] M) :
    trace K (K ⊗[R] M) (f.baseChange K) ∈ Set.range (algebraMap R K) := by
  let Z := FiniteFreeResolution.syzygy (FGModuleCat.of R M)
  let N (j : ℕ) := (Z j).obj
  let F (j : ℕ) := FiniteFreeResolution.cover (Z j)
  let p (j : ℕ) : F j →ₗ[R] N j := FiniteFreeResolution.coverπ (Z j)
  let i (j : ℕ) : N (j + 1) →ₗ[R] F j := (LinearMap.ker (p j)).subtype
  have hN (j : ℕ) : Module.Finite R (N j) := (Z j).property
  have hF (j : ℕ) : Module.Finite R (F j) := by dsimp [F]; infer_instance
  have hfree (j : ℕ) : Module.Free R (F j) := by dsimp [F]; infer_instance
  have hi (j : ℕ) : Function.Injective (i j) := Subtype.val_injective
  have hp (j : ℕ) : Function.Surjective (p j) := FiniteFreeResolution.coverπ_surjective _
  have he (j : ℕ) : Function.Exact (i j) (p j) := LinearMap.exact_subtype_ker_map _
  exact trace_baseChange_mem_range_of_free_syzygy N F hN hF hfree i p hi hp he rs.length
    (free_syzygy_of_regular_generators rs hreg hgen N F hN hfree i p hi hp he) f

end SerrePositivity
