module

public import SerrePositivity.LengthAlgebra.RootTowerLength.FiniteGeneration
public import Mathlib.RingTheory.Flat.Equalizer

/-! # 有限段の短完全列から導く正規化長さの加法性

有限段の短完全列を根の塔へ係数拡大したとき、生の数値関数の加法性を証明する。
有限生成部分加群とその商を共通の有限段で実現し、中項が有限表示な冪ねじれ加群、
左項が有限生成の短完全列にも適用する。有限段の通常の長さと証明済みの有限生成一致
だけを使い、C2 の引用や `towerLength` の構造には依存しない。
-/

@[expose] public section

set_option linter.style.haveILetI false

universe u
open IsLocalRing TensorProduct
open scoped ENNReal

namespace SerrePositivity.Section2

variable (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
  {h : ℕ} (t : Fin h → A) (p : ℕ) [Fact p.Prime]
  (ht : ∀ i, t i ∈ maximalIdeal A)

include ht

/-- 有限段から係数拡大した加群の生の上限長さは、その段の正規化した長さに等しい。
証明済みの有限生成一致を使い、旧 C1 の引用には依存しない。 -/
theorem towerLengthFun_tensor_eq_length (n : ℕ) (V : Type u) [AddCommGroup V]
    [Module (TowerStage A t p n) V] (hV : IsFiniteLength (TowerStage A t p n) V) :
    towerLengthFun A t p (Tower A t p ⊗[TowerStage A t p n] V) =
      (Module.length (TowerStage A t p n) V : ℝ≥0∞) /
        (stageRank h p n : ℝ≥0∞) := by
  haveI : IsNoetherian (TowerStage A t p n) V :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hV).1
  rw [towerLengthFun_eq_fgLength_of_noetherian A t p ht,
    fgLength_tensor A t p ht n V hV]

/-- 有限段の通常の長さの加法性から、根の塔へ係数拡大した加群の生の長さの加法性を導く。
中央の加群が有限長であることだけで、両端の有限長性も従う。 -/
theorem towerLengthFun_add_of_stage_exact (n : ℕ) (V₁ V₂ V₃ : Type u)
    [AddCommGroup V₁] [Module (TowerStage A t p n) V₁]
    [AddCommGroup V₂] [Module (TowerStage A t p n) V₂]
    [AddCommGroup V₃] [Module (TowerStage A t p n) V₃]
    (f : V₁ →ₗ[TowerStage A t p n] V₂) (g : V₂ →ₗ[TowerStage A t p n] V₃)
    (hf : Function.Injective f) (hg : Function.Surjective g) (hfg : Function.Exact f g)
    (hV₂ : IsFiniteLength (TowerStage A t p n) V₂) :
    towerLengthFun A t p (Tower A t p ⊗[TowerStage A t p n] V₂) =
      towerLengthFun A t p (Tower A t p ⊗[TowerStage A t p n] V₁) +
      towerLengthFun A t p (Tower A t p ⊗[TowerStage A t p n] V₃) := by
  have hV₁ : IsFiniteLength (TowerStage A t p n) V₁ :=
    IsFiniteLength.of_injective hV₂ hf
  have hV₃ : IsFiniteLength (TowerStage A t p n) V₃ :=
    IsFiniteLength.of_surjective hV₂ hg
  rw [towerLengthFun_tensor_eq_length A t p ht n V₁ hV₁,
    towerLengthFun_tensor_eq_length A t p ht n V₂ hV₂,
    towerLengthFun_tensor_eq_length A t p ht n V₃ hV₃,
    Module.length_eq_add_of_exact f g hf hg hfg, ENat.toENNReal_add, ENNReal.add_div]

omit ht [IsLocalRing A] [IsNoetherianRing A] in
/-- 根の塔への係数拡大は、有限段の短完全列を保つ。 -/
theorem tower_baseChange_shortExact (n : ℕ) (V₁ V₂ V₃ : Type u)
    [AddCommGroup V₁] [Module (TowerStage A t p n) V₁]
    [AddCommGroup V₂] [Module (TowerStage A t p n) V₂]
    [AddCommGroup V₃] [Module (TowerStage A t p n) V₃]
    (f : V₁ →ₗ[TowerStage A t p n] V₂) (g : V₂ →ₗ[TowerStage A t p n] V₃)
    (hf : Function.Injective f) (hg : Function.Surjective g) (hfg : Function.Exact f g) :
    Function.Injective (f.baseChange (Tower A t p)) ∧
      Function.Surjective (g.baseChange (Tower A t p)) ∧
      Function.Exact (f.baseChange (Tower A t p)) (g.baseChange (Tower A t p)) := by
  letI := flat_tower A t p n
  exact ⟨Module.Flat.lTensor_preserves_injective_linearMap f hf,
    LinearMap.lTensor_surjective (Tower A t p) hg, Module.Flat.lTensor_exact _ hfg⟩

omit [IsNoetherianRing A] in
/-- 有限段からの係数拡大の中の有限生成部分加群とその商を、
共通の有限段の部分加群と商として実現する。 -/
theorem exists_stage_submodule_and_quotient_equiv (n : ℕ) (V : Type u)
    [AddCommGroup V] [Module (TowerStage A t p n) V]
    (hV : IsFiniteLength (TowerStage A t p n) V)
    (N : Submodule (Tower A t p) (Tower A t p ⊗[TowerStage A t p n] V)) (hN : N.FG) :
    ∃ (k : ℕ) (hnk : n ≤ k),
      letI := (towerMap A t p n k hnk).toRingHom.toAlgebra
      letI := isScalarTower_towerMap_tower A t p n k hnk
      ∃ K : Submodule (TowerStage A t p k)
          (TowerStage A t p k ⊗[TowerStage A t p n] V),
        IsFiniteLength (TowerStage A t p k)
            (TowerStage A t p k ⊗[TowerStage A t p n] V) ∧
          Nonempty (Tower A t p ⊗[TowerStage A t p k] K ≃ₗ[Tower A t p] N) ∧
          Nonempty (Tower A t p ⊗[TowerStage A t p k]
            ((TowerStage A t p k ⊗[TowerStage A t p n] V) ⧸ K) ≃ₗ[Tower A t p]
              ((Tower A t p ⊗[TowerStage A t p n] V) ⧸ N)) := by
  classical
  haveI : Module.Finite (Tower A t p) N := Module.Finite.iff_fg.mpr hN
  obtain ⟨r, z, hz⟩ := Module.Finite.exists_fin (R := Tower A t p) (M := N)
  obtain ⟨k, hnk, w, hw⟩ := exists_tower_tensor_family_stage A t p n V (fun j ↦ (z j).val)
  letI := (towerMap A t p n k hnk).toRingHom.toAlgebra
  letI := isScalarTower_towerMap_tower A t p n k hnk
  let Q := TowerStage A t p k ⊗[TowerStage A t p n] V
  let M := Tower A t p ⊗[TowerStage A t p n] V
  let K : Submodule (TowerStage A t p k) Q := Submodule.span _ (Set.range w)
  let E := TensorProduct.AlgebraTensorModule.cancelBaseChange (TowerStage A t p n)
    (TowerStage A t p k) (Tower A t p) (Tower A t p) V
  let F : Q →ₗ[TowerStage A t p k] M :=
    (E.toLinearMap.restrictScalars (TowerStage A t p k)).comp
      (TensorProduct.mk (TowerStage A t p k) (Tower A t p) Q 1)
  have hF : K ≤ (N.restrictScalars (TowerStage A t p k)).comap F := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    change E (1 ⊗ₜ w j) ∈ N
    rw [hw j]
    exact (z j).property
  let FK : K →ₗ[TowerStage A t p k] N :=
    { toFun := fun x ↦ ⟨F x, hF x.property⟩
      map_add' := fun x y ↦ Subtype.ext (F.map_add x y)
      map_smul' := fun a x ↦ Subtype.ext (F.map_smul a x) }
  let L := FK.liftBaseChange (Tower A t p)
  have hLs : Function.Surjective L := by
    rw [← LinearMap.range_eq_top, ← top_le_iff, ← hz, Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    refine ⟨1 ⊗ₜ (⟨w j, Submodule.subset_span (Set.mem_range_self j)⟩ : K), ?_⟩
    apply Subtype.ext
    change (1 : Tower A t p) • E (1 ⊗ₜ w j) = (z j).val
    rw [one_smul, hw j]
  let B := K.subtype.baseChange (Tower A t p)
  have hcomm : N.subtype.comp L = E.toLinearMap.comp B := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro a x
    change a • E (1 ⊗ₜ (x : Q)) = E (a ⊗ₜ (x : Q))
    rw [← E.map_smul]
    congr 1
    simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  letI := flat_tower A t p k
  have hBi : Function.Injective B :=
    Module.Flat.lTensor_preserves_injective_linearMap K.subtype (Submodule.subtype_injective K)
  have hLi : Function.Injective L := by
    have hc : Function.Injective (N.subtype.comp L) := hcomm.symm ▸ E.injective.comp hBi
    intro x y hxy
    exact hc (congrArg (fun v : N ↦ v.val) hxy)
  let π := N.mkQ.comp E.toLinearMap
  have hπs : Function.Surjective π := N.mkQ_surjective.comp E.surjective
  have hπ : Function.Exact B π := by
    rw [LinearMap.exact_iff]
    ext x
    change π x = 0 ↔ x ∈ LinearMap.range B
    change N.mkQ (E x) = 0 ↔ _
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    constructor
    · intro hx
      obtain ⟨y, hy⟩ := hLs ⟨E x, hx⟩
      refine ⟨y, E.injective ?_⟩
      have hc := LinearMap.congr_fun hcomm y
      exact hc.symm.trans (congrArg (fun v : N ↦ v.val) hy)
    · rintro ⟨y, rfl⟩
      have hc := LinearMap.congr_fun hcomm y
      change (L y).val = E (B y) at hc
      rw [← hc]
      exact (L y).property
  let S := K.mkQ.baseChange (Tower A t p)
  have hSs : Function.Surjective S := LinearMap.lTensor_surjective _ K.mkQ_surjective
  have hS₀ := _root_.lTensor_exact (R := TowerStage A t p k) (M := K) (N := Q)
    (P := Q ⧸ K) (f := K.subtype) (g := K.mkQ) (Tower A t p)
    (LinearMap.exact_subtype_mkQ K) K.mkQ_surjective
  have hS : Function.Exact B S := hS₀
  have hker : S.ker = π.ker := hS.linearMap_ker_eq.trans hπ.linearMap_ker_eq.symm
  let eQuot := (S.quotKerEquivOfSurjective hSs).symm.trans
    ((Submodule.quotEquivOfEq _ _ hker).trans (π.quotKerEquivOfSurjective hπs))
  have hQ : IsFiniteLength (TowerStage A t p k) Q := by
    rw [← Module.length_ne_top_iff]
    change Module.length (TowerStage A t p k)
      (TowerStage A t p k ⊗[TowerStage A t p n] V) ≠ ⊤
    rw [length_tensor_towerMap A t p n k hnk ht]
    obtain ⟨l, hl⟩ := ENat.ne_top_iff_exists.mp (Module.length_ne_top_iff.mpr hV)
    rw [← hl, ← Nat.cast_mul]
    exact ENat.natCast_ne_top _
  exact ⟨k, hnk, K, hQ, ⟨LinearEquiv.ofBijective L ⟨hLi, hLs⟩⟩, ⟨eQuot⟩⟩

/-- 有限表示な冪ねじれ加群とその有限生成部分加群・商について、生の長さは加法的。
共通の有限段の部分加群の短完全列に帰着する。 -/
theorem towerLengthFun_add_submodule_of_finitePresentation (M : Type u)
    [AddCommGroup M] [Module (Tower A t p) M]
    [Module.FinitePresentation (Tower A t p) M]
    (hM : IsPowTorsion (towerMaxIdeal A t p) M)
    (N : Submodule (Tower A t p) M) (hN : N.FG) :
    towerLengthFun A t p M = towerLengthFun A t p N + towerLengthFun A t p (M ⧸ N) := by
  obtain ⟨n, V, i₁, i₂, hV, _, ⟨e⟩⟩ := exists_descent A t p M hM
  let N' := N.map e.toLinearMap
  obtain ⟨k, hnk, K, hQ, ⟨eK⟩, ⟨eQuot⟩⟩ :=
    exists_stage_submodule_and_quotient_equiv A t p ht n V hV N' (hN.map e.toLinearMap)
  letI := (towerMap A t p n k hnk).toRingHom.toAlgebra
  letI := isScalarTower_towerMap_tower A t p n k hnk
  let Q := TowerStage A t p k ⊗[TowerStage A t p n] V
  let E := TensorProduct.AlgebraTensorModule.cancelBaseChange (TowerStage A t p n)
    (TowerStage A t p k) (Tower A t p) (Tower A t p) V
  let eN : N ≃ₗ[Tower A t p] N' :=
    Submodule.equivMapOfInjective e.toLinearMap e.injective N
  let eMQ : (M ⧸ N) ≃ₗ[Tower A t p]
      ((Tower A t p ⊗[TowerStage A t p n] V) ⧸ N') :=
    Submodule.Quotient.equiv N N' e rfl
  have hleft := towerLengthFun_congr (A := A) (t := t) (p := p) (eK.trans eN.symm)
  have hright := towerLengthFun_congr (A := A) (t := t) (p := p) (eQuot.trans eMQ.symm)
  calc
    towerLengthFun A t p M = towerLengthFun A t p (Tower A t p ⊗[TowerStage A t p k] Q) :=
      (towerLengthFun_congr (E.trans e.symm)).symm
    _ = towerLengthFun A t p (Tower A t p ⊗[TowerStage A t p k] K) +
        towerLengthFun A t p (Tower A t p ⊗[TowerStage A t p k] (Q ⧸ K)) :=
      towerLengthFun_add_of_stage_exact A t p ht k K Q (Q ⧸ K) K.subtype K.mkQ
        (Submodule.subtype_injective K) K.mkQ_surjective (LinearMap.exact_subtype_mkQ K) hQ
    _ = towerLengthFun A t p N + towerLengthFun A t p (M ⧸ N) := by
      rw [hleft, hright]

/-- 中項が有限表示な冪ねじれ加群、左項が有限生成の短完全列では、生の長さは加法的。
特に、三つの加群がすべて有限表示の場合に適用できる。 -/
theorem towerLengthFun_add_of_exact_finitePresentation (M₁ M₂ M₃ : Type u)
    [AddCommGroup M₁] [Module (Tower A t p) M₁] [Module.Finite (Tower A t p) M₁]
    [AddCommGroup M₂] [Module (Tower A t p) M₂]
    [Module.FinitePresentation (Tower A t p) M₂]
    [AddCommGroup M₃] [Module (Tower A t p) M₃]
    (f : M₁ →ₗ[Tower A t p] M₂) (g : M₂ →ₗ[Tower A t p] M₃)
    (hf : Function.Injective f) (hg : Function.Surjective g) (hfg : Function.Exact f g)
    (hM₂ : IsPowTorsion (towerMaxIdeal A t p) M₂) :
    towerLengthFun A t p M₂ = towerLengthFun A t p M₁ + towerLengthFun A t p M₃ := by
  have hN : (LinearMap.range f).FG := by
    simpa only [Submodule.map_top] using (Module.Finite.fg_top (R := Tower A t p) (M := M₁)).map f
  have hh := towerLengthFun_add_submodule_of_finitePresentation A t p ht M₂ hM₂
    (LinearMap.range f) hN
  let eLeft := LinearEquiv.ofInjective f hf
  let eRight := (Submodule.quotEquivOfEq _ _ hfg.linearMap_ker_eq.symm).trans
    (g.quotKerEquivOfSurjective hg)
  rw [← towerLengthFun_congr eLeft, towerLengthFun_congr eRight] at hh
  exact hh

end SerrePositivity.Section2
