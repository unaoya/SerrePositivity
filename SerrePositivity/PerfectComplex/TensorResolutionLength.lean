module

public import SerrePositivity.HomologicalAlgebra.TorLES
public import SerrePositivity.HomologicalAlgebra.BaseChange
public import SerrePositivity.PerfectComplex.NormalizedLength
public import SerrePositivity.PerfectComplex.Closure
public import Mathlib.LinearAlgebra.TensorProduct.Prod
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition

/-!
# 分解とのテンソルのホモロジーの正規化長さ

## 概要

環準同型 `ψ : B → S`、`S` 加群 `M`、有限自由 `B` 加群からなる複体 `G`（加群 `L` の分解）について、
`M ⊗_B G = M ⊗_S (S ⊗_B G)` を `S` 加群の複体として扱う（`tensorRes`）。そのホモロジーは
`Tor^B(M, L)` に `S` の作用を載せたもので、`S` 上の正規化長さ `μ` で測れる。

論文 Lemma 5.4 の証明の評価 (5.12) の一般形を示す：`S` 線形写像 `f : P → U` の核 `K`、
余核 `W` について

  `μ(H^m(P ⊗ G)) ≤ μ(H^m(U ⊗ G)) + r_m μ(K) + r_{m−1} μ(W)`、
  `μ(H^m(U ⊗ G)) ≤ μ(H^m(P ⊗ G)) + r_{m+1} μ(K) + r_m μ(W)`

（`r_m = rank_B G^m`）。

## 方針

- `G` の項は自由なので `S ⊗_B G^m` は平坦で、`M ↦ M ⊗ G` は短完全列を保つ
  （`tensorComplex_shortExact`）。`P ↠ im f ↪ U` の二つの短完全列のホモロジー長完全列を使う。
- `μ(H^m(K ⊗ G)) ≤ μ(K ⊗_S (S ⊗_B G^m)) = r_m μ(K)`（ホモロジーは項の部分商、項は `K^{r_m}`）。

## 使われ方

`Paper/Section2/TowerApproximation.lean`（Lemma 5.4 の一般論）。
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory
open scoped ENNReal

namespace SerrePositivity

namespace TensorRes

variable {S : Type u} [CommRing S] {J : Ideal S} (μ : NormalizedLength S J)

/-! ## 一般の補題 -/

/-- 複体のホモロジーの長さは項の長さ以下（ホモロジーは項の部分商）。 -/
lemma len_homology_le_X (X : CochainComplex (ModuleCat.{u} S) ℤ) (m : ℤ)
    (hX : IsPowTorsion J (X.X m)) : μ.len (X.homology m) ≤ μ.len (X.X m) := by
  have hc : IsPowTorsion J (X.cycles m) :=
    IsPowTorsion.of_injective (X.iCycles m).hom
      ((ModuleCat.mono_iff_injective _).mp inferInstance) hX
  exact (μ.len_le_of_surjective (X.homologyπ m).hom
    ((ModuleCat.epi_iff_surjective _).mp inferInstance) hc).trans
    (μ.len_le_of_injective (X.iCycles m).hom
      ((ModuleCat.mono_iff_injective _).mp inferInstance) hX)

/-- `J` 冪ねじれ加群とのテンソル積は `J` 冪ねじれ。 -/
lemma isPowTorsion_tensor (K N : Type u) [AddCommGroup K] [Module S K] [AddCommGroup N]
    [Module S N] (hK : IsPowTorsion J K) : IsPowTorsion J (TensorProduct S K N) := by
  obtain ⟨n, hn⟩ := hK
  refine ⟨n, fun z a ↦ ?_⟩
  induction z using TensorProduct.induction_on with
  | zero => exact smul_zero _
  | tmul k l => rw [TensorProduct.smul_tmul', hn, TensorProduct.zero_tmul]
  | add x y hx hy => rw [smul_add, hx, hy, add_zero]

/-- 直積の長さは和。 -/
lemma len_prod (X Y : Type u) [AddCommGroup X] [Module S X] [AddCommGroup Y] [Module S Y]
    (hX : IsPowTorsion J X) (hY : IsPowTorsion J Y) :
    μ.len (X × Y) = μ.len X + μ.len Y := by
  refine μ.len_add_of_exact X (X × Y) Y (LinearMap.inl S X Y) (LinearMap.snd S X Y)
    LinearMap.inl_injective LinearMap.snd_surjective ?_ ?_
  · exact LinearMap.exact_iff.mpr (by rw [LinearMap.ker_snd, LinearMap.range_inl])
  · obtain ⟨a, ha⟩ := hX
    obtain ⟨b, hb⟩ := hY
    refine ⟨a + b, fun z c ↦ ?_⟩
    have hca : (c : S) ∈ J ^ a := Ideal.pow_le_pow_right (by omega) c.2
    have hcb : (c : S) ∈ J ^ b := Ideal.pow_le_pow_right (by omega) c.2
    exact Prod.ext (ha (a := ⟨c, hca⟩)) (hb (a := ⟨c, hcb⟩))

/-- `μ(K ⊗_S S^n) ≤ n · μ(K)`。 -/
lemma len_tensor_pi_le (K : Type u) [AddCommGroup K] [Module S K] (hK : IsPowTorsion J K) :
    ∀ n : ℕ, μ.len (TensorProduct S K (Fin n → S)) ≤ (n : ℝ≥0∞) * μ.len K
  | 0 => by
    have : Subsingleton (TensorProduct S K (Fin 0 → S)) := inferInstance
    rw [μ.len_eq_zero_of_subsingleton]
    exact zero_le
  | n + 1 => by
    let e : (Fin (n + 1) → S) ≃ₗ[S] S × (Fin n → S) := (Fin.consLinearEquiv S (fun _ ↦ S)).symm
    rw [μ.len_congr _ _ ((TensorProduct.congr (LinearEquiv.refl S K) e).trans
        (TensorProduct.prodRight S S K S (Fin n → S))),
      len_prod μ _ _ (isPowTorsion_tensor K S hK) (isPowTorsion_tensor K _ hK),
      μ.len_congr _ _ (TensorProduct.rid S K), Nat.cast_succ, add_mul, one_mul, add_comm]
    exact add_le_add (len_tensor_pi_le K hK n) le_rfl

/-- 有限自由 `S` 加群 `F` とのテンソル：`μ(K ⊗_S F) ≤ rank F · μ(K)`。 -/
lemma len_tensor_free_le (K : Type u) [AddCommGroup K] [Module S K] (hK : IsPowTorsion J K)
    (F : Type u) [AddCommGroup F] [Module S F] [Module.Free S F] [Module.Finite S F]
    [Nontrivial S] :
    μ.len (TensorProduct S K F) ≤ (Module.finrank S F : ℝ≥0∞) * μ.len K := by
  rw [μ.len_congr _ _ (TensorProduct.congr (LinearEquiv.refl S K)
    (Module.finBasis S F).equivFun)]
  exact len_tensor_pi_le μ K hK _

/-- 項が `J` 冪ねじれの複体のホモロジーは `J` 冪ねじれ。 -/
lemma isPowTorsion_homology_of_X (X : CochainComplex (ModuleCat.{u} S) ℤ) (m : ℤ)
    (hX : IsPowTorsion J (X.X m)) : IsPowTorsion J (X.homology m) :=
  IsPowTorsion.of_surjective (X.homologyπ m).hom
    ((ModuleCat.epi_iff_surjective _).mp inferInstance)
    (IsPowTorsion.of_injective (X.iCycles m).hom
      ((ModuleCat.mono_iff_injective _).mp inferInstance) hX)

/-! ## `M ⊗_B G` -/

variable {B : Type u} [CommRing B] (ψ : B →+* S) (G : CochainComplex (ModuleCat.{u} B) ℤ)

/-- `S ⊗_B G`（`S` 加群の複体、`ψ : B → S`）。 -/
noncomputable abbrev GS : CochainComplex (ModuleCat.{u} S) ℤ := baseChange ψ G

/-- `M ⊗_B G = M ⊗_S (S ⊗_B G)`（`S` 加群の複体）。 -/
noncomputable abbrev tensorRes (M : ModuleCat.{u} S) : CochainComplex (ModuleCat.{u} S) ℤ :=
  (tensorComplexFunctor (GS ψ G)).obj M

/-- `G` の `m` 次の項の階数（`S` 上）。 -/
noncomputable abbrev rk (m : ℤ) : ℕ := Module.finrank S ((GS ψ G).X m)

variable (hfree : ∀ i, Module.Free B (G.X i)) (hfin : ∀ i, Module.Finite B (G.X i))

include hfree in
/-- `M ↦ M ⊗_B G` は短完全列を保つ（項が平坦）。 -/
lemma tensorRes_shortExact (Sc : ShortComplex (ModuleCat.{u} S)) (hs : Sc.ShortExact) :
    (Sc.map (tensorComplexFunctor (GS ψ G))).ShortExact :=
  tensorComplex_shortExact _ (fun i ↦ by
    have := hfree i
    have : Module.Free S ((GS ψ G).X i) := free_baseChange ψ (G.X i)
    exact Module.Flat.of_free) Sc hs

/-- `M` が `J` 冪ねじれなら `M ⊗_B G` のホモロジーも。 -/
lemma isPowTorsion_tensorRes (M : ModuleCat.{u} S) (hM : IsPowTorsion J M) (m : ℤ) :
    IsPowTorsion J ((tensorRes ψ G M).homology m) :=
  isPowTorsion_homology_of_X _ m (isPowTorsion_tensor M _ hM)

include hfree hfin in
/-- `μ(H^m(K ⊗_B G)) ≤ r_m · μ(K)`。 -/
lemma len_homology_tensorRes_le (K : ModuleCat.{u} S) (hK : IsPowTorsion J K)
    (m : ℤ) : μ.len ((tensorRes ψ G K).homology m) ≤ (rk ψ G m : ℝ≥0∞) * μ.len K := by
  rcases subsingleton_or_nontrivial S with hS | hS
  · have : Subsingleton ((tensorRes ψ G K).homology m) := Module.subsingleton S _
    rw [μ.len_eq_zero_of_subsingleton]
    exact zero_le
  have := hfree m
  have := hfin m
  have : Module.Free S ((GS ψ G).X m) := free_baseChange ψ (G.X m)
  have : Module.Finite S ((GS ψ G).X m) := finite_baseChange ψ (G.X m)
  exact (len_homology_le_X μ _ m (isPowTorsion_tensor K _ hK)).trans
    (len_tensor_free_le μ K hK _)

include hfree in
/-- **評価 (5.12) の形**：`S` 線形写像 `f : P → U`（`P`、`U` は `J` 冪ねじれ）の核 `K`、余核 `W` について
`μ(H^m(P ⊗ G)) ≤ μ(H^m(U ⊗ G)) + μ(H^m(K ⊗ G)) + μ(H^{m−1}(W ⊗ G))` と
`μ(H^m(U ⊗ G)) ≤ μ(H^m(P ⊗ G)) + μ(H^{m+1}(K ⊗ G)) + μ(H^m(W ⊗ G))`。
`P ↠ im f ↪ U` の二つの短完全列のホモロジー長完全列による。 -/
theorem len_tensorRes_le_of_hom {P U : ModuleCat.{u} S} (f : P ⟶ U) (hP : IsPowTorsion J P)
    (hU : IsPowTorsion J U) (m : ℤ) :
    μ.len ((tensorRes ψ G P).homology m) ≤ μ.len ((tensorRes ψ G U).homology m) +
        μ.len ((tensorRes ψ G (ModuleCat.of S (LinearMap.ker f.hom))).homology m) +
        μ.len ((tensorRes ψ G (ModuleCat.of S (U ⧸ LinearMap.range f.hom))).homology (m - 1)) ∧
      μ.len ((tensorRes ψ G U).homology m) ≤ μ.len ((tensorRes ψ G P).homology m) +
        μ.len ((tensorRes ψ G (ModuleCat.of S (LinearMap.ker f.hom))).homology (m + 1)) +
        μ.len ((tensorRes ψ G (ModuleCat.of S (U ⧸ LinearMap.range f.hom))).homology m) := by
  let K := LinearMap.ker f.hom
  let I := LinearMap.range f.hom
  have hK : IsPowTorsion J K := IsPowTorsion.of_injective K.subtype K.injective_subtype hP
  have hI : IsPowTorsion J I := IsPowTorsion.of_injective I.subtype I.injective_subtype hU
  have hW : IsPowTorsion J (U ⧸ I) := hU.quotient I
  -- 二つの短完全列
  let S₁ := ModuleCat.shortComplexOfCompEqZero K.subtype f.hom.rangeRestrict
    (by ext x; exact LinearMap.mem_ker.mp x.2)
  have hS₁ : S₁.ShortExact := ModuleCat.shortComplex_shortExact S₁
    (show Function.Exact K.subtype f.hom.rangeRestrict from
      LinearMap.exact_iff.mpr (by rw [LinearMap.ker_rangeRestrict, Submodule.range_subtype]))
    K.injective_subtype f.hom.surjective_rangeRestrict
  let S₂ := ModuleCat.shortComplexOfCompEqZero I.subtype I.mkQ
    (by ext x; exact (Submodule.Quotient.mk_eq_zero _).mpr x.2)
  have hS₂ : S₂.ShortExact := ModuleCat.shortComplex_shortExact S₂
    (LinearMap.exact_subtype_mkQ I) I.injective_subtype I.mkQ_surjective
  have hT₁ := tensorRes_shortExact ψ G hfree S₁ hS₁
  have hT₂ := tensorRes_shortExact ψ G hfree S₂ hS₂
  have t := fun (M : ModuleCat.{u} S) (hM : IsPowTorsion J M) (k : ℤ) ↦
    isPowTorsion_tensorRes (J := J) ψ G M hM k
  -- 長完全列からの不等式
  let hP' := fun k ↦ μ.len ((tensorRes ψ G P).homology k)
  let hU' := fun k ↦ μ.len ((tensorRes ψ G U).homology k)
  let hK' := fun k ↦ μ.len ((tensorRes ψ G (ModuleCat.of S K)).homology k)
  let hI' := fun k ↦ μ.len ((tensorRes ψ G (ModuleCat.of S I)).homology k)
  let hW' := fun k ↦ μ.len ((tensorRes ψ G (ModuleCat.of S (U ⧸ I))).homology k)
  have e₁ : hP' m ≤ hK' m + hI' m := μ.len_le_add_of_exact _ _
    (LinearMap.exact_iff.mpr (hT₁.homology_exact₂ m).moduleCat_range_eq_ker.symm)
    (t (ModuleCat.of S K) hK m) (t P hP m) (t (ModuleCat.of S I) hI m)
  have e₂ : hI' m ≤ hP' m + hK' (m + 1) := μ.len_le_add_of_exact _ _
    (LinearMap.exact_iff.mpr (hT₁.homology_exact₃ m (m + 1) rfl).moduleCat_range_eq_ker.symm)
    (t P hP m) (t (ModuleCat.of S I) hI m) (t (ModuleCat.of S K) hK (m + 1))
  have e₃ : hU' m ≤ hI' m + hW' m := μ.len_le_add_of_exact _ _
    (LinearMap.exact_iff.mpr (hT₂.homology_exact₂ m).moduleCat_range_eq_ker.symm)
    (t (ModuleCat.of S I) hI m) (t U hU m) (t (ModuleCat.of S (U ⧸ I)) hW m)
  have e₄ : hI' m ≤ hW' (m - 1) + hU' m := μ.len_le_add_of_exact _ _
    (LinearMap.exact_iff.mpr (hT₂.homology_exact₁ (m - 1) m
      (show (ComplexShape.up ℤ).Rel (m - 1) m by simp)).moduleCat_range_eq_ker.symm)
    (t (ModuleCat.of S (U ⧸ I)) hW (m - 1)) (t (ModuleCat.of S I) hI m) (t U hU m)
  constructor
  · calc hP' m ≤ hK' m + hI' m := e₁
      _ ≤ hK' m + (hW' (m - 1) + hU' m) := add_le_add le_rfl e₄
      _ = hU' m + hK' m + hW' (m - 1) := by ring
  · calc hU' m ≤ hI' m + hW' m := e₃
      _ ≤ hP' m + hK' (m + 1) + hW' m := add_le_add e₂ le_rfl

/-! ## `B` に制限した `M ⊗_B G` -/

section restrict

variable {S : Type u} [CommRing S] {B : Type u} [CommRing B] (ψ : B →+* S)

/-- 項ごとの同型 `V ⊗_S (S ⊗_B N) ≅ V ⊗_B N`（`B` 線形、Mathlib の `cancelBaseChange`）。 -/
noncomputable def restrictTensorXIso (V : ModuleCat.{u} S) (N : ModuleCat.{u} B) :
    (ModuleCat.restrictScalars ψ).obj (MonoidalCategoryStruct.tensorObj V
      ((ModuleCat.extendScalars ψ).obj N)) ≅
      MonoidalCategoryStruct.tensorObj ((ModuleCat.restrictScalars ψ).obj V) N :=
  letI := ψ.toAlgebra
  letI : Module B V := Module.compHom V ψ
  haveI : IsScalarTower B S V := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  LinearEquiv.toModuleIso
    ((TensorProduct.AlgebraTensorModule.cancelBaseChange B S S V N).restrictScalars B)

/-- `B` に制限した `M ⊗_S (S ⊗_B G)` は `M ⊗_B G`（複体の同型）。 -/
noncomputable def restrictTensorResIso (G : CochainComplex (ModuleCat.{u} B) ℤ)
    (V : ModuleCat.{u} S) :
    ((ModuleCat.restrictScalars ψ).mapHomologicalComplex _).obj (tensorRes ψ G V) ≅
      (((tensoringLeft (ModuleCat.{u} B)).obj
        ((ModuleCat.restrictScalars ψ).obj V)).mapHomologicalComplex _).obj G :=
  HomologicalComplex.Hom.isoOfComponents (fun m ↦ restrictTensorXIso ψ V (G.X m))
    (fun m m' _ ↦ by
      ext x
      induction x using TensorProduct.inductionOn with
      | tmul v y =>
        induction y using TensorProduct.inductionOn with
        | tmul s n => rfl
        | add y z hy hz => erw [TensorProduct.tmul_add, map_add, map_add, hy, hz]
      | add x y hx hy => erw [map_add, map_add, hx, hy])

/-- **通常の `Tor^B` との一致**：`G` が `L` の射影分解なら、`S` 加群 `V` を `B` 加群とみた
`Tor_i^B(V, L)` は `B` に制限した `H^{-i}(V ⊗_S (S ⊗_B G))` と線形同値。 -/
noncomputable def torModuleRestrictEquiv (G : CochainComplex (ModuleCat.{u} B) ℤ)
    (L : Type u) [AddCommGroup L] [Module B L] (hG : IsResolutionOf G (ModuleCat.of B L))
    (V : ModuleCat.{u} S) (i : ℕ) :
    TorModule B i ((ModuleCat.restrictScalars ψ).obj V) L ≃ₗ[B]
      (ModuleCat.restrictScalars ψ).obj ((tensorRes ψ G V).homology (-(i : ℤ))) :=
  (torModuleIsoCochain ((ModuleCat.restrictScalars ψ).obj V) hG i ≪≫
    (HomologicalComplex.homologyFunctor _ _ (-(i : ℤ))).mapIso
      (restrictTensorResIso ψ G V).symm ≪≫
    ((tensorRes ψ G V).sc (-(i : ℤ))).mapHomologyIso (ModuleCat.restrictScalars ψ)).toLinearEquiv

end restrict


end TensorRes

end SerrePositivity
