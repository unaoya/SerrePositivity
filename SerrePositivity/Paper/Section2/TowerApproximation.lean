module

public import SerrePositivity.Paper.Section2.TowerDescent
public import SerrePositivity.PerfectComplex.TensorResolutionLength
public import SerrePositivity.PerfectComplex.NormalizedLengthComap
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import Mathlib.Algebra.Category.ModuleCat.Descent

/-!
# 塔の加群の有限段による近似（論文 Lemma 5.4 の一般的な部分）

## 概要

`A` 上有限な代数 `T` について `S = Λ ⊗_A T`、`S_j = A_j ⊗_A T` とおく（`TS`、`TSj`）。`S` 加群 `U` で
`λ_∞(U) < ∞` のものを、段 `S_j` 上の有限長加群 `V` の係数拡大 `S ⊗_{S_j} V` で近似する。

## 内容

- 段の写像 `S_j → S` と遷移写像、`S` の元はある段から来ること、有限表示な `S` 加群の段への降下
  （`exists_descentT`）。
- `S ⊗_{S_j} V ≃ Λ ⊗_{A_j} V`（`Λ` 線形、`baseChangeTowerEquiv`）と有限段の公式
  `λ_∞(S ⊗_{S_j} V) = ℓ_B(V) / p^{jh}`（`towerLengthFun_baseChangeT`）。長さは剰余体が共通なので
  `A_j`、`A`、`T`、`B` で同じ（`length_TSj_eq`）。
- `S` は `S_j` 上平坦（`flat_TS`）。`(S ⊗_{S_j} V) ⊗_B G ≅ S ⊗_{S_j} (V ⊗_B G)`
  （`tensorResBaseChangeIso`、係数拡大関手のモノイダル構造）とホモロジーとの交換から、有限段の
  `Tor` の公式（`towerLengthFun_homology_tensorRes`）。
- 近似：上限の性質 (2.3) による有限生成部分加群での近似（`exists_fg_quotient_le`）と、有限表示な
  `S` 加群 `P → U` で核・余核の長さを `ε` 以下にする近似（`exists_finitePresentation_approx`）。
- 組み立て：一段（`exists_stage_step`、評価 (5.12) は `PerfectComplex/TensorResolutionLength.lean`）と
  `ε_n = 1/(n+1)` による収束（`exists_tower_approximation`）。

## 仮定

`A` は Noether 局所環、`t_i ∈ m_A`、`p` は素数、`T` は `A` 上有限な局所環で `m_A^a T = 0`、
`A → T`、`B → T` は剰余体で全射。`λ_∞` の加法性と `λ = λ*` は引用（`TowerLength.lean` の (C1)、(C2)）。
-/

@[expose] public section

universe u

open IsLocalRing TensorProduct
open scoped ENNReal

namespace SerrePositivity

namespace Section2

variable (A : Type u) [CommRing A] {h : ℕ} (t : Fin h → A) (p : ℕ) (T : Type u) [CommRing T]
  [Algebra A T]

/-- `S = Λ ⊗_A T`。 -/
abbrev TS : Type u := Tower A t p ⊗[A] T

/-- `S_j = A_j ⊗_A T`。 -/
abbrev TSj (j : ℕ) : Type u := TowerStage A t p j ⊗[A] T

/-- 探索を短くするための直接のインスタンス。 -/
noncomputable instance (j : ℕ) : CommRing (TowerStage A t p j) := inferInstance

noncomputable instance (j : ℕ) : CommRing (TSj A t p T j) := Algebra.TensorProduct.instCommRing

noncomputable instance : CommRing (TS A t p T) := Algebra.TensorProduct.instCommRing

/-- `S_j → S`。 -/
noncomputable def stageMapT (j : ℕ) : TSj A t p T j →ₐ[A] TS A t p T :=
  Algebra.TensorProduct.map (IsScalarTower.toAlgHom A (TowerStage A t p j) (Tower A t p))
    (AlgHom.id A T)

noncomputable instance (j : ℕ) : Algebra (TSj A t p T j) (TS A t p T) :=
  (stageMapT A t p T j).toRingHom.toAlgebra

lemma stageMapT_tmul (j : ℕ) (a : TowerStage A t p j) (τ : T) :
    stageMapT A t p T j (a ⊗ₜ τ) = towerOf A t p j a ⊗ₜ τ := rfl

/-- 遷移写像 `S_i → S_j`（`i ≤ j`）。 -/
noncomputable def transMapT (i j : ℕ) (hij : i ≤ j) : TSj A t p T i →ₐ[A] TSj A t p T j :=
  Algebra.TensorProduct.map (towerMap A t p i j hij) (AlgHom.id A T)

lemma stageMapT_transMapT (i j : ℕ) (hij : i ≤ j) (y : TSj A t p T i) :
    stageMapT A t p T j (transMapT A t p T i j hij y) = stageMapT A t p T i y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a τ =>
    simp only [transMapT, Algebra.TensorProduct.map_tmul, AlgHom.coe_id, id_eq, stageMapT_tmul,
      towerOf_towerMap]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]

/-- `S` の元はある段から来る。 -/
lemma exists_stageMapT (s : TS A t p T) :
    ∃ (j : ℕ) (y : TSj A t p T j), stageMapT A t p T j y = s := by
  induction s using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, map_zero _⟩
  | tmul l τ =>
    obtain ⟨j, a, rfl⟩ := exists_towerOf A t p l
    exact ⟨j, a ⊗ₜ τ, rfl⟩
  | add x y hx hy =>
    obtain ⟨i, x', rfl⟩ := hx
    obtain ⟨j, y', rfl⟩ := hy
    refine ⟨i ⊔ j, transMapT A t p T i _ le_sup_left x' + transMapT A t p T j _ le_sup_right y', ?_⟩
    rw [map_add, stageMapT_transMapT, stageMapT_transMapT]

/-- `S` の有限個の元は共通の段から来る。 -/
lemma exists_stageMapT_family {ι : Type*} [Finite ι] (w : ι → TS A t p T) (n : ℕ) :
    ∃ (j : ℕ) (_ : n ≤ j) (z : ι → TSj A t p T j), ∀ i, stageMapT A t p T j (z i) = w i := by
  cases nonempty_fintype ι
  choose js zs hzs using fun i ↦ exists_stageMapT A t p T (w i)
  refine ⟨n ⊔ Finset.univ.sup js, le_sup_left, fun i ↦
    transMapT A t p T (js i) _ (le_sup_of_le_right (Finset.le_sup (Finset.mem_univ i))) (zs i),
    fun i ↦ ?_⟩
  rw [stageMapT_transMapT, hzs]

/-- **有限表示な `S` 加群の降下**：`n` 以上のある段 `j` と有限生成 `S_j` 加群 `V` で
`P ≃ S ⊗_{S_j} V`。関係式の成分を段に持ち上げ、`baseChangeQuotEquiv` を使う。 -/
theorem exists_descentT (P : Type u) [AddCommGroup P] [Module (TS A t p T) P]
    [Module.FinitePresentation (TS A t p T) P] (n : ℕ) :
    ∃ (j : ℕ) (_ : n ≤ j) (V : Type u) (_ : AddCommGroup V) (_ : Module (TSj A t p T j) V),
      Module.Finite (TSj A t p T j) V ∧
        Nonempty (P ≃ₗ[TS A t p T] TS A t p T ⊗[TSj A t p T j] V) := by
  classical
  obtain ⟨l, K, e, hK⟩ := Module.FinitePresentation.exists_fin (TS A t p T) P
  obtain ⟨b, k, hk⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hK
  obtain ⟨j, hnj, z, hz⟩ :=
    exists_stageMapT_family A t p T (fun ai : Fin b × Fin l ↦ k ai.1 ai.2) n
  let c : Fin b → (Fin l → TSj A t p T j) := fun a i ↦ z (a, i)
  have hc : piAlgebraMap (TSj A t p T j) (TS A t p T) (Fin l) ∘ c = k :=
    funext fun a ↦ funext fun i ↦ hz (a, i)
  refine ⟨j, hnj, (Fin l → TSj A t p T j) ⧸ Submodule.span (TSj A t p T j) (Set.range c),
    inferInstance,
    inferInstance, inferInstance, ⟨?_⟩⟩
  have hK' : K = Submodule.span (TS A t p T)
      (Set.range (piAlgebraMap (TSj A t p T j) (TS A t p T) (Fin l) ∘ c)) := by
    rw [hc, hk]
  exact e.trans ((Submodule.quotEquivOfEq _ _ hK').trans
    (baseChangeQuotEquiv (TS A t p T) c).symm)

/-! ## `S ⊗_{S_j} V ≃ Λ ⊗_{A_j} V` -/

section iso

variable (j : ℕ) (V : Type u) [AddCommGroup V] [Module (TSj A t p T j) V]
  [Module (TowerStage A t p j) V] [IsScalarTower (TowerStage A t p j) (TSj A t p T j) V]

/-- `T → S_j`。 -/
noncomputable abbrev ιT : T →ₐ[A] TSj A t p T j := Algebra.TensorProduct.includeRight

/-- `(λ, τ, v) ↦ λ ⊗ τ v`。 -/
noncomputable def fwdAux : Tower A t p →+ T →+ V →+ Tower A t p ⊗[TowerStage A t p j] V where
  toFun l :=
    { toFun := fun τ ↦
        { toFun := fun v ↦ l ⊗ₜ (ιT A t p T j τ • v)
          map_zero' := by rw [smul_zero, tmul_zero]
          map_add' := fun v w ↦ by rw [smul_add, tmul_add] }
      map_zero' := by
        ext v
        change l ⊗ₜ (ιT A t p T j 0 • v) = 0
        rw [map_zero, zero_smul, tmul_zero]
      map_add' := fun τ τ' ↦ by
        ext v
        change l ⊗ₜ (ιT A t p T j (τ + τ') • v) =
          l ⊗ₜ (ιT A t p T j τ • v) + l ⊗ₜ (ιT A t p T j τ' • v)
        rw [map_add, add_smul, tmul_add] }
  map_zero' := by
    ext τ v
    change (0 : Tower A t p) ⊗ₜ (ιT A t p T j τ • v) = 0
    rw [zero_tmul]
  map_add' := fun l l' ↦ by
    ext τ v
    change (l + l') ⊗ₜ (ιT A t p T j τ • v) =
      l ⊗ₜ (ιT A t p T j τ • v) + l' ⊗ₜ (ιT A t p T j τ • v)
    rw [add_tmul]

omit [IsScalarTower (TowerStage A t p j) (TSj A t p T j) V] in
lemma fwdAux_apply (l : Tower A t p) (τ : T) (v : V) :
    fwdAux A t p T j V l τ v = l ⊗ₜ (ιT A t p T j τ • v) := rfl

/-- `S → (V → Λ ⊗_{A_j} V)`、`λ ⊗ τ ↦ (v ↦ λ ⊗ τ v)`。 -/
noncomputable def fwdS : TS A t p T →+ V →+ Tower A t p ⊗[TowerStage A t p j] V :=
  TensorProduct.liftAddHom (fwdAux A t p T j V) (by
    intro a l τ
    ext v
    have hs : a • ιT A t p T j τ = algebraMap (TowerStage A t p j) (TSj A t p T j)
        (algebraMap A (TowerStage A t p j) a) * ιT A t p T j τ := by
      rw [Algebra.smul_def, IsScalarTower.algebraMap_apply A (TowerStage A t p j)]
    rw [fwdAux_apply, fwdAux_apply, map_smul, hs, mul_smul,
      algebraMap_smul (TSj A t p T j) (algebraMap A (TowerStage A t p j) a)
        (ιT A t p T j τ • v),
      ← TensorProduct.smul_tmul (algebraMap A (TowerStage A t p j) a) l,
      algebraMap_smul (TowerStage A t p j) a l])

lemma fwdS_tmul (l : Tower A t p) (τ : T) (v : V) :
    fwdS A t p T j V (l ⊗ₜ τ) v = l ⊗ₜ (ιT A t p T j τ • v) := rfl

lemma smul_TS_tmul (a : TowerStage A t p j) (τ' : T) (l : Tower A t p) (τ : T) :
    ((a ⊗ₜ[A] τ' : TSj A t p T j) • (l ⊗ₜ[A] τ : TS A t p T)) =
      (towerOf A t p j a * l) ⊗ₜ[A] (τ' * τ) := by
  rw [Algebra.smul_def]
  exact Algebra.TensorProduct.tmul_mul_tmul _ _ _ _

/-- バランス条件：`fwdS (y s) v = fwdS s (y v)`（`y ∈ S_j`）。 -/
lemma fwdS_smul (y : TSj A t p T j) (s : TS A t p T) (v : V) :
    fwdS A t p T j V (y • s) v = fwdS A t p T j V s (y • v) := by
  induction y using TensorProduct.induction_on generalizing s v with
  | zero => rw [zero_smul, zero_smul, map_zero, map_zero, AddMonoidHom.zero_apply]
  | tmul a τ' =>
    induction s using TensorProduct.induction_on generalizing v with
    | zero => rw [smul_zero, map_zero]; rfl
    | tmul l τ =>
      rw [smul_TS_tmul, fwdS_tmul, fwdS_tmul, ← mul_smul]
      have hy : ιT A t p T j τ * (a ⊗ₜ[A] τ') =
          algebraMap (TowerStage A t p j) (TSj A t p T j) a * ιT A t p T j (τ' * τ) := by
        change (1 ⊗ₜ[A] τ) * (a ⊗ₜ[A] τ') = (a ⊗ₜ[A] 1) * (1 ⊗ₜ[A] (τ' * τ))
        rw [Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
          mul_one, one_mul, mul_comm τ τ']
      rw [hy, mul_smul, algebraMap_smul (TSj A t p T j) a (ιT A t p T j (τ' * τ) • v),
        ← TensorProduct.smul_tmul a l (ιT A t p T j (τ' * τ) • v), Algebra.smul_def]
      rfl
    | add x z hx hz => rw [smul_add, map_add, map_add, AddMonoidHom.add_apply,
        AddMonoidHom.add_apply, hx, hz]
  | add x z hx hz => rw [add_smul, add_smul, map_add, AddMonoidHom.add_apply, hx, hz, map_add]

/-- `S ⊗_{S_j} V → Λ ⊗_{A_j} V`。 -/
noncomputable def fwdT : TS A t p T ⊗[TSj A t p T j] V →+ Tower A t p ⊗[TowerStage A t p j] V :=
  TensorProduct.liftAddHom (fwdS A t p T j V) (fun y s v ↦ fwdS_smul A t p T j V y s v)

lemma fwdT_tmul (s : TS A t p T) (v : V) : fwdT A t p T j V (s ⊗ₜ v) = fwdS A t p T j V s v :=
  rfl

/-- `Λ → (V → S ⊗_{S_j} V)`、`λ ↦ (v ↦ (λ ⊗ 1) ⊗ v)`。 -/
noncomputable def bwdAux : Tower A t p →+ V →+ TS A t p T ⊗[TSj A t p T j] V where
  toFun l := (TensorProduct.mk (TSj A t p T j) (TS A t p T) V (l ⊗ₜ[A] (1 : T))).toAddMonoidHom
  map_zero' := by ext v; simp
  map_add' l l' := by ext v; simp [add_tmul]

omit [Module (TowerStage A t p j) V]
  [IsScalarTower (TowerStage A t p j) (TSj A t p T j) V] in
lemma bwdAux_apply (l : Tower A t p) (v : V) :
    bwdAux A t p T j V l v = (l ⊗ₜ[A] (1 : T) : TS A t p T) ⊗ₜ v := rfl

/-- `Λ ⊗_{A_j} V → S ⊗_{S_j} V`。 -/
noncomputable def bwdT : Tower A t p ⊗[TowerStage A t p j] V →+ TS A t p T ⊗[TSj A t p T j] V :=
  TensorProduct.liftAddHom (bwdAux A t p T j V) (by
    intro a l v
    rw [bwdAux_apply, bwdAux_apply,
      ← algebraMap_smul (TSj A t p T j) a v,
      ← TensorProduct.smul_tmul (algebraMap (TowerStage A t p j) (TSj A t p T j) a)
        (l ⊗ₜ[A] (1 : T) : TS A t p T) v]
    change _ = ((a ⊗ₜ[A] (1 : T) : TSj A t p T j) • (l ⊗ₜ[A] (1 : T) : TS A t p T)) ⊗ₜ v
    rw [smul_TS_tmul, mul_one]
    rfl)

lemma bwdT_tmul (l : Tower A t p) (v : V) :
    bwdT A t p T j V (l ⊗ₜ v) = (l ⊗ₜ[A] (1 : T) : TS A t p T) ⊗ₜ v := rfl

lemma bwdT_fwdT (w : TS A t p T ⊗[TSj A t p T j] V) :
    bwdT A t p T j V (fwdT A t p T j V w) = w := by
  induction w using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul s v =>
    induction s using TensorProduct.induction_on with
    | zero => rw [zero_tmul, map_zero, map_zero]
    | tmul l τ =>
      rw [fwdT_tmul, fwdS_tmul, bwdT_tmul,
        ← TensorProduct.smul_tmul (ιT A t p T j τ) (l ⊗ₜ[A] (1 : T) : TS A t p T) v]
      congr 1
      change ((1 : TowerStage A t p j) ⊗ₜ[A] τ : TSj A t p T j) • (l ⊗ₜ[A] (1 : T)) = _
      rw [smul_TS_tmul, map_one, one_mul, mul_one]
    | add x z hx hz => rw [add_tmul, map_add, map_add, hx, hz]
  | add x z hx hz => rw [map_add, map_add, hx, hz]

lemma fwdT_bwdT (y : Tower A t p ⊗[TowerStage A t p j] V) :
    fwdT A t p T j V (bwdT A t p T j V y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul l v => rw [bwdT_tmul, fwdT_tmul, fwdS_tmul, map_one, one_smul]
  | add x z hx hz => rw [map_add, map_add, hx, hz]

lemma fwdT_smul (μ : Tower A t p) (w : TS A t p T ⊗[TSj A t p T j] V) :
    fwdT A t p T j V (μ • w) = μ • fwdT A t p T j V w := by
  induction w using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | tmul s v =>
    induction s using TensorProduct.induction_on with
    | zero => rw [zero_tmul, smul_zero, map_zero, smul_zero]
    | tmul l τ =>
      rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul', fwdT_tmul, fwdT_tmul,
        fwdS_tmul, fwdS_tmul, TensorProduct.smul_tmul']
    | add x z hx hz => rw [add_tmul, smul_add, map_add, map_add, hx, hz, smul_add]
  | add x z hx hz => rw [smul_add, map_add, map_add, hx, hz, smul_add]

/-- **`S ⊗_{S_j} V ≃ Λ ⊗_{A_j} V`**（`Λ` 線形）。 -/
noncomputable def baseChangeTowerEquiv :
    TS A t p T ⊗[TSj A t p T j] V ≃ₗ[Tower A t p] Tower A t p ⊗[TowerStage A t p j] V where
  toFun := fwdT A t p T j V
  invFun := bwdT A t p T j V
  map_add' := map_add _
  map_smul' := fwdT_smul A t p T j V
  left_inv := bwdT_fwdT A t p T j V
  right_inv := fwdT_bwdT A t p T j V

end iso

/-! ## `λ_∞(S ⊗_{S_j} V) = ℓ_B(V) / p^{jh}` -/

section formula

variable [IsLocalRing A] [IsNoetherianRing A] [Fact p.Prime] (ht : ∀ i, t i ∈ maximalIdeal A)
  [IsLocalRing T] [Module.Finite A T] {a : ℕ}
  (hTa : ∀ x ∈ maximalIdeal A ^ a, algebraMap A T x = 0)
  (hresT : Function.Surjective ((residue T).comp (algebraMap A T)))
  (B : Type u) [CommRing B] [Algebra B T]
  (hresB : Function.Surjective ((residue T).comp (algebraMap B T)))

/-- `B → S_j`（`B → T → S_j`）。 -/
noncomputable abbrev φB (j : ℕ) : B →+* TSj A t p T j :=
  (ιT A t p T j).toRingHom.comp (algebraMap B T)

omit [IsLocalRing A] [IsNoetherianRing A] [Fact p.Prime] [IsLocalRing T] [Module.Finite A T] in
/-- `S_j` 加群 `V` に `A_j`、`A`、`T`、`B` の作用を `S_j` 経由で入れる（局所インスタンス用）。 -/
private lemma stage_scalar_towers (j : ℕ) (V : Type u) [AddCommGroup V] [Module (TSj A t p T j) V] :
    letI : Module (TowerStage A t p j) V :=
      Module.compHom V (algebraMap (TowerStage A t p j) (TSj A t p T j))
    letI : Module A V := Module.compHom V (algebraMap A (TSj A t p T j))
    letI : Module T V := Module.compHom V (ιT A t p T j).toRingHom
    letI : Module B V := Module.compHom V (φB A t p T B j)
    IsScalarTower A (TowerStage A t p j) V ∧ IsScalarTower A T V ∧ IsScalarTower B T V ∧
      IsScalarTower A (TSj A t p T j) V := by
  let : Module (TowerStage A t p j) V :=
    Module.compHom V (algebraMap (TowerStage A t p j) (TSj A t p T j))
  let : Module A V := Module.compHom V (algebraMap A (TSj A t p T j))
  let : Module T V := Module.compHom V (ιT A t p T j).toRingHom
  let : Module B V := Module.compHom V (φB A t p T B j)
  refine ⟨IsScalarTower.of_algebraMap_smul fun x v ↦ ?_,
    IsScalarTower.of_algebraMap_smul fun x v ↦ ?_,
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl,
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl⟩
  · change algebraMap (TowerStage A t p j) (TSj A t p T j) (algebraMap A _ x) • v =
      algebraMap A (TSj A t p T j) x • v
    rw [← IsScalarTower.algebraMap_apply]
  · change ιT A t p T j (algebraMap A T x) • v = algebraMap A (TSj A t p T j) x • v
    rw [AlgHom.commutes]

omit [IsLocalRing T] in
include hTa in
/-- 有限生成 `S_j` 加群は `A_j` 上有限長で、`m_A A_j` 冪ねじれ。 -/
lemma isFiniteLength_TSj (j : ℕ) (V : Type u) [AddCommGroup V] [Module (TSj A t p T j) V]
    [Module.Finite (TSj A t p T j) V] :
    letI : Module (TowerStage A t p j) V :=
      Module.compHom V (algebraMap (TowerStage A t p j) (TSj A t p T j))
    IsFiniteLength (TowerStage A t p j) V ∧
      IsPowTorsion ((maximalIdeal A).map (algebraMap A (TowerStage A t p j))) V := by
  let : Module (TowerStage A t p j) V :=
    Module.compHom V (algebraMap (TowerStage A t p j) (TSj A t p T j))
  let : Module A V := Module.compHom V (algebraMap A (TSj A t p T j))
  obtain ⟨hAAj, -, -, hATS⟩ := stage_scalar_towers A t p T (B := T) j V
  -- `m_A^a` は `V` を消す
  have hkill : ∀ y ∈ maximalIdeal A ^ a, ∀ v : V, y • v = 0 := by
    intro y hy v
    change algebraMap A (TSj A t p T j) y • v = 0
    rw [← AlgHom.commutes (ιT A t p T j) y, hTa y hy, map_zero, zero_smul]
  have : Module.Finite A (TowerStage A t p j) := towerStage_finite A t p j
  have : Module.Finite A V := Module.Finite.trans (TSj A t p T j) V
  have hArt : IsArtinianRing (A ⧸ maximalIdeal A) :=
    inferInstanceAs (IsArtinianRing (ResidueField A))
  have hflA : IsFiniteLength A V :=
    isFiniteLength_of_le_radical_annihilator (maximalIdeal A) V fun x hx ↦
      Ideal.mem_radical_iff.mpr ⟨a, Module.mem_annihilator.mpr (hkill _ (Ideal.pow_mem_pow hx a))⟩
  refine ⟨?_, ?_⟩
  · obtain ⟨hN, hA⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp hflA
    exact isFiniteLength_iff_isNoetherian_isArtinian.mpr
      ⟨isNoetherian_of_tower A hN, isArtinian_of_tower A hA⟩
  · have hle : (maximalIdeal A ^ a).map (algebraMap A (TowerStage A t p j)) ≤
        Module.annihilator (TowerStage A t p j) V := by
      rw [Ideal.map_le_iff_le_comap]
      intro y hy
      rw [Ideal.mem_comap, Module.mem_annihilator]
      intro v
      rw [algebraMap_smul]
      exact hkill y hy v
    refine ⟨a, fun v c ↦ ?_⟩
    have hc : (c : TowerStage A t p j) ∈ (maximalIdeal A ^ a).map (algebraMap A _) := by
      rw [Ideal.map_pow]; exact c.2
    exact Module.mem_annihilator.mp (hle hc) v

omit [IsNoetherianRing A] [Module.Finite A T] in
include ht hresT hresB in
/-- `S_j` 加群の長さは `A_j` 上と `B` 上で等しい（剰余体が共通）。 -/
lemma length_TSj_eq (j : ℕ) (V : Type u) [AddCommGroup V] [Module (TSj A t p T j) V] :
    letI : Module (TowerStage A t p j) V :=
      Module.compHom V (algebraMap (TowerStage A t p j) (TSj A t p T j))
    letI : Module B V := Module.compHom V (φB A t p T B j)
    Module.length (TowerStage A t p j) V = Module.length B V := by
  let : Module (TowerStage A t p j) V :=
    Module.compHom V (algebraMap (TowerStage A t p j) (TSj A t p T j))
  let : Module A V := Module.compHom V (algebraMap A (TSj A t p T j))
  let : Module T V := Module.compHom V (ιT A t p T j).toRingHom
  let : Module B V := Module.compHom V (φB A t p T B j)
  obtain ⟨hAAj, hAT, hBT, -⟩ := stage_scalar_towers A t p T (B := B) j V
  have : IsLocalRing (TowerStage A t p j) := isLocalRing_towerStage A t p ht j
  rw [← length_eq_of_common_residueField (residue_surjective_towerStage A t p ht j) V,
    length_eq_of_common_residueField hresT V, ← length_eq_of_common_residueField hresB V]

include ht hTa hresT hresB in
/-- 有限生成 `S_j` 加群の `B` 上の長さは有限。 -/
lemma length_TSj_ne_top (j : ℕ) (V : Type u) [AddCommGroup V] [Module (TSj A t p T j) V]
    [Module.Finite (TSj A t p T j) V] :
    letI : Module B V := Module.compHom V (φB A t p T B j)
    (Module.length B V : ℝ≥0∞) ≠ ⊤ := by
  let : Module (TowerStage A t p j) V :=
    Module.compHom V (algebraMap (TowerStage A t p j) (TSj A t p T j))
  let : Module B V := Module.compHom V (φB A t p T B j)
  obtain ⟨hV, -⟩ := isFiniteLength_TSj A t p T hTa j V
  rw [← length_TSj_eq A t p T ht hresT B hresB j V]
  exact ENat.toENNReal_ne_top.mpr (Module.length_ne_top_iff.mpr hV)

include ht hTa hresT hresB in
/-- **有限段の公式（`S` の形）**：有限生成 `S_j` 加群 `V` について
`λ_∞(S ⊗_{S_j} V) = ℓ_B(V) / p^{jh}`。`S ⊗_{S_j} V ≃ Λ ⊗_{A_j} V`（`baseChangeTowerEquiv`）と (2.2)、
長さは剰余体が共通なので `A_j`、`A`、`T`、`B` で同じ。 -/
theorem towerLengthFun_baseChangeT (j : ℕ) (V : Type u) [AddCommGroup V]
    [Module (TSj A t p T j) V] [Module.Finite (TSj A t p T j) V] :
    letI := Module.compHom V (φB A t p T B j)
    towerLengthFun A t p (TS A t p T ⊗[TSj A t p T j] V) =
      (Module.length B V : ℝ≥0∞) / (stageRank h p j : ℝ≥0∞) := by
  let _ : Module (TowerStage A t p j) V :=
    Module.compHom V (algebraMap (TowerStage A t p j) (TSj A t p T j))
  have : IsScalarTower (TowerStage A t p j) (TSj A t p T j) V :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  obtain ⟨hV, hVt⟩ := isFiniteLength_TSj A t p T hTa j V
  rw [towerLengthFun_congr (baseChangeTowerEquiv A t p T j V),
    towerLengthFun_tensor A t p ht j V hV hVt, length_TSj_eq A t p T ht hresT B hresB j V]

end formula

/-! ## `S` は `S_j` 上平坦 -/

section flat

variable (j : ℕ)

/-- `fwdT` は `S_j` 線形写像と可換。 -/
lemma fwdT_lTensor (V V' : Type u) [AddCommGroup V] [Module (TSj A t p T j) V]
    [Module (TowerStage A t p j) V] [IsScalarTower (TowerStage A t p j) (TSj A t p T j) V]
    [AddCommGroup V'] [Module (TSj A t p T j) V'] [Module (TowerStage A t p j) V']
    [IsScalarTower (TowerStage A t p j) (TSj A t p T j) V'] (f : V →ₗ[TSj A t p T j] V')
    (w : TS A t p T ⊗[TSj A t p T j] V) :
    fwdT A t p T j V' (f.lTensor (TS A t p T) w) =
      (f.restrictScalars (TowerStage A t p j)).lTensor (Tower A t p) (fwdT A t p T j V w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul s v =>
    induction s using TensorProduct.induction_on with
    | zero => simp only [zero_tmul, map_zero]
    | tmul l τ =>
      rw [LinearMap.lTensor_tmul, fwdT_tmul, fwdT_tmul, fwdS_tmul, fwdS_tmul,
        LinearMap.lTensor_tmul, LinearMap.restrictScalars_apply, map_smul]
    | add x z hx hz => simp only [add_tmul, map_add, hx, hz]
  | add x z hx hz => simp only [map_add, hx, hz]

variable [Fact p.Prime]

/-- **`S` は `S_j` 上平坦**：`S ⊗_{S_j} -` は `Λ ⊗_{A_j} -`（`Λ` は `A_j` 上平坦）と自然に同型。 -/
theorem flat_TS : Module.Flat (TSj A t p T j) (TS A t p T) := by
  rw [Module.Flat.iff_lTensor_preserves_injective_linearMap]
  intro N N' _ _ _ _ f hf
  let _ : Module (TowerStage A t p j) N :=
    Module.compHom N (algebraMap (TowerStage A t p j) (TSj A t p T j))
  have : IsScalarTower (TowerStage A t p j) (TSj A t p T j) N :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let _ : Module (TowerStage A t p j) N' :=
    Module.compHom N' (algebraMap (TowerStage A t p j) (TSj A t p T j))
  have : IsScalarTower (TowerStage A t p j) (TSj A t p T j) N' :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have := flat_tower A t p j
  have hΛ : Function.Injective
      ((f.restrictScalars (TowerStage A t p j)).lTensor (Tower A t p)) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ hf
  intro x y hxy
  apply (baseChangeTowerEquiv A t p T j N).injective
  apply hΛ
  change (f.restrictScalars _).lTensor _ (fwdT A t p T j N x) =
    (f.restrictScalars _).lTensor _ (fwdT A t p T j N y)
  rw [← fwdT_lTensor, ← fwdT_lTensor, hxy]

end flat

/-! ## `Tor` の計算と段からの係数拡大 -/

section torBaseChange

open CategoryTheory MonoidalCategory TensorRes

variable (j : ℕ) {B : Type u} [CommRing B] [Algebra B T]
  (G : CochainComplex (ModuleCat.{u} B) ℤ)

/-- `S_j → S`。 -/
noncomputable abbrev φS (j : ℕ) : TSj A t p T j →+* TS A t p T := algebraMap _ _

/-- 係数拡大 `S_j`-加群 → `S`-加群。 -/
noncomputable abbrev Fj (j : ℕ) : ModuleCat.{u} (TSj A t p T j) ⥤ ModuleCat.{u} (TS A t p T) :=
  ModuleCat.extendScalars (φS A t p T j)

/-- **`M ⊗_B G` と係数拡大**：`(S ⊗_{S_j} V) ⊗_B G ≅ S ⊗_{S_j} (V ⊗_B G)`（複体の同型）。 -/
noncomputable def tensorResBaseChangeIso (V : ModuleCat.{u} (TSj A t p T j)) :
    tensorRes ((φS A t p T j).comp (φB A t p T B j)) G ((Fj A t p T j).obj V) ≅
      ((Fj A t p T j).mapHomologicalComplex _).obj (tensorRes (φB A t p T B j) G V) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun m ↦ whiskerLeftIso ((Fj A t p T j).obj V)
        ((ModuleCat.extendScalarsComp (φB A t p T B j) (φS A t p T j)).app (G.X m)) ≪≫
      Functor.Monoidal.μIso (Fj A t p T j) V
        ((ModuleCat.extendScalars (φB A t p T B j)).obj (G.X m)))
    (fun m m' _ ↦ by
      change (_ ◁ _ ≫ _) ≫ (Fj A t p T j).map (V ◁ _) = (_ ◁ _) ≫ (_ ◁ _ ≫ _)
      simp only [Category.assoc, Functor.Monoidal.μIso_hom, ← Functor.LaxMonoidal.μ_natural_right,
        ← MonoidalCategory.whiskerLeft_comp_assoc]
      congr 2
      exact ((ModuleCat.extendScalarsComp (φB A t p T B j) (φS A t p T j)).hom.naturality
        (G.d m m')).symm)

variable [Fact p.Prime]

/-- 係数拡大 `S_j → S` はホモロジーと可換（`S` は `S_j` 上平坦）。 -/
noncomputable def homologyTensorResBaseChangeIso (V : ModuleCat.{u} (TSj A t p T j)) (m : ℤ) :
    (tensorRes ((φS A t p T j).comp (φB A t p T B j)) G ((Fj A t p T j).obj V)).homology m ≅
      (Fj A t p T j).obj ((tensorRes (φB A t p T B j) G V).homology m) := by
  have hflat : (φS A t p T j).Flat := flat_TS A t p T j
  have := ModuleCat.preservesFiniteLimits_extendScalars_of_flat hflat
  exact (HomologicalComplex.homologyFunctor _ _ m).mapIso
      (tensorResBaseChangeIso A t p T j G V) ≪≫
    ((tensorRes (φB A t p T B j) G V).sc m).mapHomologyIso (Fj A t p T j)

end torBaseChange

/-! ## 有限段の `Tor` の公式 -/

section torFormula

open CategoryTheory MonoidalCategory TensorRes

variable [IsLocalRing A] [IsNoetherianRing A] [Fact p.Prime] (ht : ∀ i, t i ∈ maximalIdeal A)
  [IsLocalRing T] [Module.Finite A T] {a : ℕ}
  (hTa : ∀ x ∈ maximalIdeal A ^ a, algebraMap A T x = 0)
  (hresT : Function.Surjective ((residue T).comp (algebraMap A T)))
  {B : Type u} [CommRing B] [Algebra B T]
  (hresB : Function.Surjective ((residue T).comp (algebraMap B T)))
  (G : CochainComplex (ModuleCat.{u} B) ℤ) (hfin : ∀ i, Module.Finite B (G.X i))

omit [IsLocalRing A] [IsNoetherianRing A] [Fact p.Prime] [IsLocalRing T] [Module.Finite A T] in
/-- `S ⊗_{S_j} W`（`ModuleCat` の係数拡大）と `TS ⊗[TSj] W` の `Λ` 上の同一視。 -/
lemma towerLengthFun_extendScalars_eq (j : ℕ) (W : ModuleCat.{u} (TSj A t p T j)) :
    letI := Module.compHom ((Fj A t p T j).obj W) (algebraMap (Tower A t p) (TS A t p T))
    towerLengthFun A t p ((Fj A t p T j).obj W) =
      towerLengthFun A t p (TS A t p T ⊗[TSj A t p T j] W) := by
  let _ := Module.compHom ((Fj A t p T j).obj W) (algebraMap (Tower A t p) (TS A t p T))
  let e : (TS A t p T ⊗[TSj A t p T j] W) ≃ₗ[Tower A t p] (Fj A t p T j).obj W :=
    { toFun := fun x ↦ x
      invFun := fun x ↦ x
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun c x ↦ by
        induction x using TensorProduct.induction_on with
        | zero =>
          rw [smul_zero]
          exact (smul_zero (A := (Fj A t p T j).obj W) c).symm
        | tmul s w =>
          rw [TensorProduct.smul_tmul', Algebra.smul_def]
          exact (ModuleCat.ExtendScalars.smul_tmul (φS A t p T j)
            (algebraMap (Tower A t p) (TS A t p T) c) s w).symm
        | add x y hx hy =>
          rw [smul_add]
          exact (congrArg₂ (· + ·) hx hy).trans
            (smul_add (A := (Fj A t p T j).obj W) c _ _).symm
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  exact (towerLengthFun_congr e).symm

include ht hTa hresT hresB hfin in
/-- **有限段の `Tor` の公式**：有限生成 `S_j` 加群 `V` について
`λ_∞(H^m((S ⊗_{S_j} V) ⊗_B G)) = ℓ_B(H^m(V ⊗_B G)) / p^{jh}`。 -/
theorem towerLengthFun_homology_tensorRes (j : ℕ) (V : ModuleCat.{u} (TSj A t p T j))
    [Module.Finite (TSj A t p T j) V] (m : ℤ) :
    letI := Module.compHom
      ((tensorRes ((φS A t p T j).comp (φB A t p T B j)) G ((Fj A t p T j).obj V)).homology m)
      (algebraMap (Tower A t p) (TS A t p T))
    letI := Module.compHom ((tensorRes (φB A t p T B j) G V).homology m) (φB A t p T B j)
    towerLengthFun A t p
        ((tensorRes ((φS A t p T j).comp (φB A t p T B j)) G ((Fj A t p T j).obj V)).homology m) =
      (Module.length B ((tensorRes (φB A t p T B j) G V).homology m) : ℝ≥0∞) /
        (stageRank h p j : ℝ≥0∞) := by
  let W := (tensorRes (φB A t p T B j) G V).homology m
  -- `W` は有限生成
  have : Module.Finite (TowerStage A t p j) (TSj A t p T j) := inferInstance
  have : IsNoetherian (TowerStage A t p j) (TSj A t p T j) :=
    isNoetherian_of_isNoetherianRing_of_finite _ _
  have : IsNoetherianRing (TSj A t p T j) := isNoetherian_of_tower (TowerStage A t p j) this
  have : Module.Finite (TSj A t p T j) W := by
    have := hfin m
    have : Module.Finite (TSj A t p T j) ((GS (φB A t p T B j) G).X m) :=
      finite_baseChange (φB A t p T B j) (G.X m)
    have : Module.Finite (TSj A t p T j) ((tensorRes (φB A t p T B j) G V).X m) :=
      inferInstanceAs (Module.Finite _ (TensorProduct _ V _))
    exact homology_moduleFinite _ m
  -- 係数拡大との交換
  let e := homologyTensorResBaseChangeIso A t p T j G V m
  let _ := Module.compHom
    ((tensorRes ((φS A t p T j).comp (φB A t p T B j)) G ((Fj A t p T j).obj V)).homology m)
    (algebraMap (Tower A t p) (TS A t p T))
  let _ := Module.compHom ((Fj A t p T j).obj W) (algebraMap (Tower A t p) (TS A t p T))
  rw [towerLengthFun_congr
    { e.toLinearEquiv with
      map_smul' := fun c x ↦ e.toLinearEquiv.map_smul (algebraMap (Tower A t p) _ c) x },
    towerLengthFun_extendScalars_eq]
  exact towerLengthFun_baseChangeT A t p T ht hTa hresT B hresB j W

end torFormula

/-! ## 近似 -/

section approx

variable [IsLocalRing A]

/-- `m_A S`。 -/
noncomputable abbrev JT : Ideal (TS A t p T) :=
  (towerMaxIdeal A t p).map (algebraMap (Tower A t p) (TS A t p T))

/-- `S` 加群の正規化長さ（`λ_∞` の `Λ → S` に沿った係数制限）。 -/
noncomputable abbrev μT : NormalizedLength (TS A t p T) (JT A t p T) :=
  (towerLength A t p).comap (algebraMap (Tower A t p) (TS A t p T)) _ le_rfl

/-- **部分加群による近似**：`J` 冪ねじれで `μ(M) < ∞` の `S` 加群 `M` と `ε > 0` について、有限生成な
部分 `S` 加群 `V` で `μ(M / V) ≤ ε` となるものがある。`λ_∞` の上限の性質 (2.3) による。 -/
theorem exists_fg_quotient_le (M : Type u) [AddCommGroup M] [Module (TS A t p T) M]
    (hM : IsPowTorsion (JT A t p T) M) (hMfin : (μT A t p T).len M ≠ ⊤) (ε : ℝ≥0∞)
    (hε : 0 < ε) :
    ∃ V : Submodule (TS A t p T) M, V.FG ∧ (μT A t p T).len (M ⧸ V) ≤ ε := by
  by_cases hlt : ε < (μT A t p T).len M
  · let _ : Module (Tower A t p) M := Module.compHom M (algebraMap (Tower A t p) (TS A t p T))
    have : IsScalarTower (Tower A t p) (TS A t p T) M :=
      IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
    have hMΛ : IsPowTorsion (towerMaxIdeal A t p) M :=
      IsPowTorsion.comap (algebraMap (Tower A t p) (TS A t p T)) le_rfl M hM
    have hc : (μT A t p T).len M - ε < (towerLength A t p).len M :=
      ENNReal.sub_lt_self hMfin (ne_of_gt (lt_of_le_of_lt zero_le hlt)) hε.ne'
    obtain ⟨N, hNfg, hN⟩ := NormalizedLength.exists_fg_lt (towerLength_hasSup A t p) hMΛ hc
    obtain ⟨S₀, hS₀⟩ := hNfg
    let V := Submodule.span (TS A t p T) (S₀ : Set M)
    refine ⟨V, ⟨S₀, rfl⟩, ?_⟩
    -- `λ(N) ≤ μ(V)`
    have hVt : IsPowTorsion (JT A t p T) V := hM.submodule V
    have hNV : (towerLength A t p).len N ≤ (μT A t p T).len V := by
      let _ : Module (Tower A t p) V := Module.compHom V (algebraMap (Tower A t p) (TS A t p T))
      let ι : N →ₗ[Tower A t p] V :=
        { toFun := fun n ↦ ⟨n, by
            have : (n : M) ∈ Submodule.span (Tower A t p) (S₀ : Set M) := hS₀ ▸ n.2
            exact Submodule.span_le_restrictScalars (Tower A t p) (TS A t p T) _ this⟩
          map_add' := fun _ _ ↦ rfl
          map_smul' := fun _ _ ↦ rfl }
      exact (towerLength A t p).len_le_of_injective ι (fun x y hxy ↦ Subtype.ext
        (congrArg (fun z : V ↦ (z : M)) hxy))
        (IsPowTorsion.comap (algebraMap (Tower A t p) (TS A t p T)) le_rfl V hVt)
    have hsum := (μT A t p T).len_eq_add_quotient hM V
    have hVfin : (μT A t p T).len V ≠ ⊤ :=
      ne_top_of_le_ne_top hMfin (hsum ▸ le_self_add)
    -- `μ(M) < μ(V) + ε`
    have h1 : (μT A t p T).len M < (μT A t p T).len V + ε := by
      have := hN.trans_le hNV
      rwa [ENNReal.sub_lt_iff_lt_right (ne_top_of_lt hlt) hlt.le] at this
    rw [hsum] at h1
    exact ((ENNReal.add_lt_add_iff_left hVfin).mp h1).le
  · refine ⟨⊥, Submodule.fg_bot, ?_⟩
    rw [(μT A t p T).len_congr _ _ (Submodule.quotEquivOfEqBot ⊥ rfl)]
    exact not_lt.mp hlt

/-- **有限表示による近似**（論文 Lemma 5.4 の証明の `P_ε`）：`J` 冪ねじれで `μ(U) < ∞` の `S` 加群 `U`
と `ε > 0` について、有限表示な `S` 加群 `P` と `S` 線形写像 `f : P → U` で `μ(ker f) ≤ ε`、
`μ(coker f) ≤ ε` となるものがある。`S` が `J` 冪ねじれで、`μ(S^r) < ∞` を仮定する。 -/
theorem exists_finitePresentation_approx (U : Type u) [AddCommGroup U] [Module (TS A t p T) U]
    (hU : IsPowTorsion (JT A t p T) U) (hUfin : (μT A t p T).len U ≠ ⊤)
    (hS : IsPowTorsion (JT A t p T) (TS A t p T))
    (hSfin : ∀ r : ℕ, (μT A t p T).len (Fin r → TS A t p T) ≠ ⊤) (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ (P : Type u) (_ : AddCommGroup P) (_ : Module (TS A t p T) P)
      (_ : Module.FinitePresentation (TS A t p T) P) (f : P →ₗ[TS A t p T] U),
      IsPowTorsion (JT A t p T) P ∧ (μT A t p T).len (LinearMap.ker f) ≤ ε ∧
        (μT A t p T).len (U ⧸ LinearMap.range f) ≤ ε := by
  obtain ⟨V, hVfg, hV⟩ := exists_fg_quotient_le A t p T U hU hUfin ε hε
  obtain ⟨r, s, hs⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hVfg
  let g : (Fin r → TS A t p T) →ₗ[TS A t p T] U := Fintype.linearCombination (TS A t p T) s
  have hg : LinearMap.range g = V := by
    rw [Fintype.range_linearCombination, hs]
  -- 自由加群のねじれと有限性
  have hFt : IsPowTorsion (JT A t p T) (Fin r → TS A t p T) := by
    obtain ⟨n, hn⟩ := hS
    exact ⟨n, fun v c ↦ funext fun i ↦ hn (x := v i) (a := c)⟩
  let K := LinearMap.ker g
  have hKt : IsPowTorsion (JT A t p T) K := hFt.submodule K
  have hKfin : (μT A t p T).len K ≠ ⊤ :=
    ne_top_of_le_ne_top (hSfin r) ((μT A t p T).len_submodule_le hFt K)
  obtain ⟨K₀, hK₀fg, hK₀⟩ := exists_fg_quotient_le A t p T K hKt hKfin ε hε
  let L₀ := K₀.map K.subtype
  have hL₀ : L₀ ≤ LinearMap.ker g := Submodule.map_subtype_le K K₀
  let f := L₀.liftQ g hL₀
  refine ⟨_ ⧸ L₀, inferInstance, inferInstance, ?_, f, hFt.quotient L₀, ?_, ?_⟩
  · exact Module.finitePresentation_of_surjective L₀.mkQ L₀.mkQ_surjective
      (by rw [Submodule.ker_mkQ]; exact hK₀fg.map _)
  · -- `K / K₀ ↠ ker f`
    let π : K →ₗ[TS A t p T] LinearMap.ker f :=
      { toFun := fun x ↦ ⟨L₀.mkQ x, by
          rw [LinearMap.mem_ker, Submodule.mkQ_apply, Submodule.liftQ_apply]
          exact x.2⟩
        map_add' := fun _ _ ↦ rfl
        map_smul' := fun _ _ ↦ rfl }
    have hπ : K₀ ≤ LinearMap.ker π := by
      intro x hx
      rw [LinearMap.mem_ker]
      exact Subtype.ext ((Submodule.Quotient.mk_eq_zero _).mpr ⟨x, hx, rfl⟩)
    have hsurj : Function.Surjective (K₀.liftQ π hπ) := by
      rintro ⟨y, hy⟩
      rw [Submodule.ker_liftQ] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      exact ⟨Submodule.Quotient.mk ⟨x, hx⟩, rfl⟩
    exact ((μT A t p T).len_le_of_surjective _ hsurj (hKt.quotient K₀)).trans hK₀
  · have hr : LinearMap.range f = V := by rw [Submodule.range_liftQ, hg]
    rw [(μT A t p T).len_congr _ _ (Submodule.quotEquivOfEq _ _ hr)]
    exact hV

end approx

/-! ## `S` 自身の長さ -/

section selfLength

variable [IsLocalRing A] [IsNoetherianRing A] [Fact p.Prime] (ht : ∀ i, t i ∈ maximalIdeal A)
  [IsLocalRing T] [Module.Finite A T] {a : ℕ}
  (hTa : ∀ x ∈ maximalIdeal A ^ a, algebraMap A T x = 0)
  (hresT : Function.Surjective ((residue T).comp (algebraMap A T)))

omit [IsNoetherianRing A] [Fact p.Prime] [IsLocalRing T] [Module.Finite A T] in
include hTa in
/-- `S` は `J` 冪ねじれ（`m_A^a T = 0`）。 -/
lemma isPowTorsion_TS : IsPowTorsion (JT A t p T) (TS A t p T) := by
  have h0 : ∀ y ∈ maximalIdeal A ^ a, algebraMap A (TS A t p T) y = 0 := fun y hy ↦ by
    rw [← AlgHom.commutes (Algebra.TensorProduct.includeRight (R := A) (A := Tower A t p)
      (B := T)) y, hTa y hy, map_zero]
  have hJ : JT A t p T ^ a = (maximalIdeal A ^ a).map (algebraMap A (TS A t p T)) := by
    rw [JT, towerMaxIdeal, ← Ideal.map_pow, ← Ideal.map_pow, Ideal.map_map,
      ← IsScalarTower.algebraMap_eq]
  refine ⟨a, fun x c ↦ ?_⟩
  have hc : (c : TS A t p T) = 0 := by
    have hc : (c : TS A t p T) ∈ (maximalIdeal A ^ a).map (algebraMap A (TS A t p T)) :=
      (le_of_eq hJ) c.2
    have : (maximalIdeal A ^ a).map (algebraMap A (TS A t p T)) ≤ ⊥ := by
      rw [Ideal.map_le_iff_le_comap]
      intro y hy
      exact (h0 y hy : _)
    exact (Ideal.mem_bot).mp (this hc)
  rw [hc, zero_smul]

omit [IsNoetherianRing A] [Fact p.Prime] [IsLocalRing T] [Module.Finite A T] in
/-- `S ⊗_{S_j} V` 上の `Λ` の作用は、`S` 加群としての係数制限と左因子への作用で一致する。 -/
lemma μT_tensor_eq (j : ℕ) (V : Type u) [AddCommGroup V] [Module (TSj A t p T j) V] :
    (μT A t p T).len (TS A t p T ⊗[TSj A t p T j] V) =
      towerLengthFun A t p (TS A t p T ⊗[TSj A t p T j] V) := by
  have hinst : (Module.compHom (TS A t p T ⊗[TSj A t p T j] V)
      (algebraMap (Tower A t p) (TS A t p T)) : Module (Tower A t p) _) =
      TensorProduct.leftModule := by
    refine Module.ext' _ _ fun c x ↦ ?_
    change (algebraMap (Tower A t p) (TS A t p T) c) • x = c • x
    induction x using TensorProduct.induction_on with
    | zero => rw [smul_zero, smul_zero]
    | tmul s v =>
      rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, Algebra.smul_def c s]
    | add x y hx hy => rw [smul_add, smul_add, hx, hy]
  rw [NormalizedLength.comap_len]
  exact congrArg (@towerLengthFun A _ _ t p (TS A t p T ⊗[TSj A t p T j] V) _) hinst

include ht hTa hresT in
/-- `μ(S) < ∞`：`S ≃ S ⊗_{S_0} S_0` と有限段の公式。 -/
lemma μT_TS_ne_top : (μT A t p T).len (TS A t p T) ≠ ⊤ := by
  let r := TensorProduct.rid (TSj A t p T 0) (TS A t p T)
  let e : (TS A t p T ⊗[TSj A t p T 0] TSj A t p T 0) ≃ₗ[TS A t p T] TS A t p T :=
    { toFun := r
      invFun := r.symm
      map_add' := map_add r
      map_smul' := fun c x ↦ by
        induction x using TensorProduct.induction_on with
        | zero => rw [smul_zero, map_zero, smul_zero]
        | tmul s y =>
          rw [TensorProduct.smul_tmul', TensorProduct.rid_tmul, TensorProduct.rid_tmul,
            RingHom.id_apply, smul_eq_mul, smul_eq_mul, Algebra.smul_def, Algebra.smul_def,
            mul_left_comm]
        | add x y hx hy => rw [smul_add, map_add, hx, hy, map_add, smul_add]
      left_inv := r.left_inv
      right_inv := r.right_inv }
  rw [← (μT A t p T).len_congr _ _ e, μT_tensor_eq,
    towerLengthFun_baseChangeT A t p T ht hTa hresT T
      (by simpa using IsLocalRing.residue_surjective) 0 (TSj A t p T 0)]
  refine ENNReal.div_ne_top ?_ (by simp [stageRank])
  exact length_TSj_ne_top A t p T ht hTa hresT T (by simpa using IsLocalRing.residue_surjective) 0
    (TSj A t p T 0)

include ht hTa hresT in
/-- `μ(S^r) < ∞`。 -/
lemma μT_pi_ne_top : ∀ r : ℕ, (μT A t p T).len (Fin r → TS A t p T) ≠ ⊤
  | 0 => by rw [(μT A t p T).len_eq_zero_of_subsingleton]; exact ENNReal.zero_ne_top
  | r + 1 => by
    let e : (Fin (r + 1) → TS A t p T) ≃ₗ[TS A t p T] TS A t p T × (Fin r → TS A t p T) :=
      (Fin.consLinearEquiv (TS A t p T) (fun _ ↦ TS A t p T)).symm
    have hS := isPowTorsion_TS A t p T hTa
    have hF : IsPowTorsion (JT A t p T) (Fin r → TS A t p T) := by
      obtain ⟨n, hn⟩ := hS
      exact ⟨n, fun v c ↦ funext fun i ↦ hn (x := v i) (a := c)⟩
    rw [(μT A t p T).len_congr _ _ e, TensorRes.len_prod _ _ _ hS hF]
    exact ENNReal.add_ne_top.mpr ⟨μT_TS_ne_top A t p T ht hTa hresT, μT_pi_ne_top r⟩

end selfLength

/-! ## 組み立て -/

section assembly

/-- `S ⊗_{S_j} V` と係数拡大関手の対象の同一視（定義から等しい）。 -/
noncomputable def tensorFjEquiv (j : ℕ) (V : ModuleCat.{u} (TSj A t p T j)) :
    (TS A t p T ⊗[TSj A t p T j] V) ≃ₗ[TS A t p T] (Fj A t p T j).obj V :=
  LinearEquiv.refl _ _


open CategoryTheory TensorRes

variable [IsLocalRing A] [IsNoetherianRing A] [Fact p.Prime] (ht : ∀ i, t i ∈ maximalIdeal A)
  [IsLocalRing T] [Module.Finite A T] {a : ℕ}
  (hTa : ∀ x ∈ maximalIdeal A ^ a, algebraMap A T x = 0)
  (hresT : Function.Surjective ((residue T).comp (algebraMap A T)))
  {B : Type u} [CommRing B] [Algebra B T]
  (hresB : Function.Surjective ((residue T).comp (algebraMap B T)))

variable (B) in
/-- `B → S`（`B → T → S`）。 -/
noncomputable abbrev ψU : B →+* TS A t p T :=
  (Algebra.TensorProduct.includeRight : T →ₐ[A] TS A t p T).toRingHom.comp (algebraMap B T)

omit [IsLocalRing A] [IsNoetherianRing A] [Fact p.Prime] [IsLocalRing T] [Module.Finite A T] in
lemma φS_comp_φB (j : ℕ) : (φS A t p T j).comp (φB A t p T B j) = ψU A t p T B := by
  ext x
  change stageMapT A t p T j ((1 : TowerStage A t p j) ⊗ₜ algebraMap B T x) =
    (1 : Tower A t p) ⊗ₜ algebraMap B T x
  rw [stageMapT_tmul, map_one]

variable (B) in
/-- 段 `j` の加群の `B` 上の長さを `p^{jh}` で割ったもの。 -/
noncomputable def lenB (j : ℕ) (W : Type u) [AddCommGroup W] [Module (TSj A t p T j) W] : ℝ≥0∞ :=
  (letI := Module.compHom W (φB A t p T B j); (Module.length B W : ℝ≥0∞)) /
    (stageRank h p j : ℝ≥0∞)

include ht hTa hresT hresB in
/-- **近似の一段**：`ε > 0` と `n` について、段 `j ≥ n` と有限生成 `S_j` 加群 `V` があって、
`ℓ_B(V)/p^{jh}` と `μ(U)` の差、`ℓ_B(H^m(V ⊗_B G))/p^{jh}` と `μ(H^m(U ⊗_B G))` の差が
（階数）× `ε` 以下。論文 Lemma 5.4 の証明の一段。 -/
theorem exists_stage_step {ι : Type*} (G : ι → CochainComplex (ModuleCat.{u} B) ℤ)
    (hfree : ∀ k i, Module.Free B ((G k).X i)) (hfin : ∀ k i, Module.Finite B ((G k).X i))
    (U : ModuleCat.{u} (TS A t p T)) (hU : IsPowTorsion (JT A t p T) U)
    (hUfin : (μT A t p T).len U ≠ ⊤) (n : ℕ) (ε : ℝ≥0∞) (hε : 0 < ε) :
    ∃ (j : ℕ) (_ : n ≤ j) (V : ModuleCat.{u} (TSj A t p T j))
      (_ : Module.Finite (TSj A t p T j) V),
      (lenB A t p T B j V ≤ (μT A t p T).len U + ε ∧
        (μT A t p T).len U ≤ lenB A t p T B j V + ε) ∧
      ∀ k (m : ℤ),
        lenB A t p T B j ((tensorRes (φB A t p T B j) (G k) V).homology m) ≤
            (μT A t p T).len ((tensorRes (ψU A t p T B) (G k) U).homology m) +
              ((rk (ψU A t p T B) (G k) m : ℝ≥0∞) + rk (ψU A t p T B) (G k) (m - 1)) * ε ∧
          (μT A t p T).len ((tensorRes (ψU A t p T B) (G k) U).homology m) ≤
            lenB A t p T B j ((tensorRes (φB A t p T B j) (G k) V).homology m) +
              ((rk (ψU A t p T B) (G k) (m + 1) : ℝ≥0∞) + rk (ψU A t p T B) (G k) m) * ε := by
  obtain ⟨P, _, _, _, f, hPt, hK, hW⟩ := exists_finitePresentation_approx A t p T U hU hUfin
    (isPowTorsion_TS A t p T hTa) (μT_pi_ne_top A t p T ht hTa hresT) ε hε
  obtain ⟨j, hnj, V, _, _, hVfin, ⟨e⟩⟩ := exists_descentT A t p T P n
  let VM := ModuleCat.of (TSj A t p T j) V
  refine ⟨j, hnj, VM, hVfin, ?_, fun k m ↦ ?_⟩
  · -- `μ(P) = ℓ_B(V)/p^{jh}`
    have hP : (μT A t p T).len P = lenB A t p T B j V := by
      rw [(μT A t p T).len_congr _ _ e, μT_tensor_eq,
        towerLengthFun_baseChangeT A t p T ht hTa hresT B hresB j V]
      rfl
    have h1 := (μT A t p T).len_eq_add_ker_range f hPt
    have h2 := (μT A t p T).len_eq_add_quotient hU (LinearMap.range f)
    have hR : (μT A t p T).len (LinearMap.range f) ≤ (μT A t p T).len U :=
      (μT A t p T).len_submodule_le hU _
    rw [← hP]
    constructor
    · rw [h1, add_comm]
      exact add_le_add hR hK
    · rw [h2]
      refine add_le_add ?_ hW
      rw [h1]
      exact le_add_self
  · -- `Tor` の比較
    let μ := μT A t p T
    let fM : ModuleCat.of (TS A t p T) P ⟶ U := ModuleCat.ofHom f
    obtain ⟨hle1, hle2⟩ := len_tensorRes_le_of_hom μ (ψU A t p T B) (G k) (hfree k) fM hPt hU m
    have hKt : IsPowTorsion (JT A t p T) (LinearMap.ker f) := hPt.submodule _
    have hWt : IsPowTorsion (JT A t p T) (U ⧸ LinearMap.range f) := hU.quotient _
    have bK : ∀ m', μ.len ((tensorRes (ψU A t p T B) (G k)
        (ModuleCat.of (TS A t p T) (LinearMap.ker f))).homology m') ≤
        (rk (ψU A t p T B) (G k) m' : ℝ≥0∞) * ε := fun m' ↦
      (len_homology_tensorRes_le μ (ψU A t p T B) (G k) (hfree k) (hfin k) _ hKt m').trans
        (mul_le_mul' le_rfl hK)
    have bW : ∀ m', μ.len ((tensorRes (ψU A t p T B) (G k)
        (ModuleCat.of (TS A t p T) (U ⧸ LinearMap.range f))).homology m') ≤
        (rk (ψU A t p T B) (G k) m' : ℝ≥0∞) * ε := fun m' ↦
      (len_homology_tensorRes_le μ (ψU A t p T B) (G k) (hfree k) (hfin k) _ hWt m').trans
        (mul_le_mul' le_rfl hW)
    -- `μ(H^m(P ⊗ G)) = ℓ_B(H^m(V ⊗ G))/p^{jh}`
    have hT : μ.len ((tensorRes (ψU A t p T B) (G k) (ModuleCat.of (TS A t p T) P)).homology m) =
        lenB A t p T B j ((tensorRes (φB A t p T B j) (G k) VM).homology m) := by
      let eP : ModuleCat.of (TS A t p T) P ≅ (Fj A t p T j).obj VM :=
        (e.trans (tensorFjEquiv A t p T j VM)).toModuleIso
      refine (μ.len_congr _ _ ((HomologicalComplex.homologyFunctor _ _ m).mapIso
        ((tensorComplexFunctor (GS (ψU A t p T B) (G k))).mapIso eP)).toLinearEquiv).trans ?_
      change μ.len ((tensorRes (ψU A t p T B) (G k) ((Fj A t p T j).obj VM)).homology m) = _
      rw [← φS_comp_φB A t p T j, NormalizedLength.comap_len]
      exact towerLengthFun_homology_tensorRes A t p T ht hTa hresT hresB (G k) (hfin k) j VM m
    rw [hT] at hle1 hle2
    constructor
    · calc _ ≤ _ := hle1
        _ ≤ μ.len ((tensorRes (ψU A t p T B) (G k) U).homology m) +
              (rk (ψU A t p T B) (G k) m : ℝ≥0∞) * ε +
              (rk (ψU A t p T B) (G k) (m - 1) : ℝ≥0∞) * ε :=
          add_le_add (add_le_add le_rfl (bK m)) (bW (m - 1))
        _ = _ := by ring
    · calc _ ≤ _ := hle2
        _ ≤ lenB A t p T B j ((tensorRes (φB A t p T B j) (G k) VM).homology m) +
              (rk (ψU A t p T B) (G k) (m + 1) : ℝ≥0∞) * ε +
              (rk (ψU A t p T B) (G k) m : ℝ≥0∞) * ε :=
          add_le_add (add_le_add le_rfl (bK (m + 1))) (bW m)
        _ = _ := by ring


omit [IsLocalRing A] [IsNoetherianRing A] [Fact p.Prime] [IsLocalRing T] [Module.Finite A T] in
/-- 両側から `c_n → 0` で挟まれた列は収束する。 -/
lemma tendsto_of_le_add_of_le_add {x c : ℕ → ℝ≥0∞} {y : ℝ≥0∞} (hy : y ≠ ⊤)
    (hc : Filter.Tendsto c Filter.atTop (nhds 0)) (h1 : ∀ n, x n ≤ y + c n)
    (h2 : ∀ n, y ≤ x n + c n) : Filter.Tendsto x Filter.atTop (nhds y) := by
  rw [ENNReal.tendsto_nhds hy]
  intro ε hε
  filter_upwards [(ENNReal.tendsto_nhds_zero.mp hc) ε hε] with n hn
  exact ⟨tsub_le_iff_right.mpr ((h2 n).trans (add_le_add le_rfl hn)),
    (h1 n).trans (add_le_add le_rfl hn)⟩

omit [IsLocalRing A] [IsNoetherianRing A] [Fact p.Prime] [IsLocalRing T] [Module.Finite A T] in
lemma tendsto_const_mul_inv_succ (K : ℝ≥0∞) (hK : K ≠ ⊤) :
    Filter.Tendsto (fun n : ℕ ↦ K * ((n + 1 : ℕ) : ℝ≥0∞)⁻¹) Filter.atTop (nhds 0) := by
  have h : Filter.Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ≥0∞)⁻¹) Filter.atTop (nhds 0) :=
    ENNReal.tendsto_inv_nat_nhds_zero.comp (Filter.tendsto_add_atTop_nat 1)
  simpa using ENNReal.Tendsto.const_mul h (Or.inr hK)

include ht hTa hresT hresB in
/-- **論文 Lemma 5.4 の一般的な部分（塔の近似）**：`J` 冪ねじれで `μ(U) < ∞` の `S` 加群 `U` と、
有限自由 `B` 加群の複体の族 `G_k`（`L_k` の分解）について、段 `j_n ≥ n` と有限生成 `S_{j_n}` 加群
`V_n` の列で

  `ℓ_B(V_n) / p^{j_n h} → μ(U)`、`ℓ_B(H^m(V_n ⊗_B G_k)) / p^{j_n h} → μ(H^m(U ⊗_B G_k))`

となるものがある。 -/
theorem exists_tower_approximation {ι : Type*} (G : ι → CochainComplex (ModuleCat.{u} B) ℤ)
    (hfree : ∀ k i, Module.Free B ((G k).X i)) (hfin : ∀ k i, Module.Finite B ((G k).X i))
    (U : ModuleCat.{u} (TS A t p T)) (hU : IsPowTorsion (JT A t p T) U)
    (hUfin : (μT A t p T).len U ≠ ⊤) :
    ∃ (j : ℕ → ℕ) (V : (n : ℕ) → ModuleCat.{u} (TSj A t p T (j n))),
      (∀ n, n ≤ j n) ∧ (∀ n, Module.Finite (TSj A t p T (j n)) (V n)) ∧
      Filter.Tendsto (fun n ↦ lenB A t p T B (j n) (V n)) Filter.atTop
        (nhds ((μT A t p T).len U)) ∧
      ∀ k (m : ℤ), Filter.Tendsto
        (fun n ↦ lenB A t p T B (j n) ((tensorRes (φB A t p T B (j n)) (G k) (V n)).homology m))
        Filter.atTop (nhds ((μT A t p T).len ((tensorRes (ψU A t p T B) (G k) U).homology m))) := by
  let ε : ℕ → ℝ≥0∞ := fun n ↦ ((n + 1 : ℕ) : ℝ≥0∞)⁻¹
  have hε : ∀ n, 0 < ε n := fun n ↦ ENNReal.inv_pos.mpr (ENNReal.natCast_ne_top _)
  choose j hj V hV hlen htor using fun n ↦
    exists_stage_step A t p T ht hTa hresT hresB G hfree hfin U hU hUfin n (ε n) (hε n)
  refine ⟨j, V, hj, hV, ?_, fun k m ↦ ?_⟩
  · simpa using tendsto_of_le_add_of_le_add hUfin (tendsto_const_mul_inv_succ 1 ENNReal.one_ne_top)
      (fun n ↦ by simpa [ε] using (hlen n).1) (fun n ↦ by simpa [ε] using (hlen n).2)
  · have hfinU : (μT A t p T).len ((tensorRes (ψU A t p T B) (G k) U).homology m) ≠ ⊤ :=
      ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hUfin)
        (len_homology_tensorRes_le _ _ (G k) (hfree k) (hfin k) U hU m)
    let K : ℝ≥0∞ := (rk (ψU A t p T B) (G k) (m + 1) : ℝ≥0∞) + rk (ψU A t p T B) (G k) m +
      rk (ψU A t p T B) (G k) (m - 1)
    have hK : K ≠ ⊤ := by simp [K]
    refine tendsto_of_le_add_of_le_add hfinU (tendsto_const_mul_inv_succ K hK) (fun n ↦ ?_)
      (fun n ↦ ?_)
    · refine (htor n k m).1.trans (add_le_add le_rfl (mul_le_mul' ?_ le_rfl))
      exact le_add_self.trans_eq (add_assoc _ _ _).symm
    · refine (htor n k m).2.trans (add_le_add le_rfl (mul_le_mul' ?_ le_rfl))
      exact le_self_add

end assembly

end Section2

end SerrePositivity
