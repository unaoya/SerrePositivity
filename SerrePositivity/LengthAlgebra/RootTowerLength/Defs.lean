module

public import SerrePositivity.CommutativeAlgebra.RootTower.Basic
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.Basic.Real.ENatENNReal
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.FiniteLength
public import Mathlib.Topology.Instances.ENNReal.Lemmas

/-! # 根の塔上の長さの三つの数値関数

有限段からの降下による `presentedLength`、有限表示な全射の下限 `fgLength`、
有限生成部分加群にわたる上限 `towerLengthFun` を定義する。
この段階では加法性や有限生成の場合の一致を仮定せず、
零加群の値と線形同型による不変性を証明する。
具体的な `NormalizedLength` の組立と引用する加法性は別の層で扱う。

CLMST Definition 2.2.1 の値を有限段公式で比較するための共通の数値定義。
宣言名は既存利用先との互換性のため `SerrePositivity.Section2` に保持する。
このモジュールは `Paper/` を import しない。
-/

@[expose] public section

universe u

open IsLocalRing TensorProduct
open scoped ENNReal

namespace SerrePositivity

namespace Section2

variable (A : Type u) [CommRing A] {h : ℕ} (t : Fin h → A) (p : ℕ)

/-- 1. 有限表示の段階 `λ**`：段 `n` と有限長 `A_n` 加群 `V` で `M ≃ Λ ⊗_{A_n} V` となるもの全体に
わたる `ℓ_{A_n}(V) / p^{nh}` の下限。該当がなければ `⊤`。 -/
noncomputable def presentedLength (M : Type u) [AddCommGroup M] [Module (Tower A t p) M] :
    ℝ≥0∞ :=
  ⨅ (n : ℕ) (V : Type u) (_ : AddCommGroup V) (_ : Module (TowerStage A t p n) V)
    (_ : IsFiniteLength (TowerStage A t p n) V)
    (_ : Nonempty (M ≃ₗ[Tower A t p] Tower A t p ⊗[TowerStage A t p n] V)),
    (Module.length (TowerStage A t p n) V : ℝ≥0∞) / (stageRank h p n : ℝ≥0∞)

/-- 2. 有限生成の段階 `λ*`：有限表示な全射 `P ↠ N` にわたる `λ**(P)` の下限。 -/
noncomputable def fgLength (N : Type u) [AddCommGroup N] [Module (Tower A t p) N] : ℝ≥0∞ :=
  ⨅ (P : Type u) (_ : AddCommGroup P) (_ : Module (Tower A t p) P)
    (_ : Module.FinitePresentation (Tower A t p) P) (f : P →ₗ[Tower A t p] N)
    (_ : Function.Surjective f), presentedLength A t p P

/-- 3. 一般の加群：`λ_∞(M) = sup{λ*(N) : N ⊆ M 有限生成}`（論文 (2.3)）。 -/
noncomputable def towerLengthFun (M : Type u) [AddCommGroup M] [Module (Tower A t p) M] :
    ℝ≥0∞ :=
  ⨆ (N : Submodule (Tower A t p) M) (_ : N.FG), fgLength A t p N

variable {A t p}

/-! ## 定義から出る性質 -/

/-- `λ**` は線形同型で単調（したがって不変）。 -/
lemma presentedLength_le_of_equiv {M M' : Type u} [AddCommGroup M] [Module (Tower A t p) M]
    [AddCommGroup M'] [Module (Tower A t p) M'] (e : M ≃ₗ[Tower A t p] M') :
    presentedLength A t p M ≤ presentedLength A t p M' := by
  refine le_iInf fun n ↦ le_iInf fun V ↦ le_iInf fun i₁ ↦ le_iInf fun i₂ ↦ le_iInf fun hV ↦
    le_iInf fun ⟨e'⟩ ↦ ?_
  exact iInf_le_of_le n (iInf_le_of_le V (iInf_le_of_le i₁ (iInf_le_of_le i₂ (iInf_le_of_le hV
    (iInf_le_of_le ⟨e.trans e'⟩ le_rfl)))))

lemma presentedLength_congr {M M' : Type u} [AddCommGroup M] [Module (Tower A t p) M]
    [AddCommGroup M'] [Module (Tower A t p) M'] (e : M ≃ₗ[Tower A t p] M') :
    presentedLength A t p M = presentedLength A t p M' :=
  le_antisymm (presentedLength_le_of_equiv e) (presentedLength_le_of_equiv e.symm)

/-- `λ*` は線形同型で単調。 -/
lemma fgLength_le_of_equiv {N N' : Type u} [AddCommGroup N] [Module (Tower A t p) N]
    [AddCommGroup N'] [Module (Tower A t p) N'] (e : N ≃ₗ[Tower A t p] N') :
    fgLength A t p N ≤ fgLength A t p N' := by
  refine le_iInf fun P ↦ le_iInf fun i₁ ↦ le_iInf fun i₂ ↦ le_iInf fun hP ↦ le_iInf fun f ↦
    le_iInf fun hf ↦ ?_
  exact iInf_le_of_le P (iInf_le_of_le i₁ (iInf_le_of_le i₂ (iInf_le_of_le hP
    (iInf_le_of_le (e.symm.toLinearMap.comp f) (iInf_le_of_le (e.symm.surjective.comp hf)
      le_rfl)))))

lemma fgLength_congr {N N' : Type u} [AddCommGroup N] [Module (Tower A t p) N]
    [AddCommGroup N'] [Module (Tower A t p) N'] (e : N ≃ₗ[Tower A t p] N') :
    fgLength A t p N = fgLength A t p N' :=
  le_antisymm (fgLength_le_of_equiv e) (fgLength_le_of_equiv e.symm)

/-- 全射で得た加群の `λ*` は元の値以下。
有限表示な被覆への全射を合成して下限を比較するので、
有限生成の場合の `λ∞ = λ*` や長さの加法性の引用を使わない。 -/
lemma fgLength_le_of_surjective {M N : Type u} [AddCommGroup M]
    [Module (Tower A t p) M] [AddCommGroup N] [Module (Tower A t p) N]
    (f : M →ₗ[Tower A t p] N) (hf : Function.Surjective f) :
    fgLength A t p N ≤ fgLength A t p M := by
  refine le_iInf fun P ↦ le_iInf fun i₁ ↦ le_iInf fun i₂ ↦ le_iInf fun hP ↦
    le_iInf fun g ↦ le_iInf fun hg ↦ ?_
  exact iInf_le_of_le P (iInf_le_of_le i₁ (iInf_le_of_le i₂
    (iInf_le_of_le hP (iInf_le_of_le (f.comp g)
      (iInf_le_of_le (hf.comp hg) le_rfl)))))

/-- 有限表示加群は自分自身で被覆できるため、`λ* ≤ λ**`。
逆向きの不等式や有限段公式はこの定義的な比較には含めない。 -/
lemma fgLength_le_presentedLength (M : Type u) [AddCommGroup M]
    [Module (Tower A t p) M] [Module.FinitePresentation (Tower A t p) M] :
    fgLength A t p M ≤ presentedLength A t p M := by
  exact iInf_le_of_le M (iInf_le_of_le _ (iInf_le_of_le _
    (iInf_le_of_le inferInstance (iInf_le_of_le LinearMap.id
      (iInf_le_of_le Function.surjective_id le_rfl)))))

/-- `λ_∞` は線形同型で単調。 -/
lemma towerLengthFun_le_of_equiv {M M' : Type u} [AddCommGroup M] [Module (Tower A t p) M]
    [AddCommGroup M'] [Module (Tower A t p) M'] (e : M ≃ₗ[Tower A t p] M') :
    towerLengthFun A t p M ≤ towerLengthFun A t p M' := by
  refine iSup₂_le fun N hN ↦ le_iSup₂_of_le (N.map (e : M →ₗ[Tower A t p] M')) (hN.map _) ?_
  exact le_of_eq (fgLength_congr (Submodule.equivMapOfInjective _ e.injective N))

lemma towerLengthFun_congr {M M' : Type u} [AddCommGroup M] [Module (Tower A t p) M]
    [AddCommGroup M'] [Module (Tower A t p) M'] (e : M ≃ₗ[Tower A t p] M') :
    towerLengthFun A t p M = towerLengthFun A t p M' :=
  le_antisymm (towerLengthFun_le_of_equiv e) (towerLengthFun_le_of_equiv e.symm)

/-- 一方が零加群なら、テンソル積も零加群。 -/
lemma subsingleton_tensorProduct_of_right {R M N : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] [Subsingleton N] :
    Subsingleton (M ⊗[R] N) := inferInstance

/-- 零加群の `λ**` は `0`：段 `0`、`V = 0` で `ℓ(V)/1 = 0`。 -/
lemma presentedLength_eq_zero_of_subsingleton (M : Type u) [AddCommGroup M]
    [Module (Tower A t p) M] [Subsingleton M] : presentedLength A t p M = 0 := by
  refine le_antisymm ?_ zero_le
  let V : Type u := (⊥ : Submodule (TowerStage A t p 0) (TowerStage A t p 0))
  have : Subsingleton (Tower A t p ⊗[TowerStage A t p 0] V) :=
    subsingleton_tensorProduct_of_right
  refine iInf_le_of_le 0 (iInf_le_of_le V (iInf_le_of_le _ (iInf_le_of_le _
    (iInf_le_of_le IsFiniteLength.of_subsingleton
      (iInf_le_of_le ⟨LinearEquiv.ofSubsingleton _ _⟩ (le_of_eq ?_))))))
  rw [Module.length_eq_zero (M := V)]
  simp

/-- 零加群の `λ*` は `0`。 -/
lemma fgLength_eq_zero_of_subsingleton (N : Type u) [AddCommGroup N] [Module (Tower A t p) N]
    [Subsingleton N] : fgLength A t p N = 0 := by
  refine le_antisymm ?_ zero_le
  refine iInf_le_of_le N (iInf_le_of_le _ (iInf_le_of_le _ (iInf_le_of_le inferInstance
    (iInf_le_of_le LinearMap.id (iInf_le_of_le Function.surjective_id (le_of_eq ?_))))))
  exact presentedLength_eq_zero_of_subsingleton N

/-- 零加群の `λ_∞` は `0`。 -/
lemma towerLengthFun_eq_zero_of_subsingleton (M : Type u) [AddCommGroup M]
    [Module (Tower A t p) M] [Subsingleton M] : towerLengthFun A t p M = 0 := by
  refine le_antisymm (iSup₂_le fun N _ ↦ le_of_eq ?_) zero_le
  exact fgLength_eq_zero_of_subsingleton N

end Section2

end SerrePositivity
