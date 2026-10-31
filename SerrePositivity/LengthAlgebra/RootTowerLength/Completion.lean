module

public import SerrePositivity.CommutativeAlgebra.RootTower.Completion
public import SerrePositivity.LengthAlgebra.Normalized
public import SerrePositivity.LengthAlgebra.RootTowerLength.Additivity
public import SerrePositivity.CommutativeAlgebra.Adic.Completion.Basic
public import SerrePositivity.LengthAlgebra.QuotientBounds
public import SerrePositivity.CommutativeAlgebra.Adic.Completion.Tensor
public import SerrePositivity.CommutativeAlgebra.Length.Basic
public import Mathlib.RingTheory.TensorProduct.Quotient

/-! # 根の塔の長さの完備化への制限

## 概要

任意の塔上の正規化長さを p 進完備化上の加群へ制限して測り（直接の係数制限と完備化を経由する制限が一致する）、証明済みの根の塔の長さを完備化へ制限する。完備塔上の有限生成な冪ねじれ加群の長さの有限性、有限段のイデアルを完備塔へ拡張した商の長さ（通常長さを段の階数で割った値）、有限段から完備塔へ移した加群の長さを与える。

## 方針

有限長の段加群は p のある冪で消えるので、完備化による基底変更を未完備塔への基底変更と同定する。

## 規約

完備塔自身の Noether 性や perfectoid 性の引用は使わない。

## 使われ方

CLMST の完備塔上の長さの比較。
-/

@[expose] public noncomputable section

universe u

section CompletionPart

open CategoryTheory
open IsLocalRing
namespace SerrePositivity.Section2

variable (A : Type u) [CommRing A] [IsLocalRing A]
    {h : ℕ} (t : Fin h → A) (p : ℕ)

/-- 任意の塔上の正規化長さの、p 進完備化への係数制限。
塔上の長さは明示的な引数なので、具体的な加法性の引用に依存しない。 -/
noncomputable def completedLengthOf
    (L : NormalizedLength (Tower A t p) (towerMaxIdeal A t p)) :
    NormalizedLength (CompletedTower A t p) (completedTowerMaxIdeal A t p) :=
  L.comap (algebraMap (Tower A t p) (CompletedTower A t p)) _
    (towerMaxIdeal_map_completed A t p).le

/-- 直接の係数制限と、完備化を経由する係数制限の長さは一致する。
両立する代数作用から係数制限関手の合成同型を使い、L の同型不変性を適用する。 -/
theorem completedLengthOf_restrictScalars
    (L : NormalizedLength (Tower A t p) (towerMaxIdeal A t p))
    (C : Type u) [CommRing C] [Algebra (Tower A t p) C]
    [Algebra (CompletedTower A t p) C]
    [IsScalarTower (Tower A t p) (CompletedTower A t p) C]
    (M : Type u) [AddCommGroup M] [Module C M] :
    (letI := Module.compHom M (algebraMap (Tower A t p) C)
     L.len M) =
    (letI := Module.compHom M (algebraMap (CompletedTower A t p) C)
     (completedLengthOf A t p L).len M) := by
  exact L.len_congr
    ((ModuleCat.restrictScalars (algebraMap (Tower A t p) C)).obj (ModuleCat.of C M))
    ((ModuleCat.restrictScalars (algebraMap (Tower A t p) (CompletedTower A t p))).obj
      ((ModuleCat.restrictScalars (algebraMap (CompletedTower A t p) C)).obj
        (ModuleCat.of C M)))
    (ModuleCat.restrictScalarsComp'App
      (algebraMap (Tower A t p) (CompletedTower A t p))
      (algebraMap (CompletedTower A t p) C) (algebraMap (Tower A t p) C)
      (IsScalarTower.algebraMap_eq _ _ _) (ModuleCat.of C M)).toLinearEquiv

end SerrePositivity.Section2

end CompletionPart

section CompletedNormalizedPart

namespace SerrePositivity.RootTowerLength
open Section2 IsLocalRing

variable (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {h : ℕ} (t : Fin h → A) (p : ℕ) [Fact p.Prime]
    (ht : ∀ i, t i ∈ maximalIdeal A)

/-- 証明済みの塔の正規化長さを、p 進完備化への係数制限で測る具体的な長さ。 -/
noncomputable def completedNormalizedLength :
    NormalizedLength (CompletedTower A t p) (completedTowerMaxIdeal A t p) :=
  completedLengthOf A t p (normalizedLength A t p ht)

/-- 完備化上の加群の長さは、非完備な塔へ係数制限した三段階の数値関数。 -/
@[simp] theorem completedNormalizedLength_len (M : Type u) [AddCommGroup M]
    [Module (CompletedTower A t p) M] :
    (completedNormalizedLength A t p ht).len M =
      (letI := Module.compHom M (algebraMap (Tower A t p) (CompletedTower A t p))
       towerLengthFun A t p M) := rfl

/-- 完備化への係数制限後も、有限生成部分加群の長さの上限として計算できる。 -/
theorem completedNormalizedLength_hasSup : (completedNormalizedLength A t p ht).HasSup :=
  (normalizedLength_hasSup A t p ht).comap
    (algebraMap (Tower A t p) (CompletedTower A t p)) _
    (towerMaxIdeal_map_completed A t p).le

end SerrePositivity.RootTowerLength

end CompletedNormalizedPart

section CompletedFiniteLengthPart

namespace SerrePositivity.RootTowerLength
open Section2 IsLocalRing
variable (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {h : ℕ} (t : Fin h → A) (p : ℕ) [Fact p.Prime]
    (ht : ∀ i, t i ∈ maximalIdeal A) (hp : (p : A) ∈ maximalIdeal A)

include hp in
/-- 完備塔の極大イデアルの拡張の冪商は、正規化長さが有限。 -/
theorem completedNormalizedLength_quotient_pow_ne_top (n : ℕ) :
    (completedNormalizedLength A t p ht).len
      (CompletedTower A t p ⧸ (completedTowerMaxIdeal A t p) ^ n) ≠ ⊤ := by
  let S := Tower A t p
  let I : Ideal S := Ideal.span {(p : S)}
  let H : Ideal S := (towerMaxIdeal A t p) ^ n
  have hI : I.FG := Submodule.fg_span_singleton _
  have hpS : (p : S) ∈ towerMaxIdeal A t p := by
    simpa using Ideal.mem_map_of_mem (algebraMap A S) hp
  have hIH : I ^ n ≤ H := pow_le_pow_left'
    (((towerMaxIdeal A t p).span_singleton_le_iff_mem).mpr hpS) n
  have hH : H.FG := ((maximalIdeal A).fg_of_isNoetherianRing.map (algebraMap A S)).pow
  let : Module.FinitePresentation S (S ⧸ H) :=
    Module.finitePresentation_of_surjective H.mkQ H.mkQ_surjective (by
      rw [Submodule.ker_mkQ]
      exact hH)
  have htH : IsPowTorsion (towerMaxIdeal A t p) (S ⧸ H) := by
    refine ⟨n, ?_⟩
    rw [Module.isTorsionBySet_iff_subset_annihilator, SetLike.coe_subset_coe,
      Ideal.annihilator_quotient]
  have hmap : H.map (algebraMap S (CompletedTower A t p)) =
      (completedTowerMaxIdeal A t p) ^ n := by
    rw [Ideal.map_pow, towerMaxIdeal_map_completed]
  let e : (CompletedTower A t p ⧸ (completedTowerMaxIdeal A t p) ^ n) ≃ₐ[S] S ⧸ H :=
    (Ideal.quotientEquivAlgOfEq S hmap.symm).trans
      (adicCompletionOpenQuotientEquiv I H n hIH hI)
  let Q := CompletedTower A t p ⧸ (completedTowerMaxIdeal A t p) ^ n
  let : Module S Q := Module.compHom Q (algebraMap S (CompletedTower A t p))
  let E : Q ≃ₗ[S] S ⧸ H := { e.toAddEquiv with
    map_smul' := by
      intro r x
      change e (algebraMap S Q r * x) = algebraMap S (S ⧸ H) r * e x
      rw [map_mul, e.commutes] }
  rw [completedNormalizedLength_len]
  change towerLengthFun A t p Q ≠ ⊤
  rw [towerLengthFun_congr E]
  exact towerLengthFun_ne_top_of_finitePresentation A t p ht (S ⧸ H) htH

include hp in
/-- 完備塔上の有限生成な冪ねじれ加群は、正規化長さが有限。
完備塔のNoether性・加群の有限表示性は不要。 -/
theorem completedNormalizedLength_ne_top_of_finite
    (M : Type u) [AddCommGroup M] [Module (CompletedTower A t p) M]
    [Module.Finite (CompletedTower A t p) M]
    (hM : IsPowTorsion (completedTowerMaxIdeal A t p) M) :
    (completedNormalizedLength A t p ht).len M ≠ ⊤ :=
  NormalizedLength.len_ne_top_of_finite_of_powQuotient_ne_top
    (completedNormalizedLength A t p ht)
    (completedNormalizedLength_quotient_pow_ne_top A t p ht hp) hM

end SerrePositivity.RootTowerLength

end CompletedFiniteLengthPart

section CompletedTensorEvaluationPart

open scoped TensorProduct ENNReal
namespace SerrePositivity.RootTowerLength
open Section2 IsLocalRing TensorProduct
set_option backward.isDefEq.respectTransparency false

variable (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {h : ℕ} (t : Fin h → A) (p : ℕ) [Fact p.Prime]
    (ht : ∀ i, t i ∈ maximalIdeal A) (hp : (p : A) ∈ maximalIdeal A)

/-- 有限段の完備塔上の作用は、標準代数構造から得られる加群構造に固定する。 -/
local instance completedStageModule (n : ℕ) :
    Module (TowerStage A t p n) (CompletedTower A t p) := Algebra.toModule

omit [IsNoetherianRing A] in
include ht hp in
/-- 有限長の段加群を塔へ移すと、p のある冪で零化される。 -/
theorem exists_isTorsionBySet_p_pow_tensor (n : ℕ) (V : Type u) [AddCommGroup V]
    [Module (TowerStage A t p n) V] (hV : IsFiniteLength (TowerStage A t p n) V) :
    ∃ k : ℕ, Module.IsTorsionBySet (Tower A t p)
      (Tower A t p ⊗[TowerStage A t p n] V)
      ((Ideal.span {(p : Tower A t p)}) ^ k : Ideal (Tower A t p)) := by
  let B := TowerStage A t p n
  let S := Tower A t p
  let : IsLocalRing B := isLocalRing_towerStage A t p ht n
  obtain ⟨k, hk⟩ := SerrePositivity.IsFiniteLength.exists_isTorsionBySet_maximalIdeal_pow hV
  have hpB : (p : B) ∈ maximalIdeal B := by
    apply (le_of_isMaximal_towerStage A t p ht n (maximalIdeal B)).1
    simpa using Ideal.mem_map_of_mem (algebraMap A B) hp
  have hv : ∀ v : V, (p : B) ^ k • v = 0 := fun v =>
    hk (x := v) (a := ⟨_, Ideal.pow_mem_pow hpB k⟩)
  refine ⟨k, ?_⟩
  rw [Ideal.span_singleton_pow, Module.isTorsionBySet_span_singleton_iff]
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul s v =>
    have he : (p : S) ^ k = algebraMap B S ((p : B) ^ k) := by simp
    rw [he, smul_tmul', algebraMap_smul S ((p : B) ^ k), smul_tmul, hv, tmul_zero]
  | add x y hx hy => rw [smul_add, hx, hy, add_zero]

include hp in
/-- 完備塔からの係数制限で測る有限段加群の長さは、通常の段長さを段の階数で割った値。 -/
theorem completedNormalizedLength_tensor_eq_length (n : ℕ) (V : Type u)
    [AddCommGroup V] [Module (TowerStage A t p n) V]
    (hV : IsFiniteLength (TowerStage A t p n) V) :
    (completedNormalizedLength A t p ht).len
      (CompletedTower A t p ⊗[TowerStage A t p n] V) =
      (Module.length (TowerStage A t p n) V : ℝ≥0∞) /
        (stageRank h p n : ℝ≥0∞) := by
  let B := TowerStage A t p n
  let S := Tower A t p
  let C := CompletedTower A t p
  let W := S ⊗[B] V
  let Q := C ⊗[B] V
  obtain ⟨k, hk⟩ := exists_isTorsionBySet_p_pow_tensor A t p ht hp n V hV
  let E₁ : C ⊗[S] W ≃ₗ[C] Q :=
    AlgebraTensorModule.cancelBaseChange B S C C V
  let : Module S Q := Module.compHom Q (algebraMap S C)
  let : IsScalarTower S C Q := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let E : Q ≃ₗ[S] W := (E₁.symm.restrictScalars S).trans
    (adicCompletionTorsionTensorEquiv (Ideal.span {(p : S)})
      (Submodule.fg_span_singleton _) k hk)
  rw [completedNormalizedLength_len]
  change towerLengthFun A t p Q = _
  rw [towerLengthFun_congr E]
  exact towerLengthFun_tensor_eq_length A t p ht n V hV

end SerrePositivity.RootTowerLength

end CompletedTensorEvaluationPart

section CompletedQuotientEvaluationPart

set_option backward.isDefEq.respectTransparency false
open scoped TensorProduct ENNReal
namespace SerrePositivity.RootTowerLength
open Section2 IsLocalRing

variable (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {h : ℕ} (t : Fin h → A) (p : ℕ) [Fact p.Prime]
    (ht : ∀ i, t i ∈ maximalIdeal A) (hp : (p : A) ∈ maximalIdeal A)

/-- 有限段の完備塔上の作用を、商とテンソル積の代数構造と同じ加群構造で固定する。 -/
local instance completedQuotientStageModule (n : ℕ) :
    Module (TowerStage A t p n) (CompletedTower A t p) := Algebra.toModule

include hp in
/-- 有限段のイデアルを完備塔へ拡張した商の正規化長さは、有限段の通常商長さを
段の階数で割った値。零商も含み、イデアルの追加の性質は有限長性から必要な分だけ導く。 -/
theorem completedNormalizedLength_quotient_eq_length (n : ℕ) (I : Ideal (TowerStage A t p n))
    (hIquot : IsFiniteLength (TowerStage A t p n) (TowerStage A t p n ⧸ I)) :
    (completedNormalizedLength A t p ht).len
      (CompletedTower A t p ⧸ I.map (algebraMap (TowerStage A t p n) (CompletedTower A t p))) =
      (Module.length (TowerStage A t p n) (TowerStage A t p n ⧸ I) : ℝ≥0∞) /
        (stageRank h p n : ℝ≥0∞) := by
  rw [(completedNormalizedLength A t p ht).len_congr _ _
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot (CompletedTower A t p) I).toLinearEquiv]
  exact completedNormalizedLength_tensor_eq_length A t p ht hp n _ hIquot

end SerrePositivity.RootTowerLength

end CompletedQuotientEvaluationPart
