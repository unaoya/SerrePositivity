module

public import SerrePositivity.LengthAlgebra.Core
public import SerrePositivity.PerfectComplex.Free.Euler
public import SerrePositivity.CommutativeAlgebra.PowerTorsion.Category
public import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
public import SerrePositivity.HomologicalAlgebra.KoszulTower
public import SerrePositivity.CategoryTheory.IteratedCone

/-! # 写像錐と短完全列の Euler 評価

## 概要

短完全列のホモロジーの長完全列を長さ付きアーベル圏の Euler 定理へ渡し、ホモロジー上で零になる自己射の錐の有限長さから元のホモロジーの有限長さを導く。合成写像の錐の Euler 加法性（八面体）と、スカラーが零ホモトピックな場合の Koszul ホモロジーの長さの二項公式を与える。

## 方針

錐の長完全列を短完全列に分ける。零ホモトピーの存在より弱い、ホモロジーに誘導する写像の零性だけを使う。

## 規約

項の有限生成性・射影性、環の Noether 性、複体の有界性は使わない。長さの有限性と冪ねじれ性は三つの錐のホモロジーについてだけ要求する。

## 使われ方

Koszul の Euler 評価、CommutativeAlgebra/KoszulMultiplicity の公式。
-/

@[expose] public noncomputable section

universe u

section ShortExactEulerPart

namespace SerrePositivity
open CategoryTheory Limits
variable {R : Type u} [CommRing R] {J : Ideal R} (lam : NormalizedLength R J)

/-- 有界な短完全列で、冪ねじれ性と全ホモロジーの長さの有限性を確認すれば Euler 評価は加法的。 -/
theorem lambdaEuler_shortExact
    (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ)) (hS : S.ShortExact)
    (hb₂ : ∃ a b : ℤ, ∀ i, (i < a ∨ b < i) → IsZero (S.X₂.X i))
    (hb₃ : ∃ a b : ℤ, ∀ i, (i < a ∨ b < i) → IsZero (S.X₃.X i))
    (t₁ : ∀ i, IsPowTorsion J (S.X₁.homology i))
    (t₂ : ∀ i, IsPowTorsion J (S.X₂.homology i))
    (t₃ : ∀ i, IsPowTorsion J (S.X₃.homology i))
    (l₁ : ∀ i, lam.len (S.X₁.homology i) ≠ ⊤)
    (l₂ : ∀ i, lam.len (S.X₂.homology i) ≠ ⊤)
    (l₃ : ∀ i, lam.len (S.X₃.homology i) ≠ ⊤) :
    lambdaEuler lam S.X₂ = lambdaEuler lam S.X₁ + lambdaEuler lam S.X₃ := by
  exact LengthAlgebra.normalizedLength_euler_exact_sequence lam
    (fun i ↦ S.X₁.homology i) (fun i ↦ S.X₂.homology i) (fun i ↦ S.X₃.homology i)
    (fun i ↦ HomologicalComplex.homologyMap S.f i)
    (fun i ↦ HomologicalComplex.homologyMap S.g i)
    (fun i ↦ hS.δ i (i + 1) rfl)
    (fun i ↦ hS.homology_exact₂ i)
    (fun i ↦ hS.homology_exact₃ i (i + 1) rfl)
    (fun i ↦ hS.homology_exact₁ i (i + 1) rfl) t₁ t₂ t₃ l₁ l₂ l₃
    (by
      obtain ⟨a, b, hab⟩ := hb₂
      exact ⟨a, b, fun i hi ↦ isZero_homology_of_isZero_X S.X₂ i (hab i hi)⟩)
    (by
      obtain ⟨a, b, hab⟩ := hb₃
      exact ⟨a, b, fun i hi ↦ isZero_homology_of_isZero_X S.X₃ i (hab i hi)⟩)

end SerrePositivity

end ShortExactEulerPart

section ConeHomologyLengthPart

namespace SerrePositivity
open CategoryTheory Limits Pretriangulated
set_option backward.isDefEq.respectTransparency false
variable {R : Type u} [CommRing R] {J : Ideal R} (lam : NormalizedLength R J)

/-- ホモロジーに零写像を誘導する射の錐では、短完全列から長さの和の公式が得られる。 -/
theorem lambdaHomology_cone_of_homologyMap_eq_zero {P Q : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : P ⟶ Q) (hz : ∀ i, HomologicalComplex.homologyMap f i = 0) (q : ℤ)
    (hQ : IsPowTorsion J (Q.homology q)) (hP : IsPowTorsion J (P.homology (q + 1))) :
    IsPowTorsion J ((Cone.cone f).homology q) ∧
      lam.len ((Cone.cone f).homology q) =
        lam.len (Q.homology q) + lam.len (P.homology (q + 1)) := by
  let S := ShortComplex.mk _ _
    (comp_eq_zero_transport (Cone.S₃ f q (q + 1) rfl)
      (Cone.e q Q) (Cone.e q (Cone.cone f)) (Cone.e (q + 1) P)
      _ (Cone.δ f q (q + 1) rfl)
      (Cone.e_naturality q (CochainComplex.mappingCone.inr f)) (Cone.δ_square f q (q + 1) rfl))
  have : Mono S.f := (Cone.exact₂ f q).mono_g (hz q)
  have : Epi S.g := (Cone.exact₁ f q (q + 1) rfl).epi_f (hz (q + 1))
  have hs : S.ShortExact := ⟨Cone.exact₃ f q (q + 1) rfl⟩
  have ht : IsPowTorsion J ((Cone.cone f).homology q) :=
    (powTorsionModule J).prop_X₂_of_shortExact hs hQ hP
  exact ⟨ht, lam.len_add_of_exact _ _ _ S.f.hom S.g.hom
    ((ModuleCat.mono_iff_injective _).mp inferInstance)
    ((ModuleCat.epi_iff_surjective _).mp inferInstance)
    (LinearMap.exact_iff.mpr hs.exact.moduleCat_range_eq_ker.symm) ht⟩

/-- ホモロジーに零写像を誘導する射では、右のホモロジーの長さは錐の長さ以下。 -/
theorem lambdaHomology_le_cone_of_homologyMap_eq_zero
    {P Q : CochainComplex (ModuleCat.{u} R) ℤ} (f : P ⟶ Q) (q : ℤ)
    (hz : HomologicalComplex.homologyMap f q = 0)
    (tC : IsPowTorsion J ((Cone.cone f).homology q)) :
    lam.len (Q.homology q) ≤ lam.len ((Cone.cone f).homology q) := by
  have : Mono (HomologicalComplex.homologyMap (CochainComplex.mappingCone.inr f) q) :=
    (Cone.exact₂ f q).mono_g hz
  exact lam.len_le_of_injective
    (HomologicalComplex.homologyMap (CochainComplex.mappingCone.inr f) q).hom
    ((ModuleCat.mono_iff_injective _).mp inferInstance) tC

/-- 錐のホモロジーの長さが有限なら、右の元のホモロジーの長さも有限。 -/
theorem lambdaHomology_ne_top_of_cone_of_homologyMap_eq_zero
    {P Q : CochainComplex (ModuleCat.{u} R) ℤ} (f : P ⟶ Q) (q : ℤ)
    (hz : HomologicalComplex.homologyMap f q = 0)
    (tC : IsPowTorsion J ((Cone.cone f).homology q))
    (lC : lam.len ((Cone.cone f).homology q) ≠ ⊤) :
    lam.len (Q.homology q) ≠ ⊤ :=
  ne_top_of_le_ne_top lC (lambdaHomology_le_cone_of_homologyMap_eq_zero lam f q hz tC)

/-- ホモロジー上で零となる自己射の錐は Euler 評価零。
元のホモロジー長の有限性は、錐から導き、未知の仮定として渡さない。 -/
theorem lambdaEuler_self_cone_eq_zero_of_homologyMap_eq_zero
    {P : CochainComplex (ModuleCat.{u} R) ℤ} (f : P ⟶ P)
    (hz : ∀ q, HomologicalComplex.homologyMap f q = 0)
    (hP : ∃ a b : ℤ, ∀ i, (i < a ∨ b < i) → IsZero (P.X i))
    (hC : ∃ a b : ℤ, ∀ i, (i < a ∨ b < i) → IsZero ((Cone.cone f).X i))
    (tP : ∀ q, IsPowTorsion J (P.homology q))
    (tC : ∀ q, IsPowTorsion J ((Cone.cone f).homology q))
    (lC : ∀ q, lam.len ((Cone.cone f).homology q) ≠ ⊤) :
    lambdaEuler lam (Cone.cone f) = 0 := by
  have lP (q : ℤ) : lam.len (P.homology q) ≠ ⊤ :=
    lambdaHomology_ne_top_of_cone_of_homologyMap_eq_zero lam f q (hz q) (tC q) (lC q)
  simpa only [sub_self] using lambdaEuler_cone lam f hP hC tP tP tC lP lP lC

/-- ホモロジー上で零となる射では、錐の一つ前の次数が左のホモロジーへ全射する。 -/
theorem lambdaHomology_le_cone_prev_of_homologyMap_eq_zero
    {P Q : CochainComplex (ModuleCat.{u} R) ℤ} (f : P ⟶ Q) (q : ℤ)
    (hz : HomologicalComplex.homologyMap f q = 0)
    (tC : IsPowTorsion J ((Cone.cone f).homology (q - 1))) :
    lam.len (P.homology q) ≤ lam.len ((Cone.cone f).homology (q - 1)) := by
  have hrel : q - 1 + 1 = q := by omega
  have : Epi (Cone.δ f (q - 1) q hrel) := (Cone.exact₁ f (q - 1) q hrel).epi_f hz
  exact lam.len_le_of_surjective (Cone.δ f (q - 1) q hrel).hom
    ((ModuleCat.epi_iff_surjective _).mp inferInstance) tC

/-- 錐の冪ねじれ性は、零作用による単射から右のホモロジーへ移る。 -/
theorem isPowTorsion_of_cone_of_homologyMap_eq_zero
    {P Q : CochainComplex (ModuleCat.{u} R) ℤ} (f : P ⟶ Q) (q : ℤ)
    (hz : HomologicalComplex.homologyMap f q = 0)
    (tC : IsPowTorsion J ((Cone.cone f).homology q)) : IsPowTorsion J (Q.homology q) := by
  have : Mono (HomologicalComplex.homologyMap (CochainComplex.mappingCone.inr f) q) :=
    (Cone.exact₂ f q).mono_g hz
  exact IsPowTorsion.of_injective
    (HomologicalComplex.homologyMap (CochainComplex.mappingCone.inr f) q).hom
    ((ModuleCat.mono_iff_injective _).mp inferInstance) tC

end SerrePositivity

end ConeHomologyLengthPart

section ConeCompositionEulerPart

namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits

variable {R : Type u} [CommRing R] {J : Ideal R} (lam : NormalizedLength R J)

/-- 合成写像の錐の Euler 評価は、二つの写像の錐の Euler 評価の和。
有界性は最初の錐と合成の錐にだけ要求すれば十分である。 -/
theorem lambdaEuler_mappingCone_comp
    {P Q W : CochainComplex (ModuleCat.{u} R) ℤ} (f : P ⟶ Q) (g : Q ⟶ W)
    (hf : ∃ a b : ℤ, ∀ q, q < a ∨ b < q → IsZero ((Cone.cone f).X q))
    (hfg : ∃ a b : ℤ, ∀ q, q < a ∨ b < q → IsZero ((Cone.cone (f ≫ g)).X q))
    (tf : ∀ q, IsPowTorsion J ((Cone.cone f).homology q))
    (tfg : ∀ q, IsPowTorsion J ((Cone.cone (f ≫ g)).homology q))
    (tg : ∀ q, IsPowTorsion J ((Cone.cone g).homology q))
    (lf : ∀ q, lam.len ((Cone.cone f).homology q) ≠ ⊤)
    (lfg : ∀ q, lam.len ((Cone.cone (f ≫ g)).homology q) ≠ ⊤)
    (lg : ∀ q, lam.len ((Cone.cone g).homology q) ≠ ⊤) :
    lambdaEuler lam (Cone.cone (f ≫ g)) =
      lambdaEuler lam (Cone.cone f) + lambdaEuler lam (Cone.cone g) := by
  let a := (CochainComplex.mappingConeCompTriangle f g).mor₁
  let e := CochainComplex.mappingConeCompHomotopyEquiv f g
  have hb : ∃ b₁ b₂ : ℤ, ∀ q, q < b₁ ∨ b₂ < q → IsZero ((Cone.cone a).X q) := by
    obtain ⟨a₁, b₁, h₁⟩ := hf
    obtain ⟨a₂, b₂, h₂⟩ := hfg
    refine ⟨min a₁ a₂ - 1, max b₁ b₂, fun q hq ↦ ?_⟩
    rw [CochainComplex.mappingCone.isZero_X_iff]
    constructor
    · apply h₁
      rcases hq with hq | hq
      · left; omega
      · right; omega
    · apply h₂
      rcases hq with hq | hq
      · left; omega
      · right; omega
  have tc : ∀ q, IsPowTorsion J ((Cone.cone a).homology q) := fun q ↦
    IsPowTorsion.of_equiv (e.toHomologyIso q).toLinearEquiv (tg q)
  have lc : ∀ q, lam.len ((Cone.cone a).homology q) ≠ ⊤ := by
    intro q
    rw [← lam.len_congr _ _ (e.toHomologyIso q).toLinearEquiv]
    exact lg q
  have h := lambdaEuler_cone lam a hfg hb tf tfg tc lf lfg lc
  have he := lambdaEuler_eq_of_homotopyEquiv lam e
  change lambdaEuler lam (Cone.cone g) = lambdaEuler lam (Cone.cone a) at he
  rw [← he] at h
  change lambdaEuler lam (Cone.cone g) =
    lambdaEuler lam (Cone.cone (f ≫ g)) - lambdaEuler lam (Cone.cone f) at h
  linarith

/-- スカラー乗法の正冪の錐の Euler 評価は指数倍。
条件は各正冪の錐にのみ課し、元の複体には長さ・冪ねじれの条件を課さない。 -/
theorem lambdaEuler_scalarCone_pow (P : CochainComplex (ModuleCat.{u} R) ℤ) (a : R)
    (hb : ∀ n : ℕ, 0 < n → ∃ b₁ b₂ : ℤ, ∀ q,
      q < b₁ ∨ b₂ < q → IsZero ((Cone.cone (smulId (a ^ n) P)).X q))
    (ht : ∀ n : ℕ, 0 < n → ∀ q,
      IsPowTorsion J ((Cone.cone (smulId (a ^ n) P)).homology q))
    (hl : ∀ n : ℕ, 0 < n → ∀ q,
      lam.len ((Cone.cone (smulId (a ^ n) P)).homology q) ≠ ⊤)
    (k : ℕ) (hk : 0 < k) :
    lambdaEuler lam (Cone.cone (smulId (a ^ k) P)) =
      (k : ℝ) * lambdaEuler lam (Cone.cone (smulId a P)) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  induction n with
  | zero => simp
  | succ n ih =>
      have hc : smulId (a ^ (n + 1)) P ≫ smulId a P = smulId (a ^ (n + 2)) P := by
        simp [smulId, ← mul_smul, pow_succ, mul_comm]
      have ht₁ := ht (n + 1) (by omega)
      have hl₁ := hl (n + 1) (by omega)
      have ht₂ := ht (n + 2) (by omega)
      have hl₂ := hl (n + 2) (by omega)
      have hb₂ := hb (n + 2) (by omega)
      have ht₃ := ht 1 one_pos
      have hl₃ := hl 1 one_pos
      rw [pow_one] at ht₃ hl₃
      rw [← hc] at ht₂ hl₂ hb₂
      have he := lambdaEuler_mappingCone_comp lam (smulId (a ^ (n + 1)) P)
        (smulId a P) (hb (n + 1) (by omega)) hb₂ ht₁ ht₂ ht₃ hl₁ hl₂ hl₃
      rw [hc] at he
      rw [he, ih (by omega)]
      push_cast
      ring

end SerrePositivity

end ConeCompositionEulerPart

section KoszulHomologyLengthPart

namespace SerrePositivity

open CategoryTheory Limits Pretriangulated

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R]

variable {J : Ideal R} (lam : NormalizedLength R J)

/-- 零ホモトピックな射の錐の長さ公式。ホモロジー零の一般定理への互換入口。 -/
lemma lambdaHomology_null_cone {P Q : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : P ⟶ Q) (hf : Homotopy f 0) (q : ℤ)
    (hQ : IsPowTorsion J (Q.homology q)) (hP : IsPowTorsion J (P.homology (q + 1))) :
    IsPowTorsion J ((Cone.cone f).homology q) ∧
      lam.len ((Cone.cone f).homology q) =
        lam.len (Q.homology q) + lam.len (P.homology (q + 1)) :=
  lambdaHomology_cone_of_homologyMap_eq_zero lam f
    (fun i ↦ by simpa only [HomologicalComplex.homologyMap_zero] using hf.homologyMap_eq i)
    q hQ hP

/-- 零スカラーの Koszul 構成は、各次数の冪ねじれ性と長さの有限性を保つ。
有界性・射影性を使わず、各段の短完全列だけを用いる。 -/
lemma lambdaHomology_koszul_null_finite {e : ℕ} (x : Fin e → R)
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hx : ∀ j, Nonempty (Homotopy (smulId (x j) P) 0))
    (ht : ∀ q, IsPowTorsion J (P.homology q)) (hfin : ∀ q, lam.len (P.homology q) ≠ ⊤) :
    (∀ q, IsPowTorsion J ((koszulComplexOn x P).homology q)) ∧
    (∀ q, lam.len ((koszulComplexOn x P).homology q) ≠ ⊤) := by
  induction e with
  | zero => exact ⟨ht, hfin⟩
  | succ e ih =>
    obtain ⟨ht', hfin'⟩ := ih (Fin.init x) (fun j ↦ hx j.castSucc)
    have hn : Nonempty (Homotopy
        (smulId (x (Fin.last e)) (koszulComplexOn (Fin.init x) P)) 0) :=
      (nonempty_homotopy_smul_id_zero_iff _ _).mpr
        (koszulComplexOn_smul_zero (Fin.init x) P
          (fun j ↦ (nonempty_homotopy_smul_id_zero_iff _ _).mp (hx j.castSucc))
          (x (Fin.last e)) ((nonempty_homotopy_smul_id_zero_iff _ _).mp (hx (Fin.last e))))
    have hc (q : ℤ) := lambdaHomology_null_cone lam _ hn.some q (ht' q) (ht' (q + 1))
    refine ⟨fun q ↦ (hc q).1, fun q ↦ ?_⟩
    change lam.len ((Cone.cone _).homology q) ≠ ⊤
    rw [(hc q).2]
    exact ENNReal.add_ne_top.mpr ⟨hfin' q, hfin' (q + 1)⟩

/-- 実際の Koszul 塔の長さは、共通の錐の係数作用素で計算される。
有限性の確認と数値漸化式の一般論を分離し、無限分解にも適用できる。 -/
lemma lambdaHomology_koszul_null_pow {e : ℕ} (x : Fin e → R)
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hx : ∀ j, Nonempty (Homotopy (smulId (x j) P) 0))
    (ht : ∀ q, IsPowTorsion J (P.homology q)) (hfin : ∀ q, lam.len (P.homology q) ≠ ⊤) :
    (∀ q, IsPowTorsion J ((koszulComplexOn x P).homology q)) ∧
    (∀ q, lam.len ((koszulComplexOn x P).homology q) ≠ ⊤) ∧
    ∀ q, (lam.len ((koszulComplexOn x P).homology q)).toReal =
      ((cochainLengthShift + 1) ^ e) (fun q ↦ (lam.len (P.homology q)).toReal) q := by
  have hf := lambdaHomology_koszul_null_finite lam x P hx ht hfin
  refine ⟨hf.1, hf.2, ?_⟩
  let y : ℕ → R := fun j ↦ if h : j < e then x ⟨j, h⟩ else 0
  have hy : (fun j : Fin e ↦ y j) = x := by funext j; simp [y, j.isLt]
  have hh (k : ℕ) (hk : k ≤ e) (j : Fin k) :
      Nonempty (Homotopy (smulId (y j) P) 0) := by
    simpa [y, show (j : ℕ) < e by omega] using hx ⟨j, by omega⟩
  have hb := coneLength_pow_of_recurrence
    (fun k q ↦ (lam.len ((koszulComplexOn (fun j : Fin k ↦ y j) P).homology q)).toReal) e
    (fun k hk q ↦ by
      have hf' := lambdaHomology_koszul_null_finite lam _ P (hh k (by omega)) ht hfin
      have hn : Nonempty (Homotopy
          (smulId (y k) (koszulComplexOn (fun j : Fin k ↦ y j) P)) 0) :=
        (nonempty_homotopy_smul_id_zero_iff _ _).mpr
          (koszulComplexOn_smul_zero _ P
            (fun j ↦ (nonempty_homotopy_smul_id_zero_iff _ _).mp (hh k (by omega) j))
            (y k) ((nonempty_homotopy_smul_id_zero_iff _ _).mp
              (by simpa only [y, dite_eq_left hk, smulId] using hx ⟨k, hk⟩)))
      have hc := lambdaHomology_null_cone lam _ hn.some q (hf'.1 q) (hf'.1 (q + 1))
      have hre := congrArg ENNReal.toReal hc.2
      rw [ENNReal.toReal_add (hf'.2 q) (hf'.2 (q + 1))] at hre
      exact hre)
  intro q
  have hbq := congrFun hb q
  change (lam.len ((koszulComplexOn (fun j : Fin e ↦ y j) P).homology q)).toReal =
    ((cochainLengthShift + 1) ^ e) (fun q ↦ (lam.len (P.homology q)).toReal) q at hbq
  rw [hy] at hbq
  exact hbq

/-- 零ホモトピックなスカラーの Koszul ホモロジー長の二項係数公式。 -/
theorem lambdaHomology_koszul_null_binomial {e : ℕ} (x : Fin e → R)
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hx : ∀ j, Nonempty (Homotopy (smulId (x j) P) 0))
    (ht : ∀ q, IsPowTorsion J (P.homology q)) (hfin : ∀ q, lam.len (P.homology q) ≠ ⊤) (q : ℤ) :
    (lam.len ((koszulComplexOn x P).homology q)).toReal =
      ∑ j ∈ Finset.range (e + 1), (e.choose j : ℝ) * (lam.len (P.homology (q + j))).toReal := by
  rw [(lambdaHomology_koszul_null_pow lam x P hx ht hfin).2.2 q, coneLength_binomial]

end SerrePositivity

end KoszulHomologyLengthPart
