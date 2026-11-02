module

public import SerrePositivity.CommutativeAlgebra.Koszul.Basic
public import SerrePositivity.HomologicalAlgebra.Complex.ConeLES
public import Mathlib.Algebra.Homology.HomotopyCategory.HomologicalFunctor
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
public import Mathlib.Algebra.Homology.ShortComplex.Linear
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.RingTheory.Regular.RegularSequence
public import SerrePositivity.HomologicalAlgebra.Resolution
public import SerrePositivity.HomologicalAlgebra.KProjectiveLift
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import SerrePositivity.HomologicalAlgebra.Tor

/-!
# Koszul 複体の完全性と射影分解

## 概要

正則列 `x` の Koszul 複体 `K(x; R)` が `R/(x)` の自由分解であること、すなわち `H^i(K(x)) = 0 (i ≠ 0)`
かつ `H^0(K(x)) ≅ R/(x)` であることを示す（`isKoszulResolution_of_isWeaklyRegular`）。この性質を
`IsKoszulResolution x` と名付け、これをみたす `K(x)` を Mathlib の射影分解に仕立て
（`koszulResolution`）、`Tor_i^A(C, A/(z))` を Koszul ホモロジー `H_i(φ z; C)` で計算する
（`torAlgKoszulEquiv`。論文 (3.9)）。Koszul 複体の定義と項の性質は `Koszul/Basic.lean`。

## 証明の筋道

`n` についての帰納法。`K(x_0, …, x_n) = Cone(x_n • 𝟙 : K' → K')`（`K' = K(x_0, …, x_{n-1})`）なので、
写像錐の長完全列（`HomologicalAlgebra/ConeLES.lean` の `Cone.exact₁₂₃` を `φ = x_n • 𝟙 K'` に適用）

  `H^i(K') →(x_n) H^i(K') → H^i(Cone) → H^{i+1}(K') →(x_n) H^{i+1}(K')`

が使える。帰納法の仮定で `H^i(K') = 0 (i ≠ 0)`、`H^0(K') ≅ R/I`（`I = (x_0, …, x_{n-1})`）とすると、

- `i ≠ 0, -1` では両端が零なので `H^i(Cone) = 0`。
- `i = -1` では `H^{-1}(Cone) → H^0(K') →(x_n) H^0(K')` で、`x_n` が `R/I` 上で正則（非零因子）なので
  第二の射が単射、よって `H^{-1}(Cone) = 0`。正則性を使うのはここだけである。
- `i = 0` では `H^0(K') →(x_n) H^0(K') → H^0(Cone) → 0` から `H^0(Cone) ≅ (R/I)/x_n = R/(I, x_n)`。
  これには正則性は要らない（`homologyZeroEquiv_succ`、`koszulComplex_homology_zero_equiv`）。

## 内容

1. `IsKoszulResolution` と完全性の証明。
2. 添加写像 `koszulAugmentation : K(x) → (R/(x))[0]`。`K(x)` が分解なら擬同型で、K 射影的な複体
   からの持ち上げ（`HomologicalAlgebra/KProjectiveLift.lean`）の行き先になる
   （`PerfectComplex/KoszulGeneration.lean`）。
3. `IsResolutionOf`（`HomologicalAlgebra/Resolution.lean`）への変換と、Mathlib の
   `ProjectiveResolution` への変換 `koszulResolution`。
4. `Tor` との同一視 `torAlgKoszulIso`、`torAlgKoszulEquiv`。
-/

@[expose] public section

universe u

open CategoryTheory Limits Pretriangulated

namespace SerrePositivity

variable {R : Type u} [CommRing R]

/-- `K(x; R)` が `R/(x)` の分解であること：`0` 以外の次数でホモロジーが零で、`0` 次のホモロジーは
`R/(x)`（`x` の生成するイデアルによる商環）と線形同型。同型を `Nonempty` で包んでいるので `Prop`
である。正則局所環の正則パラメータ系についてはこれが成り立つ（A1、`CommutativeAlgebra/RegularLocalRing.lean`
から `isKoszulResolution_of_isWeaklyRegular` で）が、Lemma 3.5b の証明はこの性質だけを使うので、
仮定としてこの形で受け取る。 -/
structure IsKoszulResolution {n : ℕ} (x : Fin n → R) : Prop where
  /-- `i ≠ 0` でホモロジーは零（`K(x)` は `0` 次以外で完全）。 -/
  isZero : ∀ i : ℤ, i ≠ 0 → IsZero ((koszulComplex x).homology i)
  /-- `0` 次のホモロジーと `R/(x)` の線形同型の存在。 -/
  equiv : Nonempty ((koszulComplex x).homology 0 ≃ₗ[R] R ⧸ Ideal.span (Set.range x))

/-- `n = 0`：空列の Koszul 複体 `K(∅) = R`（`0` 次に集中）は `R/(0) = R` の分解である。
帰納法の出発点。 -/
lemma isKoszulResolution_zero (x : Fin 0 → R) : IsKoszulResolution x where
  isZero i hi := by
    rw [koszulComplex_zero]
    exact HomologicalComplex.isZero_single_obj_homology _ _ _ _ hi
  equiv := by
    rw [koszulComplex_zero]
    refine ⟨(HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0
      (ModuleCat.of R R)).toLinearEquiv.trans (Submodule.quotEquivOfEqBot _ ?_).symm⟩
    rw [Set.range_eq_empty, Ideal.span_empty]

/-- 弱正則列 `x_0, …, x_n` について、はじめの `n` 個 `x_0, …, x_{n-1}` も弱正則列で、最後の元 `x_n` は
`R/(x_0, …, x_{n-1})` 上で正則（非零因子）である。Mathlib の `IsWeaklyRegular` の、列の連結
`append` についての特徴づけを、列を `x_0, …, x_{n-1}` と `[x_n]` に分けて適用する。帰納法で
正則性の仮定を分解するのに使う。 -/
lemma isWeaklyRegular_init_and_isSMulRegular_last {n : ℕ} (x : Fin (n + 1) → R)
    (hx : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn x)) :
    RingTheory.Sequence.IsWeaklyRegular R (List.ofFn (Fin.init x)) ∧
      IsSMulRegular (R ⧸ Ideal.span (Set.range (Fin.init x))) (x (Fin.last n)) := by
  rw [List.ofFn_succ', List.concat_eq_append, RingTheory.Sequence.isWeaklyRegular_append_iff,
    RingTheory.Sequence.isWeaklyRegular_singleton_iff] at hx
  change RingTheory.Sequence.IsWeaklyRegular R (List.ofFn (Fin.init x)) ∧
    IsSMulRegular (R ⧸ (Ideal.ofList (List.ofFn (Fin.init x)) • ⊤ : Submodule R R))
      (x (Fin.last n)) at hx
  refine ⟨hx.1, ?_⟩
  have hset : {r : R | r ∈ List.ofFn (Fin.init x)} = Set.range (Fin.init x) := by
    ext; simp [List.mem_ofFn]
  have h : (Ideal.ofList (List.ofFn (Fin.init x)) • ⊤ : Submodule R R) =
      Ideal.span (Set.range (Fin.init x)) := by
    rw [Ideal.smul_eq_mul, Ideal.mul_top, Ideal.ofList, hset]
  rw [h] at hx
  exact hx.2

/-- 帰納段の `0` 次：`H^1(K') = 0` と `H^0(K') ≃ R/I` から、`H^0(Cone(a • 𝟙 K')) ≃ R/(I, a)`。
長完全列 `H^0(K') →(a) H^0(K') → H^0(Cone) → H^1(K') = 0` から `H^0(Cone)` は `a` 倍写像の余核。
同型 `e` で移すと `(R/I)/(a) = R/(I + (a))`、そして `I + (a) = (x)`。正則性は要らない。 -/
theorem homologyZeroEquiv_succ {n : ℕ} (x : Fin (n + 1) → R)
    (h1 : IsZero ((koszulComplex (Fin.init x)).homology 1))
    (e : (koszulComplex (Fin.init x)).homology 0 ≃ₗ[R] R ⧸ Ideal.span (Set.range (Fin.init x))) :
    Nonempty ((koszulComplex x).homology 0 ≃ₗ[R] R ⧸ Ideal.span (Set.range x)) := by
  set K := koszulComplex (Fin.init x) with hK
  set a := x (Fin.last n) with ha
  set I : Ideal R := Ideal.span (Set.range (Fin.init x)) with hI
  have hmap : HomologicalComplex.homologyMap (smulId a K) 0 = a • 𝟙 (K.homology 0) := by
    rw [smulId, homologyMap_smul, HomologicalComplex.homologyMap_id]
  change Nonempty ((Cone.cone (smulId a K)).homology 0 ≃ₗ[R] R ⧸ Ideal.span (Set.range x))
  have h2 := Cone.exact₂ (smulId a K) 0
  have h3 := Cone.exact₃ (smulId a K) 0 1 rfl
  have hepi : Epi (HomologicalComplex.homologyMap
      (CochainComplex.mappingCone.inr (smulId a K)) 0) :=
    h3.epi_f (h1.eq_zero_of_tgt _)
  have hsurj : Function.Surjective
      (HomologicalComplex.homologyMap (CochainComplex.mappingCone.inr (smulId a K)) 0).hom :=
    (ModuleCat.epi_iff_surjective _).mp hepi
  have hrk : LinearMap.range (HomologicalComplex.homologyMap (smulId a K) 0).hom =
      LinearMap.ker (HomologicalComplex.homologyMap
        (CochainComplex.mappingCone.inr (smulId a K)) 0).hom :=
    (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mp h2
  rw [hmap] at hrk
  -- `Q = a • (R/I) ⊆ R/I`
  let Q : Submodule R (R ⧸ I) := LinearMap.range (a • LinearMap.id : (R ⧸ I) →ₗ[R] R ⧸ I)
  have hmapQ : (LinearMap.range (a • 𝟙 (K.homology 0)).hom).map (e : K.homology 0 →ₗ[R] R ⧸ I)
      = Q := by
    rw [← LinearMap.range_comp]
    have : (e : K.homology 0 →ₗ[R] R ⧸ I) ∘ₗ (a • 𝟙 (K.homology 0)).hom =
        (a • LinearMap.id : (R ⧸ I) →ₗ[R] R ⧸ I) ∘ₗ (e : K.homology 0 →ₗ[R] R ⧸ I) := by
      ext y
      simp
    rw [this, LinearMap.range_comp_of_range_eq_top _ e.range]
  have hQ : Q = Submodule.span R {Submodule.Quotient.mk a} := by
    ext y
    simp only [Q, LinearMap.mem_range, LinearMap.smul_apply, LinearMap.id_apply,
      Submodule.mem_span_singleton]
    constructor
    · rintro ⟨z, rfl⟩
      obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective I z
      exact ⟨r, by rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, smul_eq_mul,
        smul_eq_mul, mul_comm]⟩
    · rintro ⟨r, rfl⟩
      exact ⟨Submodule.Quotient.mk r, by rw [← Submodule.Quotient.mk_smul,
        ← Submodule.Quotient.mk_smul, smul_eq_mul, smul_eq_mul, mul_comm]⟩
  have hsup : Submodule.map I.mkQ (I ⊔ Submodule.span R {a}) = Q := by
    rw [Submodule.map_sup, Submodule.mkQ_map_self, Submodule.map_span, Set.image_singleton,
      bot_sup_eq, hQ, Submodule.mkQ_apply]
  have hrange : Set.range x = insert a (Set.range (Fin.init x)) := by
    have := Fin.range_snoc (Fin.init x) (x (Fin.last n))
    rwa [Fin.snoc_init_self] at this
  have hspan : I ⊔ Submodule.span R {a} = Ideal.span (Set.range x) := by
    rw [hI, hrange]
    change _ = Submodule.span R _
    rw [Submodule.span_insert, sup_comm]
  have eq₁ : (K.homology 0 ⧸ LinearMap.range (a • 𝟙 (K.homology 0)).hom) ≃ₗ[R]
      (R ⧸ I) ⧸ Q :=
    Submodule.Quotient.equiv _ Q e hmapQ
  have eq₂ : ((R ⧸ I) ⧸ Submodule.map I.mkQ (I ⊔ Submodule.span R {a})) ≃ₗ[R]
      R ⧸ (I ⊔ Submodule.span R {a}) :=
    Submodule.quotientQuotientEquivQuotient I (I ⊔ Submodule.span R {a}) le_sup_left
  exact ⟨(LinearMap.quotKerEquivOfSurjective _ hsurj).symm.trans
    ((Submodule.quotEquivOfEq _ _ hrk.symm).trans (eq₁.trans
      ((Submodule.quotEquivOfEq _ _ hsup.symm).trans
        (eq₂.trans (Submodule.quotEquivOfEq _ _ hspan)))))⟩

/-- 任意の列 `x` について `H^0(K(x)) ≃ R/(x)`。正則性は要らない。`n` についての帰納法で
`homologyZeroEquiv_succ` を使う（`H^1(K') = 0` は項が零だから）。Lemma 3.4 と Lemma 3.5b の
正規化長さ側で、`λ(C/zC)` を Koszul ホモロジーの `0` 次として扱うのに使う。 -/
theorem koszulComplex_homology_zero_equiv :
    ∀ {n : ℕ} (x : Fin n → R),
      Nonempty ((koszulComplex x).homology 0 ≃ₗ[R] R ⧸ Ideal.span (Set.range x))
  | 0, x => (isKoszulResolution_zero x).equiv
  | _ + 1, x =>
    homologyZeroEquiv_succ x (koszulComplex_isZero_homology_of_pos _ 1 one_pos)
      (koszulComplex_homology_zero_equiv (Fin.init x)).some

/-- 帰納段：`K' = K(x_0, …, x_{n-1})` が `R/I` の分解で、`a = x_n` が `R/I` 上で正則なら、
`K(x) = Cone(a • 𝟙 K')` は `R/(I, a) = R/(x)` の分解である。`0` 次は `homologyZeroEquiv_succ`。
`i ≠ 0` のホモロジーは、`i = -1` では連結射 `δ : H^{-1}(Cone) → H^0(K')` が単射（`H^{-1}(K') = 0`）で、
かつ `δ` のあとに `a` 倍を合成すると零（長完全列）、`a` 倍は単射（正則性）なので `δ = 0`、よって
`H^{-1}(Cone) = 0`。他の `i` では長完全列の両端 `H^i(K')`、`H^{i+1}(K')` が零。 -/
theorem isKoszulResolution_succ {n : ℕ} (x : Fin (n + 1) → R)
    (ih : IsKoszulResolution (Fin.init x))
    (hreg : IsSMulRegular (R ⧸ Ideal.span (Set.range (Fin.init x))) (x (Fin.last n))) :
    IsKoszulResolution x := by
  set K := koszulComplex (Fin.init x) with hK
  set a := x (Fin.last n) with ha
  set I : Ideal R := Ideal.span (Set.range (Fin.init x)) with hI
  obtain ⟨e⟩ := ih.equiv
  have hmap : ∀ i, HomologicalComplex.homologyMap (smulId a K) i = a • 𝟙 (K.homology i) := by
    intro i
    rw [smulId, homologyMap_smul, HomologicalComplex.homologyMap_id]
  have hinj : Function.Injective (fun y : K.homology 0 ↦ a • y) := by
    intro y z hyz
    apply e.injective
    apply hreg
    simpa only [map_smul] using congrArg e hyz
  have hmono : Mono (a • 𝟙 (K.homology 0)) := by
    rw [ModuleCat.mono_iff_injective]
    intro y z h
    exact hinj (by simpa using h)
  have h10 : (-1 : ℤ) + 1 = 0 := by norm_num
  refine ⟨fun i hi ↦ ?_, homologyZeroEquiv_succ x (ih.isZero 1 one_ne_zero) e⟩
  change IsZero ((Cone.cone (smulId a K)).homology i)
  by_cases hi1 : i = -1
  · subst hi1
    have h3 := Cone.exact₃ (smulId a K) (-1) 0 h10
    have hz : IsZero (K.homology (-1)) := ih.isZero (-1) (by norm_num)
    have hmonoδ : Mono (Cone.δ (smulId a K) (-1) 0 h10) := h3.mono_g (hz.eq_zero_of_src _)
    have hcomp : Cone.δ (smulId a K) (-1) 0 h10 ≫
        HomologicalComplex.homologyMap (smulId a K) 0 = 0 :=
      comp_eq_zero_transport (Cone.S₁ (smulId a K) (-1) 0 h10) _ _ _ _ _
        (Cone.δ_square (smulId a K) (-1) 0 h10) (Cone.e_naturality 0 (smulId a K))
    rw [hmap 0] at hcomp
    have hδ : Cone.δ (smulId a K) (-1) 0 h10 = 0 := zero_of_comp_mono _ hcomp
    rw [IsZero.iff_id_eq_zero, ← cancel_mono (Cone.δ (smulId a K) (-1) 0 h10), Category.id_comp,
      zero_comp, hδ]
  · have h3 := Cone.exact₃ (smulId a K) i (i + 1) rfl
    exact h3.isZero_of_both_isZero (ih.isZero i hi) (ih.isZero (i + 1) (by omega))

/-- **Koszul 複体の完全性**：`x` が弱正則列なら `K(x; R)` は `R/(x)` の分解である。`n` についての
帰納法で、`isWeaklyRegular_init_and_isSMulRegular_last` で仮定を分解し、`isKoszulResolution_succ` を
使う。正則局所環の正則パラメータ系は弱正則列（A1、`CommutativeAlgebra/RegularLocalRing.lean`）なので、
Lemma 3.5b の前提 `IsKoszulResolution z` がここから出る。 -/
theorem isKoszulResolution_of_isWeaklyRegular {n : ℕ} (x : Fin n → R)
    (hx : RingTheory.Sequence.IsWeaklyRegular R (List.ofFn x)) : IsKoszulResolution x := by
  induction n with
  | zero => exact isKoszulResolution_zero x
  | succ n ih =>
    obtain ⟨hinit, hreg⟩ := isWeaklyRegular_init_and_isSMulRegular_last x hx
    exact isKoszulResolution_succ x (ih _ hinit) hreg

end SerrePositivity

end

/-!
## Koszul 複体を射影分解に仕立てる

`K(x)` が `R/(x)` の分解（`IsKoszulResolution x`）なら、`IsResolutionOf`
（`HomologicalAlgebra/Resolution.lean`）の条件をみたす（各項は有限自由なので射影的）。したがって
`toChain K(x)` は `ModuleCat.of R (R ⧸ (x))` の Mathlib の意味での `ProjectiveResolution` になる
（`koszulResolution`）。

その前に、添加写像 `koszulAugmentation : K(x) → (R/(x))[0]` を作る。`0` 次の成分は
`K^0 → H^0(K(x)) ≅ R/(x)` で、`K(x)` が分解なら擬同型である。デヴィサージュ
（`PerfectComplex/KoszulGeneration.lean`）では、`Q → k[0]` をこの擬同型に沿って `Q → K(z)` に
持ち上げる。
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace SerrePositivity

variable {R : Type u} [CommRing R]

/-! ## 添加写像 -/

section augmentation

variable {n : ℕ} {x : Fin n → R}

/-- Koszul 複体の微分 `K^0 → K^1` は零（`1` 次の項が零だから）。添加写像を作るときの前提。 -/
lemma koszulComplex_d_zero_one : (koszulComplex x).d 0 1 = 0 :=
  (koszulComplex_isZero_X_of_pos x 1 one_pos).eq_of_tgt _ _

variable (hx : IsKoszulResolution x)

/-- `IsKoszulResolution` のもつ線形同型 `H^0(K(x)) ≃ R/(x)` を、`ModuleCat` の同型にしたもの。 -/
noncomputable def koszulH0Iso :
    (koszulComplex x).homology 0 ≅ ModuleCat.of R (R ⧸ Ideal.span (Set.range x)) :=
  hx.equiv.some.toModuleIso

/-- 添加写像 `K(x) → (R/(x))[0]`。`0` 次の成分は `K^0 → H^0(K(x)) ≅ R/(x)`、他の次数は零
（`HomologicalAlgebra/KProjectiveLift.lean` の `toSingleOfHomology`）。 -/
noncomputable def koszulAugmentation :
    koszulComplex x ⟶
      (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
        (ModuleCat.of R (R ⧸ Ideal.span (Set.range x))) :=
  toSingleOfHomology (koszulComplex x) koszulComplex_d_zero_one (koszulH0Iso hx).hom

/-- `K(x)` が `R/(x)` の分解なら、添加写像は擬同型である：`0` 次では同型を誘導し、他の次数では両辺の
ホモロジーが零だから（`quasiIso_toSingleOfHomology`）。 -/
instance quasiIso_koszulAugmentation : QuasiIso (koszulAugmentation hx) :=
  quasiIso_toSingleOfHomology _ _ _ hx.isZero

end augmentation

/-! ## 射影分解 -/

variable {n : ℕ} (x : Fin n → R) (hx : IsKoszulResolution x)

/-- `K(x)` が `R/(x)` の分解なら、`IsResolutionOf (K(x)) (R/(x))` の形にもなる：正の次数で零、各項が
射影的（有限自由）、ホモロジーが `0` 次に集中、`H^0 ≅ R/(x)`。 -/
noncomputable def isResolutionOf_koszul :
    IsResolutionOf (koszulComplex x) (ModuleCat.of R (R ⧸ Ideal.span (Set.range x))) where
  isZero_X := koszulComplex_isZero_X_of_pos x
  projective := koszulComplex_projective_X x
  isZero_homology := hx.isZero
  homologyZeroIso := hx.equiv.some.toModuleIso

/-- **Koszul 分解**：`K(x)` が `R/(x)` の分解なら、`toChain K(x)`（ℕ 添字の chain 複体に制限したもの）は
`ModuleCat.of R (R ⧸ (x))` の Mathlib の意味での射影分解である。`Tor` を Koszul 複体で計算するための
形。 -/
noncomputable def koszulResolution :
    ProjectiveResolution (ModuleCat.of R (R ⧸ Ideal.span (Set.range x))) :=
  (isResolutionOf_koszul x hx).toProjectiveResolution

end SerrePositivity

end

/-!
## `Tor` と Koszul ホモロジー

`z` の Koszul 複体が `A/(z)` の分解なら、`A` 代数 `C`（構造は `φ : A →+* C`）に対して

  `Tor_i^A(C, A/(z)) ≅ H_i(φ z; C)`

（左辺は `TorAlg φ i (A ⧸ (z))`、右辺は `K(φ z; C)` の `-i` 次ホモロジー）。論文 (3.9) の形で、
`Tor` を cochain 分解で計算すること（`HomologicalAlgebra/Tor.lean` の `torIsoCochain`）と、基底変更が
Koszul 複体と両立すること（`baseChangeKoszulIso`）による。正規化長さ `λ` で `Tor` を測るとき
（Lemma 3.4、Corollary 2.6）に、右辺の Koszul ホモロジーについての仮定 (3.9) に帰着させる。
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace SerrePositivity

variable {A C : Type u} [CommRing A] [CommRing C] (φ : A →+* C)

/-- **`Tor` と Koszul ホモロジー**：`K(z)` が `A/(z)` の分解なら、`Tor_i^A(C, A/(z)) ≅ H^{-i}(K(φ z; C))`。
`torIsoCochain` で `H^{-i}(K(z) ⊗_A C)` に移し、`baseChangeKoszulIso` で `K(z) ⊗_A C ≅ K(φ z; C)` とする。 -/
noncomputable def torAlgKoszulIso {n : ℕ} (z : Fin n → A) (hz : IsKoszulResolution z) (i : ℕ) :
    ((ModuleCat.extendScalars.{u, u, u} φ).leftDerived i).obj
        (ModuleCat.of A (A ⧸ Ideal.span (Set.range z))) ≅
      (koszulComplex (φ ∘ z)).homology (-(i : ℤ)) :=
  torIsoCochain φ (isResolutionOf_koszul z hz) i ≪≫
    (HomologicalComplex.homologyFunctor _ _ (-(i : ℤ))).mapIso (baseChangeKoszulIso φ z)

/-- `torAlgKoszulIso` を `C` 線形同値 `TorAlg φ i (A ⧸ (z)) ≃ₗ[C] koszulHomologySelf (φ ∘ z) i` として
述べたもの。正規化長さで測るときに使う形（`IntersectionMultiplicity/NormalizedTor.lean`）。 -/
noncomputable def torAlgKoszulEquiv {n : ℕ} (z : Fin n → A) (hz : IsKoszulResolution z) (i : ℕ) :
    TorAlg φ i (A ⧸ Ideal.span (Set.range z)) ≃ₗ[C] koszulHomologySelf (φ ∘ z) i :=
  (torAlgKoszulIso φ z hz i).toLinearEquiv

end SerrePositivity

end
