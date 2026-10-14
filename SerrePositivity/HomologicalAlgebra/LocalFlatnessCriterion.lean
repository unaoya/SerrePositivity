module

public import SerrePositivity.HomologicalAlgebra.TorLES
public import SerrePositivity.CommutativeAlgebra.FiniteLength
public import Mathlib.RingTheory.Filtration
public import Mathlib.RingTheory.Flat.Tensor
public import Mathlib.RingTheory.LocalRing.RingHom.Basic
public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.CategoryTheory.Monoidal.Tor

/-! # 局所平坦性判定法

## 概要

`A → B` を Noether 局所環の局所準同型、`M` を有限生成 `B` 加群とする。
`Tor_1^A(M, k) = 0`（`k` は `A` の剰余体）なら、`M` は `A` 上平坦である
（Matsumura『可換環論』定理 22.3 の一部）。

## 方針

1. **有限長の加群**：`Tor_1^A(M, -)` は短完全列の両端で消えれば中央でも消える。
   有限長の加群は単純加群 `≅ k` による拡大の繰り返しなので、`Tor_1^A(M, N) = 0`。
2. **一般のイデアル**：Mathlib のイデアルによる平坦性判定から、各イデアル `I` について
   `M ⊗ I → M` の単射性を示せばよい。核の元 `x` をとる。Artin–Rees から
   `I ∩ m^{n+c} ⊆ m^n I` となる `c` がある。短完全列
   `0 → I/(I ∩ m^{n+c}) → A/m^{n+c} → A/(I + m^{n+c}) → 0` の右端は有限長なので、
   1 と Tor の長完全列から `M ⊗ I/(I ∩ m^{n+c}) → M ⊗ A/m^{n+c}` は単射。
   よって `x` は `M ⊗ I/m^n I = (M ⊗ I)/m^n(M ⊗ I)` で零、つまり `x ∈ m^n (M ⊗ I)`。
   `M ⊗ I` は有限生成 `B` 加群で `m B ⊆ m_B` なので、Krull の交叉定理から `x = 0`。

## 規約

Tor はこのリポジトリの `TorModule A i M N`（第2変数の分解で計算）で、`M` を第1変数に置く。
長完全列は第2変数についてのもの（`LeftDerivedLES`）を使う。

## 使われ方

`formalization-plans/serre-equal-characteristic.md` の S5・S6。
冪級数加群 `D[[Y]]` の `k[[Y]]` 上の平坦性を、`Y` が正則列であることから導くのに使う。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory IsLocalRing TensorProduct

namespace SerrePositivity

variable {A : Type u} [CommRing A] (M : Type u) [AddCommGroup M] [Module A M]

section les

variable {V₁ V₂ V₃ : Type u} [AddCommGroup V₁] [Module A V₁]
  [AddCommGroup V₂] [Module A V₂] [AddCommGroup V₃] [Module A V₃]
  (f : V₁ →ₗ[A] V₂) (g : V₂ →ₗ[A] V₃) (hf : Function.Injective f)
  (hg : Function.Surjective g) (hfg : Function.Exact f g)

include hf hg hfg in
/-- 短完全列の両端で `Tor_1^A(M, -)` が消えれば、中央でも消える。 -/
theorem torModule_one_subsingleton_of_exact
    (h₁ : Subsingleton (TorModule A 1 M V₁)) (h₃ : Subsingleton (TorModule A 1 M V₃)) :
    Subsingleton (TorModule A 1 M V₂) := by
  obtain ⟨α, β, _, hαβ, _, _, _⟩ := torModule_longExact M f g hf hg hfg
  refine ⟨fun x y ↦ ?_⟩
  have hx : ∀ z : TorModule A 1 M V₂, z = 0 := by
    intro z
    obtain ⟨w, hw⟩ := ((hαβ 1) z).mp (Subsingleton.elim _ _)
    rw [← hw, Subsingleton.elim w 0, map_zero]
  rw [hx x, hx y]

/-- 長完全列の零次の射 `α₀` は、零次の Tor とテンソル積の自然な同一視で `M ⊗ f` と共役。
特に `α₀` が単射であることと `M ⊗ f` が単射であることは同値。 -/
theorem injective_alpha_zero_iff :
    Function.Injective (LeftDerivedLES.α ((tensoringLeft (ModuleCat.{u} A)).obj
      (ModuleCat.of A M)) f 0).hom ↔ Function.Injective (f.lTensor M) := by
  let G := (tensoringLeft (ModuleCat.{u} A)).obj (ModuleCat.of A M)
  rw [LeftDerivedLES.α_eq_map]
  let e := G.leftDerivedZeroIsoSelf
  have hnat := e.hom.naturality (ModuleCat.ofHom f)
  have hG : (G.map (ModuleCat.ofHom f)).hom =
      (e.hom.app (ModuleCat.of A V₂)).hom ∘ₗ
        ((G.leftDerived 0).map (ModuleCat.ofHom f)).hom ∘ₗ
          (e.inv.app (ModuleCat.of A V₁)).hom := by
    rw [← ModuleCat.hom_comp, ← ModuleCat.hom_comp, Category.assoc, hnat]
    simp
  change _ ↔ Function.Injective (G.map (ModuleCat.ofHom f)).hom
  rw [hG, LinearMap.coe_comp, LinearMap.coe_comp]
  constructor
  · intro hα
    refine ((e.app (ModuleCat.of A V₂)).toLinearEquiv.injective.comp hα).comp ?_
    exact (e.app (ModuleCat.of A V₁)).symm.toLinearEquiv.injective
  · intro h x y hxy
    have hinv : ∀ v, (e.inv.app (ModuleCat.of A V₁)).hom ((e.hom.app (ModuleCat.of A V₁)).hom v) =
        v := fun v ↦ by
      rw [← ModuleCat.comp_apply, Iso.hom_inv_id_app]
      rfl
    have h' := h (a₁ := (e.hom.app (ModuleCat.of A V₁)).hom x)
      (a₂ := (e.hom.app (ModuleCat.of A V₁)).hom y)
      (by simp only [Function.comp_apply, hinv]; exact congrArg _ hxy)
    rw [← hinv x, ← hinv y, h']

include hf hg hfg in
/-- `Tor_1^A(M, V₃) = 0` なら、短完全列 `0 → V₁ → V₂ → V₃ → 0` に `M ⊗ -` を施しても単射のまま。
長完全列の `Tor_1(M, V₃) → M ⊗ V₁ → M ⊗ V₂` と、零次の Tor とテンソル積の自然な同一視による。 -/
theorem lTensor_injective_of_torModule_one (h₃ : Subsingleton (TorModule A 1 M V₃)) :
    Function.Injective (f.lTensor M) := by
  let G := (tensoringLeft (ModuleCat.{u} A)).obj (ModuleCat.of A M)
  have hex := LeftDerivedLES.exact_δα G f g hf hg hfg 0
  rw [← injective_alpha_zero_iff]
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨w, rfl⟩ := (hex z).mp hz
  have : w = 0 := @Subsingleton.elim _ h₃ w 0
  rw [this, map_zero]

include hf hg hfg in
/-- `Tor_1^A(M, V₂) = 0` で `M ⊗ f` が単射なら `Tor_1^A(M, V₃) = 0`。
長完全列 `Tor_1(M, V₂) → Tor_1(M, V₃) → M ⊗ V₁ → M ⊗ V₂` による。 -/
theorem torModule_one_subsingleton_of_lTensor_injective
    (h₂ : Subsingleton (TorModule A 1 M V₂)) (hinj : Function.Injective (f.lTensor M)) :
    Subsingleton (TorModule A 1 M V₃) := by
  let G := (tensoringLeft (ModuleCat.{u} A)).obj (ModuleCat.of A M)
  have hα := (injective_alpha_zero_iff M f).mpr hinj
  have hδα := LeftDerivedLES.exact_δα G f g hf hg hfg 0
  have hβδ := LeftDerivedLES.exact_βδ G f g hf hg hfg 0
  have hz : ∀ z : TorModule A 1 M V₃, z = 0 := by
    intro z
    have h0 : (LeftDerivedLES.δ G f g hf hg hfg 0).hom z = 0 :=
      hα ((hδα.apply_apply_eq_zero z).trans (map_zero _).symm)
    obtain ⟨w, hw⟩ := (hβδ z).mp h0
    rw [← hw, @Subsingleton.elim _ h₂ w 0]
    exact (LeftDerivedLES.β G f g hf hg hfg (0 + 1)).hom.map_zero
  exact ⟨fun x y ↦ by rw [hz x, hz y]⟩

end les

/-- 零加群を第2変数とする Tor は零。 -/
theorem torModule_subsingleton_right_of_subsingleton (N : Type u) [AddCommGroup N] [Module A N]
    [Subsingleton N] (i : ℕ) : Subsingleton (TorModule A i M N) := by
  apply ModuleCat.subsingleton_of_isZero
  exact ((tensoringLeft (ModuleCat.{u} A)).obj (ModuleCat.of A M) |>.leftDerived i).map_isZero
    (ModuleCat.isZero_of_subsingleton _)

/-- 線形同値な第2変数の Tor は同時に消える。 -/
theorem torModule_subsingleton_of_linearEquiv {N N' : Type u} [AddCommGroup N] [Module A N]
    [AddCommGroup N'] [Module A N'] (e : N ≃ₗ[A] N') (i : ℕ)
    (h : Subsingleton (TorModule A i M N)) : Subsingleton (TorModule A i M N') :=
  have := h
  ((((Tor (ModuleCat.{u} A) i).obj (ModuleCat.of A M)).mapIso
    e.toModuleIso).symm.toLinearEquiv).injective.subsingleton

variable [IsLocalRing A]

/-- **有限長の加群**：`Tor_1^A(M, k) = 0` なら、有限長の任意の `N` について `Tor_1^A(M, N) = 0`。
単純加群は剰余体と同型なので、組成列に沿って長完全列で帰納する。 -/
theorem torModule_one_subsingleton_of_isFiniteLength
    (hk : Subsingleton (TorModule A 1 M (ResidueField A)))
    (N : Type u) [AddCommGroup N] [Module A N] (hN : IsFiniteLength A N) :
    Subsingleton (TorModule A 1 M N) := by
  induction hN with
  | of_subsingleton => exact torModule_subsingleton_right_of_subsingleton M _ 1
  | @of_simple_quotient V _ _ P _ _ ih =>
    have hq : Subsingleton (TorModule A 1 M (V ⧸ P)) := by
      obtain ⟨I, hI, ⟨e⟩⟩ := (isSimpleModule_iff_quot_maximal (R := A) (M := V ⧸ P)).mp
        inferInstance
      have hIm : I = maximalIdeal A := IsLocalRing.eq_maximalIdeal hI
      subst hIm
      exact torModule_subsingleton_of_linearEquiv M e.symm 1 hk
    exact torModule_one_subsingleton_of_exact M P.subtype P.mkQ P.injective_subtype
      P.mkQ_surjective (LinearMap.exact_subtype_mkQ P) ih hq

variable [IsNoetherianRing A]

/-- 極大イデアルの冪を含むイデアルによる商は有限長。 -/
lemma isFiniteLength_quotient_of_maximalIdeal_pow_le (J : Ideal A) (n : ℕ)
    (h : maximalIdeal A ^ n ≤ J) : IsFiniteLength A (A ⧸ J) := by
  let : IsArtinianRing (A ⧸ maximalIdeal A) := inferInstanceAs (IsArtinianRing (ResidueField A))
  apply isFiniteLength_of_le_radical_annihilator (maximalIdeal A)
  rw [Ideal.annihilator_quotient]
  intro x hx
  exact ⟨n, h (Ideal.pow_mem_pow hx n)⟩

variable {B : Type u} [CommRing B] [Algebra A B] [Module B M] [IsScalarTower A B M]

omit [IsLocalRing A] [IsNoetherianRing A] in
/-- `M` が有限生成 `B` 加群、`N` が有限生成 `A` 加群なら、`M ⊗_A N` は有限生成 `B` 加群。
`A^q → N` の全射をテンソルし、`M ⊗_A A^q ≅ M^q` を使う。 -/
lemma finite_tensorProduct_left [Module.Finite B M] (N : Type u) [AddCommGroup N] [Module A N]
    [Module.Finite A N] : Module.Finite B (M ⊗[A] N) := by
  obtain ⟨q, φ, hφ⟩ := Module.Finite.exists_fin' A N
  let ψ : M ⊗[A] (Fin q → A) →ₗ[B] M ⊗[A] N := TensorProduct.AlgebraTensorModule.lTensor B M φ
  have hψ : Function.Surjective ψ := LinearMap.lTensor_surjective M hφ
  have : Module.Finite B (M ⊗[A] (Fin q → A)) :=
    Module.Finite.equiv (TensorProduct.piScalarRight A B M (Fin q)).symm
  exact Module.Finite.of_surjective ψ hψ

omit [IsNoetherianRing A] in
/-- 冪 `m^n` の元によるスカラー倍で書ける元は、`B` 加群として `m_B^n` 倍の中にある。 -/
lemma tmul_mem_maximalIdeal_pow_smul [IsLocalRing B] [IsLocalHom (algebraMap A B)] (n : ℕ)
    (I : Ideal A) (m : M) (i : I) (hi : i ∈ (maximalIdeal A ^ n • ⊤ : Submodule A I)) :
    m ⊗ₜ[A] i ∈ (maximalIdeal B ^ n • ⊤ : Submodule B (M ⊗[A] I)) := by
  refine Submodule.smul_induction_on hi (fun a ha j _ ↦ ?_) (fun x y hx hy ↦ ?_)
  · rw [TensorProduct.tmul_smul, ← algebraMap_smul B a]
    apply Submodule.smul_mem_smul _ Submodule.mem_top
    have h1 : algebraMap A B a ∈ (maximalIdeal A ^ n).map (algebraMap A B) :=
      Ideal.mem_map_of_mem _ ha
    rw [Ideal.map_pow] at h1
    exact Ideal.pow_right_mono (map_maximalIdeal_le (algebraMap A B)) n h1
  · rw [TensorProduct.tmul_add]
    exact add_mem hx hy

/-- **局所平坦性判定法**：`A → B` を Noether 局所環の局所準同型、`M` を有限生成 `B` 加群とする。
`Tor_1^A(M, k) = 0` なら `M` は `A` 上平坦。各イデアル `I` について `M ⊗ I → M` の核の元が
Artin–Rees と有限長の場合から `m_B` の全ての冪の中にあることを示し、Krull の交叉定理を使う。 -/
theorem flat_of_torModule_one_residueField [IsLocalRing B] [IsNoetherianRing B]
    [IsLocalHom (algebraMap A B)] [Module.Finite B M]
    (hk : Subsingleton (TorModule A 1 M (ResidueField A))) : Module.Flat A M := by
  rw [Module.Flat.iff_lTensor_injective']
  intro I
  rw [injective_iff_map_eq_zero]
  intro x hx
  have : Module.Finite B (M ⊗[A] I) := finite_tensorProduct_left M I
  have hmem : ∀ n : ℕ, x ∈ (maximalIdeal B ^ n • ⊤ : Submodule B (M ⊗[A] I)) := by
    intro n
    -- Artin–Rees
    obtain ⟨c, hc⟩ := Ideal.exists_pow_inf_eq_pow_smul (maximalIdeal A) (M := A) I
    set J : Ideal A := maximalIdeal A ^ (n + c)
    have hAR : J ⊓ I ≤ maximalIdeal A ^ n • I := by
      have h := hc (n + c) (by omega)
      rw [Nat.add_sub_cancel] at h
      have hJ : (maximalIdeal A ^ (n + c) • ⊤ : Submodule A A) = J := by
        rw [Ideal.smul_eq_mul, Ideal.mul_top]
      rw [hJ] at h
      rw [h]
      exact Submodule.smul_mono le_rfl inf_le_right
    let P : Submodule A I := Submodule.comap I.subtype J
    let Q : Submodule A I := maximalIdeal A ^ n • ⊤
    have hPQ : P ≤ Q := by
      intro i hi
      have hi' : (i : A) ∈ maximalIdeal A ^ n • I := hAR ⟨(hi : (i : A) ∈ J), i.2⟩
      have hmap : Q.map I.subtype = maximalIdeal A ^ n • I := by
        rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype]
      rw [← hmap] at hi'
      obtain ⟨j, hj, hji⟩ := hi'
      rwa [Subtype.ext hji] at hj
    -- 短完全列 `0 → I/P → A/J → A/(I + J) → 0`
    let f : I ⧸ P →ₗ[A] A ⧸ J := P.mapQ J I.subtype le_rfl
    let g : A ⧸ J →ₗ[A] A ⧸ (I ⊔ J) := Submodule.factor le_sup_right
    have hf : Function.Injective f := by
      rw [injective_iff_map_eq_zero]
      intro z hz
      obtain ⟨i, rfl⟩ := Submodule.Quotient.mk_surjective P z
      rw [Submodule.Quotient.mk_eq_zero]
      exact (Submodule.Quotient.mk_eq_zero J).mp hz
    have hg : Function.Surjective g := Submodule.factor_surjective _
    have hfg : Function.Exact f g := by
      intro y
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective J y
      change Submodule.Quotient.mk (p := I ⊔ J) a = 0 ↔ _
      rw [Submodule.Quotient.mk_eq_zero]
      constructor
      · intro ha
        obtain ⟨i, hi, j, hj, rfl⟩ := Submodule.mem_sup.mp ha
        refine ⟨Submodule.Quotient.mk ⟨i, hi⟩, ?_⟩
        change Submodule.Quotient.mk (p := J) i = _
        rw [Submodule.Quotient.eq]
        simpa using J.neg_mem hj
      · rintro ⟨z, hz⟩
        obtain ⟨i, rfl⟩ := Submodule.Quotient.mk_surjective P z
        have h := (Submodule.Quotient.eq J).mp hz
        have : a = (i : A) - ((i : A) - a) := by ring
        rw [this]
        exact sub_mem (Submodule.mem_sup_left i.2) (Submodule.mem_sup_right h)
    have h₃ := torModule_one_subsingleton_of_isFiniteLength M hk _
      (isFiniteLength_quotient_of_maximalIdeal_pow_le (I ⊔ J) (n + c) le_sup_right)
    have hinj := lTensor_injective_of_torModule_one M f g hf hg hfg h₃
    -- `x` は `M ⊗ I/P` で零
    have hcomm : f ∘ₗ P.mkQ = J.mkQ ∘ₗ I.subtype := rfl
    have h1 : P.mkQ.lTensor M x = 0 := by
      apply hinj
      rw [map_zero, ← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hcomm,
        LinearMap.lTensor_comp, LinearMap.comp_apply, hx, map_zero]
    have h2 : Q.mkQ.lTensor M x = 0 := by
      have hq : Submodule.factor hPQ ∘ₗ P.mkQ = Q.mkQ := rfl
      rw [← hq, LinearMap.lTensor_comp, LinearMap.comp_apply, h1, map_zero]
    have key : ∀ y : M ⊗[A] Q, Q.subtype.lTensor M y ∈
        (maximalIdeal B ^ n • ⊤ : Submodule B (M ⊗[A] I)) := by
      intro y
      induction y with
      | tmul m q => exact tmul_mem_maximalIdeal_pow_smul M n I m q q.2
      | add y z hy hz =>
        rw [map_add]
        exact add_mem hy hz
    obtain ⟨y, rfl⟩ := ((_root_.lTensor_exact M (LinearMap.exact_subtype_mkQ Q)
      Q.mkQ_surjective) x).mp h2
    exact key y
  have hbot := Ideal.iInf_pow_smul_eq_bot_of_isLocalRing (M := M ⊗[A] I)
    (maximalIdeal B) (maximalIdeal.isMaximal B).ne_top
  have : x ∈ (⨅ i : ℕ, maximalIdeal B ^ i • ⊤ : Submodule B (M ⊗[A] I)) :=
    Submodule.mem_iInf _ |>.mpr hmem
  rwa [hbot, Submodule.mem_bot] at this

section regular

open RingTheory.Sequence

omit [IsLocalRing A] [IsNoetherianRing A] in
/-- 環自身を第2変数とする `Tor_1` は零。 -/
theorem torModule_one_self_subsingleton : Subsingleton (TorModule A 1 M A) :=
  ModuleCat.subsingleton_of_isZero
    (isZero_Tor_succ_of_projective (ModuleCat.{u} A) (ModuleCat.of A M) (ModuleCat.of A A) 0)

omit [IsLocalRing A] [IsNoetherianRing A] in
/-- 列 `rs` が `A` と `M` の両方で弱正則なら、各 `j` で `Tor_1^A(M, A/(r_1, …, r_j)) = 0`。
`0 → A/I_j --r_{j+1}--> A/I_j → A/I_{j+1} → 0` の長完全列で `j` について帰納する。
零次の射は `M/I_jM` 上の `r_{j+1}` 倍なので、`M` 上の正則性から単射。 -/
theorem torModule_one_quotient_ofList_subsingleton (rs : List A)
    (hA : IsWeaklyRegular A rs) (hM : IsWeaklyRegular M rs) :
    ∀ j ≤ rs.length, Subsingleton (TorModule A 1 M (A ⧸ Ideal.ofList (rs.take j))) := by
  intro j
  induction j with
  | zero =>
    intro _
    have h0 : Ideal.ofList ([] : List A) = ⊥ := Ideal.ofList_nil
    rw [List.take_zero, h0]
    exact torModule_subsingleton_of_linearEquiv M (AlgEquiv.quotientBot A A).toLinearEquiv.symm 1
      (torModule_one_self_subsingleton M)
  | succ j ih =>
    intro hj
    have hjl : j < rs.length := hj
    set I := Ideal.ofList (rs.take j)
    set r := rs[j]
    have hI : (I • ⊤ : Submodule A A) = I := by rw [Ideal.smul_eq_mul, Ideal.mul_top]
    have htake : Ideal.ofList (rs.take (j + 1)) = I ⊔ Ideal.span {r} := by
      rw [List.take_add_one, List.getElem?_eq_getElem hjl, Option.toList_some, Ideal.ofList_append,
        Ideal.ofList_singleton]
    rw [htake]
    -- 短完全列 `0 → A/I → A/I → A/(I + (r)) → 0`
    let f : (A ⧸ I) →ₗ[A] (A ⧸ I) := r • LinearMap.id
    let g : (A ⧸ I) →ₗ[A] A ⧸ (I ⊔ Ideal.span {r}) := Submodule.factor le_sup_left
    have hregA := hA.regular_mod_prev j hjl
    rw [hI] at hregA
    have hf : Function.Injective f := hregA
    have hg : Function.Surjective g := Submodule.factor_surjective _
    have hfg : Function.Exact f g := by
      intro y
      obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective I y
      change Submodule.Quotient.mk (p := I ⊔ Ideal.span {r}) a = 0 ↔ _
      rw [Submodule.Quotient.mk_eq_zero]
      constructor
      · intro ha
        obtain ⟨i, hi, s, hs, rfl⟩ := Submodule.mem_sup.mp ha
        obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp hs
        refine ⟨Submodule.Quotient.mk t, ?_⟩
        change r • Submodule.Quotient.mk (p := I) t = Submodule.Quotient.mk (i + t * r)
        rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq]
        simpa [smul_eq_mul, mul_comm] using I.neg_mem hi
      · rintro ⟨z, hz⟩
        obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective I z
        change r • Submodule.Quotient.mk (p := I) t = Submodule.Quotient.mk a at hz
        rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq] at hz
        have : a = r • t - (r • t - a) := by ring
        rw [this]
        exact sub_mem (Submodule.mem_sup_right (Ideal.mem_span_singleton'.mpr ⟨t, by
          simp [smul_eq_mul, mul_comm]⟩)) (Submodule.mem_sup_left hz)
    -- 零次の射の単射性
    have hinj : Function.Injective (f.lTensor M) := by
      have hfl : f.lTensor M = r • LinearMap.id := by
        rw [LinearMap.lTensor_smul, LinearMap.lTensor_id]
      rw [hfl]
      let e := TensorProduct.tensorQuotEquivQuotSMul M I
      have hregM : IsSMulRegular (M ⧸ (I • ⊤ : Submodule A M)) r := hM.regular_mod_prev j hjl
      intro x y hxy
      apply e.injective
      apply hregM
      simp only [LinearMap.smul_apply, LinearMap.id_apply] at hxy
      change r • e x = r • e y
      rw [← map_smul, ← map_smul, hxy]
    exact torModule_one_subsingleton_of_lTensor_injective M f g hf hg hfg (ih (Nat.le_of_succ_le hj)) hinj

/-- **正則列による平坦性**：`A → B` を Noether 局所環の局所準同型、`M` を有限生成 `B` 加群とする。
極大イデアルを生成する `A` の弱正則列が `M` 上でも弱正則なら、`M` は `A` 上平坦。
`Tor_1^A(M, k) = 0` を列の長さの帰納法で示し、局所平坦性判定法を適用する。 -/
theorem flat_of_isWeaklyRegular [IsLocalRing B] [IsNoetherianRing B]
    [IsLocalHom (algebraMap A B)] [Module.Finite B M] (rs : List A)
    (hspan : Ideal.ofList rs = maximalIdeal A)
    (hA : IsWeaklyRegular A rs) (hM : IsWeaklyRegular M rs) : Module.Flat A M := by
  apply flat_of_torModule_one_residueField (B := B) M
  have h := torModule_one_quotient_ofList_subsingleton M rs hA hM rs.length le_rfl
  rw [List.take_length, hspan] at h
  exact h

end regular

end SerrePositivity
