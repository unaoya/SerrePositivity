module

public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.RingTheory.FiniteLength
public import Mathlib.RingTheory.HopkinsLevitzki
public import Mathlib.RingTheory.KrullDimension.Zero
public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.LocalRing.Quotient
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.LinearAlgebra.Quotient.Defs

/-! # 有限長の加群

## 概要

可換環上の有限長加群（`IsFiniteLength`）の基本を集める。単純加群・Noether 環上での判定
（零化イデアルの根基が Artin なイデアルを含めば有限長、`isFiniteLength_of_le_radical_annihilator`）、
局所環上の単純加群と剰余体、`m` を生成する列による商、短完全列・完全列での長さの加法性、
係数制限と半線形全単射での不変性、有限自由加群とのテンソル積の長さ、長さの自然数値
（`lengthNat`）とその加法性、像による商の長さ、スカラー倍による部分商の長さの比較、
有限フィルトレーションによるイデアルの冪の零化を含む。

## 方針

有限長は Noether かつ Artin（Mathlib の `isFiniteLength_iff_isNoetherian_isArtinian`）で判定し、
長さの加法性は Mathlib の `Module.length_eq_add_of_exact` による。

## 規約

長さは Mathlib の `Module.length`（`ℕ∞` 値）。自然数値が要るときは `lengthNat`。

## 使われ方

長さを扱う全ての層（Hilbert–Samuel、Koszul、正規化長さ、K 理論、CLMST）。
-/

@[expose] public section

universe u

open CategoryTheory Limits IsLocalRing

namespace SerrePositivity

section

variable {A : Type u} [CommRing A]

/-- 単純加群は有限長である（長さ `1`）。単純加群は Noether かつ Artin だから。 -/
lemma isFiniteLength_of_isSimpleModule (M : Type u) [AddCommGroup M] [Module A M]
    [IsSimpleModule A M] : IsFiniteLength A M :=
  isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩

end

/-! ## Noether 環上 -/

section noetherian

variable {T : Type u} [CommRing T] [IsNoetherianRing T]

/-- Noether 環 `T` で、`T ⧸ I` が Artin 環かつ `I ⊆ √J` なら、`T ⧸ J` も Artin 環である。
Noether 環の商が Artin であることは、Krull 次元が `0`、すなわち極小素イデアルがすべて極大である
ことと同値（Hopkins–Levitzki）。`J` の極小素イデアル `p` は `√J ⊇ I` を含むので `T ⧸ I` の
素イデアルを与え、`T ⧸ I` が Artin なのでそこで極大、したがって `T` でも極大である。 -/
lemma isArtinianRing_quotient_of_le_radical (I J : Ideal T)
    [IsArtinianRing (T ⧸ I)] (hIJ : I ≤ J.radical) : IsArtinianRing (T ⧸ J) := by
  have : IsNoetherianRing (T ⧸ J) :=
    isNoetherianRing_of_surjective T _ (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
  apply (isArtinianRing_iff_krullDimLE_zero).mpr
  apply Ideal.krullDimLE_zero_quotient_iff_forall_minimalPrimes_isMaximal.mpr
  intro p hp
  have : p.IsPrime := hp.1.1
  have hIp : I ≤ p := hIJ.trans ((Ideal.IsPrime.radical_le_iff ‹p.IsPrime›).mpr hp.1.2)
  have : (p.map (Ideal.Quotient.mk I)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by simpa using hIp)
  have : (p.map (Ideal.Quotient.mk I)).IsMaximal := Ideal.IsPrime.isMaximal' inferInstance
  have h := Ideal.comap_isMaximal_of_surjective (Ideal.Quotient.mk I)
    Ideal.Quotient.mk_surjective (K := p.map (Ideal.Quotient.mk I))
  simpa [Ideal.comap_map_of_surjective, sup_eq_right.mpr hIp] using h

/-- Noether 環 `T` 上の有限生成加群 `M` について、`T ⧸ I` が Artin 環で `I ⊆ √(Ann M)` なら、`M` は
有限長である。幾何的には「`M` の台が Artin 的な閉部分スキーム `V(I)` に含まれる」という条件。
`T ⧸ Ann M` は `isArtinianRing_quotient_of_le_radical` により Artin 環で、`M` はその上の有限生成
加群なので Noether かつ Artin、よって有限長。`M` の `T` 加群としての Noether 性・Artin 性は、
作用が `T ⧸ Ann M` を経由することから移す。 -/
lemma isFiniteLength_of_le_radical_annihilator (I : Ideal T)
    [IsArtinianRing (T ⧸ I)] (M : Type*) [AddCommGroup M] [Module T M]
    [Module.Finite T M] (hI : I ≤ (Module.annihilator T M).radical) : IsFiniteLength T M := by
  have : IsArtinianRing (T ⧸ Module.annihilator T M) :=
    isArtinianRing_quotient_of_le_radical I _ hI
  let hM := Module.isTorsionBySet_annihilator T M
  let := hM.module
  let : RingHomSurjective (Ideal.Quotient.mk (Module.annihilator T M)) :=
    ⟨Ideal.Quotient.mk_surjective⟩
  have : IsNoetherian (T ⧸ Module.annihilator T M) M :=
    isNoetherian_of_surjective hM.semilinearMap
      (LinearMap.range_eq_top.mpr Function.surjective_id)
  have : IsArtinian (T ⧸ Module.annihilator T M) M := inferInstance
  have : IsArtinian T M :=
    (hM.semilinearMap.isArtinian_iff_of_bijective Function.bijective_id).mpr inferInstance
  exact isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩

end noetherian

open scoped TensorProduct

/-- Noether 局所環 `R` 上の有限生成加群 `M`、`N` について、`I M = 0`、`J N = 0` で `√(I + J) = m` なら、
`M ⊗_R N` は有限長である。純テンソル `m ⊗ n` を、`I` の元は `m` 側で、`J` の元は `n` 側で消すので
`(I + J)(M ⊗ N) = 0`。したがって `m = √(I + J) ⊆ √(Ann(M ⊗ N))` で、`R ⧸ m` は体（Artin 環）なので
`isFiniteLength_of_le_radical_annihilator` が使える。正則性や交点理論の入力は要らない。
Lemma 5.2 で、`R/P` と `R/Q` の交点が閉点なら `T ⊗_R M` が有限長であることを示すのに使う
（以前は入力クラスの仮定だった）。 -/
theorem length_tensorProduct_ne_top_of_annihilator {R : Type u}
    [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (I J : Ideal R) (M N : Type u) [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module.Finite R M] [Module.Finite R N]
    (hI : I ≤ Module.annihilator R M) (hJ : J ≤ Module.annihilator R N)
    (h : (I ⊔ J).radical = maximalIdeal R) : Module.length R (M ⊗[R] N) ≠ ⊤ := by
  have hann : I ⊔ J ≤ Module.annihilator R (M ⊗[R] N) := by
    apply sup_le
    · intro a ha
      rw [Module.mem_annihilator]
      intro x
      induction x using TensorProduct.inductionOn with
      | tmul m n =>
        rw [TensorProduct.smul_tmul', (Module.mem_annihilator.mp (hI ha)) m]
        simp
      | add x y hx hy => simp [smul_add, hx, hy]
    · intro a ha
      rw [Module.mem_annihilator]
      intro x
      induction x using TensorProduct.inductionOn with
      | tmul m n =>
        rw [← TensorProduct.tmul_smul, (Module.mem_annihilator.mp (hJ ha)) n]
        simp
      | add x y hx hy => simp [smul_add, hx, hy]
  apply Module.length_ne_top_iff.mpr
  let : Field (R ⧸ maximalIdeal R) := Ideal.Quotient.field _
  exact isFiniteLength_of_le_radical_annihilator (maximalIdeal R) (M ⊗[R] N)
    (h ▸ Ideal.radical_mono hann)

/-! ## 局所環上 -/

variable {A : Type u} [CommRing A] [IsLocalRing A]
variable {M : Type u} [AddCommGroup M] [Module A M]

/-- 局所環 `A` 上の単純加群は剰余体 `A ⧸ m` と線形同型である。単純加群は極大イデアル `I` による商
`A ⧸ I` と同型（Mathlib の `isSimpleModule_iff_quot_maximal`）で、局所環の極大イデアルは `m` だけ
だから。 -/
lemma IsSimpleModule.nonempty_linearEquiv_quotient_maximalIdeal [IsSimpleModule A M] :
    Nonempty (M ≃ₗ[A] A ⧸ maximalIdeal A) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp ‹IsSimpleModule A M›
  exact ⟨e.trans (Submodule.quotEquivOfEq I (maximalIdeal A) (eq_maximalIdeal hI))⟩

omit [IsLocalRing A] in
/-- 部分加群 `N ≤ M` で `M ⧸ N` が単純なら `ℓ(M) = ℓ(N) + 1`。短完全列 `0 → N → M → M ⧸ N → 0` での
長さの加法性と、単純加群の長さが `1` であることによる。組成列についての帰納法の一段で使う。 -/
lemma Module.length_eq_succ_of_isSimpleModule_quotient (N : Submodule A M)
    [IsSimpleModule A (M ⧸ N)] : Module.length A M = Module.length A N + 1 := by
  rw [Module.length_eq_add_of_exact N.subtype N.mkQ N.injective_subtype N.mkQ_surjective
    (LinearMap.exact_subtype_mkQ N), Module.length_eq_one A (M ⧸ N)]

/-- 局所環上の有限長加群 `M` は、極大イデアル `m` のある冪で消える。組成列についての帰納法：
`M ⧸ N` が単純（`≃ A ⧸ m`）で `N` が `m^n` で消えるなら、`m M ⊆ N` なので `m^{n+1} M ⊆ m^n N = 0`。
`Tor` が冪ねじれであること（`TorFiniteLength.lean`）と、基底変更した分解のホモロジーの台
（`IntersectionMultiplicity/ResolutionEvaluation.lean`）に使う。 -/
lemma IsFiniteLength.exists_isTorsionBySet_maximalIdeal_pow (h : IsFiniteLength A M) :
    ∃ n : ℕ, Module.IsTorsionBySet A M ((maximalIdeal A) ^ n : Ideal A) := by
  induction h with
  | of_subsingleton => exact ⟨0, fun x _ ↦ Subsingleton.elim _ _⟩
  | @of_simple_quotient M _ _ N _ _ ih =>
    obtain ⟨n, hn⟩ := ih
    refine ⟨n + 1, ?_⟩
    obtain ⟨e⟩ :=
      IsSimpleModule.nonempty_linearEquiv_quotient_maximalIdeal (A := A) (M := M ⧸ N)
    -- `m • M ⊆ N`：`M ⧸ N ≃ A ⧸ m` は `m` で消える
    have hmN : ∀ (c : A), c ∈ maximalIdeal A → ∀ x : M, c • x ∈ N := by
      intro c hc x
      rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]
      apply e.injective
      rw [map_smul, map_zero]
      obtain ⟨y, hy⟩ :=
        Submodule.Quotient.mk_surjective (maximalIdeal A) (e (Submodule.Quotient.mk x))
      rw [← hy, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact Ideal.mul_mem_right y _ hc
    intro x a
    obtain ⟨a, ha⟩ := a
    change a • x = 0
    have ha' : a ∈ maximalIdeal A ^ n * maximalIdeal A := by rw [← pow_succ]; exact ha
    refine Submodule.mul_induction_on ha' (fun b hb c hc ↦ ?_) (fun u v hu hv ↦ ?_)
    · -- `(b * c) • x = b • (c • x)`、`c • x ∈ N`、`N` は `m ^ n` で消える
      rw [mul_smul]
      have := @hn ⟨c • x, hmN c hc x⟩ ⟨b, hb⟩
      rw [Subtype.ext_iff] at this
      simpa using this
    · rw [add_smul, hu, hv, add_zero]

/-! ## `m` を生成する列 -/

section span

variable {e : ℕ} {z : Fin e → A} (hz : Ideal.span (Set.range z) = maximalIdeal A)

include hz in
/-- `z` が `m` を生成すれば、`A ⧸ (z) = A ⧸ m` は剰余体なので Artin 環である。台つき完全複体の
ホモロジーが有限長であること（`PerfectComplex/OrdinaryEuler.lean` の `chiOrdHom`）の前提として使う。 -/
lemma isArtinianRing_quotient_span_of_eq : IsArtinianRing (A ⧸ Ideal.span (Set.range z)) := by
  rw [hz]
  exact inferInstanceAs (IsArtinianRing (ResidueField A))

include hz in
/-- `z` が `m` を生成すれば、`A ⧸ (z) = A ⧸ m` は単純 `A` 加群である（`m` が極大だから）。
Koszul 複体 `K(z)` の `0` 次ホモロジー `A/(z)` の長さが `1` であること
（`PerfectComplex/KoszulGeneration.lean`）に使う。 -/
lemma isSimpleModule_quotient_span_of_eq : IsSimpleModule A (A ⧸ Ideal.span (Set.range z)) := by
  rw [hz, isSimpleModule_iff_isCoatom]
  exact Ideal.isMaximal_def.mp (maximalIdeal.isMaximal A)

include hz in
/-- `z` が `m` を生成するとき、有限生成で零でない加群 `H` から `A ⧸ (z) = k` への全射がある。
有限生成加群の部分加群の束では `⊥` の上に極大部分加群（coatom）`N` があり、`H ⧸ N` は単純、
したがって `A ⧸ m = A ⧸ (z)` と同型。合成 `H → H ⧸ N ≅ A ⧸ (z)` が求める全射である。
デヴィサージュ（`PerfectComplex/KoszulGeneration.lean`）で、`H^0(Q) ≠ 0` のときに `Q → K(z)` を
作る出発点になる。 -/
lemma exists_surjective_quotient_span (H : ModuleCat.{u} A) [Module.Finite A H]
    (hH : ¬ IsZero H) :
    ∃ ε : H ⟶ ModuleCat.of A (A ⧸ Ideal.span (Set.range z)), Function.Surjective ε.hom := by
  have : Nontrivial H := by
    rw [ModuleCat.isZero_iff_subsingleton] at hH
    exact not_subsingleton_iff_nontrivial.mp hH
  obtain h | ⟨N, hN, -⟩ := IsCoatomic.eq_top_or_exists_le_coatom (⊥ : Submodule A H)
  · exact absurd h bot_ne_top
  have : IsSimpleModule A (H ⧸ N) := isSimpleModule_iff_isCoatom.mpr hN
  obtain ⟨φ⟩ := IsSimpleModule.nonempty_linearEquiv_quotient_maximalIdeal (A := A) (M := H ⧸ N)
  let ψ := φ.trans (Submodule.quotEquivOfEq _ _ hz.symm)
  exact ⟨ModuleCat.ofHom (ψ.toLinearMap ∘ₗ N.mkQ), ψ.surjective.comp N.mkQ_surjective⟩

end span

end SerrePositivity

end

/-!
## 剰余体が同じときの長さの比較

環準同型 `A → T` で `T` が局所環、合成 `A → T → T/m_T` が全射（`A` と `T` の剰余体が同じ）なら、
`T` 加群の `A` 上の長さと `T` 上の長さは一致する（`length_eq_of_common_residueField`）。
鍵は、単純 `T` 加群が `A` 上でも単純であること：単純 `T` 加群は `T/m_T` と同型で、`T` の任意の元は
`A` の元と `m_T` の元の和に書けるので、`T` の作用は `A` の作用で尽くされる。論文の Lemma 3.5b
（`χ_T` を `A` 上の長さで測る、`Paper/Section3/NormComparison.lean`）と Lemma 5.2
（`IntersectionMultiplicity/ResolutionEvaluation.lean`）で使う。
-/

@[expose] public section

universe u

open CategoryTheory IsLocalRing

namespace SerrePositivity

/-! ## 係数制限と長さ -/

section restrictScalars

variable {A T : Type u} [CommRing A] [CommRing T] [Algebra A T]

/-- `T` 加群 `M` が `A` 加群として（係数制限して）有限長なら、`T` 加群としても有限長である。
`T` 部分加群は `A` 部分加群でもあるので、`A` 上の Noether 性・Artin 性（部分加群の鎖の有限性）が
`T` 上に移る。基底変更した分解のホモロジーが `T` 上有限長であること
（`IntersectionMultiplicity/ResolutionEvaluation.lean`）に使う。 -/
lemma finiteLength_of_restrictScalars (M : ModuleCat.{u} T)
    (hM : IsFiniteLength A ((ModuleCat.restrictScalars (algebraMap A T)).obj M)) :
    IsFiniteLength T M := by
  let : Module A M := Module.compHom M (algebraMap A T)
  have : IsScalarTower A T M := IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
  have h : IsFiniteLength A M := hM
  obtain ⟨hn, ha⟩ := isFiniteLength_iff_isNoetherian_isArtinian.mp h
  exact isFiniteLength_iff_isNoetherian_isArtinian.mpr
    ⟨isNoetherian_of_tower A hn, isArtinian_of_tower A ha⟩

end restrictScalars

section semilinear

variable {R S : Type u} [CommRing R] [CommRing S]

/-- 全射な環準同型 `φ : R → S` の上の半線形全単射 `f : M → N`（`f(r • x) = φ(r) • f(x)`）は長さを
保つ。`φ` が全射なので `f` は部分加群の束の順序同型 `Submodule R M ≃o Submodule S N` を誘導し
（Mathlib の `orderIsoMapComapOfBijective`）、長さは部分加群の束の Krull 次元だから。 -/
lemma length_eq_of_semilinear_bijective (φ : R →+* S) (hφ : Function.Surjective φ)
    {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]
    (f : M →ₛₗ[φ] N) (hf : Function.Bijective f) : Module.length R M = Module.length S N := by
  have : RingHomSurjective φ := ⟨hφ⟩
  rw [Module.length, Module.length, WithBot.unbot_inj,
    Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComapOfBijective f hf)]

set_option backward.isDefEq.respectTransparency false in
/-- 係数環と代数の同型が構造写像と可換なら、対応する商の長さは等しい。
商の環同型を係数環の同型に関する半線形全単射として扱う。 -/
lemma length_quotient_eq_of_equiv
    (T U : Type u) [CommRing T] [CommRing U] [Algebra R T] [Algebra S U]
    (eR : R ≃+* S) (eT : T ≃+* U)
    (he : ∀ r, eT (algebraMap R T r) = algebraMap S U (eR r)) (I : Ideal T) :
    Module.length R (T ⧸ I) = Module.length S (U ⧸ I.map eT.toRingHom) := by
  let e := Ideal.quotientEquiv I (I.map eT.toRingHom) eT rfl
  let f : (T ⧸ I) →ₛₗ[eR.toRingHom] (U ⧸ I.map eT.toRingHom) :=
    { e.toAddEquiv.toAddMonoidHom with
      map_smul' := by
        intro r x
        obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
        change e (Ideal.Quotient.mk I (r • x)) = eR r • e (Ideal.Quotient.mk I x)
        simp only [e, Ideal.quotientEquiv_mk]
        simp only [Algebra.smul_def, map_mul, he, Ideal.Quotient.mk_algebraMap] }
  exact length_eq_of_semilinear_bijective eR.toRingHom eR.surjective f e.bijective

/-- 環同型 `σ : R ≃+* S` に沿って係数を制限しても（`r • x` を `σ(r) • x` に取り替えても）長さは
変わらない。恒等写像が `σ` 半線形全単射になることと `length_eq_of_semilinear_bijective` による。
ひねり `g^*P` の通常の Euler 評価が不変であること（`PerfectComplex/OrdinaryEuler.lean` の
`chiOrd_twist`）に使う。 -/
lemma length_restrictScalars_equiv (σ : R ≃+* S) (M : ModuleCat.{u} S) :
    Module.length R ((ModuleCat.restrictScalars σ.toRingHom).obj M) = Module.length S M := by
  let f : (ModuleCat.restrictScalars σ.toRingHom).obj M →ₛₗ[σ.toRingHom] M :=
    { toFun := id, map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }
  exact length_eq_of_semilinear_bijective σ.toRingHom σ.surjective f Function.bijective_id

end semilinear

end SerrePositivity

end

@[expose] public section

open scoped TensorProduct

namespace SerrePositivity

variable {R : Type u} [CommRing R]

/-- 有限自由加群とのテンソル積の長さは、自由加群の階数ともう一方の長さの積。
有限基底でテンソル積を有限直和に同一視し、長さの加法性を使う。長さの有限性は不要。 -/
lemma length_tensorProduct_of_finite_free_left (M N : Type u) [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module.Free R M] [Module.Finite R M] :
    Module.length R (M ⊗[R] N) = Module.finrank R M * Module.length R N := by
  classical
  nontriviality R using Module.length_eq_zero
  let b := Module.Free.chooseBasis R M
  let e := TensorProduct.congr b.equivFun (LinearEquiv.refl R N) ≪≫ₗ
    TensorProduct.piLeft R N (fun _ : Module.Free.ChooseBasisIndex R M => R) ≪≫ₗ
    LinearEquiv.piCongrRight (fun _ => TensorProduct.lid R N)
  rw [e.length_eq, Module.length_pi_of_fintype]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  congr 1
  exact_mod_cast (Module.finrank_eq_card_basis b).symm

/-- 完全列の両端が有限長なら中央も有限長。中央を核と像に分け、
両端の部分商の有限長性と短完全列での長さの加法性を使う。 -/
lemma isFiniteLength_of_exact {M N L : Type u} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup L] [Module R L]
    (f : M →ₗ[R] N) (g : N →ₗ[R] L) (he : Function.Exact f g)
    (hM : IsFiniteLength R M) (hL : IsFiniteLength R L) : IsFiniteLength R N := by
  have hk : IsFiniteLength R (LinearMap.ker g) := by
    rw [LinearMap.exact_iff.mp he]
    exact hM.of_surjective f.surjective_rangeRestrict
  have hr := hL.of_injective (LinearMap.range g).injective_subtype
  apply Module.length_ne_top_iff.mp
  rw [Module.length_eq_add_of_exact (LinearMap.ker g).subtype g.rangeRestrict
    (LinearMap.ker g).injective_subtype g.surjective_rangeRestrict
    (by rw [LinearMap.exact_iff]; ext x; simp)]
  exact WithTop.add_ne_top.mpr ⟨Module.length_ne_top_iff.mpr hk, Module.length_ne_top_iff.mpr hr⟩

end SerrePositivity

end

@[expose] public noncomputable section

universe u v w

section Value

namespace SerrePositivity
variable {R : Type u} [CommRing R]

/-- 短完全列の自然数値の長さ。中央の有限長性から両端の有限性も得る。 -/
lemma lengthNat_add_of_exact {M N P : Type u}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (hf : Function.Injective f) (hg : Function.Surjective g) (he : Function.Exact f g)
    (hN : IsFiniteLength R N) :
    (Module.length R N).toNat = (Module.length R M).toNat + (Module.length R P).toNat := by
  rw [Module.length_eq_add_of_exact f g hf hg he,
    ENat.toNat_add (Module.length_ne_top_iff.mpr (hN.of_injective hf))
      (Module.length_ne_top_iff.mpr (hN.of_surjective hg))]

/-- 有限長加群の長さは、核と像の長さの和。 -/
lemma lengthNat_ker_add_range {M N : Type u} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) (hM : IsFiniteLength R M) :
    (Module.length R M).toNat = (Module.length R f.ker).toNat +
      (Module.length R f.range).toNat := by
  have h := lengthNat_add_of_exact f.ker.subtype f.ker.mkQ
    (Submodule.subtype_injective _) (Submodule.mkQ_surjective _)
    (LinearMap.exact_subtype_mkQ f.ker) hM
  rwa [f.quotKerEquivRange.length_eq] at h

/-- 完全列の有限長な中央の長さは、前後の像の長さの和。 -/
lemma lengthNat_eq_add_range {M N P : Type u}
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (he : Function.Exact f g) (hN : IsFiniteLength R N) :
    (Module.length R N).toNat = (Module.length R f.range).toNat +
      (Module.length R g.range).toNat := by
  rw [lengthNat_ker_add_range g hN, ← LinearMap.exact_iff.mp he]

end SerrePositivity

end Value

section QuotientImage

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
variable {R S : Type*} [CommRing R] [CommRing S]

/-- 核を含むイデアルによる商と、その全射像による商の同型。 -/
def quotientImageEquiv (f : R →+* S) (hf : Function.Surjective f)
    (I : Ideal R) (hker : RingHom.ker f ≤ I) : R ⧸ I ≃+* S ⧸ I.map f := by
  have heq : I = (I.map f).comap f := by
    rw [Ideal.comap_map_of_surjective f hf, ← RingHom.ker_eq_comap_bot,
      sup_eq_left.mpr hker]
  exact RingEquiv.ofBijective (Ideal.quotientMap (I.map f) f heq.le)
    ⟨Ideal.quotientMap_injective' heq.ge, Ideal.quotientMap_surjective hf⟩

@[simp] theorem quotientImageEquiv_mk (f : R →+* S) (hf : Function.Surjective f)
    (I : Ideal R) (hker : RingHom.ker f ≤ I) (a : R) :
    quotientImageEquiv f hf I hker (Ideal.Quotient.mk I a) =
      Ideal.Quotient.mk (I.map f) (f a) := rfl

/-- 長さは全射環準同型と商同型を通じて移せる。 -/
theorem length_quotient_eq_image_of_surjective (f : R →+* S) (hf : Function.Surjective f)
    (I : Ideal R) (hker : RingHom.ker f ≤ I) :
    Module.length R (R ⧸ I) = Module.length S (S ⧸ I.map f) := by
  let e := quotientImageEquiv f hf I hker
  let g : R ⧸ I →ₛₗ[f] S ⧸ I.map f :=
    { e.toAddEquiv.toAddMonoidHom with
      map_smul' := by
        intro r a
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
        change e (Ideal.Quotient.mk I (r * a)) =
          Ideal.Quotient.mk (I.map f) (f r * f a)
        exact congrArg (Ideal.Quotient.mk (I.map f)) (f.map_mul r a) }
  let : RingHomSurjective f := ⟨hf⟩
  rw [Module.length, Module.length, WithBot.unbot_inj,
    Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComapOfBijective g e.bijective)]

end SerrePositivity

end QuotientImage

section SmulSubquotient

namespace SerrePositivity

variable {R : Type u} [CommRing R]

/-- 有限長の加群の自己準同型では、核と余核の長さが等しい。
核と像による分解と、像と余核による分解の二つで全体の長さを書き、像の長さを打ち消す。 -/
lemma length_ker_eq_length_quotient_range {M : Type u} [AddCommGroup M] [Module R M]
    (f : M →ₗ[R] M) (hM : IsFiniteLength R M) :
    Module.length R (LinearMap.ker f) = Module.length R (M ⧸ LinearMap.range f) := by
  have h₁ := lengthNat_ker_add_range f hM
  have h₂ := lengthNat_add_of_exact (LinearMap.range f).subtype (LinearMap.range f).mkQ
    (Submodule.subtype_injective _) (Submodule.mkQ_surjective _)
    (LinearMap.exact_subtype_mkQ _) hM
  have hker : Module.length R (LinearMap.ker f) ≠ ⊤ :=
    Module.length_ne_top_iff.mpr (hM.of_injective (Submodule.subtype_injective _))
  have hquot : Module.length R (M ⧸ LinearMap.range f) ≠ ⊤ :=
    Module.length_ne_top_iff.mpr (hM.of_surjective (Submodule.mkQ_surjective _))
  rw [← ENat.natCast_toNat hker, ← ENat.natCast_toNat hquot]
  congr 1
  omega

/-- 有限長の加群 `W` に単射で入る `Z` から全射 `Z ↠ H` があり、`c` が `H` を消すなら、
`ℓ(H) ≤ ℓ(0 :_W c)`。全射は `Z / cZ` を経由し、`ℓ(Z / cZ) = ℓ(0 :_Z c) ≤ ℓ(0 :_W c)`。 -/
theorem length_le_length_ker_smul_of_subquotient
    {W Z H : Type u} [AddCommGroup W] [Module R W] [AddCommGroup Z] [Module R Z]
    [AddCommGroup H] [Module R H] (hW : IsFiniteLength R W)
    (ι : Z →ₗ[R] W) (hι : Function.Injective ι) (π : Z →ₗ[R] H) (hπ : Function.Surjective π)
    (c : R) (hc : ∀ x : H, c • x = 0) :
    Module.length R H ≤ Module.length R (LinearMap.ker (c • LinearMap.id : W →ₗ[R] W)) := by
  have hZ : IsFiniteLength R Z := hW.of_injective hι
  -- 全射は `Z / cZ` を経由する
  have hle : LinearMap.range (c • LinearMap.id : Z →ₗ[R] Z) ≤ LinearMap.ker π := by
    rintro _ ⟨z, rfl⟩
    simp [hc]
  have h₁ : Module.length R H ≤
      Module.length R (Z ⧸ LinearMap.range (c • LinearMap.id : Z →ₗ[R] Z)) :=
    Module.length_le_of_surjective
      ((LinearMap.range (c • LinearMap.id : Z →ₗ[R] Z)).liftQ π hle)
      (by
        intro x
        obtain ⟨z, rfl⟩ := hπ x
        exact ⟨Submodule.Quotient.mk z, rfl⟩)
  -- `0 :_Z c` は `0 :_W c` に単射で入る
  have hker : LinearMap.ker (c • LinearMap.id : Z →ₗ[R] Z) ≤
      (LinearMap.ker (c • LinearMap.id : W →ₗ[R] W)).comap ι := by
    intro z hz
    simp only [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply,
      Submodule.mem_comap] at hz ⊢
    rw [← map_smul, hz, map_zero]
  have h₂ : Module.length R (LinearMap.ker (c • LinearMap.id : Z →ₗ[R] Z)) ≤
      Module.length R (LinearMap.ker (c • LinearMap.id : W →ₗ[R] W)) :=
    Module.length_le_of_injective
      ((ι.restrict hker))
      (by
        intro a b hab
        apply Subtype.ext
        apply hι
        exact congrArg Subtype.val hab)
  rw [← length_ker_eq_length_quotient_range _ hZ] at h₁
  exact h₁.trans h₂

/-- 有限個の直積上のスカラー倍の核は、各成分の核の直積と線形同値。 -/
def kerSmulPiEquiv (β : ℕ) (W : Type u) [AddCommGroup W] [Module R W] (c : R) :
    LinearMap.ker (c • LinearMap.id : (Fin β → W) →ₗ[R] (Fin β → W)) ≃ₗ[R]
      (Fin β → LinearMap.ker (c • LinearMap.id : W →ₗ[R] W)) where
  toFun v j := ⟨v.1 j, by
    have h := congrFun (LinearMap.mem_ker.mp v.2) j
    rw [LinearMap.mem_ker]
    exact h⟩
  invFun w := ⟨fun j ↦ (w j).1, by
    rw [LinearMap.mem_ker]
    funext j
    exact LinearMap.mem_ker.mp (w j).2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- 有限個の直積上のスカラー倍の核の長さは、成分の核の長さの `β` 倍。 -/
lemma length_ker_smul_pi (β : ℕ) (W : Type u) [AddCommGroup W] [Module R W] (c : R) :
    Module.length R (LinearMap.ker (c • LinearMap.id : (Fin β → W) →ₗ[R] (Fin β → W))) =
      β • Module.length R (LinearMap.ker (c • LinearMap.id : W →ₗ[R] W)) := by
  rw [(kerSmulPiEquiv β W c).length_eq, Module.length_pi_of_fintype]
  simp

end SerrePositivity

end SmulSubquotient

section FiltrationAnnihilator

open scoped Pointwise

namespace SerrePositivity
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- An annihilator of a subquotient lowers scalar multiples of the upper submodule. -/
lemma ideal_smul_le_of_subquotient_annihilated (I : Ideal R) (U V : Submodule R M)
    (hI : I ≤ Module.annihilator R (V ⧸ U.comap V.subtype)) : I • V ≤ U := by
  rw [Submodule.smul_le]
  intro r hr x hx
  have h := Module.mem_annihilator.mp (hI hr) (Submodule.Quotient.mk (⟨x, hx⟩ : V))
  have hm : r • (⟨x, hx⟩ : V) ∈ U.comap V.subtype :=
    (Submodule.Quotient.mk_eq_zero _).mp (by
      simpa only [Submodule.Quotient.mk_smul] using h)
  exact hm

/-- Each multiplication lowers one filtration step, so the nth ideal power lowers n steps. -/
lemma ideal_pow_smul_finite_filtration_le (I : Ideal R) (F : ℕ → Submodule R M) (e : ℕ)
    (hstep : ∀ k : ℕ, k < e → I • F (k + 1) ≤ F k) (n : ℕ) :
    ∀ k : ℕ, k + n ≤ e → I ^ n • F (k + n) ≤ F k := by
  induction n with
  | zero => intro k _; simp
  | succ n ih =>
    intro k hk
    rw [pow_succ, Submodule.mul_smul, Nat.add_succ]
    calc
      I ^ n • (I • F (k + n + 1)) ≤ I ^ n • F (k + n) :=
        smul_mono_right _ (hstep (k + n) (by omega))
      _ ≤ F k := ih k (by omega)

/-- A filtration of e annihilated factors gives I^e annihilation, with no finiteness hypothesis. -/
lemma ideal_pow_annihilator_of_finite_filtration (I : Ideal R)
    (F : ℕ → Submodule R M) (e : ℕ) (hzero : F 0 = ⊥) (htop : F e = ⊤)
    (hstep : ∀ k : ℕ, k < e → I • F (k + 1) ≤ F k) :
    I ^ e ≤ Module.annihilator R M := by
  have h : I ^ e • (⊤ : Submodule R M) ≤ ⊥ := by
    simpa only [Nat.zero_add, hzero, htop] using
      ideal_pow_smul_finite_filtration_le I F e hstep e 0 (by omega)
  intro r hr
  rw [Module.mem_annihilator]
  intro x
  exact (Submodule.mem_bot R).mp (h (Submodule.smul_mem_smul hr (Submodule.mem_top : x ∈ ⊤)))

/-- Annihilation of the actual successive subquotients gives the same explicit exponent. -/
lemma ideal_pow_annihilator_of_finite_quotient_filtration (I : Ideal R)
    (F : ℕ → Submodule R M) (e : ℕ) (hzero : F 0 = ⊥) (htop : F e = ⊤)
    (hquot : ∀ k : ℕ, k < e →
      I ≤ Module.annihilator R (F (k + 1) ⧸ (F k).comap (F (k + 1)).subtype)) :
    I ^ e ≤ Module.annihilator R M :=
  ideal_pow_annihilator_of_finite_filtration I F e hzero htop
    (fun k hk => ideal_smul_le_of_subquotient_annihilated I (F k) (F (k + 1)) (hquot k hk))

end SerrePositivity

end FiltrationAnnihilator

end
