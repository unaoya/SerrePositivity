module

public import Mathlib.Algebra.Category.ModuleCat.Basic
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

/-!
# 有限長加群

## 概要

加群の長さ `Module.length`（`ℕ∞` 値）と有限長性 `IsFiniteLength` についての補題を集める。
このプロジェクトでは、Euler 標数の各項（`Tor` の長さ、複体のホモロジーの長さ）が有限であることを
示す場面と、組成列についての帰納法（Lemma 3.4）で、次の事実を繰り返し使う。

## 内容

1. **Noether 環上の有限長の判定**：`T ⧸ I` が Artin 環で、有限生成加群 `M` の零化イデアルの根基が
   `I` を含むなら、`M` は有限長（`isFiniteLength_of_le_radical_annihilator`）。`M` は実質的に Artin 環
   `T / Ann M` 上の有限生成加群なので、Noether かつ Artin、すなわち有限長である。台つき完全複体の
   ホモロジーが有限長であること（`PerfectComplex/OrdinaryEuler.lean`）と、交点が有限長なら
   テンソル積が有限長であること（`length_tensorProduct_ne_top_of_annihilator`）に使う。
2. **局所環上の組成列**（Lemma 3.4 の帰納法、`notes/lemma-3-4.md`）：単純加群は剰余体 `A ⧸ m` と
   同型、`M ⧸ N` が単純なら `ℓ(M) = ℓ(N) + 1`、有限長加群は `m` の冪で消える。また `z` が `m` を
   生成すれば `A ⧸ (z)` は剰余体で、有限生成な非零加群はそこへ全射する
   （`PerfectComplex/KoszulGeneration.lean` のデヴィサージュで使う）。
3. **剰余体が同じときの長さの比較**：`A → T` で `T` が局所環、`A → T → T/m_T` が全射なら、
   `T` 加群の `A` 上の長さと `T` 上の長さは一致する（`length_eq_of_common_residueField`）。
   単純 `T` 加群が `A` 上でも単純だからである。Lemma 3.5b で `χ_T` を `A` 上の長さで測り直すときと、
   Lemma 5.2 で基底変更した分解の Euler 評価を比べるときに使う。
4. **係数制限・半線形同型と長さ**：係数制限して有限長ならもとの環上でも有限長
   （`finiteLength_of_restrictScalars`）、全射な環準同型の上の半線形全単射は長さを保つ
   （`length_eq_of_semilinear_bijective`）。後者は特に環自己同型に沿った係数制限に使い、ひねり
   `g^*P` の Euler 評価が不変であること（`PerfectComplex/OrdinaryEuler.lean`）の根拠になる。
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
    [IsArtinianRing (T ⧸ I)] (M : Type u) [AddCommGroup M] [Module T M]
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
（`χ_T` を `A` 上の長さで測る、`Paper/Lemma3_5/Ordinary.lean`）と Lemma 5.2
（`IntersectionMultiplicity/ResolutionEvaluation.lean`）で使う。
-/

@[expose] public section

universe u

open CategoryTheory IsLocalRing

namespace SerrePositivity

section length

variable {A T : Type u} [CommRing A] [CommRing T] [Algebra A T] [IsLocalRing T]
  (hres : Function.Surjective ((residue T).comp (algebraMap A T)))

include hres in
/-- 剰余体が同じ（`A → T → T/m_T` が全射）なら、単純 `T` 加群 `S` は `A` 加群としても単純である。
単純 `T` 加群は `T ⧸ m_T` と同型なので `m_T` は `S` を消す。任意の `t ∈ T` は、剰余体への全射性から
`a ∈ A` の像と `m_T` の元の和に書けるので、`S` 上で `t` 倍は `a` 倍に等しい。したがって `S` の
`A` 部分加群は自動的に `T` 部分加群であり、`T` 上の単純性（部分加群は `⊥` か `⊤`）から `A` 上の
単純性が従う。 -/
lemma isSimpleModule_of_residue_surjective (S : Type u) [AddCommGroup S] [Module T S]
    [Module A S] [IsScalarTower A T S] [IsSimpleModule T S] : IsSimpleModule A S := by
  obtain ⟨φ⟩ := IsSimpleModule.nonempty_linearEquiv_quotient_maximalIdeal (A := T) (M := S)
  -- `m_T` は `S` を消す
  have hkill : ∀ t ∈ maximalIdeal T, ∀ x : S, t • x = 0 := by
    intro t ht x
    apply φ.injective
    rw [map_smul, map_zero]
    obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (φ x)
    rw [← hy, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ ht
  -- `A` 部分加群は `T` 部分加群
  have hT : ∀ (p : Submodule A S) (t : T) (x : S), x ∈ p → t • x ∈ p := by
    intro p t x hx
    obtain ⟨a, ha⟩ := hres (residue T t)
    have hm : t - algebraMap A T a ∈ maximalIdeal T := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero]
      exact ha.symm
    have : t • x = a • x := by
      rw [← sub_eq_zero, ← algebraMap_smul T a x, ← sub_smul]
      exact hkill _ hm x
    rw [this]
    exact p.smul_mem a hx
  have : Nontrivial S := IsSimpleModule.nontrivial T S
  refine { eq_bot_or_eq_top := fun p ↦ ?_ }
  let q : Submodule T S :=
    { carrier := p
      add_mem' := p.add_mem
      zero_mem' := p.zero_mem
      smul_mem' := fun t x hx ↦ hT p t x hx }
  rcases IsSimpleOrder.eq_bot_or_eq_top q with h | h
  · left
    ext x
    have := SetLike.ext_iff.mp h x
    simpa [q] using this
  · right
    ext x
    have := SetLike.ext_iff.mp h x
    simpa [q] using this

include hres in
/-- 剰余体が同じ局所環 `T` 上では、`T` 加群 `M` の `A` 上の長さと `T` 上の長さは一致する。
`M` が `T` 上有限長なら組成列についての帰納法：単純な商 `M ⧸ N` は `A` 上でも単純
（`isSimpleModule_of_residue_surjective`）なので、どちらの長さも一段で `1` ずつ増える。
`T` 上無限長なら `A` 上も無限長：`A` 上有限長なら Noether かつ Artin で、それは `T` 上の Noether 性・
Artin 性を含意する（`isNoetherian_of_tower`、`isArtinian_of_tower`）から。 -/
theorem length_eq_of_common_residueField (M : Type u) [AddCommGroup M] [Module T M]
    [Module A M] [IsScalarTower A T M] : Module.length A M = Module.length T M := by
  by_cases h : IsFiniteLength T M
  · suffices H : ∀ (M : Type u) [AddCommGroup M] [Module T M], IsFiniteLength T M →
        ∀ [Module A M] [IsScalarTower A T M], Module.length A M = Module.length T M from
      H M h
    intro M _ _ h
    induction h with
    | of_subsingleton => intro _ _; simp [Module.length_eq_zero]
    | @of_simple_quotient M _ _ N _ _ ih =>
      intro _ _
      have := isSimpleModule_of_residue_surjective hres (M ⧸ N)
      rw [Module.length_eq_succ_of_isSimpleModule_quotient N,
        Module.length_eq_add_of_exact (N.subtype.restrictScalars A) (N.mkQ.restrictScalars A)
          N.injective_subtype N.mkQ_surjective (LinearMap.exact_subtype_mkQ N),
        Module.length_eq_one A (M ⧸ N), ih]
  · have hT : Module.length T M = ⊤ := by
      by_contra hne
      exact h (Module.length_ne_top_iff.mp hne)
    rw [hT]
    by_contra hne
    have hA := Module.length_ne_top_iff.mp hne
    rw [isFiniteLength_iff_isNoetherian_isArtinian] at hA
    obtain ⟨_, _⟩ := hA
    have : IsNoetherian T M := isNoetherian_of_tower A inferInstance
    have : IsArtinian T M := isArtinian_of_tower A inferInstance
    exact h (isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩)

include hres in
/-- `length_eq_of_common_residueField` を、`ModuleCat` の係数制限関手 `restrictScalars` の言葉で
述べたもの：係数制限した `T` 加群の `A` 上の長さは `T` 上の長さに等しい。複体の各項が `ModuleCat`
の対象として現れる場面（`Paper/Lemma3_5/Ordinary.lean`、Lemma 5.2）で使う形。 -/
lemma length_restrictScalars_eq (M : ModuleCat.{u} T) :
    Module.length A ((ModuleCat.restrictScalars (algebraMap A T)).obj M) =
      Module.length T M := by
  let : Module A M := Module.compHom M (algebraMap A T)
  have : IsScalarTower A T M := ⟨fun a t m ↦ by
    rw [Algebra.smul_def, mul_smul]
    rfl⟩
  exact length_eq_of_common_residueField hres M

end length

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

/-- 環自己同型 `σ : R ≃+* R` に沿って係数を制限しても（`r • x` を `σ(r) • x` に取り替えても）長さは
変わらない。恒等写像が `σ` 半線形全単射になることと `length_eq_of_semilinear_bijective` による。
ひねり `g^*P` の通常の Euler 評価が不変であること（`PerfectComplex/OrdinaryEuler.lean` の
`chiOrd_twist`）に使う。 -/
lemma length_restrictScalars_equiv (σ : R ≃+* R) (M : ModuleCat.{u} R) :
    Module.length R ((ModuleCat.restrictScalars σ.toRingHom).obj M) = Module.length R M := by
  let f : (ModuleCat.restrictScalars σ.toRingHom).obj M →ₛₗ[σ.toRingHom] M :=
    { toFun := id, map_add' := fun _ _ ↦ rfl, map_smul' := fun _ _ ↦ rfl }
  exact length_eq_of_semilinear_bijective σ.toRingHom σ.surjective f Function.bijective_id

end semilinear

end SerrePositivity

end
