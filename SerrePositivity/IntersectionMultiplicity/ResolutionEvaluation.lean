module

public import SerrePositivity.CategoryTheory.AlternatingSum
public import SerrePositivity.HomologicalAlgebra.BaseChangeEquivalence
public import SerrePositivity.HomologicalAlgebra.TorLES
public import SerrePositivity.CommutativeAlgebra.Length.Euler
public import SerrePositivity.CommutativeAlgebra.KoszulResolution
public import SerrePositivity.PerfectComplex.Free.Euler
public import Mathlib.Algebra.Ring.Action.Group
public import Mathlib.CategoryTheory.Adjunction.Unique
public import SerrePositivity.IntersectionMultiplicity.Basic
public import SerrePositivity.HomologicalAlgebra.TorFiniteLength
public import SerrePositivity.PerfectComplex.Free.Support
public import SerrePositivity.PerfectComplex.Free.K0
public import SerrePositivity.CommutativeAlgebra.Length.Basic

/-!
# 分解の係数拡大と Euler 評価

## 概要

加群 `M` の射影 cochain 分解 `F`（`IsResolutionOf F M`、`HomologicalAlgebra/Resolution.lean`）を
係数拡大した複体の `-i` 次ホモロジーは `Tor_i` である（`torIsoCochain`）。このファイルは、それを使って
複体の Euler 評価を `Tor` の Euler 評価に書き換える：

- `lambdaEuler lam (F ⊗_R C) = lambdaChi lam φ M`（正規化長さ、`lambdaEuler_baseChange_resolution`）、
- `chiOrd (F ⊗_R T) = χ^R(T, M)`（通常の長さ。剰余体が同じとき、`chiOrd_baseChange_resolution`）。

また、二段階の係数拡大 `R → T → C` と、ひねり `twist g` を、合成した構造射による一段階の係数拡大に
書き換える（`baseChangeCompIso`、`twistBaseChangeIso`）。ひねりは係数制限なので、係数拡大として
書き直すと `g⁻¹` が現れる。これが Lemma 5.2 で `c_σ` の添字に逆元が出る理由である
（`Paper/Section5/FirstComparison.lean`）。

後半では、有限な局所代数 `T` と、`T ⊗_R M` が有限長な有限生成加群 `M` について、`M` の有界有限自由
分解の係数拡大 `F ⊗_R T` が `T` の閉点に台をもつ完全複体であることを示す
（`isPerfectSupported_baseChange_resolution`）。ホモロジー `Tor_i^R(T, M)` が有限長なので `m_T` の
冪で消え、ホモロジーの台の条件から零ホモトピーの条件に移す（`PerfectComplex/Support.lean`）。

後半には、Koszul Euler 特性と交点重複度の同一視 `koszulEulerChar_eq_chi`、
有界有限自由分解をもつ加群と有限長加群の交点 Euler 特性の階数公式を置く。
後者は、syzygy の短完全列と Tor の長完全列から証明する
`chi_eq_sum_finrank_mul_length_of_resolution` と、分解の階数の交代和を使う。
このファイルの一般公式に未証明入力はない。

## 規約

cochain の `-i` 次が `Tor_i`。交代和の整数添字から自然数添字への移行は `alternating_finsum_eq_nat`。
`Tor` は一貫して第 2 変数を分解して計算し、`Tor` の対称性は使わない。Euler 評価の等式には有界性・
有限長性は要らない（規約による値も含めて成り立つ）が、台つき完全複体を作る定理では要る。
Lemma 3.5 には依存しない。
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace SerrePositivity

variable {R T C : Type u} [CommRing R] [CommRing T] [CommRing C]
variable {J : Ideal C} (lam : NormalizedLength C J)

/-- 正の次数の項が零な `C` 複体 `K` で、各 `i` について `Tor_i^R(C, M) ≃ H^{-i}(K)` なら、
`lambdaEuler lam K = lambdaChi lam φ M`。正の次数のホモロジーは零なので `alternating_finsum_eq_nat` で
添字を `ℕ` に移し、各項を線形同型で取り替える。有限性は仮定しない（規約による値も含めた等式）。 -/
theorem lambdaEuler_eq_lambdaChi_of_homologyEquiv (φ : R →+* C)
    (M : Type u) [AddCommGroup M] [Module R M]
    (K : CochainComplex (ModuleCat.{u} C) ℤ)
    (hpos : ∀ i : ℤ, 0 < i → IsZero (K.X i))
    (e : ∀ i : ℕ, TorAlg φ i M ≃ₗ[C] K.homology (-(i : ℤ))) :
    lambdaEuler lam K = lambdaChi lam φ M := by
  have hz (i : ℤ) (hi : 0 < i) : (lam.len (K.homology i)).toReal = 0 := by
    have : Subsingleton (K.homology i) := ModuleCat.subsingleton_of_isZero
      ((K.sc i).isZero_homology_of_isZero_X₂ (hpos i hi))
    simp [lam.len_eq_zero_of_subsingleton]
  unfold lambdaEuler
  rw [alternating_finsum_eq_nat _ hz]
  unfold lambdaChi
  congr 1
  funext i
  have hlen := lam.len_congr _ _ (e i)
  simp only [hlen]

/-- `M` の射影 cochain 分解 `F` を `φ : R → C` で係数拡大した複体の正規化 Euler 評価は、`Tor` の
正規化 Euler 評価 `lambdaChi lam φ M` に等しい（`torIsoCochain` と
`lambdaEuler_eq_lambdaChi_of_homologyEquiv`）。 -/
theorem lambdaEuler_baseChange_resolution (φ : R →+* C)
    {M : Type u} [AddCommGroup M] [Module R M]
    {F : CochainComplex (ModuleCat.{u} R) ℤ} (hF : IsResolutionOf F (ModuleCat.of R M)) :
    lambdaEuler lam (baseChange φ F) = lambdaChi lam φ M :=
  lambdaEuler_eq_lambdaChi_of_homologyEquiv lam φ M (baseChange φ F)
    (baseChange_isZero_X_of_pos φ F hF.isZero_X)
    (fun i ↦ (torIsoCochain φ hF i).toLinearEquiv)

/-- 二段階で係数拡大した分解 `(F ⊗_R T) ⊗_T C` の `-i` 次ホモロジーは、合成 `ψ ∘ φ` についての
`Tor_i^R(C, M)` と `C` 線形同型（`torIsoCochain` と `baseChangeCompIso`）。 -/
noncomputable def torAlgBaseChangeCompEquiv (φ : R →+* T) (ψ : T →+* C)
    {M : Type u} [AddCommGroup M] [Module R M]
    {F : CochainComplex (ModuleCat.{u} R) ℤ} (hF : IsResolutionOf F (ModuleCat.of R M))
    (i : ℕ) : TorAlg (ψ.comp φ) i M ≃ₗ[C]
      (baseChange ψ (baseChange φ F)).homology (-(i : ℤ)) :=
  ((torIsoCochain (ψ.comp φ) hF i) ≪≫
    (HomologicalComplex.homologyFunctor _ _ (-(i : ℤ))).mapIso
      (baseChangeCompIso φ ψ F).symm).toLinearEquiv

/-- `chiLam lam ψ (F ⊗_R T) = lambdaChi lam (ψ ∘ φ) M`：分解を `R → T` で係数拡大した複体の `chiLam`
（さらに `T → C` で係数拡大して `λ` で測る）は、合成 `R → C` についての `Tor` の評価に等しい。 -/
theorem chiLam_baseChange_resolution (φ : R →+* T) (ψ : T →+* C)
    {M : Type u} [AddCommGroup M] [Module R M]
    {F : CochainComplex (ModuleCat.{u} R) ℤ} (hF : IsResolutionOf F (ModuleCat.of R M)) :
    chiLam lam ψ (baseChange φ F) = lambdaChi lam (ψ.comp φ) M := by
  change lambdaEuler lam (baseChange ψ (baseChange φ F)) = _
  rw [lambdaEuler_eq_of_homotopyEquiv lam (HomotopyEquiv.ofIso (baseChangeCompIso φ ψ F))]
  exact lambdaEuler_baseChange_resolution lam (ψ.comp φ) hF

variable {G : Type u} [Group G] [MulSemiringAction G T]

/-- `g^*(F ⊗_R T) ≅ F ⊗_R T`（後者は `R → T →{g⁻¹} T` に沿った係数拡大）：ひねり `twist g` は `g` に
沿った係数制限で、これは `g⁻¹` に沿った係数拡大と同型（`restrictScalarsIsoExtendInverse`）、あとは
`baseChangeCompIso`。 -/
noncomputable def twistBaseChangeIso (φ : R →+* T) (g : G)
    (F : CochainComplex (ModuleCat.{u} R) ℤ) :
    twist g (baseChange φ F) ≅
      baseChange ((MulSemiringAction.toRingHom G T g⁻¹).comp φ) F := by
  let σ := MulSemiringAction.toRingEquiv G T g
  have he : σ.symm.toRingHom = MulSemiringAction.toRingHom G T g⁻¹ := by
    ext x
    rfl
  change ((ModuleCat.restrictScalars σ.toRingHom).mapHomologicalComplex _).obj
    (baseChange φ F) ≅ _
  refine (NatIso.mapHomologicalComplex (restrictScalarsIsoExtendInverse σ)
    (ComplexShape.up ℤ)).app
    (baseChange φ F) ≪≫ ?_
  simpa only [he] using baseChangeCompIso φ σ.symm.toRingHom F

/-- ひねって係数拡大した分解 `(g^*(F ⊗_R T)) ⊗_T C` の `-i` 次ホモロジーは、構造射
`R → T →{g⁻¹} T → C` についての `Tor_i^R(C, M)` と `C` 線形同型（`twistBaseChangeIso` と
`torAlgBaseChangeCompEquiv`）。一貫して第 2 変数 `M` を分解するので `Tor` の対称性は要らない。
Lemma 5.2 で `c_σ` の各項が有限であることを言うのに使う。 -/
noncomputable def torAlgTwistBaseChangeEquiv (φ : R →+* T) (ψ : T →+* C) (g : G)
    {M : Type u} [AddCommGroup M] [Module R M]
    {F : CochainComplex (ModuleCat.{u} R) ℤ} (hF : IsResolutionOf F (ModuleCat.of R M))
    (i : ℕ) : TorAlg (ψ.comp ((MulSemiringAction.toRingHom G T g⁻¹).comp φ)) i M ≃ₗ[C]
      (baseChange ψ (twist g (baseChange φ F))).homology (-(i : ℤ)) :=
  ((torAlgBaseChangeCompEquiv ((MulSemiringAction.toRingHom G T g⁻¹).comp φ) ψ hF i).toModuleIso ≪≫
    (HomologicalComplex.homologyFunctor _ _ (-(i : ℤ))).mapIso
      (((ModuleCat.extendScalars ψ).mapHomologicalComplex (ComplexShape.up ℤ)).mapIso
        (twistBaseChangeIso φ g F).symm)).toLinearEquiv

/-- `chiLam lam ψ (g^*(F ⊗_R T)) = lambdaChi lam (ψ ∘ g⁻¹ ∘ φ) M`：ひねった分解の正規化 Euler 評価は、
`g⁻¹` でひねった構造射についての `Tor` の評価に等しい。Lemma 5.2 の `χ_C(σ^*L) = c_{σ⁻¹}`。 -/
theorem chiLam_twist_baseChange_resolution (φ : R →+* T) (ψ : T →+* C) (g : G)
    {M : Type u} [AddCommGroup M] [Module R M]
    {F : CochainComplex (ModuleCat.{u} R) ℤ} (hF : IsResolutionOf F (ModuleCat.of R M)) :
    chiLam lam ψ (twist g (baseChange φ F)) =
      lambdaChi lam (ψ.comp ((MulSemiringAction.toRingHom G T g⁻¹).comp φ)) M := by
  change lambdaEuler lam (baseChange ψ (twist g (baseChange φ F))) = _
  rw [lambdaEuler_eq_of_homotopyEquiv lam
    ((ModuleCat.extendScalars ψ).mapHomotopyEquiv (HomotopyEquiv.ofIso (twistBaseChangeIso φ g F)))]
  exact chiLam_baseChange_resolution lam ((MulSemiringAction.toRingHom G T g⁻¹).comp φ) ψ hF

end SerrePositivity

end

/-!
## 有限な局所代数への係数拡大

Noether 環 `R` 上有限な局所環 `T` について：

- 剰余体への写像 `R → T → T/m_T` が全射なら、分解 `F` の係数拡大 `F ⊗_R T` の通常の Euler 評価は
  交点重複度 `χ^R(T, M)` に一致する（`chiOrd_baseChange_resolution`）。`H^{-i}(F ⊗_R T) ≅ Tor_i^R(T, M)`
  （`HomologicalAlgebra/Tor.lean` の `ordinaryTorIso`）で、`T` 上の長さと `R` 上の長さが一致する
  （`length_restrictScalars_eq`）から。
- さらに `F` が有界有限自由で `T ⊗_R M` が有限長なら、`F ⊗_R T` は `T` の閉点に台をもつ完全複体
  （`isPerfectSupported_baseChange_resolution`）。`Tor_i^R(T, M)` の有限長性
  （`CommutativeAlgebra/TorFiniteLength.lean`）から `m_T` の冪で消え、ホモロジーの台と零ホモトピーの
  対応（`PerfectComplex/Support.lean`）で台の条件に移す。
-/

public section

universe u

open CategoryTheory Limits IsLocalRing TensorProduct

namespace SerrePositivity

variable {R T : Type u} [CommRing R] [IsNoetherianRing R]
  [CommRing T] [IsLocalRing T] [Algebra R T]
  [Module.Finite R T]

omit [IsNoetherianRing R] [Module.Finite R T] in
/-- 剰余体への写像 `R → T → T/m_T` が全射なら、`M` の分解 `F` の係数拡大 `F ⊗_R T` の通常の Euler 評価は
交点重複度 `χ^R(T, M)` に等しい。各 `i` で `ℓ_T(H^{-i}(F ⊗_R T)) = ℓ_R(Tor_i^R(T, M))`
（`ordinaryTorIso` と `length_restrictScalars_eq`）、正の次数は零、あとは交代和の添字の取り直しと
`ℤ` から `ℝ` への移行。有限長性や分解の有界性は要らない（規約による値も含めた等式）。 -/
theorem chiOrd_baseChange_resolution
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (hF : IsResolutionOf F (ModuleCat.of R M))
    (hres : Function.Surjective ((residue T).comp (algebraMap R T))) :
    chiOrd (baseChange (algebraMap R T) F) = (chi R T M : ℝ) := by
  let K := baseChange (algebraMap R T) F
  have hlen (i : ℕ) : Module.length T (K.homology (-(i : ℤ))) = torLength R i T M := by
    let e := ordinaryTorIso (T := T) M F hF i
    exact (length_restrictScalars_eq hres _).symm.trans e.length_eq
  have hz (i : ℤ) (hi : 0 < i) : ((Module.length T (K.homology i)).toNat : ℝ) = 0 := by
    have := ModuleCat.subsingleton_of_isZero (isZero_homology_of_isZero_X _ _
      (baseChange_isZero_X_of_pos (algebraMap R T) F hF.isZero_X i hi))
    simp [Module.length_eq_zero]
  change (∑ᶠ i : ℤ, ((i.negOnePow : ℤ) : ℝ) *
    ((Module.length T (K.homology i)).toNat : ℝ)) = _
  unfold chi
  apply alternating_finsum_eq_int_cast _ _ hz
  intro i
  simp only [hlen, Int.cast_natCast]

/-- `T ⊗_R M` が有限長なら、`M` の有界有限自由分解 `F` の係数拡大 `F ⊗_R T` は、`√(w) = m_T` なる任意の
列 `w` に台をもつ完全 `T` 複体である。有界性・有限自由性は係数拡大で保たれる
（`PerfectComplex/Closure.lean`）。ホモロジーは `Tor_i^R(T, M)`（`ordinaryTorIso`）で、`T ⊗_R M` が
有限長なら `Tor` も有限長（`isFiniteLength_torModule`）、したがって `m_T` の冪で消える
（`exists_isTorsionBySet_maximalIdeal_pow`）ので `HasHomologySupport (w) L`、あとは
`isPerfectSupported_of_homologySupport`。Lemma 5.2 で `L = F ⊗_R D` を Lemma 3.5 に渡すための条件。 -/
theorem isPerfectSupported_baseChange_resolution
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (hF : IsResolutionOf F (ModuleCat.of R M))
    (hbound : ∃ a b : ℤ, ∀ i, (i < a ∨ b < i) → IsZero (F.X i))
    (hfree : ∀ i, Module.Free R (F.X i)) (hfinite : ∀ i, Module.Finite R (F.X i))
    (htensor : Module.length R (T ⊗[R] M) ≠ ⊤)
    {e : ℕ} (w : Fin e → T) (hw : (Ideal.span (Set.range w)).radical = maximalIdeal T) :
    IsPerfectSupported w (baseChange (algebraMap R T) F) := by
  have : IsNoetherianRing T := IsNoetherianRing.of_finite R T
  let L := baseChange (algebraMap R T) F
  have finiteX : ∀ i, Module.Finite T (L.X i) := by
    intro i
    have := hfinite i
    exact finite_baseChange (algebraMap R T) (F.X i)
  have freeX : ∀ i, Module.Free T (L.X i) := by
    intro i
    have := hfree i
    exact free_baseChange (algebraMap R T) (F.X i)
  have boundedL : ∃ a b : ℤ, ∀ i, (i < a ∨ b < i) → IsZero (L.X i) :=
    baseChange_bounded (algebraMap R T) F hbound
  have finiteH : ∀ i : ℤ, IsFiniteLength T (L.homology i) := by
    intro i
    by_cases hi : 0 < i
    · have hz : IsZero (L.homology i) := isZero_homology_of_isZero_X _ _
        (baseChange_isZero_X_of_pos (algebraMap R T) F hF.isZero_X i hi)
      have := ModuleCat.subsingleton_of_isZero hz
      exact IsFiniteLength.of_subsingleton
    · obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = -(n : ℤ) :=
        ⟨(-i).toNat, by rw [Int.toNat_of_nonneg (by omega), neg_neg]⟩
      let e := ordinaryTorIso (T := T) M F hF n
      have ht := isFiniteLength_torModule T M (Module.length_ne_top_iff.mp htensor) n
      exact finiteLength_of_restrictScalars (L.homology (-(n : ℤ)))
        (e.symm.isFiniteLength ht)
  have supported : HasHomologySupport (Ideal.span (Set.range w)) L := by
    apply (homologySupport_iff_le_radical_annihilator _ L finiteX).mpr
    intro i
    obtain ⟨n, hn⟩ := IsFiniteLength.exists_isTorsionBySet_maximalIdeal_pow (finiteH i)
    have hpow : (maximalIdeal T) ^ n ≤ Module.annihilator T (L.homology i) := by
      rwa [Module.isTorsionBySet_iff_subset_annihilator, SetLike.coe_subset_coe] at hn
    have hm : maximalIdeal T ≤ (Module.annihilator T (L.homology i)).radical := by
      intro x hx
      exact ⟨n, hpow (Ideal.pow_mem_pow hx n)⟩
    exact ((Ideal.span (Set.range w)).le_radical.trans_eq hw).trans hm
  exact isPerfectSupported_of_homologySupport w L finiteX freeX boundedL supported

end SerrePositivity

end

@[expose] public section

open CategoryTheory Limits

namespace SerrePositivity

variable {R : Type u} [CommRing R]

/-- 有限自由な第1変数と有限長な第2変数に対する Tor はすべて有限長。
0 次は有限直和の長さの計算、正次数は平坦性による消滅を使う。 -/
lemma isFiniteLength_torModule_of_finite_free_left (M N : Type u) [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module.Free R M] [Module.Finite R M]
    (hN : IsFiniteLength R N) (i : ℕ) : IsFiniteLength R (TorModule R i M N) := by
  cases i with
  | zero =>
    apply (torModuleZeroEquiv R M N).symm.isFiniteLength
    apply Module.length_ne_top_iff.mp
    rw [length_tensorProduct_of_finite_free_left]
    rw [← ENat.natCast_toNat (Module.length_ne_top_iff.mpr hN)]
    simpa only [Nat.cast_mul] using
      ENat.natCast_ne_top (Module.finrank R M * (Module.length R N).toNat)
  | succ i =>
    have := torModule_subsingleton_of_flat (R := R) M N i
    exact .of_subsingleton

/-- 有限自由な第1変数の交点 Euler 特性は、その階数と第2変数の長さの積。
高次 Tor が消えるので 0 次だけを計算する。長さは `toNat` の規約も含めた等式。 -/
lemma chi_of_finite_free_left (M N : Type u) [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module.Free R M] [Module.Finite R M] :
    (chi R M N : ℝ) = (Module.finrank R M : ℝ) * (Module.length R N).toNat := by
  unfold chi
  rw [finsum_eq_single _ 0]
  · simp only [pow_zero, one_mul, torLength, (torModuleZeroEquiv R M N).length_eq,
      length_tensorProduct_of_finite_free_left, ENat.toNat_mul, ENat.toNat_natCast,
      Nat.cast_mul, Int.cast_mul, Int.cast_natCast]
  · intro i hi
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi
    have := torModule_subsingleton_of_flat (R := R) M N j
    simp [torLength, Module.length_eq_zero]

/-- 第1変数の短完全列に対し、左端と中央の Tor が有限長かつ高次で零なら、
右端についても同じことが成り立ち、交点 Euler 特性は加法的である。
長完全列から有限長性と消滅を移し、その長さの交代和を取る。環の Noether 性は不要。 -/
lemma torEuler_shortExact_left
    (M₁ M₂ M₃ N : Type u) [AddCommGroup M₁] [Module R M₁]
    [AddCommGroup M₂] [Module R M₂] [AddCommGroup M₃] [Module R M₃]
    [AddCommGroup N] [Module R N]
    (f : M₁ →ₗ[R] M₂) (g : M₂ →ₗ[R] M₃)
    (hf : Function.Injective f) (hg : Function.Surjective g) (he : Function.Exact f g)
    (h₁ : ∀ i, IsFiniteLength R (TorModule R i M₁ N))
    (h₂ : ∀ i, IsFiniteLength R (TorModule R i M₂ N))
    (z₁ : ∃ n, ∀ i, n < i → Subsingleton (TorModule R i M₁ N))
    (z₂ : ∃ n, ∀ i, n < i → Subsingleton (TorModule R i M₂ N)) :
    (∀ i, IsFiniteLength R (TorModule R i M₃ N)) ∧
    (∃ n, ∀ i, n < i → Subsingleton (TorModule R i M₃ N)) ∧
    chi R M₂ N = chi R M₁ N + chi R M₃ N := by
  obtain ⟨α, β, δ, hab, hbd, hda, hb⟩ := torModule_longExact_left N f g hf hg he
  have h₃ : ∀ i, IsFiniteLength R (TorModule R i M₃ N) := by
    intro i
    cases i with
    | zero => exact (h₂ 0).of_surjective hb
    | succ i => exact isFiniteLength_of_exact (β (i + 1)) (δ i) (hbd i) (h₂ (i + 1)) (h₁ i)
  have z₃ : ∃ n, ∀ i, n < i → Subsingleton (TorModule R i M₃ N) := by
    obtain ⟨a, ha⟩ := z₁
    obtain ⟨b, hb'⟩ := z₂
    refine ⟨a + b + 1, ?_⟩
    intro i hi
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
    have := ha j (by omega)
    have := hb' (j + 1) (by omega)
    have hinj := (LinearMap.injective_iff_eq_zero_of_exact (hbd j)).mpr
      (Subsingleton.elim _ _)
    exact hinj.subsingleton
  refine ⟨h₃, z₃, ?_⟩
  exact lengthEuler_finsum_longExact
    (fun i => ModuleCat.of R (TorModule R i M₁ N))
    (fun i => ModuleCat.of R (TorModule R i M₂ N))
    (fun i => ModuleCat.of R (TorModule R i M₃ N))
    α β δ hab hbd hda hb h₁ h₂ h₃ z₁ z₂ z₃

/-- 有界有限自由分解と有限長加群に対する Euler–Poincaré 公式。
Tor の長さの交代和は、分解の階数の交代和と有限長加群の長さの積に等しい。
分解の syzygy の短完全列に沿って有限長性と高次消滅を降下帰納法で示し、
Tor の Euler 特性の加法性を足し合わせる。正則性・局所性・Noether 性も、Tor の対称性も使わない。 -/
theorem chi_eq_sum_finrank_mul_length_of_resolution
    (R M N : Type u) [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (hlength : IsFiniteLength R N)
    (P : ProjectiveResolution (ModuleCat.of R M))
    (hfree : ∀ i, Module.Free R (P.complex.X i))
    (hfinite : ∀ i, Module.Finite R (P.complex.X i))
    (n : ℕ) (hz : ∀ i, n < i → IsZero (P.complex.X i)) :
    (chi R M N : ℝ) =
      (∑ i ∈ Finset.range (n + 1), (-1 : ℝ) ^ i * Module.finrank R (P.complex.X i)) *
        (Module.length R N).toNat := by
  let Z := ResolutionSyzygy.obj P
  have hlast : Subsingleton (Z (n + 1)) := ModuleCat.subsingleton_of_isZero
    (ResolutionSyzygy.isZero_obj_succ P n (hz _ (by omega)))
  have lastTor (i : ℕ) : Subsingleton (TorModule R i (Z (n + 1)) N) :=
    torModule_subsingleton_left (R := R) (Z (n + 1)) N i
  have hT : ∀ k, k ≤ n + 1 →
      (∀ i, IsFiniteLength R (TorModule R i (Z k) N)) ∧
      (∃ b, ∀ i, b < i → Subsingleton (TorModule R i (Z k) N)) := by
    intro k hk
    induction hk using Nat.decreasingInduction with
    | self =>
      refine ⟨?_, ⟨0, fun i _ => lastTor i⟩⟩
      intro i
      have := lastTor i
      exact .of_subsingleton
    | of_succ k hk ih =>
      have := hfree k
      have := hfinite k
      have h := torEuler_shortExact_left (Z (k + 1)) (P.complex.X k) (Z k) N
        (ResolutionSyzygy.ι P k).hom (ResolutionSyzygy.π P k).hom
        (ResolutionSyzygy.injective_ι P k) (ResolutionSyzygy.surjective_π P k)
        (ResolutionSyzygy.exact P k) ih.1
        (isFiniteLength_torModule_of_finite_free_left _ N hlength) ih.2
        ⟨0, fun i hi => by
          obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
          exact torModule_subsingleton_of_flat (R := R) _ N j⟩
      exact ⟨h.1, h.2.1⟩
  let c := fun k => (chi R (Z k) N : ℝ)
  let r := fun k => (Module.finrank R (P.complex.X k) : ℝ) * (Module.length R N).toNat
  have step (k : ℕ) (hk : k ≤ n) : r k = c (k + 1) + c k := by
    have := hfree k
    have := hfinite k
    have h := torEuler_shortExact_left (Z (k + 1)) (P.complex.X k) (Z k) N
      (ResolutionSyzygy.ι P k).hom (ResolutionSyzygy.π P k).hom
      (ResolutionSyzygy.injective_ι P k) (ResolutionSyzygy.surjective_π P k)
      (ResolutionSyzygy.exact P k) (hT (k + 1) (by omega)).1
      (isFiniteLength_torModule_of_finite_free_left _ N hlength) (hT (k + 1) (by omega)).2
      ⟨0, fun i hi => by
        obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
        exact torModule_subsingleton_of_flat (R := R) _ N j⟩
    have he := congrArg (fun a : ℤ => (a : ℝ)) h.2.2
    rw [Int.cast_add, chi_of_finite_free_left _ N] at he
    exact he
  have hs : ∀ k, k ≤ n → (∑ i ∈ Finset.range (k + 1), (-1 : ℝ) ^ i * r i) =
      c 0 + (-1 : ℝ) ^ k * c (k + 1) := by
    intro k
    induction k with
    | zero => intro hk; simpa [add_comm] using step 0 hk
    | succ k ih =>
      intro hk
      rw [Finset.sum_range_succ, ih (by omega), step (k + 1) hk, pow_succ]
      ring
  have hc : c (n + 1) = 0 := by
    dsimp [c, chi]
    have he : ∀ i, torLength R i (Z (n + 1)) N = 0 := by
      intro i
      have := lastTor i
      exact Module.length_eq_zero
    simp [he]
  have h := hs n le_rfl
  rw [hc, mul_zero, add_zero] at h
  change c 0 = _
  rw [← h, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  dsimp [r]
  ring

/-- 整域上で有界有限自由分解をもつ加群 `M` と有限長加群 `N` の交点 Euler 特性は
`rank(M) · length(N)` に等しい。正則局所性を仮定せず、分解を明示的に受け取る。
テンソルした分解の Euler–Poincaré 公式を上の定理から適用し、
階数の交代和は証明済みの `resolution_alternating_finrank` で計算する。 -/
lemma chi_eq_finrank_mul_length_of_resolution
    (R M N : Type u) [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (hN : IsFiniteLength R N)
    (F : CochainComplex (ModuleCat.{u} R) ℤ) (hF : IsResolutionOf F (ModuleCat.of R M))
    (hfree : ∀ i, Module.Free R (F.X i))
    (hfinite : ∀ i, Module.Finite R (F.X i))
    (hbounded : ∃ a b : ℤ, ∀ i, (i < a ∨ b < i) → IsZero (F.X i)) :
    (chi R M N : ℝ) = (Module.finrank R M : ℝ) * (Module.length R N).toNat := by
  obtain ⟨a, b, hb⟩ := hbounded
  let P := hF.toProjectiveResolution
  let n := (-a).toNat
  have hp (i : ℕ) : Module.Free R (P.complex.X i) := hfree _
  have hf (i : ℕ) : Module.Finite R (P.complex.X i) := hfinite _
  have hz (i : ℕ) (hi : n < i) : IsZero (P.complex.X i) := by
    apply hb _ (Or.inl ?_)
    dsimp [n] at hi
    change 0 - (i : ℤ) < a
    omega
  rw [chi_eq_sum_finrank_mul_length_of_resolution R M N hN P hp hf n hz,
    resolution_alternating_finrank P hf n (hz _ (by omega))]

/-- `K(z)` が `A/(z)` の分解なら、係数 `T` の Koszul Euler 特性は
`χ^A(T, A/(z))` に等しい。基底変更した分解のホモロジーを通常の Tor と同一視し、
整数添字の交代和を非負のホモロジー次数に直す。長さの有限性や正則局所性は不要。 -/
lemma koszulEulerChar_eq_chi (A T : Type u) [CommRing A] [CommRing T] [Algebra A T]
    {e : ℕ} (z : Fin e → A) (hz : IsKoszulResolution z) :
    koszulEulerChar A T z = (chi A T (A ⧸ Ideal.span (Set.range z)) : ℝ) := by
  let U := ModuleCat.restrictScalars (algebraMap A T)
  let K := koszulComplex (algebraMap A T ∘ z)
  have hl (i : ℕ) : Module.length A (U.obj (K.homology (-(i : ℤ)))) =
      torLength A i T (A ⧸ Ideal.span (Set.range z)) := by
    let ek := (HomologicalComplex.homologyFunctor (ModuleCat T) (ComplexShape.up ℤ)
      (-(i : ℤ))).mapIso (baseChangeKoszulIso (algebraMap A T) z)
    exact ((U.mapIso ek.symm).toLinearEquiv.trans
      (ordinaryTorIso (A ⧸ Ideal.span (Set.range z)) (koszulComplex z)
        (isResolutionOf_koszul z hz) i)).length_eq
  have hp (i : ℤ) (hi : 0 < i) : ((Module.length A (U.obj (K.homology i))).toNat : ℝ) = 0 := by
    have h := isZero_homology_of_isZero_X K i (koszulComplex_isZero_X_of_pos _ i hi)
    have := ModuleCat.subsingleton_of_isZero (Functor.map_isZero U h)
    simp [Module.length_eq_zero]
  unfold koszulEulerChar chi
  apply alternating_finsum_eq_int_cast _ _ hp
  intro i
  simp only [hl, Int.cast_natCast]

end SerrePositivity

end
