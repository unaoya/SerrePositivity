module

public import SerrePositivity.HomologicalAlgebra.Tor
public import SerrePositivity.PerfectComplex.NormalizedEuler
public import Mathlib.Algebra.Ring.Action.Group
public import Mathlib.CategoryTheory.Adjunction.Unique
public import SerrePositivity.Inputs.IntersectionTheory
public import SerrePositivity.PerfectComplex.Support
public import SerrePositivity.PerfectComplex.Closure
public import SerrePositivity.CommutativeAlgebra.FiniteLength

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

/-- 正の添字で `0` になる実数列 `a : ℤ → ℝ` について、交代和 `Σ_{i ∈ ℤ} (-1)^i a_i` は
`Σ_{n ∈ ℕ} (-1)^n a_{-n}` に等しい。`finsum` の台が `{-n}` に含まれることと、単射 `n ↦ -n` に沿った
`finsum` の取り直し（`finsum_mem_range`）による。有限台を仮定せず、`finsum` の規約による値も含めて
成り立つ。 -/
lemma alternating_finsum_eq_nat (a : ℤ → ℝ) (hpos : ∀ i, 0 < i → a i = 0) :
    (∑ᶠ i : ℤ, ((i.negOnePow : ℤ) : ℝ) * a i) =
      ∑ᶠ n : ℕ, (-1 : ℝ) ^ n * a (-(n : ℤ)) := by
  let f := fun i : ℤ ↦ ((i.negOnePow : ℤ) : ℝ) * a i
  let g := fun i : ℕ ↦ -(i : ℤ)
  have hg : Function.Injective g := by
    intro i j hij
    dsimp [g] at hij
    exact_mod_cast neg_injective hij
  have hs : Function.support f ⊆ Set.range g := by
    intro i hi
    have hnonpos : i ≤ 0 := by
      by_contra hn
      exact hi (by simp [f, hpos i (by omega)])
    refine ⟨(-i).toNat, ?_⟩
    dsimp [g]
    rw [Int.toNat_of_nonneg (by omega), neg_neg]
  have hfull : (∑ᶠ i ∈ Set.range g, f i) = ∑ᶠ i : ℤ, f i := by
    rw [← finsum_mem_inter_support f (Set.range g), Set.inter_eq_right.mpr hs,
      finsum_mem_support]
  change (∑ᶠ i : ℤ, f i) = _
  rw [← hfull, finsum_mem_range hg]
  simp only [f, g, Int.negOnePow_neg, Int.cast_negOnePow_natCast]

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

/-- 二段階の係数拡大 `(F ⊗_R T) ⊗_T C` と一段階の係数拡大 `F ⊗_R C`（合成 `ψ ∘ φ : R → C` に沿う）の
複体の同型。Mathlib の `ModuleCat.extendScalarsComp`（関手の合成の自然同型）を各項に施す。 -/
noncomputable def baseChangeCompIso (φ : R →+* T) (ψ : T →+* C)
    (F : CochainComplex (ModuleCat.{u} R) ℤ) :
    baseChange ψ (baseChange φ F) ≅ baseChange (ψ.comp φ) F :=
  (Functor.mapHomologicalComplexCompIso (ModuleCat.extendScalarsComp φ ψ).symm
    (ComplexShape.up ℤ)).app F

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

/-- 環自己同型 `σ` に沿った係数制限は、逆 `σ⁻¹` に沿った係数拡大と自然同型：`restrictScalars σ` は
圏同値で `restrictScalars σ⁻¹` の左随伴、一方 `extendScalars σ⁻¹` も `restrictScalars σ⁻¹` の左随伴
なので、左随伴の一意性（`Adjunction.leftAdjointUniq`）による。ノルム比較で群の添字に逆元が現れる
理由。 -/
noncomputable def restrictScalarsIsoExtendInverse (σ : T ≃+* T) :
    ModuleCat.restrictScalars.{u} σ.toRingHom ≅ ModuleCat.extendScalars σ.symm.toRingHom :=
  Adjunction.leftAdjointUniq (ModuleCat.restrictScalarsEquivalenceOfRingEquiv σ).toAdjunction
    (ModuleCat.extendRestrictScalarsAdj σ.symm.toRingHom)

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
    obtain ⟨e⟩ := Inputs.TorHomologicalAlgebra.ordinaryTorIso T M F hF i
    exact (length_restrictScalars_eq hres _).symm.trans e.length_eq
  have hz (i : ℤ) (hi : 0 < i) : ((Module.length T (K.homology i)).toNat : ℝ) = 0 := by
    have := ModuleCat.subsingleton_of_isZero (isZero_homology_of_isZero_X _ _
      (baseChange_isZero_X_of_pos (algebraMap R T) F hF.isZero_X i hi))
    simp [Module.length_eq_zero]
  change (∑ᶠ i : ℤ, ((i.negOnePow : ℤ) : ℝ) *
    ((Module.length T (K.homology i)).toNat : ℝ)) = _
  rw [alternating_finsum_eq_nat _ hz]
  unfold chi
  have hcast : (((∑ᶠ i : ℕ, (-1 : ℤ) ^ i * ((torLength R i T M).toNat : ℤ)) : ℤ) : ℝ) =
      ∑ᶠ i : ℕ, ((((-1 : ℤ) ^ i * ((torLength R i T M).toNat : ℤ)) : ℤ) : ℝ) := by
    exact (Int.castRingHom ℝ).toAddMonoidHom.map_finsum_of_injective Int.cast_injective
      (fun i : ℕ ↦ (-1 : ℤ) ^ i * ((torLength R i T M).toNat : ℤ))
  rw [hcast]
  congr 1
  funext i
  simp only [hlen, Int.cast_mul,
    Int.cast_pow, Int.cast_neg, Int.cast_one, Int.cast_natCast]

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
      obtain ⟨e⟩ := Inputs.TorHomologicalAlgebra.ordinaryTorIso T M F hF n
      have ht := Inputs.TorHomologicalAlgebra.finiteTor T M htensor n
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
