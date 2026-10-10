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
# 分解の係数拡大、台、Euler 評価

射影コチェイン分解の `-i` 次ホモロジーを `Tor_i` に同一視し、Euler 評価を計算する。
前半では、整数から自然数への添字の変更、係数拡大の合成、自己同型によるひねりを扱う。
ひねりは係数制限で定義しているので、係数拡大として書き直すと群の逆元が現れる。

後半では、一般の環上の入力 `TorHomologicalAlgebra` を使い、通常の長さでの評価と、
有限長の交わりから得られる台の条件を示す。通常の評価の等式自体には有界性・有限長性は不要だが、
台つき完全複体を作る定理では有界有限自由分解とテンソル積の有限長性を仮定する。
補題3.5や Tor の対称性は用いない。
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace SerrePositivity

/-- 正次数で零になる実数値の列の交代和を、整数添字から `-n` の自然数添字へ移す。
有限台を仮定せず、`finsum` の定義上の値も含めて成り立つ。 -/
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

/-- 正次数の項が零のコチェイン複体について、`H^{-i}` と `Tor_i` の線形同値を使い、
整数添字の Euler 評価を自然数添字の Tor の Euler 評価に同一視する。
ここでは有限性を仮定しない。無限の長さや無限の台に対する定義上の値も含めた等式である。 -/
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

/-- 加群の任意の射影コチェイン分解を係数拡大すると、その正規化 Euler 評価は
係数拡大の左導来関手で定めた Tor の Euler 評価に一致する。 -/
theorem lambdaEuler_baseChange_resolution (φ : R →+* C)
    {M : Type u} [AddCommGroup M] [Module R M]
    {F : CochainComplex (ModuleCat.{u} R) ℤ} (hF : IsResolutionOf F (ModuleCat.of R M)) :
    lambdaEuler lam (baseChange φ F) = lambdaChi lam φ M :=
  lambdaEuler_eq_lambdaChi_of_homologyEquiv lam φ M (baseChange φ F)
    (baseChange_isZero_X_of_pos φ F hF.isZero_X)
    (fun i ↦ (torIsoCochain φ hF i).toLinearEquiv)

/-- `R → T → C` に沿う二段階の係数拡大を、合成 `R → C` に沿う係数拡大に同一視する複体の同型。 -/
noncomputable def baseChangeCompIso (φ : R →+* T) (ψ : T →+* C)
    (F : CochainComplex (ModuleCat.{u} R) ℤ) :
    baseChange ψ (baseChange φ F) ≅ baseChange (ψ.comp φ) F :=
  (Functor.mapHomologicalComplexCompIso (ModuleCat.extendScalarsComp φ ψ).symm
    (ComplexShape.up ℤ)).app F

/-- 射影分解を二段階で係数拡大した複体の `-i` 次ホモロジーを、
合成した環準同型に対する `Tor_i` と線形同値にする。 -/
noncomputable def torAlgBaseChangeCompEquiv (φ : R →+* T) (ψ : T →+* C)
    {M : Type u} [AddCommGroup M] [Module R M]
    {F : CochainComplex (ModuleCat.{u} R) ℤ} (hF : IsResolutionOf F (ModuleCat.of R M))
    (i : ℕ) : TorAlg (ψ.comp φ) i M ≃ₗ[C]
      (baseChange ψ (baseChange φ F)).homology (-(i : ℤ)) :=
  ((torIsoCochain (ψ.comp φ) hF i) ≪≫
    (HomologicalComplex.homologyFunctor _ _ (-(i : ℤ))).mapIso
      (baseChangeCompIso φ ψ F).symm).toLinearEquiv

/-- 分解の二段階の係数拡大による正規化 Euler 評価を、合成した係数構造での Tor の評価に書き換える。 -/
theorem chiLam_baseChange_resolution (φ : R →+* T) (ψ : T →+* C)
    {M : Type u} [AddCommGroup M] [Module R M]
    {F : CochainComplex (ModuleCat.{u} R) ℤ} (hF : IsResolutionOf F (ModuleCat.of R M)) :
    chiLam lam ψ (baseChange φ F) = lambdaChi lam (ψ.comp φ) M := by
  change lambdaEuler lam (baseChange ψ (baseChange φ F)) = _
  rw [lambdaEuler_eq_of_homotopyEquiv lam (HomotopyEquiv.ofIso (baseChangeCompIso φ ψ F))]
  exact lambdaEuler_baseChange_resolution lam (ψ.comp φ) hF

/-- 環自己同型に沿う係数制限を、その逆自己同型に沿う係数拡大に同一視する自然同型。
ノルム比較で群の添字に逆元が現れる理由となる。 -/
noncomputable def restrictScalarsIsoExtendInverse (σ : T ≃+* T) :
    ModuleCat.restrictScalars.{u} σ.toRingHom ≅ ModuleCat.extendScalars σ.symm.toRingHom :=
  Adjunction.leftAdjointUniq (ModuleCat.restrictScalarsEquivalenceOfRingEquiv σ).toAdjunction
    (ModuleCat.extendRestrictScalarsAdj σ.symm.toRingHom)

variable {G : Type u} [Group G] [MulSemiringAction G T]

/-- 係数拡大した複体を `g` でひねることを、元の環準同型に `g⁻¹` を合成した係数拡大に同一視する。 -/
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

/-- ひねりと二段階の係数拡大を行った分解のホモロジーを、逆元でひねった係数構造の Tor と同一視する。
一貫して第2変数の加群を分解するため、Tor の対称性を必要としない。 -/
noncomputable def torAlgTwistBaseChangeEquiv (φ : R →+* T) (ψ : T →+* C) (g : G)
    {M : Type u} [AddCommGroup M] [Module R M]
    {F : CochainComplex (ModuleCat.{u} R) ℤ} (hF : IsResolutionOf F (ModuleCat.of R M))
    (i : ℕ) : TorAlg (ψ.comp ((MulSemiringAction.toRingHom G T g⁻¹).comp φ)) i M ≃ₗ[C]
      (baseChange ψ (twist g (baseChange φ F))).homology (-(i : ℤ)) :=
  ((torAlgBaseChangeCompEquiv ((MulSemiringAction.toRingHom G T g⁻¹).comp φ) ψ hF i).toModuleIso ≪≫
    (HomologicalComplex.homologyFunctor _ _ (-(i : ℤ))).mapIso
      (((ModuleCat.extendScalars ψ).mapHomologicalComplex (ComplexShape.up ℤ)).mapIso
        (twistBaseChangeIso φ g F).symm)).toLinearEquiv

/-- ひねった分解の正規化 Euler 評価は、逆元でひねった係数構造の Tor の Euler 評価に一致する。 -/
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

剰余体への写像が全射なら、通常の長さで測った分解の Euler 評価は交点重複度に一致する。
さらに有界有限自由分解とテンソル積の有限長性があれば、係数拡大した複体は閉点に台をもつ。
後者は `PerfectComplex/Support.lean` のホモロジーの台と零ホモトピーの対応を用いる。
いずれも必要な Tor の同一視・有限長性は `Inputs.TorHomologicalAlgebra` から受け取る。
-/

public section

universe u

open CategoryTheory Limits IsLocalRing TensorProduct

namespace SerrePositivity

variable {R T : Type u} [CommRing R] [IsNoetherianRing R]
  [Inputs.TorHomologicalAlgebra R] [CommRing T] [IsLocalRing T] [Algebra R T]
  [Module.Finite R T]

omit [IsNoetherianRing R] [Module.Finite R T] in
/-- 係数環の剰余体への写像が全射なら、係数拡大した分解の通常 Euler 評価は `χ^R(T, M)` に一致する。
長さの係数制限不変性と入力 `ordinaryTorIso` による。有限長性や分解の有界性はこの等式には不要である。 -/
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

/-- 有限な局所代数 `T` と有限生成加群 `M` のテンソル積が有限長なら、
`M` の有界有限自由分解を `T` に係数拡大した複体は、閉点に台をもつ完全複体となる。
Tor の有限長性は入力クラスから受け取り、ホモロジーの台を零ホモトピーの条件に変換する。 -/
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
        (Module.length_ne_top_iff.mp (ne_of_eq_of_ne e.length_eq ht))
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
