module

public import SerrePositivity.HomologicalAlgebra.ConeLES
public import SerrePositivity.HomologicalAlgebra.Tor
public import SerrePositivity.PerfectComplex.Support
public import SerrePositivity.PerfectComplex.K0
public import Mathlib.Basic.ENNReal.Real
public import Mathlib.Data.Int.Interval
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Noetherian.Nilpotent

/-!
# 加法的な正規化長さによる Euler 評価

`C` 上の複体の評価 `lambdaEuler` と、係数拡大の Tor の評価 `lambdaChi` を定義する。
ホモトピー同値による不変性は有限性なしに示せる。写像錐についての加法性には、
ホモロジーが長さの加法性の対象となる冪ねじれ加群であること、評価の有限性、有界性を用いる。
係数環 `C` の Noether 性は仮定しない。

通常の長さは `NormalizedLength.ordinary` という特殊例なので、通常の Euler 評価の加法性も
ここから導く。後半では、係数拡大後のホモロジーが正規化長さの加法性の対象となることを確認し、
有限性を仮定して `chiLam` を台つき完全複体の `K₀` 上の準同型にする。

有限性を Koszul ホモロジーの評価から導く段階は、補題3.5aの
`Paper/Lemma3_5/Normalized.lean` に残る未証明部分であり、このファイルでは証明しない。
-/

@[expose] public section

universe u

open CategoryTheory Limits IsLocalRing
open scoped ENNReal

namespace SerrePositivity

section general

variable {C : Type u} [CommRing C] {J : Ideal C} (lam : NormalizedLength C J)

/-- `C` 上のコチェイン複体のホモロジーを正規化長さで測った Euler 評価。
`Σ_i (-1)^i λ(H^i(P))` を実数値で定義する。`toReal` は無限長を零に送り、
`finsum` は非零項が無限にある場合に零を返すため、通常の有限和として使うには別途有限性が必要である。 -/
noncomputable def lambdaEuler (P : CochainComplex (ModuleCat.{u} C) ℤ) : ℝ :=
  ∑ᶠ i : ℤ, ((i.negOnePow : ℤ) : ℝ) * (lam.len (P.homology i)).toReal

/-- 正規化長さ `λ` による Euler 標数 `Σ_i (-1)^i λ(Tor_i^R(C, N))`。
`C` の `R` 代数構造は `φ : R →+* C` で与える。無限の長さは `ENNReal.toReal` で `0` になる。
論文 (5.2) の `c_σ` は `φ = ι_σ`、`N = E'` の場合。`lambdaEuler` との関係は
`IntersectionMultiplicity/ResolutionEvaluation.lean`。 -/
noncomputable def lambdaChi {R : Type u} [CommRing R] (φ : R →+* C)
    (N : Type u) [AddCommGroup N] [Module R N] : ℝ :=
  ∑ᶠ i : ℕ, (-1 : ℝ) ^ i * (lam.len (TorAlg φ i N)).toReal

/-- 完全な列 `M → N → L` の中央の長さを、二つの写像の像の長さの和に分解する。
`N` が `J` の冪で消え、正規化長さが有限であることにより、加法性を実数値へ移せる。 -/
lemma lambdaLengthReal_eq_add_range {M N L : Type u} [AddCommGroup M] [Module C M]
    [AddCommGroup N] [Module C N] [AddCommGroup L] [Module C L]
    (f : M →ₗ[C] N) (g : N →ₗ[C] L) (hfg : Function.Exact f g)
    (tN : IsPowTorsion J N) (hN : lam.len N ≠ ⊤) :
    (lam.len N).toReal = (lam.len (LinearMap.range f)).toReal +
      (lam.len (LinearMap.range g)).toReal := by
  have hk : lam.len (LinearMap.ker g) ≠ ⊤ :=
    ne_top_of_le_ne_top hN (lam.len_submodule_le tN _)
  have hr : lam.len (LinearMap.range g) ≠ ⊤ :=
    ne_top_of_le_ne_top hN (lam.len_range_le g tN)
  rw [lam.len_eq_add_ker_range g tN, ENNReal.toReal_add hk hr,
    ← LinearMap.exact_iff.mp hfg]

/-- 複体の項が有界なら、ホモロジーの正規化長さを実数に移した関数は有限な台をもつ。 -/
lemma lambdaHomology_hasFiniteSupport (P : CochainComplex (ModuleCat.{u} C) ℤ)
    (hP : ∃ a b : ℤ, ∀ i, (i < a ∨ b < i) → IsZero (P.X i)) :
    Function.HasFiniteSupport (fun i ↦ (lam.len (P.homology i)).toReal) := by
  obtain ⟨a, b, hab⟩ := hP
  apply (Set.finite_Icc a b).subset
  intro i hi
  by_contra hn
  have hzero : IsZero (P.homology i) :=
    (P.sc i).isZero_homology_of_isZero_X₂ (hab i (by simp only [Set.mem_Icc] at hn; omega))
  have := ModuleCat.subsingleton_of_isZero hzero
  exact hi (by simp [lam.len_eq_zero_of_subsingleton])

/-- ホモトピー同値な複体は同じ正規化 Euler 評価をもつ。
各次数のホモロジーが線形同値になるため、有限性の仮定なしに成り立つ。 -/
lemma lambdaEuler_eq_of_homotopyEquiv {P Q : CochainComplex (ModuleCat.{u} C) ℤ}
    (h : HomotopyEquiv P Q) : lambdaEuler lam P = lambdaEuler lam Q := by
  unfold lambdaEuler
  congr 1
  funext i
  rw [lam.len_congr _ _ (h.toHomologyIso i).toLinearEquiv]

/-- 整数添字の交代和で添字を一つずらすと符号が反転する。`finsum` の規約を含めて成り立つ。 -/
private lemma alternating_finsum_shift (f : ℤ → ℝ) :
    (∑ᶠ i : ℤ, ((i.negOnePow : ℤ) : ℝ) * f (i - 1)) =
      -(∑ᶠ i : ℤ, ((i.negOnePow : ℤ) : ℝ) * f i) := by
  calc
    _ = ∑ᶠ i : ℤ, (((i + 1).negOnePow : ℤ) : ℝ) * f i := by
      have h := finsum_comp_equiv (Equiv.addRight (1 : ℤ))
        (f := fun i : ℤ ↦ ((i.negOnePow : ℤ) : ℝ) * f (i - 1))
      simpa using h.symm
    _ = ∑ᶠ i : ℤ, -(((i.negOnePow : ℤ) : ℝ) * f i) := by
      congr 1
      funext i
      simp [Int.negOnePow_add]
    _ = _ := finsum_neg_distrib _

set_option maxHeartbeats 800000 in
-- ホモロジーの対象に依存する型を含む三つの完全列の移送に、追加の処理時間を許す。
/-- 写像錐の三角形に対する正規化 Euler 評価の加法性。
各ホモロジーが `J` の冪で消え、正規化長さが有限で、指定した複体の項が有界であるとき、
`χ(Cone f) = χ(Q) - χ(P)` を長完全列の像の長さの相殺から導く。係数環の Noether 性は不要である。 -/
theorem lambdaEuler_cone {P Q : CochainComplex (ModuleCat.{u} C) ℤ} (f : P ⟶ Q)
    (hQ : ∃ a b : ℤ, ∀ i, (i < a ∨ b < i) → IsZero (Q.X i))
    (hC : ∃ a b : ℤ, ∀ i, (i < a ∨ b < i) → IsZero ((Cone.cone f).X i))
    (tP : ∀ i, IsPowTorsion J (P.homology i))
    (tQ : ∀ i, IsPowTorsion J (Q.homology i))
    (tC : ∀ i, IsPowTorsion J ((Cone.cone f).homology i))
    (lP : ∀ i, lam.len (P.homology i) ≠ ⊤)
    (lQ : ∀ i, lam.len (Q.homology i) ≠ ⊤)
    (lC : ∀ i, lam.len ((Cone.cone f).homology i) ≠ ⊤) :
    lambdaEuler lam (Cone.cone f) = lambdaEuler lam Q - lambdaEuler lam P := by
  let α := fun i ↦ (HomologicalComplex.homologyMap f i).hom
  let β := fun i ↦ (HomologicalComplex.homologyMap (CochainComplex.mappingCone.inr f) i).hom
  let δ := fun i ↦ (Cone.δ f i (i + 1) rfl).hom
  let a := fun i ↦ (lam.len (LinearMap.range (α i))).toReal
  let b := fun i ↦ (lam.len (LinearMap.range (β i))).toReal
  let d := fun i ↦ (lam.len (LinearMap.range (δ i))).toReal
  have ha : Function.HasFiniteSupport a := by
    apply (lambdaHomology_hasFiniteSupport lam Q hQ).subset
    intro i hi hz
    have hz' : lam.len (Q.homology i) = 0 := by
      have hn := lQ i
      simpa [ENNReal.toReal_eq_zero_iff, hn] using hz
    have : lam.len (LinearMap.range (α i)) = 0 :=
      le_antisymm (hz' ▸ lam.len_submodule_le (tQ i) _) bot_le
    exact hi (by simp [a, this])
  have hb : Function.HasFiniteSupport b := by
    apply (lambdaHomology_hasFiniteSupport lam (Cone.cone f) hC).subset
    intro i hi hz
    have hz' : lam.len ((Cone.cone f).homology i) = 0 := by
      have hn := lC i
      simpa [ENNReal.toReal_eq_zero_iff, hn] using hz
    have : lam.len (LinearMap.range (β i)) = 0 :=
      le_antisymm (hz' ▸ lam.len_submodule_le (tC i) _) bot_le
    exact hi (by simp [b, this])
  have hd : Function.HasFiniteSupport d := by
    apply (lambdaHomology_hasFiniteSupport lam (Cone.cone f) hC).subset
    intro i hi hz
    have hz' : lam.len ((Cone.cone f).homology i) = 0 := by
      have hn := lC i
      simpa [ENNReal.toReal_eq_zero_iff, hn] using hz
    have : lam.len (LinearMap.range (δ i)) = 0 :=
      le_antisymm (hz' ▸ lam.len_range_le (δ i) (tC i)) bot_le
    exact hi (by simp [d, this])
  have hQlen : ∀ i, ((lam.len (Q.homology i)).toReal : ℝ) = a i + b i := fun i ↦
    lambdaLengthReal_eq_add_range lam (α i) (β i)
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
        (Cone.exact₂ f i)) (tQ i) (lQ i)
  have hClen : ∀ i, ((lam.len ((Cone.cone f).homology i)).toReal : ℝ) = b i + d i := fun i ↦
    lambdaLengthReal_eq_add_range lam (β i) (δ i)
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
        (Cone.exact₃ f i (i + 1) rfl)) (tC i) (lC i)
  have hPlen : ∀ i, ((lam.len (P.homology i)).toReal : ℝ) = d (i - 1) + a i := by
    intro i
    obtain ⟨j, rfl⟩ : ∃ j : ℤ, i = j + 1 := ⟨i - 1, by omega⟩
    rw [add_sub_cancel_right]
    exact lambdaLengthReal_eq_add_range lam (δ j) (α (j + 1))
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp
        (Cone.exact₁ f j (j + 1) rfl)) (tP (j + 1)) (lP (j + 1))
  have haw : Function.HasFiniteSupport (fun i : ℤ ↦ ((i.negOnePow : ℤ) : ℝ) * a i) :=
    ha.mul_right _
  have hbw : Function.HasFiniteSupport (fun i : ℤ ↦ ((i.negOnePow : ℤ) : ℝ) * b i) :=
    hb.mul_right _
  have hdw : Function.HasFiniteSupport (fun i : ℤ ↦ ((i.negOnePow : ℤ) : ℝ) * d i) :=
    hd.mul_right _
  have hds : Function.HasFiniteSupport (fun i : ℤ ↦ ((i.negOnePow : ℤ) : ℝ) * d (i - 1)) := by
    have hdp : Function.HasFiniteSupport (fun i : ℤ ↦ d (i - 1)) :=
      hd.preimage (Equiv.subRight (1 : ℤ)).injective.injOn
    exact hdp.mul_right _
  have eQ : lambdaEuler lam Q = (∑ᶠ i : ℤ, ((i.negOnePow : ℤ) : ℝ) * a i) +
      (∑ᶠ i : ℤ, ((i.negOnePow : ℤ) : ℝ) * b i) := by
    simp_rw [lambdaEuler, hQlen, mul_add]
    exact finsum_add_distrib haw hbw
  have eC : lambdaEuler lam (Cone.cone f) = (∑ᶠ i : ℤ, ((i.negOnePow : ℤ) : ℝ) * b i) +
      (∑ᶠ i : ℤ, ((i.negOnePow : ℤ) : ℝ) * d i) := by
    simp_rw [lambdaEuler, hClen, mul_add]
    exact finsum_add_distrib hbw hdw
  have eP : lambdaEuler lam P = -(∑ᶠ i : ℤ, ((i.negOnePow : ℤ) : ℝ) * d i) +
      (∑ᶠ i : ℤ, ((i.negOnePow : ℤ) : ℝ) * a i) := by
    simp_rw [lambdaEuler, hPlen, mul_add]
    rw [finsum_add_distrib hds haw, alternating_finsum_shift]
  rw [eC, eQ, eP]
  ring

/-- 台の零ホモトピー条件から、ホモロジーが有限生成イデアル `J` の冪で消えることを導く。
`J` が生成元の張るイデアルの根基に含まれることを用いる。 -/
lemma supported_homology_isPowTorsion (hfg : J.FG) {n : ℕ}
    {w : Fin n → C} (hJ : J ≤ (Ideal.span (Set.range w)).radical)
    {P : CochainComplex (ModuleCat.{u} C) ℤ} (hP : IsSupported w P) (i : ℤ) :
    IsPowTorsion J (P.homology i) :=
  IsPowTorsion.of_le_radical_annihilator hfg (hJ.trans (by
    have h := Ideal.radical_mono (hP.le_radical_annihilator i)
    simpa only [Ideal.radical_idem] using h))

/-! ## 通常の長さを正規化長さの特殊例として扱う -/

/-- 拡張自然数を拡張非負実数経由で実数に移す操作は、`toNat` 経由の変換と一致する。
両方の変換で `⊤` は零に送られる。 -/
lemma toReal_toENNReal (n : ℕ∞) : (n : ℝ≥0∞).toReal = (n.toNat : ℝ) := by
  induction n using ENat.recTopCoe with
  | top => simp
  | coe k => simp

/-- 通常の Euler 評価は、正規化長さに通常の加群長を選んだ `lambdaEuler` の特殊例である。 -/
lemma chiOrd_eq_lambdaEuler_ordinary {T : Type u} [CommRing T]
    (P : CochainComplex (ModuleCat.{u} T) ℤ) :
    chiOrd P = lambdaEuler (NormalizedLength.ordinary T) P := by
  unfold chiOrd lambdaEuler
  simp only [NormalizedLength.ordinary_len, toReal_toENNReal]

end general

/-! ## 台つき完全複体の正規化 Euler 評価

環の塔 `A → T → C`、`m_A` 準素なイデアルを生成する列 `z`、`m_A C` の冪ねじれ加群上で
加法的な正規化長さを考える。`z` に台をもつ完全 `T` 複体の係数拡大のホモロジーは
この加法性の対象となる。その長さの有限性を仮定して、評価を `K₀` 上の準同型にする。
-/

section supported

variable {A T C : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [CommRing T]
  [Algebra A T] [CommRing C] [Algebra T C] [Algebra A C] [IsScalarTower A T C]
  {e : ℕ} {z : Fin e → A} {lam : NormalizedLength C ((maximalIdeal A).map (algebraMap A C))}

/-- 基底の極大イデアルに台をもつ完全複体を `C` に係数拡大すると、
そのホモロジーは `m_A C` の冪で消える。これにより正規化長さの加法性を適用できる。 -/
lemma chiLam_homology_isPowTorsion
    (hz : (Ideal.span (Set.range z)).radical = maximalIdeal A)
    {P : CochainComplex (ModuleCat.{u} T) ℤ}
    (hP : IsPerfectSupported (algebraMap A T ∘ z) P) (i : ℤ) :
    IsPowTorsion ((maximalIdeal A).map (algebraMap A C))
      ((baseChange (algebraMap T C) P).homology i) := by
  have hfg := (maximalIdeal A).fg_of_isNoetherianRing.map (algebraMap A C)
  have hJ : (maximalIdeal A).map (algebraMap A C) ≤
      (Ideal.span (Set.range (algebraMap A C ∘ z))).radical := by
    have h := Ideal.map_radical_le (algebraMap A C) (I := Ideal.span (Set.range z))
    rw [hz, Ideal.map_span, ← Set.range_comp] at h
    exact h
  have hs : IsSupported (algebraMap A C ∘ z) (baseChange (algebraMap T C) P) := by
    have h := isSupported_baseChange (algebraMap T C) hP.supported
    have heq : algebraMap T C ∘ (algebraMap A T ∘ z) = algebraMap A C ∘ z := by
      funext j
      exact (IsScalarTower.algebraMap_apply A T C (z j)).symm
    rwa [heq] at h
  exact supported_homology_isPowTorsion hfg hJ hs i

omit [IsNoetherianRing A] [Algebra A T] [Algebra T C] [IsScalarTower A T C] in
/-- 係数拡大後の正規化 Euler 評価 `chiLam` は、元の複体のホモトピー同値で不変である。 -/
lemma chiLam_eq_of_homotopyEquiv (φ : T →+* C)
    {P Q : CochainComplex (ModuleCat.{u} T) ℤ} (h : HomotopyEquiv P Q) :
    chiLam lam φ P = chiLam lam φ Q :=
  lambdaEuler_eq_of_homotopyEquiv lam ((ModuleCat.extendScalars φ).mapHomotopyEquiv h)

/-- 台つき完全複体とその写像錐について、係数拡大後のホモロジーの正規化長さが有限なら、
`chiLam` は写像錐の関係式を保つ。有限性そのものは仮定として受け取る。 -/
lemma chiLam_cone_of_finite
    (hz : (Ideal.span (Set.range z)).radical = maximalIdeal A)
    (hfinite : ∀ (P : PerfSupp T (algebraMap A T ∘ z)) (i : ℤ),
      lam.len ((baseChange (algebraMap T C) P.1).homology i) ≠ ⊤)
    (P Q : PerfSupp T (algebraMap A T ∘ z)) (f : P.1 ⟶ Q.1)
    (hc : IsPerfectSupported (algebraMap A T ∘ z) (CochainComplex.mappingCone f)) :
    chiLam lam (algebraMap T C) (CochainComplex.mappingCone f) =
      chiLam lam (algebraMap T C) Q.1 - chiLam lam (algebraMap T C) P.1 := by
  let F := ModuleCat.extendScalars.{u, u, u} (algebraMap T C)
  let fC := (F.mapHomologicalComplex (ComplexShape.up ℤ)).map f
  let k : baseChange (algebraMap T C) (CochainComplex.mappingCone f) ≅ Cone.cone fC :=
    HomologicalComplex.homotopyCofiber.mapHomologicalComplexObjIso f F
  have hbound : ∃ a b : ℤ, ∀ i, (i < a ∨ b < i) → IsZero ((Cone.cone fC).X i) := by
    obtain ⟨a, b, hab⟩ := baseChange_bounded (algebraMap T C) _ hc.bounded
    exact ⟨a, b, fun i hi ↦ (HomologicalComplex.Hom.isoApp k i).isZero_iff.mp (hab i hi)⟩
  have tC : ∀ i, IsPowTorsion ((maximalIdeal A).map (algebraMap A C))
      ((Cone.cone fC).homology i) := fun i ↦
    IsPowTorsion.of_equiv
      (((HomologicalComplex.homologyFunctor _ _ i).mapIso k).toLinearEquiv)
      (chiLam_homology_isPowTorsion hz hc i)
  have lC : ∀ i, lam.len ((Cone.cone fC).homology i) ≠ ⊤ := by
    intro i
    have hi := lam.len_congr _ _
      (((HomologicalComplex.homologyFunctor _ _ i).mapIso k).toLinearEquiv)
    exact ne_of_eq_of_ne hi.symm (hfinite ⟨_, hc⟩ i)
  change lambdaEuler lam (baseChange (algebraMap T C) (CochainComplex.mappingCone f)) =
    lambdaEuler lam (baseChange (algebraMap T C) Q.1) -
      lambdaEuler lam (baseChange (algebraMap T C) P.1)
  rw [lambdaEuler_eq_of_homotopyEquiv lam (HomotopyEquiv.ofIso k)]
  exact lambdaEuler_cone lam fC
    (baseChange_bounded (algebraMap T C) _ Q.2.bounded) hbound
    (chiLam_homology_isPowTorsion hz P.2) (chiLam_homology_isPowTorsion hz Q.2) tC
    (hfinite P) (hfinite Q) lC

/-- すべての対象のホモロジー評価が有限であるという仮定のもとで、
正規化 Euler 評価を台つき完全複体の `K₀` から実数への加法群準同型に降ろす。 -/
noncomputable def chiLamHom_of_finite
    (hz : (Ideal.span (Set.range z)).radical = maximalIdeal A)
    (hfinite : ∀ (P : PerfSupp T (algebraMap A T ∘ z)) (i : ℤ),
      lam.len ((baseChange (algebraMap T C) P.1).homology i) ≠ ⊤) :
    K0Supported T (algebraMap A T ∘ z) →+ ℝ :=
  K0.lift (fun P ↦ chiLam lam (algebraMap T C) P.1)
    (fun _ _ h ↦ chiLam_eq_of_homotopyEquiv (algebraMap T C) h)
    (chiLam_cone_of_finite hz hfinite)

/-- 正規化 Euler 準同型を複体の類に適用すると、その複体の `chiLam` に一致する。 -/
@[simp]
lemma chiLamHom_of_finite_mk
    (hz : (Ideal.span (Set.range z)).radical = maximalIdeal A)
    (hfinite : ∀ (P : PerfSupp T (algebraMap A T ∘ z)) (i : ℤ),
      lam.len ((baseChange (algebraMap T C) P.1).homology i) ≠ ⊤)
    (P : PerfSupp T (algebraMap A T ∘ z)) :
    chiLamHom_of_finite hz hfinite (K0.mk P) = chiLam lam (algebraMap T C) P.1 :=
  K0.lift_mk _ _ _ _

end supported

end SerrePositivity
