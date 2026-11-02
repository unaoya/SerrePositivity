module

public import SerrePositivity.HomologicalAlgebra.Complex.ConeLES
public import SerrePositivity.HomologicalAlgebra.Tor
public import SerrePositivity.PerfectComplex.Free.Support
public import SerrePositivity.PerfectComplex.Free.K0
public import SerrePositivity.LengthAlgebra.Core
public import Mathlib.Basic.ENNReal.Real
public import Mathlib.Data.Int.Interval
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.RingTheory.Noetherian.Nilpotent
public import SerrePositivity.CommutativeAlgebra.Length.Basic
public import SerrePositivity.HomologicalAlgebra.Complex.Basic
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-! # 台つき完全複体の Euler 評価

## 概要

正規化長さで測った Euler 評価 `lambdaEuler lam P` = Σ (-1)^i λ(H^i(P)) と、通常の長さによる `chiOrd` を、台つき完全複体の K₀ 上の準同型にする。

## 方針

写像錐の長完全列での加法性（LengthAlgebra/Core の Euler 定理）から K₀ の関係式を確かめる。

## 規約

`lambdaEuler`・`chiOrd` は CLMST が名前と定義の展開で使うので変えない（refactor-plan §4.2.6）。

## 使われ方

Paper の Lemma 3.5・§4、LengthAlgebra、IntersectionMultiplicity。
-/

@[expose] public noncomputable section

universe u

section NormalizedEulerPart

open CategoryTheory Limits IsLocalRing
open scoped ENNReal

namespace SerrePositivity

section general

variable {C : Type u} [CommRing C] {J : Ideal C} (lam : NormalizedLength C J)

/-- 複体 `P` のホモロジーを正規化長さ `λ` で測った Euler 評価 `Σ_i (-1)^i λ(H^i(P))`（実数値）。
`toReal` は無限長を `0` に送り、`finsum` は非零項が無限個なら `0` を返すので、通常の有限和として
使うには有界性と有限性が別に要る。`chiLam`（`Basic.lean`）は係数拡大した複体のこれ。 -/
noncomputable def lambdaEuler (P : CochainComplex (ModuleCat.{u} C) ℤ) : ℝ :=
  ∑ᶠ i : ℤ, ((i.negOnePow : ℤ) : ℝ) * (lam.len (P.homology i)).toReal

/-- `Tor` を正規化長さ `λ` で測った Euler 標数 `Σ_i (-1)^i λ(Tor_i^R(C, N))`（実数値）。`C` の `R` 代数
構造は `φ : R →+* C` で与え、`Tor_i^R(C, N)` は `TorAlg φ i N`（`HomologicalAlgebra/Tor.lean`）。
無限の長さは `0` になる。論文 (5.2) の `c_σ` は `φ = ι_σ`（ひねった構造射）、`N = E'` の場合。
`N` の分解 `P` をとれば `lambdaEuler lam (P ⊗ C)` に等しい
（`IntersectionMultiplicity/ResolutionEvaluation.lean`）。 -/
noncomputable def lambdaChi {R : Type u} [CommRing R] (φ : R →+* C)
    (N : Type u) [AddCommGroup N] [Module R N] : ℝ :=
  ∑ᶠ i : ℕ, (-1 : ℝ) ^ i * (lam.len (TorAlg φ i N)).toReal

/-- 複体 `P` が `Q` の直和因子なら、ホモロジーも直和因子となる。
`Q` のホモロジーが `J` 冪ねじれで正規化長さが有限なら、`P` のホモロジーの長さも有限。 -/
lemma lambdaHomology_ne_top_of_retract {P Q : CochainComplex (ModuleCat.{u} C) ℤ}
    (h : Retract P Q) (i : ℤ) (tQ : IsPowTorsion J (Q.homology i))
    (hQ : lam.len (Q.homology i) ≠ ⊤) : lam.len (P.homology i) ≠ ⊤ := by
  let hh := h.map (HomologicalComplex.homologyFunctor (ModuleCat.{u} C) (ComplexShape.up ℤ) i)
  exact ne_top_of_le_ne_top hQ (lam.len_le_of_injective hh.i.hom
    ((ModuleCat.mono_iff_injective hh.i).mp inferInstance) tQ)

/-- ホモトピー同値な複体の `lambdaEuler` は等しい。各次数のホモロジーが線形同型で、`λ` は同型で
不変だから。有限性・有界性の仮定は要らない（両辺が規約どおりに同じ値をとる）。 -/
lemma lambdaEuler_eq_of_homotopyEquiv {P Q : CochainComplex (ModuleCat.{u} C) ℤ}
    (h : HomotopyEquiv P Q) : lambdaEuler lam P = lambdaEuler lam Q := by
  unfold lambdaEuler
  congr 1
  funext i
  rw [lam.len_congr _ _ (h.toHomologyIso i).toLinearEquiv]

/-- **写像錐についての加法性**：`f : P ⟶ Q` について `λ-χ(Cone f) = λ-χ(Q) - λ-χ(P)`。
有限長さの冪ねじれ加群のアーベル圏に長完全列を入れ、共通の Euler 加法性を適用する。
`Q` と `Cone f` の有界性、各ホモロジーの冪ねじれ性・長さの有限性を使う。
複体の射影性・有限生成性、環の Noether 性、Koszul 条件は要求しない。 -/
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
  have h := LengthAlgebra.normalizedLength_euler_exact_sequence lam
    (fun i ↦ P.homology i) (fun i ↦ Q.homology i) (fun i ↦ (Cone.cone f).homology i)
    (fun i ↦ HomologicalComplex.homologyMap f i)
    (fun i ↦ HomologicalComplex.homologyMap (CochainComplex.mappingCone.inr f) i)
    (fun i ↦ Cone.δ f i (i + 1) rfl)
    (fun i ↦ Cone.exact₂ f i) (fun i ↦ Cone.exact₃ f i (i + 1) rfl)
    (fun i ↦ Cone.exact₁ f i (i + 1) rfl) tP tQ tC lP lQ lC
    (by
      obtain ⟨a, b, hab⟩ := hQ
      exact ⟨a, b, fun i hi ↦ isZero_homology_of_isZero_X Q i (hab i hi)⟩)
    (by
      obtain ⟨a, b, hab⟩ := hC
      exact ⟨a, b, fun i hi ↦ isZero_homology_of_isZero_X (Cone.cone f) i (hab i hi)⟩)
  change lambdaEuler lam Q = lambdaEuler lam P + lambdaEuler lam (Cone.cone f) at h
  exact (eq_sub_iff_add_eq).mpr (by simpa only [add_comm] using h.symm)

/-- `w` に台をもつ複体のホモロジーは、`J ⊆ √(w)` なる有限生成イデアル `J` の冪で消える。台の条件から
`(w) ⊆ √(Ann H^i(P))`（`IsSupported.le_radical_annihilator`）なので `J ⊆ √(Ann H^i(P))`、あとは
`IsPowTorsion.of_le_radical_annihilator`。正規化長さの加法性の対象であることの根拠。 -/
lemma supported_homology_isPowTorsion (hfg : J.FG) {n : ℕ}
    {w : Fin n → C} (hJ : J ≤ (Ideal.span (Set.range w)).radical)
    {P : CochainComplex (ModuleCat.{u} C) ℤ} (hP : IsSupported w P) (i : ℤ) :
    IsPowTorsion J (P.homology i) :=
  IsPowTorsion.of_le_radical_annihilator hfg (hJ.trans (by
    have h := Ideal.radical_mono (hP.le_radical_annihilator i)
    simpa only [Ideal.radical_idem] using h))

/-- 各元の作用が零ホモトピックなら、係数つき Koszul 複体のホモロジーの有限性は
元の複体へ戻る。冪ねじれ性は `J` の有限生成性と `J ⊆ √(x)` から導く。
有界性や項の自由性はこの引き戻し自体には必要ない。 -/
lemma lambdaHomology_ne_top_of_koszulComplexOn (hfg : J.FG) {n : ℕ}
    (x : Fin n → C) (hJ : J ≤ (Ideal.span (Set.range x)).radical)
    (P : CochainComplex (ModuleCat.{u} C) ℤ)
    (h : ∀ j, Nonempty (Homotopy (smulId (x j) P) 0)) (i : ℤ)
    (hfinite : lam.len ((koszulComplexOn x P).homology i) ≠ ⊤) :
    lam.len (P.homology i) ≠ ⊤ :=
  lambdaHomology_ne_top_of_retract lam (retractKoszulComplexOn x P h) i
    (supported_homology_isPowTorsion hfg hJ (isSupported_koszulComplexOn x P) i) hfinite

/-! ## 通常の長さを正規化長さの特殊例として扱う -/

/-- `ℕ∞` の値を `ℝ≥0∞` 経由で実数に移しても、`toNat` 経由で移しても同じ（どちらも `⊤` を `0` に
送る）。`chiOrd`（`toNat` 経由）と `lambdaEuler (ordinary T)`（`toReal` 経由）を比べるのに使う。 -/
lemma toReal_toENNReal (n : ℕ∞) : (n : ℝ≥0∞).toReal = (n.toNat : ℝ) := by
  induction n using ENat.recTopCoe with
  | top => simp
  | coe k => simp

/-- 通常の Euler 評価 `chiOrd` は、正規化長さとして通常の長さ `NormalizedLength.ordinary T` をとった
`lambdaEuler` に等しい。これで `lambdaEuler` の定理が `chiOrd` に特殊化できる（`OrdinaryEuler.lean`）。 -/
lemma chiOrd_eq_lambdaEuler_ordinary {T : Type u} [CommRing T]
    (P : CochainComplex (ModuleCat.{u} T) ℤ) :
    chiOrd P = lambdaEuler (NormalizedLength.ordinary T) P := by
  unfold chiOrd lambdaEuler
  simp only [NormalizedLength.ordinary_len, toReal_toENNReal]

end general

/-! ## 台つき完全複体の正規化 Euler 評価

論文 Lemma 3.5a の設定：環の塔 `A → T → C`（`A` は Noether 局所環）、`√(z) = m_A` なる `A` の元の列
`z`、`m_A C` の冪ねじれ加群の上で加法的な正規化長さ `lam`。`z` に台をもつ完全 `T` 複体 `P` を `C` に
係数拡大した `P ⊗_T C` のホモロジーは `m_A C` の冪で消える（`chiLam_homology_isPowTorsion`）ので、
`lam` の加法性の対象になる。その長さの有限性を仮定して、`chiLam lam (algebraMap T C) P` を
`K₀^{(z)}(T)` 上の準同型にする（`chiLamHom_of_finite`）。
-/

section supported

variable {A T C : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [CommRing T]
  [Algebra A T] [CommRing C] [Algebra T C] [Algebra A C] [IsScalarTower A T C]
  {e : ℕ} {z : Fin e → A} {lam : NormalizedLength C ((maximalIdeal A).map (algebraMap A C))}

/-- `√(z) = m_A` のとき、`z` に台をもつ完全 `T` 複体 `P` の係数拡大 `P ⊗_T C` のホモロジーは `m_A C` の
冪で消える。`P ⊗_T C` は `z` の `C` での像に台をもち（`isSupported_baseChange`）、
`m_A C = (√(z)) C ⊆ √((z) C)` なので `supported_homology_isPowTorsion` が使える。`m_A` が有限生成で
あることに `A` の Noether 性を使う。 -/
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
/-- `chiLam` はもとの複体のホモトピー同値で不変（係数拡大はホモトピー同値を保つ）。 -/
lemma chiLam_eq_of_homotopyEquiv (φ : T →+* C)
    {P Q : CochainComplex (ModuleCat.{u} T) ℤ} (h : HomotopyEquiv P Q) :
    chiLam lam φ P = chiLam lam φ Q :=
  lambdaEuler_eq_of_homotopyEquiv lam ((ModuleCat.extendScalars φ).mapHomotopyEquiv h)

/-- 係数拡大後のホモロジーの `λ` がすべて有限（`hfinite`）なら、`chiLam` は錐の関係式
`chiLam (Cone f) = chiLam Q - chiLam P` をみたす。係数拡大は写像錐と可換
（`(Cone f) ⊗_T C ≅ Cone(f ⊗_T C)`）なので、`lambdaEuler_cone` を `f ⊗_T C` に適用する。冪ねじれの
条件は `chiLam_homology_isPowTorsion`、有界性は `baseChange_bounded`。 -/
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

/-- 有限性の仮定 `hfinite` のもとで、`chiLam` を `K₀^{(z)}(T)` から `ℝ` への準同型に降ろしたもの。
`K0.lift` にホモトピー不変性と錐の関係式を渡す。Lemma 3.5a・3.5b の正規化長さ側
（`Paper/Section3/NormComparison.lean`）で、`K0.hom_ext_koszul` と組み合わせて使う。 -/
noncomputable def chiLamHom_of_finite
    (hz : (Ideal.span (Set.range z)).radical = maximalIdeal A)
    (hfinite : ∀ (P : PerfSupp T (algebraMap A T ∘ z)) (i : ℤ),
      lam.len ((baseChange (algebraMap T C) P.1).homology i) ≠ ⊤) :
    K0Supported T (algebraMap A T ∘ z) →+ ℝ :=
  K0.lift (fun P ↦ chiLam lam (algebraMap T C) P.1)
    (fun _ _ h ↦ chiLam_eq_of_homotopyEquiv (algebraMap T C) h)
    (chiLam_cone_of_finite hz hfinite)

/-- `chiLamHom_of_finite [P] = chiLam lam (algebraMap T C) P`。 -/
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

end NormalizedEulerPart

section OrdinaryEulerPart

open CategoryTheory Limits

namespace SerrePositivity

variable {T : Type u} [CommRing T] [IsNoetherianRing T]

/-- Noether 環 `T` 上、`T/(w)` が Artin 環なら、`w` に台をもつ完全複体 `P` の各ホモロジー `H^i(P)` は
有限長である。`H^i(P)` は有限生成（項が有限生成で `T` が Noether）で、台の条件から
`(w) ⊆ √(Ann H^i(P))`（`IsSupported.le_radical_annihilator`）なので、
`isFiniteLength_of_le_radical_annihilator` が使える。長さ代数や正規化基底の選択は要らない。 -/
theorem homology_finiteLength_of_isPerfectSupported {e : ℕ} {w : Fin e → T}
    [IsArtinianRing (T ⧸ Ideal.span (Set.range w))]
    {P : CochainComplex (ModuleCat.{u} T) ℤ} (hP : IsPerfectSupported w P) (i : ℤ) :
    IsFiniteLength T (P.homology i) := by
  have := hP.finite i
  have := homology_moduleFinite P i
  exact isFiniteLength_of_le_radical_annihilator _ _ (hP.supported.le_radical_annihilator i)

omit [IsNoetherianRing T] in
/-- `chiOrd` はホモトピー同値で不変（`lambdaEuler_eq_of_homotopyEquiv` の特殊化）。有限性は要らない。 -/
lemma chiOrd_eq_of_homotopyEquiv {P Q : CochainComplex (ModuleCat.{u} T) ℤ}
    (h : HomotopyEquiv P Q) : chiOrd P = chiOrd Q := by
  rw [chiOrd_eq_lambdaEuler_ordinary, chiOrd_eq_lambdaEuler_ordinary]
  exact lambdaEuler_eq_of_homotopyEquiv _ h

omit [IsNoetherianRing T] in
/-- **写像錐についての加法性**：`Q` と `Cone f` が有界で、`P`、`Q`、`Cone f` のホモロジーが有限長なら
`χ(Cone f) = χ(Q) - χ(P)`。`lambdaEuler_cone` に `NormalizedLength.ordinary` を代入する。`J = ⊥` の
冪ねじれ条件は `IsPowTorsion.bot` で自動、`ℕ∞` の有限性を `ℝ≥0∞` の有限性に移す。 -/
theorem chiOrd_cone {P Q : CochainComplex (ModuleCat.{u} T) ℤ} (f : P ⟶ Q)
    (hQ : ∃ a b : ℤ, ∀ i, (i < a ∨ b < i) → IsZero (Q.X i))
    (hC : ∃ a b : ℤ, ∀ i, (i < a ∨ b < i) → IsZero ((Cone.cone f).X i))
    (lP : ∀ i, Module.length T (P.homology i) ≠ ⊤)
    (lQ : ∀ i, Module.length T (Q.homology i) ≠ ⊤)
    (lC : ∀ i, Module.length T ((Cone.cone f).homology i) ≠ ⊤) :
    chiOrd (Cone.cone f) = chiOrd Q - chiOrd P := by
  simp only [chiOrd_eq_lambdaEuler_ordinary]
  exact lambdaEuler_cone _ f hQ hC (fun _ ↦ IsPowTorsion.bot) (fun _ ↦ IsPowTorsion.bot)
    (fun _ ↦ IsPowTorsion.bot) (fun i ↦ ENat.toENNReal_ne_top.mpr (lP i))
    (fun i ↦ ENat.toENNReal_ne_top.mpr (lQ i)) (fun i ↦ ENat.toENNReal_ne_top.mpr (lC i))

/-- Noether 環 `T` 上、`T/(w)` が Artin 環のとき、`chiOrd` を `K₀^{(w)}(T)` から `ℝ` への準同型に
降ろしたもの。`K0.lift` にホモトピー不変性と錐の関係式（有限性は
`homology_finiteLength_of_isPerfectSupported` で供給）を渡す。Lemma 3.5b の通常の長さ側
（`Paper/Section3/NormComparison.lean`）で `K0.hom_ext_koszul` と組み合わせて使う。 -/
noncomputable def chiOrdHom {e : ℕ} (w : Fin e → T)
    [IsArtinianRing (T ⧸ Ideal.span (Set.range w))] : K0Supported T w →+ ℝ :=
  K0.lift (fun P ↦ chiOrd P.1)
    (fun _ _ h ↦ chiOrd_eq_of_homotopyEquiv h)
    (fun P Q f hc ↦ chiOrd_cone f Q.2.bounded hc.bounded
      (fun i ↦ Module.length_ne_top_iff.mpr (homology_finiteLength_of_isPerfectSupported P.2 i))
      (fun i ↦ Module.length_ne_top_iff.mpr (homology_finiteLength_of_isPerfectSupported Q.2 i))
      (fun i ↦ Module.length_ne_top_iff.mpr (homology_finiteLength_of_isPerfectSupported hc i)))

/-- `chiOrdHom w [P] = chiOrd P`。 -/
@[simp]
lemma chiOrdHom_mk {e : ℕ} (w : Fin e → T)
    [IsArtinianRing (T ⧸ Ideal.span (Set.range w))] (P : PerfSupp T w) :
    chiOrdHom w (K0.mk P) = chiOrd P.1 := K0.lift_mk _ _ _ _

/-! ## 環自己同型に沿う係数制限 -/

omit [IsNoetherianRing T] in
/-- 環自己同型 `σ : T ≃+* T` に沿って複体の係数を制限しても `chiOrd` は変わらない。係数制限は圏同値
なのでホモロジーと可換で（`mapHomologyIso`）、環自己同型に沿った係数制限は加群の長さを変えない
（`length_restrictScalars_equiv`）から。有限長性・有界性の仮定は要らない。 -/
lemma chiOrd_restrictScalars_equiv (σ : T ≃+* T)
    (P : CochainComplex (ModuleCat.{u} T) ℤ) :
    chiOrd (((ModuleCat.restrictScalars σ.toRingHom).mapHomologicalComplex _).obj P) =
      chiOrd P := by
  let F := ModuleCat.restrictScalars.{u} σ.toRingHom
  have : F.IsEquivalence := inferInstance
  unfold chiOrd
  congr 1
  funext i
  let e : ((F.mapHomologicalComplex _).obj P).homology i ≅ F.obj (P.homology i) :=
    (P.sc i).mapHomologyIso F
  rw [e.toLinearEquiv.length_eq, length_restrictScalars_equiv]

omit [IsNoetherianRing T] in
/-- ひねりは `chiOrd` を保つ：`χ(g^*P) = χ(P)`。ひねりは環自己同型 `g •` に沿った係数制限だから。
§5（`Paper/Section5/`）で、`G` 軌道の和の `χ` を計算するときに使う。 -/
lemma chiOrd_twist {G : Type u} [Group G] [MulSemiringAction G T]
    (g : G) (P : CochainComplex (ModuleCat.{u} T) ℤ) : chiOrd (twist g P) = chiOrd P :=
  chiOrd_restrictScalars_equiv (MulSemiringAction.toRingEquiv G T g) P

end SerrePositivity

end OrdinaryEulerPart
