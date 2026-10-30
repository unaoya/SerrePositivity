module

public import SerrePositivity.HomologicalAlgebra.Resolution
public import Mathlib.Algebra.Homology.Augment
public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import SerrePositivity.CommutativeAlgebra.RegularSequence
public import SerrePositivity.CommutativeAlgebra.RegularLocalRing.Basic
public import SerrePositivity.CommutativeAlgebra.Localization.Lattice
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Module.FinitePresentation
public import SerrePositivity.HomologicalAlgebra.FiniteFreeBaseChange
public import SerrePositivity.HomologicalAlgebra.TorFlatBaseChangeVanishing
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.TensorProduct.Finite
public import SerrePositivity.HomologicalAlgebra.KProjectiveLift
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import SerrePositivity.CommutativeAlgebra.Length.Basic
public import SerrePositivity.CommutativeAlgebra.KoszulResolution

/-! # 有界有限自由分解

## 概要

Noether 環上の有限生成加群について、有限自由加群からの全射と核を繰り返し選んで有限自由分解を作り、第 n 核が自由なら長さ n で止める。極大イデアルが正則列で生成される局所環（正則局所環）とその局所化では有界有限自由分解が存在する（`regularResolution`・`localizedRegularResolution`）。局所化に沿った有限加群の降下、有限自由分解を持つ加群の自己準同型のトレースの降下（正則局所環の正規性に使う）、各項の大きさを保つ馬蹄構成、剰余体の固定された分解から任意の有限長加群の分解を長さに比例する大きさで作ること（`exists_free_resolution_length_mul`）を与える。

## 方針

分解の延長は短完全列と核の射影分解から中央の分解を作ることの反復。馬蹄構成は導来圏の連結射を K 射影性で鎖写像に持ち上げて写像余錐を取る。

## 規約

`coverRank`・`cover`・`coverπ` は `(Module.Finite.exists_fin' R M).choose` で作っている（refactor-plan §3.4.5）。交点重複度の消滅定理などの引用には依存しない。

## 使われ方

交点重複度（Tor の高次消滅と加法性）、正則局所環の正規性、Paper §4 の複体の列のランクの評価。
-/

@[expose] public noncomputable section

universe u v w

section FiniteFreeResolutionPart

open CategoryTheory Limits
namespace SerrePositivity

variable {R : Type u} [CommRing R]

set_option backward.isDefEq.respectTransparency false in
/-- 短完全列 `0 → K → F → M → 0` で `F` が射影的なら、`K` の射影分解の先頭に
`F` を付けることで `M` の射影分解が得られる。増大写像と完全性を含めて構成する。 -/
noncomputable def prependResolution {K F M : ModuleCat.{u} R} [Projective F]
    (P : ProjectiveResolution K) (f : K ⟶ F) (g : F ⟶ M)
    (hf : Function.Injective f.hom) (hg : Function.Surjective g.hom)
    (he : Function.Exact f.hom g.hom) : ProjectiveResolution M := by
  let a : P.complex.X 0 ⟶ F := P.π.f 0 ≫ f
  have ha : P.complex.d 1 0 ≫ a = 0 := by
    dsimp [a]
    rw [← Category.assoc, P.complex_d_comp_π_f_zero, zero_comp]
  let C := P.complex.augment a ha
  have hag : a ≫ g = 0 := by
    ext x
    exact he.apply_apply_eq_zero _
  have hex0 : Function.Exact a.hom g.hom := by
    rw [LinearMap.exact_iff]
    rw [LinearMap.exact_iff] at he
    change LinearMap.ker g.hom = LinearMap.range (f.hom.comp (P.π.f 0).hom)
    rw [he]
    exact (LinearMap.range_comp_of_range_eq_top f.hom
      (LinearMap.range_eq_top.mpr ((ModuleCat.epi_iff_surjective _).mp inferInstance))).symm
  have hex1 : Function.Exact (P.complex.d 1 0).hom a.hom := by
    rw [LinearMap.exact_iff]
    change LinearMap.ker (f.hom.comp (P.π.f 0).hom) = _
    rw [LinearMap.ker_comp, LinearMap.ker_eq_bot.mpr hf,
      Submodule.comap_bot]
    exact ((ShortComplex.moduleCat_exact_iff_range_eq_ker _).mp P.exact₀).symm
  refine { complex := C, projective := ?_, π :=
    (ChainComplex.toSingle₀Equiv C M).symm ⟨g, hag⟩, quasiIso := ?_ }
  · intro i
    cases i with
    | zero => exact inferInstanceAs (Projective F)
    | succ i => exact P.projective i
  · constructor
    intro i
    cases i with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff, ShortComplex.quasiIso_iff_of_zeros']
      · exact ⟨(ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr hex0,
          (ModuleCat.epi_iff_surjective g).mpr hg⟩
      all_goals rfl
    | succ i =>
      rw [quasiIsoAt_iff_exactAt' _ _ (ChainComplex.exactAt_succ_single_obj _ _)]
      rw [HomologicalComplex.exactAt_iff' _ (i + 2) (i + 1) i (by simp) (by simp)]
      cases i with
      | zero => exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr hex1
      | succ i => exact P.exact_succ i

set_option backward.isDefEq.respectTransparency false in
/-- 有限生成の核 `K i` と有限自由項 `F i` からなる短完全列の族について、
第 `n` 核が自由なら、それを最終項として長さ `n` の有限自由分解を構成できる。 -/
lemma exists_resolution_of_free_syzygy
    (K F : ℕ → ModuleCat.{u} R) (hfinite : ∀ i, Module.Finite R (K i))
    (hfree : ∀ i, Module.Free R (F i)) (hFfinite : ∀ i, Module.Finite R (F i))
    (ι : ∀ i, K (i + 1) →ₗ[R] F i) (π : ∀ i, F i →ₗ[R] K i)
    (hinj : ∀ i, Function.Injective (ι i)) (hsurj : ∀ i, Function.Surjective (π i))
    (hex : ∀ i, Function.Exact (ι i) (π i)) (n : ℕ) (hn : Module.Free R (K n)) :
    ∃ P : ProjectiveResolution (K 0), (∀ i, n < i → IsZero (P.complex.X i)) ∧
      (∀ i, Module.Free R (P.complex.X i)) ∧ (∀ i, Module.Finite R (P.complex.X i)) := by
  induction n generalizing K F with
  | zero =>
    let := hn
    let := hfinite 0
    let P := ProjectiveResolution.self (K 0)
    have hz (i : ℕ) (hi : i ≠ 0) : IsZero (P.complex.X i) :=
      HomologicalComplex.isZero_single_obj_X _ _ _ _ hi
    refine ⟨P, fun i hi => hz i (by omega), ?_, ?_⟩
    · intro i
      by_cases hi : i = 0
      · subst i; exact hn
      · let := ModuleCat.subsingleton_of_isZero (hz i hi)
        exact Module.Free.of_subsingleton _ _
    · intro i
      by_cases hi : i = 0
      · subst i; exact hfinite 0
      · let := ModuleCat.subsingleton_of_isZero (hz i hi)
        infer_instance
  | succ n ih =>
    obtain ⟨P, hb, hfr, hfi⟩ := ih (fun i => K (i + 1)) (fun i => F (i + 1))
      (fun i => hfinite (i + 1)) (fun i => hfree (i + 1)) (fun i => hFfinite (i + 1))
      (fun i => ι (i + 1)) (fun i => π (i + 1)) (fun i => hinj (i + 1))
      (fun i => hsurj (i + 1)) (fun i => hex (i + 1)) hn
    let := hfree 0
    let Q := prependResolution P (ModuleCat.ofHom (ι 0)) (ModuleCat.ofHom (π 0))
      (hinj 0) (hsurj 0) (hex 0)
    refine ⟨Q, ?_, ?_, ?_⟩
    · intro i hi
      cases i with
      | zero => omega
      | succ i => exact hb i (by omega)
    · intro i
      cases i with
      | zero => exact hfree 0
      | succ i => exact hfr i
    · intro i
      cases i with
      | zero => exact hFfinite 0
      | succ i => exact hfi i

namespace FiniteFreeResolution

/-- 有限生成加群への全射を与える有限自由加群の階数を一つ選ぶ。 -/
noncomputable def coverRank (M : FGModuleCat.{u} R) : ℕ :=
  (Module.Finite.exists_fin' R M).choose

/-- 有限生成加群への全射の始域として、有限自由加群 `Rⁿ` を選ぶ。 -/
noncomputable def cover (M : FGModuleCat.{u} R) : ModuleCat.{u} R :=
  ModuleCat.of R (Fin (coverRank M) → R)

/-- Mathlib の有限生成性の特徴付けから選んだ、有限自由加群からの全射。 -/
noncomputable def coverπ (M : FGModuleCat.{u} R) : cover M →ₗ[R] M :=
  (Module.Finite.exists_fin' R M).choose_spec.choose
/-- 選んだ有限自由加群からの射が全射であること。 -/
lemma coverπ_surjective (M : FGModuleCat.{u} R) : Function.Surjective (coverπ M) :=
  (Module.Finite.exists_fin' R M).choose_spec.choose_spec

/-- 選んだ全射の始域は自由加群である。 -/
instance cover_free (M : FGModuleCat.{u} R) : Module.Free R (cover M) := by
  unfold cover
  infer_instance

/-- 選んだ全射の始域は有限生成である。 -/
instance cover_finite (M : FGModuleCat.{u} R) : Module.Finite R (cover M) := by
  unfold cover
  infer_instance

/-- 有限自由加群からの全射の核を繰り返して得られる加群。第 `0` 核は元の加群。
Noether 性により、各段階の核も有限生成である。 -/
noncomputable def syzygy [IsNoetherianRing R] (M : FGModuleCat.{u} R) : ℕ → FGModuleCat.{u} R
  | 0 => M
  | n + 1 => FGModuleCat.of R (LinearMap.ker (coverπ (syzygy M n)))
end FiniteFreeResolution

set_option backward.isDefEq.respectTransparency false in
/-- 極大イデアルが長さ `d` の正則列で生成される Noether 局所環上では、
任意の有限生成加群に長さ `d` 以下の有限自由分解が存在する。
正則局所環の定義や次元の定理を仮定しない一般論。 -/
lemma exists_finite_free_resolution_of_regular_generators [IsNoetherianRing R] [IsLocalRing R]
    (rs : List R) (hreg : RingTheory.Sequence.IsWeaklyRegular R rs)
    (hgen : Ideal.ofList rs = IsLocalRing.maximalIdeal R)
    (M : ModuleCat.{u} R) [Module.Finite R M] :
    ∃ P : ProjectiveResolution M, (∀ i, rs.length < i → IsZero (P.complex.X i)) ∧
      (∀ i, Module.Free R (P.complex.X i)) ∧ (∀ i, Module.Finite R (P.complex.X i)) := by
  let Z := FiniteFreeResolution.syzygy (FGModuleCat.of R M)
  let K (i : ℕ) := (Z i).obj
  let F (i : ℕ) := FiniteFreeResolution.cover (Z i)
  let π (i : ℕ) : F i →ₗ[R] K i := FiniteFreeResolution.coverπ (Z i)
  let ι (i : ℕ) : K (i + 1) →ₗ[R] F i := (LinearMap.ker (π i)).subtype
  have hfinite (i : ℕ) : Module.Finite R (K i) := (Z i).property
  have hfree (i : ℕ) : Module.Free R (F i) := by
    dsimp [F, FiniteFreeResolution.cover]
    infer_instance
  have hFfinite (i : ℕ) : Module.Finite R (F i) := by
    dsimp [F, FiniteFreeResolution.cover]
    infer_instance
  have hinj (i : ℕ) : Function.Injective (ι i) := Subtype.val_injective
  have hsurj (i : ℕ) : Function.Surjective (π i) := FiniteFreeResolution.coverπ_surjective _
  have hex (i : ℕ) : Function.Exact (ι i) (π i) := LinearMap.exact_subtype_ker_map _
  exact exists_resolution_of_free_syzygy K F hfinite hfree hFfinite ι π hinj hsurj hex
    rs.length (free_syzygy_of_regular_generators rs hreg hgen K F hfinite hfree ι π hinj hsurj hex)

/-- 長さ `n` の有限自由射影分解を、次数 `[-n, 0]` に乗る整数添字の有限自由分解へ移す。 -/
lemma bounded_finite_free_cochain_of_projectiveResolution {M : ModuleCat.{u} R}
    (P : ProjectiveResolution M) (n : ℕ) (hb : ∀ i, n < i → IsZero (P.complex.X i))
    (hfree : ∀ i, Module.Free R (P.complex.X i))
    (hfinite : ∀ i, Module.Finite R (P.complex.X i)) :
    ∃ F : CochainComplex (ModuleCat.{u} R) ℤ,
      Nonempty (IsResolutionOf F M) ∧
      (∀ i, (i < -(n : ℤ) ∨ 0 < i) → IsZero (F.X i)) ∧
      (∀ i, Module.Free R (F.X i)) ∧ (∀ i, Module.Finite R (F.X i)) := by
  classical
  refine ⟨extRes P, ⟨isResolutionOf_extRes P⟩, ?_, ?_, ?_⟩
  · intro i hi
    by_cases h : ∃ j : ℕ, embUp.f j = i
    · obtain ⟨j, rfl⟩ := h
      exact IsZero.of_iso (hb j (by
        change 0 - (j : ℤ) < -(n : ℤ) ∨ 0 < 0 - (j : ℤ) at hi
        omega))
        (P.complex.extendXIso embUp rfl)
    · exact HomologicalComplex.isZero_extend_X _ _ _ (fun j hj => h ⟨j, hj⟩)
  · intro i
    by_cases h : ∃ j : ℕ, embUp.f j = i
    · obtain ⟨j, rfl⟩ := h
      let := hfree j
      exact Module.Free.of_equiv (P.complex.extendXIso embUp rfl).toLinearEquiv.symm
    · let := ModuleCat.subsingleton_of_isZero
        (HomologicalComplex.isZero_extend_X P.complex embUp i (fun j hj => h ⟨j, hj⟩))
      exact Module.Free.of_subsingleton _ _
  · intro i
    by_cases h : ∃ j : ℕ, embUp.f j = i
    · obtain ⟨j, rfl⟩ := h
      let := hfinite j
      exact Module.Finite.equiv (P.complex.extendXIso embUp rfl).toLinearEquiv.symm
    · let := ModuleCat.subsingleton_of_isZero
        (HomologicalComplex.isZero_extend_X P.complex embUp i (fun j hj => h ⟨j, hj⟩))
      infer_instance
end SerrePositivity

end FiniteFreeResolutionPart

section RegularLocalResolutionPart

open CategoryTheory
namespace SerrePositivity
variable (R : Type u) [CommRing R] [IsRegularLocalRing R]

/-- 正則局所環上の有界有限自由分解の存在。極大イデアルの正則生成列を選び、
一般定理から自然数添字の有限自由分解を構成し、整数添字へ移す。
正則パラメータの正則性を含めて証明済み。 -/
theorem regularResolution (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    ∃ F : CochainComplex (ModuleCat.{u} R) ℤ,
      Nonempty (IsResolutionOf F (ModuleCat.of R M)) ∧
      (∃ a b : ℤ, ∀ i, (i < a ∨ b < i) → CategoryTheory.Limits.IsZero (F.X i)) ∧
      (∀ i, Module.Free R (F.X i)) ∧ (∀ i, Module.Finite R (F.X i)) := by
  obtain ⟨rs, hreg, hgen, _⟩ := exists_regular_generators R
  obtain ⟨P, hb, hfree, hfinite⟩ :=
    exists_finite_free_resolution_of_regular_generators rs hreg hgen (ModuleCat.of R M)
  obtain ⟨F, hF, hbound, hfree, hfinite⟩ :=
    bounded_finite_free_cochain_of_projectiveResolution P rs.length hb hfree hfinite
  exact ⟨F, hF, ⟨-(rs.length : ℤ), 0, hbound⟩, hfree, hfinite⟩

end SerrePositivity

end RegularLocalResolutionPart

section FiniteLocalizationDescentPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory Limits
open scoped ModuleCat.Algebra TensorProduct
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  (P : Submonoid R) [IsLocalization P A]

include P in
/-- Finite modules over a localization descend to finitely presented source modules. -/
lemma exists_finitePresentation_descent [IsNoetherianRing R]
    (M : ModuleCat.{u} A) [Module.Finite A M] :
    ∃ M₀ : ModuleCat.{u} R, Module.Finite R M₀ ∧ Module.FinitePresentation R M₀ ∧
      Nonempty (A ⊗[R] M₀ ≃ₗ[A] M) := by
  obtain ⟨L, hL, hloc⟩ := exists_finite_lattice (B := A) P (N := M)
  have : Module.Finite R L := Module.Finite.of_fg hL
  exact ⟨ModuleCat.of R L, inferInstance, Module.finitePresentation_of_finite R L,
    ⟨hloc.tensorEquiv (B := A)⟩⟩

end SerrePositivity

end FiniteLocalizationDescentPart

section LocalizedRegularResolutionPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory Limits
open scoped ModuleCat.Algebra TensorProduct
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  (P : Submonoid R) [IsLocalization P A]

include P in
/-- A localized regular local resolution resolves every finite localization module. -/
lemma localizedRegularResolution [IsRegularLocalRing R]
    (M : ModuleCat.{u} A) [Module.Finite A M] :
    ∃ F : CochainComplex (ModuleCat.{u} A) ℤ,
      Nonempty (IsResolutionOf F M) ∧
      (∃ a b : ℤ, ∀ i, (i < a ∨ b < i) → IsZero (F.X i)) ∧
      (∀ i, Module.Free A (F.X i)) ∧ (∀ i, Module.Finite A (F.X i)) := by
  obtain ⟨M₀, hfinite, _, ⟨e⟩⟩ := exists_finitePresentation_descent P M
  have := hfinite
  obtain ⟨F, ⟨hF⟩, hb, hfree, hfin⟩ := regularResolution R M₀
  have : Module.Flat R A := IsLocalization.flat A P
  let hA := isResolutionOf_baseChange_of_flat R A M₀ hF
  refine ⟨baseChange (algebraMap R A) F,
    ⟨{ hA with homologyZeroIso := hA.homologyZeroIso ≪≫ e.toModuleIso }⟩,
    baseChange_bounded _ _ hb, ?_, ?_⟩
  · intro i
    have := hfree i
    exact free_baseChange _ _
  · intro i
    have := hfin i
    exact finite_baseChange _ _

end SerrePositivity

end LocalizedRegularResolutionPart

section FiniteResolutionTracePart

namespace SerrePositivity

open LinearMap
open scoped TensorProduct

/-- 有限次元ベクトル空間の短完全列と両立する自己準同型のトレースは加法的。
列を線形に分裂させ、恒等写像を二つの射影の和として計算する。 -/
theorem trace_eq_add_of_exact
    {K U V W : Type u} [Field K]
    [AddCommGroup U] [Module K U] [FiniteDimensional K U]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (i : U →ₗ[K] V) (p : V →ₗ[K] W)
    (hi : Function.Injective i) (hp : Function.Surjective p) (he : Function.Exact i p)
    (a : U →ₗ[K] U) (b : V →ₗ[K] V) (c : W →ₗ[K] W)
    (hab : b.comp i = i.comp a) (hbc : p.comp b = c.comp p) :
    trace K V b = trace K U a + trace K W c := by
  obtain ⟨s, hs⟩ := p.exists_rightInverse_of_surjective (LinearMap.range_eq_top.mpr hp)
  let q : V →ₗ[K] LinearMap.range i :=
    (LinearMap.id - s.comp p).codRestrict _ (by
      intro x
      apply (he (x - s (p x))).mp
      simp only [map_sub]
      exact sub_eq_zero.mpr (congrArg (fun f : W →ₗ[K] W ↦ f (p x)) hs).symm)
  let t : V →ₗ[K] U := (LinearEquiv.ofInjective i hi).symm.toLinearMap.comp q
  have hit : i.comp t = LinearMap.id - s.comp p := by
    ext x
    exact congrArg Subtype.val ((LinearEquiv.ofInjective i hi).apply_symm_apply (q x))
  have hti : t.comp i = LinearMap.id := by
    ext x
    apply hi
    have hh := congrArg (fun f : V →ₗ[K] V ↦ f (i x)) hit
    simpa [he.apply_apply_eq_zero x] using hh
  have hb : b = i.comp (t.comp b) + s.comp (p.comp b) := by
    rw [← LinearMap.comp_assoc, hit, LinearMap.sub_comp, LinearMap.id_comp]
    simp [LinearMap.comp_assoc]
  rw [hb, map_add]
  congr 1
  · rw [trace_comp_comm' (t.comp b) i, LinearMap.comp_assoc, hab,
      ← LinearMap.comp_assoc, hti, LinearMap.id_comp]
  · rw [trace_comp_comm' (p.comp b) s, hbc, LinearMap.comp_assoc, hs, LinearMap.comp_id]

/-- 有限自由加群の短完全列を有限回たどり、最後の核も自由なら、体への係数拡大後の
トレースは基底環から来る。核の自己準同型は射影性による持ち上げから構成する。 -/
theorem trace_baseChange_mem_range_of_free_syzygy
    {R K : Type u} [CommRing R] [Field K] [Algebra R K] [Module.Flat R K]
    (Z F : ℕ → ModuleCat.{u} R)
    (hZ : ∀ j, Module.Finite R (Z j))
    (hF : ∀ j, Module.Finite R (F j)) (hfree : ∀ j, Module.Free R (F j))
    (i : ∀ j, Z (j + 1) →ₗ[R] F j) (p : ∀ j, F j →ₗ[R] Z j)
    (hi : ∀ j, Function.Injective (i j)) (hp : ∀ j, Function.Surjective (p j))
    (he : ∀ j, Function.Exact (i j) (p j))
    (n : ℕ) (hn : Module.Free R (Z n)) (f : Z 0 →ₗ[R] Z 0) :
    trace K (K ⊗[R] Z 0) (f.baseChange K) ∈ Set.range (algebraMap R K) := by
  induction n generalizing Z F with
  | zero =>
    let := hn
    let := hZ 0
    exact ⟨trace R (Z 0) f, (trace_baseChange f K).symm⟩
  | succ n ih =>
    let := hfree 0
    let := hF 0
    let := hZ 0
    let := hZ 1
    obtain ⟨b, hb⟩ := Module.projective_lifting_property (p 0) (f.comp (p 0)) (hp 0)
    let q : Z 1 →ₗ[R] LinearMap.range (i 0) :=
      (b.comp (i 0)).codRestrict _ (by
        intro x
        apply (he 0 (b (i 0 x))).mp
        have h := congrArg (fun g : F 0 →ₗ[R] Z 0 ↦ g (i 0 x)) hb
        simpa [(he 0).apply_apply_eq_zero x] using h)
    let a : Z 1 →ₗ[R] Z 1 := (LinearEquiv.ofInjective (i 0) (hi 0)).symm.toLinearMap.comp q
    have ha : b.comp (i 0) = (i 0).comp a := by
      ext x
      exact (congrArg Subtype.val
        ((LinearEquiv.ofInjective (i 0) (hi 0)).apply_symm_apply (q x))).symm
    obtain ⟨r, hr⟩ := ih (fun j ↦ Z (j + 1)) (fun j ↦ F (j + 1))
      (fun j ↦ hZ (j + 1)) (fun j ↦ hF (j + 1)) (fun j ↦ hfree (j + 1))
      (fun j ↦ i (j + 1)) (fun j ↦ p (j + 1))
      (fun j ↦ hi (j + 1)) (fun j ↦ hp (j + 1)) (fun j ↦ he (j + 1)) hn a
    have ht := trace_eq_add_of_exact ((i 0).baseChange K) ((p 0).baseChange K)
      (Module.Flat.lTensor_preserves_injective_linearMap (M := K) (i 0) (hi 0))
      ((p 0).baseChange_surjective K (hp 0)) (Module.Flat.lTensor_exact K (he 0))
      (a.baseChange K) (b.baseChange K) (f.baseChange K)
      (by simpa only [LinearMap.baseChange_comp] using congrArg (LinearMap.baseChange K) ha)
      (by simpa only [LinearMap.baseChange_comp] using congrArg (LinearMap.baseChange K) hb)
    refine ⟨trace R (F 0) b - r, ?_⟩
    rw [map_sub, hr, ← trace_baseChange b K, ht, add_sub_cancel_left]

/-- 極大イデアルが正則列で生成される局所環では、任意の有限加群の自己準同型について
平坦な体への係数拡大後のトレースが基底環に属する。最終核の自由性は既存の分解構成による。 -/
theorem trace_baseChange_mem_range_of_regular_generators
    {R K : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [Field K] [Algebra R K] [Module.Flat R K]
    (rs : List R) (hreg : RingTheory.Sequence.IsWeaklyRegular R rs)
    (hgen : Ideal.ofList rs = IsLocalRing.maximalIdeal R)
    (M : ModuleCat.{u} R) [Module.Finite R M] (f : M →ₗ[R] M) :
    trace K (K ⊗[R] M) (f.baseChange K) ∈ Set.range (algebraMap R K) := by
  let Z := FiniteFreeResolution.syzygy (FGModuleCat.of R M)
  let N (j : ℕ) := (Z j).obj
  let F (j : ℕ) := FiniteFreeResolution.cover (Z j)
  let p (j : ℕ) : F j →ₗ[R] N j := FiniteFreeResolution.coverπ (Z j)
  let i (j : ℕ) : N (j + 1) →ₗ[R] F j := (LinearMap.ker (p j)).subtype
  have hN (j : ℕ) : Module.Finite R (N j) := (Z j).property
  have hF (j : ℕ) : Module.Finite R (F j) := by dsimp [F]; infer_instance
  have hfree (j : ℕ) : Module.Free R (F j) := by dsimp [F]; infer_instance
  have hi (j : ℕ) : Function.Injective (i j) := Subtype.val_injective
  have hp (j : ℕ) : Function.Surjective (p j) := FiniteFreeResolution.coverπ_surjective _
  have he (j : ℕ) : Function.Exact (i j) (p j) := LinearMap.exact_subtype_ker_map _
  exact trace_baseChange_mem_range_of_free_syzygy N F hN hF hfree i p hi hp he rs.length
    (free_syzygy_of_regular_generators rs hreg hgen N F hN hfree i p hi hp he) f

end SerrePositivity

end FiniteResolutionTracePart

section ControlledHorseshoePart

open CategoryTheory Limits Pretriangulated

namespace SerrePositivity

section derived

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- K 射影的な複体からの導来圏の射は鎖写像で表せる。
ホモトピー圏での完全忠実性と、ホモトピー商の射の全射性を組み合わせる。 -/
lemma exists_chainMap_of_derivedHom (P Q : CochainComplex C ℤ) [P.IsKProjective]
    (d : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj Q) :
    ∃ f : P ⟶ Q, DerivedCategory.Q.map f = d := by
  obtain ⟨g, hg⟩ := (CochainComplex.IsKProjective.Qh_map_bijective P
    ((HomotopyCategory.quotient _ _).obj Q)).surjective
      ((DerivedCategory.quotientCompQhIso C).hom.app P ≫ d ≫
        (DerivedCategory.quotientCompQhIso C).inv.app Q)
  obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient _ _).map_surjective g
  refine ⟨f, ?_⟩
  rw [← cancel_epi ((DerivedCategory.quotientCompQhIso C).hom.app P),
    ← (DerivedCategory.quotientCompQhIso C).hom.naturality f]
  change DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map f) ≫ _ = _
  rw [hg]
  simp

/-- 導来圏の同型から各次数のホモロジーの同型を得る。
ホモロジー関手の局所化との比較同型を両側に挿入する。 -/
noncomputable def homologyIsoOfDerivedIso (P Q : CochainComplex C ℤ)
    (e : DerivedCategory.Q.obj P ≅ DerivedCategory.Q.obj Q) (i : ℤ) :
    P.homology i ≅ Q.homology i :=
  (DerivedCategory.homologyFunctorFactors C i).symm.app P ≪≫
    (DerivedCategory.homologyFunctor C i).mapIso e ≪≫
      (DerivedCategory.homologyFunctorFactors C i).app Q

end derived

variable {R : Type u} [CommRing R]

/-- 射影分解は導来圏で元の加群の単一複体と同型。
零次ホモロジーへの増大射が擬同型であることを使う。 -/
noncomputable def derivedIsoOfResolution [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (M : ModuleCat.{u} R)
    (hP : IsResolutionOf P M) :
    DerivedCategory.Q.obj P ≅ (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M := by
  let ε := toSingleOfHomology P (d_zero_one_eq_zero P hP.isZero_X) hP.homologyZeroIso.hom
  have : QuasiIso ε := quasiIso_toSingleOfHomology P
    (d_zero_one_eq_zero P hP.isZero_X) hP.homologyZeroIso.hom hP.isZero_homology
  exact asIso (DerivedCategory.Q.map ε)

/-- `Q → P[1]` の写像余錐の `i` 次の項は `Q^i ⊕ P^i`。
二つのシフトの添字を打ち消し、写像錐の直和表示を使う。 -/
noncomputable def extensionCoconeXIso (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (f : Q ⟶ P⟦(1 : ℤ)⟧) (i : ℤ) :
    (CochainComplex.mappingCocone f).X i ≅ Q.X i ⊞ P.X i :=
  CochainComplex.shiftFunctorObjXIso (CochainComplex.mappingCone f) (-1) i (i - 1) (by omega) ≪≫
    HomologicalComplex.homotopyCofiber.XIsoBiprod f (i - 1) i (by change i - 1 + 1 = i; omega) ≪≫
      biprod.mapIso (Iso.refl _) (CochainComplex.shiftFunctorObjXIso P 1 (i - 1) i (by omega))

/-- 短完全列の両端の分解を使い、中央の加群を表す写像余錐を構成する。
連結射を持ち上げ、回転した二つの区別三角形の同型から中央の同型を得る。 -/
lemma exists_extensionCocone [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (hP : IsResolutionOf P S.X₁) (hQ : IsResolutionOf Q S.X₃) :
    ∃ f : Q ⟶ P⟦(1 : ℤ)⟧,
      Nonempty (DerivedCategory.Q.obj (CochainComplex.mappingCocone f) ≅
        (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj S.X₂) := by
  have : ∀ i, Projective (Q.X i) := hQ.projective
  have : Q.IsStrictlyLE 0 := (CochainComplex.isStrictlyLE_iff Q 0).mpr hQ.isZero_X
  have : Q.IsKProjective := CochainComplex.isKProjective_of_projective Q 0
  let eQ := derivedIsoOfResolution Q S.X₃ hQ
  let eP := (DerivedCategory.Q.commShiftIso (1 : ℤ)).app P ≪≫
    (shiftFunctor _ (1 : ℤ)).mapIso (derivedIsoOfResolution P S.X₁ hP)
  obtain ⟨f, hf⟩ := exists_chainMap_of_derivedHom Q (P⟦(1 : ℤ)⟧)
    (eQ.hom ≫ hS.singleδ ≫ eP.inv)
  let T := DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCocone.triangle f)
  have hT : T ∈ distTriang _ := DerivedCategory.mappingCocone_triangle_distinguished f
  let e := isoTriangleOfIso₁₂ T.rotate hS.singleTriangle.rotate.rotate
    (rot_of_distTriang _ hT)
    (rot_of_distTriang _ (rot_of_distTriang _ hS.singleTriangle_distinguished))
    eQ eP (by
      change DerivedCategory.Q.map f ≫ eP.hom = eQ.hom ≫ hS.singleδ
      rw [hf]
      simp)
  exact ⟨f, ⟨(shiftFunctor _ (1 : ℤ)).preimageIso (Triangle.π₃.mapIso e)⟩⟩

/-- 短完全列の中央の射影分解で、各項が両端の同じ次数の直和になるものがある。
写像余錐の導来圏での同型からホモロジーを同定し、項の射影性を直和から移す。 -/
theorem exists_horseshoe_resolution
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (hP : IsResolutionOf P S.X₁) (hQ : IsResolutionOf Q S.X₃) :
    ∃ E : CochainComplex (ModuleCat.{u} R) ℤ, Nonempty (IsResolutionOf E S.X₂) ∧
      ∀ i, Nonempty (E.X i ≅ Q.X i ⊞ P.X i) := by
  let := HasDerivedCategory.standard (ModuleCat.{u} R)
  obtain ⟨f, ⟨e⟩⟩ := exists_extensionCocone S hS P Q hP hQ
  let E := CochainComplex.mappingCocone f
  let H := fun i ↦ homologyIsoOfDerivedIso E
    ((HomologicalComplex.single _ _ 0).obj S.X₂) e i
  refine ⟨E, ?_, fun i ↦ ⟨extensionCoconeXIso P Q f i⟩⟩
  refine ⟨{
    isZero_X := ?_
    projective := ?_
    isZero_homology := ?_
    homologyZeroIso := H 0 ≪≫ HomologicalComplex.singleObjHomologySelfIso _ 0 S.X₂ }⟩
  · intro i hi
    exact ((biprod_isZero_iff _ _).mpr ⟨hQ.isZero_X i hi, hP.isZero_X i hi⟩).of_iso
      (extensionCoconeXIso P Q f i)
  · intro i
    have := hQ.projective i
    have := hP.projective i
    exact Projective.of_iso (extensionCoconeXIso P Q f i).symm inferInstance
  · intro i hi
    exact (HomologicalComplex.isZero_single_obj_homology _ _ S.X₂ i hi).of_iso (H i)

/-- 馬蹄構成は両端の共通の下限と有限自由性を保ち、各次数の階数は和になる。
§4 の長さに関する帰納法で、段数が増えても分解の次数幅を固定するために使う。 -/
theorem exists_controlled_horseshoe [Nontrivial R]
    (S : ShortComplex (ModuleCat.{u} R)) (hS : S.ShortExact)
    (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (hP : IsResolutionOf P S.X₁) (hQ : IsResolutionOf Q S.X₃)
    (hPf : ∀ i, Module.Free R (P.X i)) (hQf : ∀ i, Module.Free R (Q.X i))
    (hPn : ∀ i, Module.Finite R (P.X i)) (hQn : ∀ i, Module.Finite R (Q.X i))
    (a : ℤ) (hPb : ∀ i, i < a → IsZero (P.X i))
    (hQb : ∀ i, i < a → IsZero (Q.X i)) :
    ∃ E : CochainComplex (ModuleCat.{u} R) ℤ, Nonempty (IsResolutionOf E S.X₂) ∧
      (∀ i, Module.Free R (E.X i)) ∧ (∀ i, Module.Finite R (E.X i)) ∧
      (∀ i, i < a → IsZero (E.X i)) ∧
      ∀ i, Module.finrank R (E.X i) = Module.finrank R (P.X i) + Module.finrank R (Q.X i) := by
  obtain ⟨E, hE, he⟩ := exists_horseshoe_resolution S hS P Q hP hQ
  have hf (i : ℤ) : Module.Free R (E.X i) ∧ Module.Finite R (E.X i) := by
    have := hPf i
    have := hQf i
    have := hPn i
    have := hQn i
    obtain ⟨hfree, hfinite⟩ := free_finite_biprod (Q.X i) (P.X i)
    let e := (he i).some.toLinearEquiv
    exact ⟨Module.Free.of_equiv e.symm, Module.Finite.equiv e.symm⟩
  refine ⟨E, hE, fun i ↦ (hf i).1, fun i ↦ (hf i).2, ?_, ?_⟩
  · intro i hi
    exact ((biprod_isZero_iff _ _).mpr ⟨hQb i hi, hPb i hi⟩).of_iso (he i).some
  · intro i
    have := hPf i
    have := hQf i
    have := hPn i
    have := hQn i
    let e := (he i).some ≪≫ ModuleCat.biprodIsoProd (Q.X i) (P.X i)
    rw [e.toLinearEquiv.finrank_eq, Module.finrank_prod, add_comm]

end SerrePositivity

end ControlledHorseshoePart

section ControlledResolutionPart

open CategoryTheory Limits IsLocalRing

namespace SerrePositivity

variable {A : Type u} [CommRing A] [IsLocalRing A]

/-- 剰余体の固定された有限自由分解 `K` から、有限長加群 `M` の分解を作る。
各項の階数は `ℓ(M) * rank(K^i)` であり、分解の下限 `a` は変わらない。
組成列の単純な商を剰余体と同定し、馬蹄構成によって階数を加算する。 -/
theorem exists_free_resolution_length_mul
    (K : CochainComplex (ModuleCat.{u} A) ℤ)
    (hK : IsResolutionOf K (ModuleCat.of A (A ⧸ maximalIdeal A)))
    (hKf : ∀ i, Module.Free A (K.X i)) (hKn : ∀ i, Module.Finite A (K.X i))
    (a : ℤ) (hKb : ∀ i, i < a → IsZero (K.X i))
    (M : Type u) [AddCommGroup M] [Module A M] (hM : IsFiniteLength A M) :
    ∃ P : CochainComplex (ModuleCat.{u} A) ℤ,
      Nonempty (IsResolutionOf P (ModuleCat.of A M)) ∧
      (∀ i, Module.Free A (P.X i)) ∧ (∀ i, Module.Finite A (P.X i)) ∧
      (∀ i, i < a → IsZero (P.X i)) ∧
      ∀ i, Module.finrank A (P.X i) = (Module.length A M).toNat * Module.finrank A (K.X i) := by
  induction hM with
  | of_subsingleton =>
    rename_i M _ _ _
    let P := (HomologicalComplex.single (ModuleCat.{u} A) (ComplexShape.up ℤ) 0).obj
      (ModuleCat.of A M)
    have hz : IsZero P := (HomologicalComplex.single _ _ 0).map_isZero
      (ModuleCat.isZero_iff_subsingleton.mpr inferInstance : IsZero (ModuleCat.of A M))
    have hzi (i : ℤ) : IsZero (P.X i) := (HomologicalComplex.eval _ _ i).map_isZero hz
    have hp : IsResolutionOf P (ModuleCat.of A M) := {
      isZero_X := fun i _ ↦ hzi i
      projective := fun i ↦ projective_of_free (isZero_moduleCat_free (hzi i))
      isZero_homology := fun i hi ↦ HomologicalComplex.isZero_single_obj_homology _ _ _ i hi
      homologyZeroIso := HomologicalComplex.singleObjHomologySelfIso _ 0 _ }
    refine ⟨P, ⟨hp⟩, fun i ↦ isZero_moduleCat_free (hzi i),
      fun i ↦ isZero_moduleCat_finite (hzi i), fun i _ ↦ hzi i, ?_⟩
    intro i
    have : Subsingleton (P.X i) := ModuleCat.isZero_iff_subsingleton.mp (hzi i)
    have := isZero_moduleCat_free (hzi i)
    simp [Module.finrank_eq_zero_of_subsingleton, Module.length_eq_zero]
  | @of_simple_quotient M _ _ N _ hN ih =>
    obtain ⟨P, ⟨hP⟩, hPf, hPn, hPb, hPr⟩ := ih
    obtain ⟨e⟩ := IsSimpleModule.nonempty_linearEquiv_quotient_maximalIdeal (A := A) (M := M ⧸ N)
    let hQ : IsResolutionOf K (ModuleCat.of A (M ⧸ N)) :=
      { hK with homologyZeroIso := hK.homologyZeroIso ≪≫ e.symm.toModuleIso }
    let S : ShortComplex (ModuleCat.{u} A) :=
      ModuleCat.shortComplexOfCompEqZero N.subtype N.mkQ (by ext; simp)
    have hS : S.ShortExact := by
      refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
      · rw [ShortComplex.moduleCat_exact_iff]
        intro y hy
        exact (LinearMap.exact_subtype_mkQ N y).mp hy
      · exact (ModuleCat.mono_iff_injective _).mpr N.injective_subtype
      · exact (ModuleCat.epi_iff_surjective _).mpr N.mkQ_surjective
    obtain ⟨E, hE, hEf, hEn, hEb, hEr⟩ :=
      exists_controlled_horseshoe S hS P K hP hQ hPf hKf hPn hKn a hPb hKb
    refine ⟨E, hE, hEf, hEn, hEb, ?_⟩
    intro i
    rw [hEr i, hPr i, Module.length_eq_succ_of_isSimpleModule_quotient N,
      ENat.toNat_add (Module.length_ne_top_iff.mpr hN) (by simp), ENat.toNat_one]
    ring

end SerrePositivity

end ControlledResolutionPart
