module

public import SerrePositivity.HomologicalAlgebra.Resolution
public import Mathlib.Algebra.Homology.Augment
public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import SerrePositivity.CommutativeAlgebra.RegularSequence

/-!
# 有界有限自由分解の構成

まず短完全列と核の射影分解から、中央の射影加群を先頭に付けた分解を作る。
これを繰り返すことで、第 `n` 核が自由な有限自由分解を長さ `n` で止める。

Noether 環上の有限生成加群について有限自由加群からの全射とその核を繰り返し選ぶ。
選択の対象には Mathlib の有限生成加群の圏 `FGModuleCat` を使う。
仮定をまとめる独自の構造体や入力クラスは導入しない。
極大イデアルが正則列で生成される局所環の場合には、一般補題
`free_syzygy_of_regular_generators` によって最後の核が自由になる。

最後に Mathlib の自然数添字の射影分解を、本プロジェクトの整数添字の分解へ移す。
このファイルに未証明の入力はない。
-/

@[expose] public section

open CategoryTheory Limits
universe u
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
