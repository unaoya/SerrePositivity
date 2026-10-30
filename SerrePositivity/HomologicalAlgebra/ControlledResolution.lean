module

public import SerrePositivity.HomologicalAlgebra.ControlledHorseshoe
public import SerrePositivity.CommutativeAlgebra.Length.Basic
public import SerrePositivity.CommutativeAlgebra.KoszulResolution

/-!
# 長さに比例する大きさの有限自由分解

## 概要

局所環の剰余体の固定された有限自由分解から、任意の有限長加群の有限自由分解を作る。
次数の下限は固定分解と同じで、各項の階数は固定分解の階数と加群の長さの積になる。
§4 の複体列では、この評価により長さ `O(s)`・`o(s)` からランクの同じ評価を得る。

## 方針と仮定

有限長性の組成列による帰納法と `exists_controlled_horseshoe` を使う。
正則性や一般の自由分解存在定理は仮定せず、剰余体の分解を個別の引数として与える。
特に Koszul 分解を使えば、共通の次数範囲をパラメータの個数で制御できる。
長さは有限であることを仮定して `Module.length` の `toNat` を使う。
-/

@[expose] public section

universe u

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
