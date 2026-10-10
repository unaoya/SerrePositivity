module

public import SerrePositivity.HomologicalAlgebra.MinimalBetti
public import Mathlib.Algebra.Homology.Embedding.StupidTrunc
public import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-! # 極小自由分解の有限切り詰め

極小自由分解の `0,…,l` 次を残し、cochain の `[-l,0]` 次に置く。
項は有限自由であり、残した項の階数と微分の極小性を保持する。
切り詰めは分解ではなく、左端に誤差のホモロジーを残す。
-/

@[expose] public section

universe u

open CategoryTheory Limits IsLocalRing

namespace SerrePositivity.MinimalFreeResolution

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable (M : FGModuleCat.{u} R) (l : ℕ)

/-- 極小分解の `[-l,0]` 次を残す、項ごとの切り詰め。 -/
noncomputable def truncated : CochainComplex (ModuleCat.{u} R) ℤ :=
  (extRes (resolution M)).stupidTrunc (ComplexShape.embeddingUpIntGE (-(l : ℤ)))

/-- 切り詰めで残した項は、元の極小自由分解の項と同型。 -/
noncomputable def truncatedXIso (i : ℕ) (hi : i ≤ l) :
    (truncated M l).X (-(i : ℤ)) ≅ term M i :=
  (extRes (resolution M)).stupidTruncXIso (ComplexShape.embeddingUpIntGE (-(l : ℤ)))
    (i := l - i) (by simp; omega) ≪≫
  (complex M).extendXIso embUp (by simp)

lemma truncated_isZero_X (q : ℤ) (hq : q < -(l : ℤ) ∨ 0 < q) :
    IsZero ((truncated M l).X q) := by
  rcases hq with hq | hq
  · apply HomologicalComplex.isZero_stupidTrunc_X
    simpa only [ComplexShape.notMem_range_embeddingUpIntGE_iff] using hq
  · have : (extRes (resolution M)).IsStrictlyLE 0 :=
      (CochainComplex.isStrictlyLE_iff _ _).mpr (isResolutionOf_extRes _).isZero_X
    have : (truncated M l).IsStrictlyLE 0 := by unfold truncated; infer_instance
    exact (truncated M l).isZero_of_isStrictlyLE 0 q hq

instance truncated_free (q : ℤ) : Module.Free R ((truncated M l).X q) := by
  by_cases h : q < -(l : ℤ) ∨ 0 < q
  · have := ModuleCat.subsingleton_of_isZero (truncated_isZero_X M l q h)
    exact Module.Free.of_subsingleton _ _
  · have hq : q = -(((-q).toNat : ℕ) : ℤ) := by omega
    rw [hq]
    exact Module.Free.of_equiv (truncatedXIso M l (-q).toNat (by omega)).toLinearEquiv.symm

instance truncated_finite (q : ℤ) : Module.Finite R ((truncated M l).X q) := by
  by_cases h : q < -(l : ℤ) ∨ 0 < q
  · have := ModuleCat.subsingleton_of_isZero (truncated_isZero_X M l q h)
    infer_instance
  · have hq : q = -(((-q).toNat : ℕ) : ℤ) := by omega
    rw [hq]
    exact Module.Finite.equiv (truncatedXIso M l (-q).toNat (by omega)).toLinearEquiv.symm

/-- 残した項の階数は、同じ次数の Betti 数に一致する。 -/
lemma truncated_finrank (i : ℕ) (hi : i ≤ l) :
    Module.finrank R ((truncated M l).X (-(i : ℤ))) =
      MinimalGenerators.rank (syzygy M i) := by
  rw [(truncatedXIso M l i hi).toLinearEquiv.finrank_eq]
  change Module.finrank R (Fin (MinimalGenerators.rank (syzygy M i)) → R) = _
  simp

lemma truncated_finrank_eq_length_tor (i : ℕ) (hi : i ≤ l) :
    (Module.finrank R ((truncated M l).X (-(i : ℤ))) : ℕ∞) =
      Module.length R (TorModule R i M (R ⧸ maximalIdeal R)) := by
  rw [truncated_finrank M l i hi, length_tor]

/-- 項の同型で移した切り詰めの微分は、元の極小分解の微分そのもの。 -/
lemma truncated_d (i : ℕ) (hi : i + 1 ≤ l) :
    (truncatedXIso M l (i + 1) hi).inv ≫
      (truncated M l).d (-((i + 1 : ℕ) : ℤ)) (-(i : ℤ)) ≫
      (truncatedXIso M l i (by omega)).hom = d M i := by
  unfold truncatedXIso truncated HomologicalComplex.stupidTrunc
  rw [HomologicalComplex.extend_d_eq _ _
    (show (ComplexShape.embeddingUpIntGE (-(l : ℤ))).f (l - (i + 1)) =
      -((i + 1 : ℕ) : ℤ) by simp; omega)
    (show (ComplexShape.embeddingUpIntGE (-(l : ℤ))).f (l - i) = -(i : ℤ) by simp; omega)]
  simp only [HomologicalComplex.stupidTruncXIso, Iso.trans_inv, Iso.trans_hom,
    Category.assoc, Iso.inv_hom_id_assoc]
  rw [HomologicalComplex.restriction_d_eq _ _
    (show (ComplexShape.embeddingUpIntGE (-(l : ℤ))).f (l - (i + 1)) =
      -((i + 1 : ℕ) : ℤ) by simp; omega)
    (show (ComplexShape.embeddingUpIntGE (-(l : ℤ))).f (l - i) = -(i : ℤ) by simp; omega)]
  simp only [HomologicalComplex.restrictionXIso, eqToIso]
  rw [HomologicalComplex.extend_d_eq _ _ (by simp : embUp.f (i + 1) = -((i + 1 : ℕ) : ℤ))
    (by simp : embUp.f i = -(i : ℤ))]
  simp only [resolution_complex, Category.assoc, eqToHom_trans_assoc, eqToHom_refl,
    Category.id_comp, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id, complex_d]

/-- 零次の標準基底に関する微分の座標は、切り詰め後も極大イデアルに入る。 -/
lemma truncated_minimal (x : (truncated M l).X (-1)) (j : Fin (MinimalGenerators.rank M)) :
    (truncatedXIso M l 0 (Nat.zero_le l)).hom ((truncated M l).d (-1) 0 x) j ∈
      maximalIdeal R := by
  by_cases h : 1 ≤ l
  · have hd := truncated_d M l 0 h
    have he := congrArg (fun f ↦ f ((truncatedXIso M l 1 h).hom x) j) hd
    have he' : (truncatedXIso M l 0 (Nat.zero_le l)).hom
        ((truncated M l).d (-1) 0 x) j = d M 0 ((truncatedXIso M l 1 h).hom x) j := by
      simpa using he
    rw [he']
    exact d_coordinate_mem M 0 ((truncatedXIso M l 1 h).hom x) j
  · have hz := truncated_isZero_X M l (-1) (Or.inl (by omega))
    rw [hz.eq_zero_of_src ((truncated M l).d (-1) 0)]
    change (truncatedXIso M l 0 (Nat.zero_le l)).hom.hom 0 j ∈ maximalIdeal R
    rw [map_zero]
    exact (maximalIdeal R).zero_mem

end SerrePositivity.MinimalFreeResolution
