module

public import SerrePositivity.CommutativeAlgebra.AbsolutelyIntegrallyClosed.Basic
public import Mathlib.FieldTheory.AlgebraicClosure
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Valuation.Integral
public import Mathlib.RingTheory.Valuation.LocalSubring

/-!
概要：代数閉分数体への付値環の拡大（BM18 Lemmas 3.28, 3.29）。
方針：局所準同型を付値部分環に分解し、整域への単射から平坦性を得る。
規約：付値部分環の逆像から元の付値部分環への射も忠実平坦。
使われ方：v 被覆を作るための絶対整閉な試験付値環。
-/

@[expose] public noncomputable section

universe u

open Polynomial CategoryTheory

namespace SerrePositivity

/-- 代数閉体の付値部分環は絶対整閉（BM18 Definition 3.26）。 -/
theorem valuationSubring_aic {K : Type u} [Field K] [IsAlgClosed K]
    (W : ValuationSubring K) : IsAbsolutelyIntegrallyClosed W := by
  intro P hP hd
  let f := algebraMap W K
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root (P.map f) (by
    rw [hP.degree_map]
    exact (natDegree_pos_iff_degree_pos.mp hd).ne')
  have hint : IsIntegral W x := ⟨P, hP, by
    rw [← eval_map]
    exact hx⟩
  have hxW : x ∈ W := by
    have hv := (ValuationRing.integers W K).mem_of_integral hint
    exact (W.valuation_le_one_iff x).mp hv
  refine ⟨⟨x, hxW⟩, ?_⟩
  apply IsFractionRing.injective W K
  rw [map_zero, ← eval_map_apply]
  exact hx

/-- 付値整域から整域への単射な局所準同型は忠実平坦。 -/
theorem faithfullyFlat_of_injective_local_valuation
    {V W : Type u} [CommRing V] [IsDomain V] [ValuationRing V]
    [CommRing W] [IsDomain W] [IsLocalRing W]
    (e : V →+* W) [IsLocalHom e] (he : Function.Injective e) : e.FaithfullyFlat := by
  let := e.toAlgebra
  let : IsLocalHom (algebraMap V W) := inferInstanceAs (IsLocalHom e)
  let : Module.IsTorsionFree V W := Module.isTorsionFree_iff_algebraMap_injective.mpr he
  let : Module.Flat V W := Module.Flat.flat_iff_torsion_eq_bot_of_isBezout.mpr
    (Submodule.isTorsionFree_iff_torsion_eq_bot.mp inferInstance)
  exact RingHom.faithfullyFlat_algebraMap_iff.mpr Module.FaithfullyFlat.of_flat_of_isLocalHom

/-- 体の埋め込みによる付値部分環の逆像から元の付値部分環への射。 -/
def valuationSubringComapHom {K L : Type u} [Field K] [Field L]
    (W : ValuationSubring L) (f : K →+* L) : W.comap f →+* W :=
  (f.comp (algebraMap (W.comap f) K)).codRestrict W.toSubring (fun x => x.property)

/-- 体の埋め込みによる付値部分環の逆像からの射は忠実平坦（BM18 Lemma 3.29）。 -/
theorem valuationSubringComapHom_faithfullyFlat {K L : Type u} [Field K] [Field L]
    (W : ValuationSubring L) (f : K →+* L) :
    (valuationSubringComapHom W f).FaithfullyFlat := by
  let g := valuationSubringComapHom W f
  have hg : Function.Injective g := fun _ _ h =>
    Subtype.ext (f.injective (congrArg Subtype.val h))
  let : IsLocalHom g := ⟨fun x hx => by
    obtain ⟨y, hy⟩ := isUnit_iff_dvd_one.mp hx
    have he : f (x : K) * (y : L) = 1 := congrArg Subtype.val hy.symm
    have hne : f (x : K) ≠ 0 := by
      intro hz
      simp [hz] at he
    have hy' : f ((x : K)⁻¹) = (y : L) := by
      rw [map_inv₀]
      exact (mul_eq_one_iff_inv_eq₀ hne).mp he
    let z : W.comap f := ⟨(x : K)⁻¹, by
      change f ((x : K)⁻¹) ∈ W
      rw [hy']
      exact y.property⟩
    have hne' : (x : K) ≠ 0 := fun hz => hne (by rw [hz, map_zero])
    exact isUnit_iff_dvd_one.mpr ⟨z, Subtype.ext (mul_inv_cancel₀ hne').symm⟩⟩
  exact faithfullyFlat_of_injective_local_valuation g hg

/-- 付値環を分数体の代数閉包の付値部分環に忠実平坦に拡大する（BM18 Lemma 3.28）。 -/
theorem exists_valuationSubring_algebraicClosure (V : Type u) [CommRing V]
    [IsDomain V] [ValuationRing V] :
    ∃ (W : ValuationSubring (AlgebraicClosure (FractionRing V)))
      (h : ∀ v : V, algebraMap V (AlgebraicClosure (FractionRing V)) v ∈ W),
      RingHom.FaithfullyFlat
        (RingHom.codRestrict (algebraMap V (AlgebraicClosure (FractionRing V))) W.toSubring h) := by
  let K := FractionRing V
  let L := AlgebraicClosure K
  let f := algebraMap V L
  obtain ⟨W, h, hloc⟩ := IsLocalRing.exists_factor_valuationRing f
  let e : V →+* W := f.codRestrict W.toSubring h
  let : IsLocalHom e := hloc
  have hinj : Function.Injective f := by
    change Function.Injective (algebraMap V L)
    rw [IsScalarTower.algebraMap_eq V K L]
    exact (RingHom.injective (algebraMap K L)).comp (IsFractionRing.injective V K)
  exact ⟨W, h, faithfullyFlat_of_injective_local_valuation e
    (fun _ _ he => hinj (congrArg Subtype.val he))⟩

end SerrePositivity
