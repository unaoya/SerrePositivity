module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineCechSource
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineReductionPushout
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PolynomialFrobeniusCech
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineCechSource
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.CrystallineCompletedFreeDelta
import all SerrePositivity.BhattScholze.Prismatic.Envelopes.CompletedFreeDeltaResidue
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PolynomialFrobeniusCech
import all SerrePositivity.HomologicalAlgebra.Cosimplicial.Quotient

/-!
# 完備自由 δ Čech 余脈体の mod p

## 概要
結晶基底の自由 δ Čech 余脈体を mod p で多項式 Čech 余脈体と同一視する。

## 方針
係数を剰余体へ移し、反復 δ 座標を添字で付け替える。

## 規約
各頂点に全ての反復 δ 座標を置く。

## 使われ方
結晶の橋の押し出し比較。
-/

public noncomputable section

open CategoryTheory SerrePositivity.Cosimplicial
open SerrePositivity.DerivedCompletion

universe u

namespace SerrePositivity.BhattScholze.Prismatic

variable (p : ℕ) [Fact p.Prime] (r : ℕ)

local notation "Z" => (crystallineBasePrism p)
local notation "S" n => AffineIndex r (SimplexCategory.len n)
local notation "B" n => completedFreeDelta Z (S n)
local notation "B₀" n => RelativeFreeDeltaRing (R := crystallineBase p) (S n)
local notation "D₀" n => relativeFreeDeltaStructure (S n) (OrientedPrism.deltaStructure Z)
local notation "D" n => completedFreeDeltaStructure Z (S n)
local notation "η" n => crystallineCompletedFreeDeltaUnit p (S n)

private def coordEquiv (n : SimplexCategory) :
    AffineIndex.{u} r n.len × ℕ ≃ (Fin r × ℕ) × Fin (n.len + 1) where
  toFun t := ((t.1.down.1, t.2), t.1.down.2)
  invFun t := (⟨(t.1.1,t.2)⟩, t.1.2)
  left_inv := by rintro ⟨⟨⟨_,_⟩⟩,_⟩; rfl
  right_inv := by rintro ⟨⟨_,_⟩,_⟩; rfl

private def rawRename {m n : SimplexCategory} (θ : m ⟶ n) : (B₀ m) →+* (B₀ n) :=
  (MvPolynomial.rename (fun t => (crystallineCechIndexMap r θ t.1, t.2))).toRingHom

private theorem rawRename_isDeltaHom {m n : SimplexCategory} (θ : m ⟶ n) :
    (D₀ m).IsDeltaHom (D₀ n) (rawRename.{u} p r θ) := by
  apply DeltaStructure.isDeltaHom_mvPolynomial
  · intro a
    simp only [rawRename, relativeFreeDeltaStructure_delta_C, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom, MvPolynomial.rename_C]
  · rintro ⟨s,i⟩
    simp only [rawRename, relativeFreeDeltaStructure_delta_X, AlgHom.toRingHom_eq_coe,
      AlgHom.coe_toRingHom, MvPolynomial.rename_X]

private theorem sourceMap_comp_unit {m n : SimplexCategory} (θ : m ⟶ n) :
    (crystallineCechSourceMap.{u} p r θ).comp (η m) = (η n).comp (rawRename p r θ) := by
  let f := (crystallineCechSourceMap.{u} p r θ).comp (η m)
  let g := (η n).comp (rawRename.{u} p r θ)
  have hf := (crystallineCechSourceMap_spec.{u} p r θ).1.comp
    (crystallineCompletedFreeDeltaUnit_isDeltaHom p (S m))
  have hg := (crystallineCompletedFreeDeltaUnit_isDeltaHom p (S n)).comp
    (rawRename_isDeltaHom.{u} p r θ)
  have hX (s : AffineIndex.{u} r m.len) :
      f (MvPolynomial.X (s, 0)) = g (MvPolynomial.X (s, 0)) := by
    have hx := (crystallineCechSourceMap_spec.{u} p r θ).2.2 s
    change crystallineCechSourceMap p r θ ((η m) (MvPolynomial.X (s, 0))) =
      (η n) ((rawRename p r θ) (MvPolynomial.X (s, 0)))
    rw [show (rawRename.{u} p r θ) (MvPolynomial.X (s, 0)) =
        MvPolynomial.X (crystallineCechIndexMap r θ s, 0) from MvPolynomial.rename_X _ _]
    exact hx
  apply MvPolynomial.ringHom_ext'
  · apply RingHom.ext
    intro a
    change crystallineCechSourceMap p r θ ((η m) (MvPolynomial.C a)) =
      (η n) ((rawRename p r θ) (MvPolynomial.C a))
    rw [show (rawRename.{u} p r θ) (MvPolynomial.C a) = MvPolynomial.C a
        from MvPolynomial.rename_C _ _]
    exact DFunLike.congr_fun (crystallineCechSourceMap_spec p r θ).2.1 a
  · rintro ⟨s,i⟩
    change f (MvPolynomial.X (s, i)) = g (MvPolynomial.X (s, i))
    rw [relativeFreeDeltaHom_X_iterates (Z).deltaStructure (D n) f hf,
      relativeFreeDeltaHom_X_iterates (Z).deltaStructure (D n) g hg, hX]

private def rawResidue (n : SimplexCategory) :
    ((B₀ n) ⧸ Ideal.span {(p : B₀ n)}) ≃+*
      MvPolynomial ((Fin r × ℕ) × Fin (n.len + 1)) (cartierBase.{u} p) :=
  (crystallineRawFreeDeltaResidue p (S n)).trans
    ((MvPolynomial.mapEquiv ((S n) × ℕ) (cartierBaseEquiv p).symm).trans
      (MvPolynomial.renameEquiv (cartierBase p) (coordEquiv.{u} r n)).toRingEquiv)

private theorem rawResidue_mk (n : SimplexCategory) (f : B₀ n) :
    rawResidue.{u} p r n (Ideal.Quotient.mk _ f) =
      MvPolynomial.rename (coordEquiv.{u} r n)
        (MvPolynomial.map (Ideal.Quotient.mk (Z).ideal) f) := by
  change MvPolynomial.rename (coordEquiv.{u} r n)
      (MvPolynomial.map (cartierBaseEquiv p).symm.toRingHom
        (MvPolynomial.map (cartierBaseEquiv p).toRingHom
          (MvPolynomial.map (Ideal.Quotient.mk (Z).ideal) f))) = _
  have h : (cartierBaseEquiv p).symm.toRingHom.comp (cartierBaseEquiv p).toRingHom =
      RingHom.id _ := RingHom.ext fun x => (cartierBaseEquiv p).symm_apply_apply x
  rw [MvPolynomial.map_map, h, MvPolynomial.map_id]

private def termResidue (n : SimplexCategory) :
    (modPrimeCosimplicial p (crystallineCechSource.{u} p r)).obj n ≃+*
      (polynomialCech (cartierBase.{u} p) (Fin r × ℕ)).obj n := by
  change ((B n) ⧸ Ideal.span {(p : B n) ^ (1 : ℕ)}) ≃+* _
  let e := crystallineCompletedFreeDeltaResidue p (S n)
  exact (Ideal.quotEquivOfEq (congrArg (fun a : B n => Ideal.span {a}) (pow_one (p : B n)))).trans
    (e.trans ((MvPolynomial.mapEquiv ((S n) × ℕ) (cartierBaseEquiv p).symm).trans
      (MvPolynomial.renameEquiv (cartierBase p) (coordEquiv.{u} r n)).toRingEquiv))

private theorem termResidue_unit (n : SimplexCategory) (f : B₀ n) :
    termResidue.{u} p r n (Ideal.Quotient.mk _ ((η n) f)) =
      rawResidue.{u} p r n (Ideal.Quotient.mk _ f) := by
  exact congrArg
    (fun y : MvPolynomial ((AffineIndex.{u} r n.len) × ℕ) (ZMod p) =>
      MvPolynomial.rename (coordEquiv.{u} r n) (MvPolynomial.map (cartierBaseEquiv p).symm.toRingHom y))
    (crystallineCompletedFreeDeltaResidue_unit p (AffineIndex.{u} r n.len) f)

private theorem termQuotient_surjective (n : SimplexCategory) :
    Function.Surjective (fun f : RelativeFreeDeltaRing (R := crystallineBase.{u} p)
        (AffineIndex.{u} r n.len) =>
      (Ideal.Quotient.mk (Ideal.span
        {(p : completedFreeDelta (crystallineBasePrism.{u} p) (AffineIndex.{u} r n.len)) ^ (1 : ℕ)}))
        ((crystallineCompletedFreeDeltaUnit p (AffineIndex.{u} r n.len)) f)) := by
  intro y
  obtain ⟨x, hx⟩ := (rawResidue.{u} p r n).surjective (termResidue.{u} p r n y)
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨f, (termResidue p r n).injective ((termResidue_unit p r n f).trans hx)⟩

/-- 結晶基底の完備自由 δ Čech 余脈体の剰余は、多項式 Čech 余脈体。 -/
def crystallineCechResidueIso :
    modPrimeCosimplicial p (crystallineCechSource.{u} p r) ≅
      polynomialCech (cartierBase.{u} p) (Fin r × ℕ) :=
  NatIso.ofComponents (fun n => (termResidue p r n).toCommRingCatIso) (fun {m n} θ => by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro y
    obtain ⟨f, rfl⟩ := termQuotient_surjective.{u} p r m y
    let ρ : (Fin r × ℕ) × Fin (m.len + 1) → (Fin r × ℕ) × Fin (n.len + 1) :=
      fun t => (t.1, θ.toOrderHom t.2)
    change termResidue p r n
      (Ideal.Quotient.mk _ ((crystallineCechSourceMap p r θ) ((η m) f))) =
      MvPolynomial.rename ρ (termResidue p r m (Ideal.Quotient.mk _ ((η m) f)))
    have h := DFunLike.congr_fun (sourceMap_comp_unit.{u} p r θ) f
    change crystallineCechSourceMap p r θ ((η m) f) = (η n) (rawRename p r θ f) at h
    rw [h, termResidue_unit, termResidue_unit, rawResidue_mk, rawResidue_mk]
    change MvPolynomial.rename (coordEquiv.{u} r n)
        (MvPolynomial.map (Ideal.Quotient.mk (Z).ideal)
          (MvPolynomial.rename (fun t => (crystallineCechIndexMap r θ t.1, t.2)) f)) = _
    rw [MvPolynomial.map_rename, MvPolynomial.rename_rename, MvPolynomial.rename_rename]
    rfl)

end SerrePositivity.BhattScholze.Prismatic
