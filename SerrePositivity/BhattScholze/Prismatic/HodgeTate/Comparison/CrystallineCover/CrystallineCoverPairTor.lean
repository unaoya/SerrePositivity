module

public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.CrystallineCover.CrystallineCoverCochainTor
public import SerrePositivity.CommutativeAlgebra.KoszulRegular.PrincipalReduction

/-!
# 結晶被覆の mod p の A 上の振幅二

## 概要
被覆の mod p を A の二元の Koszul 商からの平坦射で表す。

## 方針
式 (6) の二重商を (p,d) の通常商に同定し、非有界 Koszul 模型の下界を使う。

## 規約
BS 著者版 Construction 6.1。完全 Koszul の上界三の前段。

## 使われ方
任意の複体に対する完全 Tor 振幅の評価。
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
namespace SerrePositivity.BhattScholze.Prismatic.Construction61
open CategoryTheory CategoryTheory.Limits DifferentialGraded

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] (P : OrientedPrism p A)

/-- A の (p,d) の二座標。 -/
abbrev coverPairCoordinates : Fin 2 → A := Fin.snoc (fun _ : Fin 1 => (p : A)) P.generator

/-- 概要：A/d が p 正則なら (p,d) の Koszul 複体は通常商の分解。
方針：d の正則性と剰余の p 正則性を 分冪包と δ 除算包の比較 の順序交換の入力にする。
規約：BS 著者版 Construction 6.1 の仮定。
使われ方：A 上の振幅二。 -/
theorem coverPairCoordinates_regular
    (hR : IsSMulRegular (A ⧸ P.ideal) (p : A ⧸ P.ideal)) :
    IsKoszulResolution (coverPairCoordinates P) := by
  have hmod : IsKoszulResolution
      (Ideal.Quotient.mk (Ideal.span {P.generator}) ∘ (fun _ : Fin 1 => (p : A))) := by
    apply isKoszulResolution_of_isWeaklyRegular
    rw [show List.ofFn (Ideal.Quotient.mk (Ideal.span {P.generator}) ∘
      (fun _ : Fin 1 => (p : A))) = [(p : A ⧸ Ideal.span {P.generator})] by
        simp [List.ofFn_succ, Function.comp_def]]
    apply (RingTheory.Sequence.isWeaklyRegular_singleton_iff _ _).mpr
    exact hR
  exact isKoszulResolution_snoc_of_regular_mod (fun _ : Fin 1 => (p : A)) P.generator
    P.generator_regular (RingEquiv.refl (A ⧸ Ideal.span {P.generator})) hmod

private theorem pairIdeal_eq :
    Ideal.span (Set.range (coverPairCoordinates P)) =
      (Ideal.span {(p : A)}) ⊔ Ideal.span {P.generator} := by
  rw [← Ideal.span_union]
  congr 1
  ext a
  simp [coverPairCoordinates, Fin.exists_fin_succ, Fin.snoc]

private theorem generatorIdeal_map_eq :
    (Ideal.span {P.generator}).map (Ideal.Quotient.mk (Ideal.span {(p : A)})) =
      Ideal.span {coverModPGenerator P} := by
  rw [Ideal.map_span, Set.image_singleton]

private def doublePairQuotientEquiv :
    (ModP A p ⧸ Ideal.span {coverModPGenerator P}) ≃+*
      (A ⧸ Ideal.span (Set.range (coverPairCoordinates P))) :=
  (Ideal.quotEquivOfEq (generatorIdeal_map_eq P).symm).trans
    ((DoubleQuot.quotQuotEquivQuotSup (Ideal.span {(p : A)}) (Ideal.span {P.generator})).trans
      (Ideal.quotEquivOfEq (pairIdeal_eq P).symm))

private theorem doublePairQuotientEquiv_unit (a : A) :
    doublePairQuotientEquiv P
      (Ideal.Quotient.mk _ (Ideal.Quotient.mk (Ideal.span {(p : A)}) a)) =
      Ideal.Quotient.mk (Ideal.span (Set.range (coverPairCoordinates P))) a := by
  unfold doublePairQuotientEquiv
  rw [RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk, RingEquiv.trans_apply]
  change Ideal.quotEquivOfEq (pairIdeal_eq P).symm
    (DoubleQuot.quotQuotEquivQuotSup (Ideal.span {(p : A)}) (Ideal.span {P.generator})
      (DoubleQuot.quotQuotMk (Ideal.span {(p : A)}) (Ideal.span {P.generator}) a)) = _
  rw [DoubleQuot.quotQuotEquivQuotSup_quotQuotMk, Ideal.quotEquivOfEq_mk]

/-- A から被覆の実際の mod p への標準射。 -/
abbrev coverMapToModP : A →+* ModP (crystallineCoverRing P) p :=
  (alphaModP P).comp (Ideal.Quotient.mk (Ideal.span {(p : A)}))

/-- (p,d) の通常商から被覆の mod p への射。 -/
def coverPairFlatMap
    (hR : IsSMulRegular (A ⧸ P.ideal) (p : A ⧸ P.ideal)) :
    (A ⧸ Ideal.span (Set.range (coverPairCoordinates P))) →+* ModP (crystallineCoverRing P) p :=
  ((coverResidueFlatMap P hR).comp (residueFrobenius P)).comp
    (doublePairQuotientEquiv P).symm.toRingHom

/-- 概要：(p,d) の商から被覆の mod p への射は忠実平坦。
方針：式 (6) の二つの忠実平坦射と二重商の同型を合成する。
規約：BS 著者版 Construction 6.1、Construction 6.1 の明示的な完全平坦性入力。
使われ方：A 上の振幅二と保存性。 -/
theorem coverPairFlatMap_faithfullyFlat
    (hF : IsCompletelyFlat (Ideal.span {coverModPGenerator P})
      (baseChangeScalarModule (modPMap p P.deltaStructure.frobeniusLift)))
    (hR : IsSMulRegular (A ⧸ P.ideal) (p : A ⧸ P.ideal)) :
    (coverPairFlatMap P hR).FaithfullyFlat :=
  RingHom.FaithfullyFlat.stableUnderComposition _ _
    (RingHom.FaithfullyFlat.of_bijective (doublePairQuotientEquiv P).symm.bijective)
    (RingHom.FaithfullyFlat.stableUnderComposition _ _
      (residueFrobenius_faithfullyFlat P hF) (coverResidueFlatMap_faithfullyFlat P hR))

/-- 概要：A から被覆の mod p への標準射は正則二元の商を経由する。
方針：式 (6) と二重商の標準係数脚の一致を使う。
規約：BS 著者版 Construction 6.1 の標準射そのもの。
使われ方：実際の底変換を有限 Koszul 模型で計算する。 -/
theorem coverMapToModP_factorization
    (hR : IsSMulRegular (A ⧸ P.ideal) (p : A ⧸ P.ideal)) :
    coverMapToModP P = (coverPairFlatMap P hR).comp
      (Ideal.Quotient.mk (Ideal.span (Set.range (coverPairCoordinates P)))) := by
  have hi (a : A) : (doublePairQuotientEquiv P).symm
      (Ideal.Quotient.mk (Ideal.span (Set.range (coverPairCoordinates P))) a) =
        Ideal.Quotient.mk _ (Ideal.Quotient.mk (Ideal.span {(p : A)}) a) := by
    apply (doublePairQuotientEquiv P).injective
    rw [RingEquiv.apply_symm_apply, doublePairQuotientEquiv_unit]
  apply RingHom.ext
  intro a
  have hf := RingHom.congr_fun (alphaModP_factorization P hR)
    (Ideal.Quotient.mk (Ideal.span {(p : A)}) a)
  change alphaModP P (Ideal.Quotient.mk (Ideal.span {(p : A)}) a) = _
  rw [hf]
  simp only [coverPairFlatMap, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe,
    RingEquiv.coe_toRingHom, hi]

/-- 概要：被覆の mod p の A 上の非有界な底変換は下界を高々二下げる。
方針：正則二元の商の実際の K-flat 模型を、忠実平坦な標的へ底変換する。
規約：BS 著者版 Construction 6.1。任意の複体の分解射を明示する。
使われ方：完全 Koszul の振幅三の評価。 -/
theorem coverMapToModP_homology_isZero_below
    (hF : IsCompletelyFlat (Ideal.span {coverModPGenerator P})
      (baseChangeScalarModule (modPMap p P.deltaStructure.frobeniusLift)))
    (hR : IsSMulRegular (A ⧸ P.ideal) (p : A ⧸ P.ideal))
    {L K : CochainComplex (ModuleCat.{u} A) ℤ} (q : L ⟶ K) [QuasiIso q]
    (hL : complexKFlat A L) (m : ℤ)
    (hK : ∀ i : ℤ, i < m → IsZero (K.homology i))
    (i : ℤ) (hi : i < m - 2) :
    IsZero ((baseChange (coverMapToModP P) L).homology i) := by
  let q₀ := Ideal.Quotient.mk (Ideal.span (Set.range (coverPairCoordinates P)))
  have h₀ : ∀ j : ℤ, j < m - 2 → IsZero ((baseChange q₀ L).homology j) := by
    intro j hj
    exact regularQuotientBaseChange_homology_isZero_below (coverPairCoordinates P)
      (coverPairCoordinates_regular P hR) q hL m hK j hj
  let g := coverPairFlatMap P hR
  have h₁ := flatBaseChange_homology_isZero_below g
    (coverPairFlatMap_faithfullyFlat P hF hR).flat (baseChange q₀ L) (m - 2) h₀ i hi
  let e := (HomologicalComplex.homologyFunctor _ _ i).mapIso (baseChangeCompIso q₀ g L)
  have h₂ : IsZero ((baseChange (g.comp q₀) L).homology i) := h₁.of_iso e.symm
  have hf : coverMapToModP P = g.comp q₀ := coverMapToModP_factorization P hR
  simpa only [← hf] using h₂

end SerrePositivity.BhattScholze.Prismatic.Construction61
