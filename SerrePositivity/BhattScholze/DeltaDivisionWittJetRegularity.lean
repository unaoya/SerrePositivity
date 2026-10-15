module

public import SerrePositivity.BhattScholze.DeltaDivisionWittRelationIdeal
public import SerrePositivity.CommutativeAlgebra.KoszulResolution
public import SerrePositivity.HomologicalAlgebra.DerivedQuotientKoszul

/-! # 下位関係商におけるδ反復関係とWitt根関係の正則性

既存の主イデアル置換等式を使用する。p正則性・ghost単射・δd単元条件を明示する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]
variable (D : DeltaStructure p A)
variable (hp : Function.Injective (fun z : A ↦ (p : A) * z))
variable (hg : Function.Injective (WittVector.ghostMap : WittVector p A → ℕ → A))
variable (I : Ideal A) (hpI : (p : A) ∈ I) (d x a : A) (hdI : d ∈ I)
variable (v : Aˣ) (hv : (v : A) = D.delta d) (n : ℕ)
variable (hlower : ∀ i ≤ n + 1, D.delta^[i] (d * x - a) ∈ I)
include hp hg hpI hdI hv hlower

/-- 下位関係商内では、次段δ反復関係とWitt根関係が同じ主イデアルを生成する。 -/
theorem deltaDivision_next_jet_quotient_span_eq_witt :
    Ideal.span {Ideal.Quotient.mk I (D.delta^[n + 2] (d * x - a))} =
      Ideal.span {Ideal.Quotient.mk I (deltaDivisionWittRelationElement D d x a v n)} := by
  have h := congrArg (Ideal.map (Ideal.Quotient.mk I))
    (deltaDivision_next_jet_sup_span_eq_witt_relation D hp hg I hpI d x a hdI v hv n hlower)
  simpa only [Ideal.map_sup, Ideal.map_quotient_self, bot_sup_eq,
    Ideal.map_span, Set.image_singleton] using h

/-- 商内の元のδ反復関係が非零因子であることは、Witt根関係の正則性と同値。 -/
theorem deltaDivision_next_jet_quotient_isSMulRegular_iff_witt :
    IsSMulRegular (A ⧸ I) (Ideal.Quotient.mk I (D.delta^[n + 2] (d * x - a))) ↔
      IsSMulRegular (A ⧸ I)
        (Ideal.Quotient.mk I (deltaDivisionWittRelationElement D d x a v n)) := by
  have go (r t : A ⧸ I) (he : Ideal.span {r} = Ideal.span {t})
      (ht : IsSMulRegular (A ⧸ I) t) : IsSMulRegular (A ⧸ I) r := by
    have hm : t ∈ Ideal.span {r} := he.symm ▸ Ideal.mem_span_singleton_self t
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hm
    have ht' : IsRegular t := isLeftRegular_iff_isRegular.mp ht
    rw [hc] at ht'
    exact ht'.of_mul_left.left
  have he := deltaDivision_next_jet_quotient_span_eq_witt D hp hg I hpI d x a hdI v hv n hlower
  exact ⟨go _ _ he.symm, go _ _ he⟩

/-- 商内のWitt根関係が正則なら、元の次段δ反復関係の実Koszul分解を得る。 -/
theorem deltaDivision_next_jet_quotient_isKoszulResolution
    (hreg : IsSMulRegular (A ⧸ I)
      (Ideal.Quotient.mk I (deltaDivisionWittRelationElement D d x a v n))) :
    SerrePositivity.IsKoszulResolution
      (fun _ : Fin 1 ↦ Ideal.Quotient.mk I (D.delta^[n + 2] (d * x - a))) := by
  apply SerrePositivity.isKoszulResolution_of_isWeaklyRegular
  rw [List.ofFn_const, List.replicate_one,
    RingTheory.Sequence.isWeaklyRegular_singleton_iff]
  exact (deltaDivision_next_jet_quotient_isSMulRegular_iff_witt
    D hp hg I hpI d x a hdI v hv n hlower).mpr hreg

/-- 元のδ反復関係による導来商は、共通の実Koszul錐関手と自然同型。 -/
def deltaDivision_next_jet_quotient_derivedKoszulNatIso
    (hreg : IsSMulRegular (A ⧸ I)
      (Ideal.Quotient.mk I (deltaDivisionWittRelationElement D d x a v n))) :
    boundedAboveDerivedBaseChange
        (Ideal.Quotient.mk (Ideal.span {Ideal.Quotient.mk I (D.delta^[n + 2] (d * x - a))})) ⋙
      boundedAboveDerivedRestrictScalars
        (Ideal.Quotient.mk (Ideal.span {Ideal.Quotient.mk I (D.delta^[n + 2] (d * x - a))})) ⋙
      DerivedCategory.Minus.ι ≅
    DerivedCategory.Minus.ι ⋙ DerivedCompletion.derivedScalarConeFunctor (A ⧸ I)
      (Ideal.Quotient.mk I (D.delta^[n + 2] (d * x - a))) :=
  restrictedDerivedQuotientKoszulNatIso _
    ((deltaDivision_next_jet_quotient_isSMulRegular_iff_witt
      D hp hg I hpI d x a hdI v hv n hlower).mpr hreg)

end SerrePositivity.BhattScholze
