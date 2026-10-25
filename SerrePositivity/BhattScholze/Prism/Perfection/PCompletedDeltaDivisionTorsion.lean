module

public import SerrePositivity.BhattScholze.Prism.Perfection.PCompletedDeltaDivision
public import SerrePositivity.BhattScholze.Delta.Perfect.PerfectDelta

/-! # 旧dねじれ除去とp進完備δ除算完全化の比較

著者公開版Prop 7.2の旧ねじれ除去商と、具体的なp進完備δ完全化を比較する。
dがdistinguishedなら、除算添加環のp進完備δ完全化と、旧dねじれのδ閉包商を
先に取ってから同じ完全化を施した環は、標準射と両立するδ環同型を持つ。
一般の導来(p,d)完備化や超限反復とは同定しない。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R] {σ : Type v}

/-- 旧dねじれのδ閉包商が誘導する、具体的なp進完備δ完全化間の標準射。 -/
def pCompletedDeltaDivisionTorsionMap (D : DeltaStructure p R) (d : R) (a : σ → R) :
    PCompletedDeltaDivision D d a →+*
      PCompletedDeltaPerfection (deltaDivisionTorsionStructure D d a) :=
  pCompletedDeltaMap (deltaAdjoinDivisionStructure D d a) (deltaDivisionTorsionStructure D d a)
    (Ideal.Quotient.mk _)
    ((deltaAdjoinDivisionStructure D d a).isDeltaHom_quotient_mk _
      ((deltaAdjoinDivisionStructure D d a).isStable_deltaClosure _))

/-- 標準比較射はδ射。 -/
theorem pCompletedDeltaDivisionTorsionMap_isDeltaHom
    (D : DeltaStructure p R) (d : R) (a : σ → R) :
    (pCompletedDeltaDivisionStructure D d a).IsDeltaHom
      (pCompletedDeltaPerfectionStructure (deltaDivisionTorsionStructure D d a))
      (pCompletedDeltaDivisionTorsionMap D d a) :=
  pCompletedDeltaMap_isDeltaHom _ _ _ _

/-- 標準比較射は元の基底射と可換。 -/
theorem pCompletedDeltaDivisionTorsionMap_comp_base
    (D : DeltaStructure p R) (d : R) (a : σ → R) :
    (pCompletedDeltaDivisionTorsionMap D d a).comp (pCompletedDeltaDivisionMap D d a) =
      (pCompletedDeltaPerfectionMap (deltaDivisionTorsionStructure D d a)).comp
        (deltaDivisionTorsionMap D d a) := by
  let DB := deltaAdjoinDivisionStructure D d a
  let DT := deltaDivisionTorsionStructure D d a
  let q : DeltaAdjoinDivision D d a →+* DeltaDivisionTorsionQuotient D d a := Ideal.Quotient.mk _
  have hq : DB.IsDeltaHom DT q := DB.isDeltaHom_quotient_mk _ (DB.isStable_deltaClosure _)
  have h : (pCompletedDeltaDivisionTorsionMap D d a).comp (pCompletedDeltaPerfectionMap DB) =
      (pCompletedDeltaPerfectionMap DT).comp q := pCompletedDeltaMap_comp_map DB DT q hq
  change (pCompletedDeltaDivisionTorsionMap D d a).comp
      ((pCompletedDeltaPerfectionMap DB).comp (deltaAdjoinDivisionMap D d a)) =
    (pCompletedDeltaPerfectionMap DT).comp (q.comp (deltaAdjoinDivisionMap D d a))
  rw [← RingHom.comp_assoc, h, RingHom.comp_assoc]

/-- dがdistinguishedなら、旧dねじれ除去が誘導する標準p進完備δ完全化射は全単射。
逆射はねじれ除去の普遍性と既存完全化の普遍性から作り、両合成を外延性で検証する。 -/
theorem pCompletedDeltaDivisionTorsionMap_bijective
    (D : DeltaStructure p R) (d : R) (hd : D.IsDistinguished d) (a : σ → R) :
    Function.Bijective (pCompletedDeltaDivisionTorsionMap D d a) := by
  let DB := deltaAdjoinDivisionStructure D d a
  let DT := deltaDivisionTorsionStructure D d a
  let q : DeltaAdjoinDivision D d a →+* DeltaDivisionTorsionQuotient D d a := Ideal.Quotient.mk _
  let jB := pCompletedDeltaPerfectionMap DB
  let jT := pCompletedDeltaPerfectionMap DT
  let f := pCompletedDeltaDivisionTorsionMap D d a
  let EC := pCompletedDeltaDivisionStructure D d a
  let := pCompletedDeltaDivision_isAdicComplete D d a
  let := pCompletedDeltaPerfection_isAdicComplete DT
  have hq : DB.IsDeltaHom DT q := DB.isDeltaHom_quotient_mk _ (DB.isStable_deltaClosure _)
  have hFj : f.comp jB = jT.comp q := pCompletedDeltaMap_comp_map DB DT q hq
  obtain ⟨k, hk, _⟩ := DB.existsUnique_torsionReductionHom
    (deltaAdjoinDivisionMap D d a d) EC jB (pCompletedDeltaPerfectionMap_isDeltaHom DB)
    (pCompletedDeltaDivisionMap_mul_injective D d a hd)
  let g := pCompletedDeltaLift DT EC (pCompletedDeltaDivision_isPerfect D d a) k hk.2
  have hgj : g.comp jT = k := pCompletedDeltaLift_comp_map DT EC
    (pCompletedDeltaDivision_isPerfect D d a) k hk.2
  have hgd : (pCompletedDeltaPerfectionStructure DT).IsDeltaHom EC g :=
    pCompletedDeltaLift_isDeltaHom DT EC (pCompletedDeltaDivision_isPerfect D d a) k hk.2
  have hfd := pCompletedDeltaDivisionTorsionMap_isDeltaHom D d a
  have hGF : g.comp f = RingHom.id (PCompletedDeltaDivision D d a) := by
    apply pCompletedDeltaHom_ext DB EC (pCompletedDeltaDivision_isPerfect D d a)
      _ _ (hgd.comp hfd) EC.isDeltaHom_id
    change (g.comp f).comp jB = (RingHom.id _).comp jB
    rw [RingHom.comp_assoc, hFj, ← RingHom.comp_assoc, hgj, hk.1, RingHom.id_comp]
  have hfk : f.comp k = jT := by
    apply RingHom.ext
    intro x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    change f (k (q b)) = jT (q b)
    rw [show k (q b) = jB b from RingHom.congr_fun hk.1 b]
    exact RingHom.congr_fun hFj b
  have hFG : f.comp g = RingHom.id (PCompletedDeltaPerfection DT) := by
    apply pCompletedDeltaHom_ext DT (pCompletedDeltaPerfectionStructure DT)
      (pCompletedDeltaPerfection_isPerfect DT) _ _ (hfd.comp hgd)
      (pCompletedDeltaPerfectionStructure DT).isDeltaHom_id
    change (f.comp g).comp jT = (RingHom.id _).comp jT
    rw [RingHom.comp_assoc, hgj, hfk, RingHom.id_comp]
  have hl : Function.LeftInverse g f := fun x ↦ RingHom.congr_fun hGF x
  have hr : Function.RightInverse g f := fun x ↦ RingHom.congr_fun hFG x
  exact ⟨hl.injective, hr.surjective⟩

/-- 旧dねじれのδ閉包商を前に施す二つの具体的候補の環同型。 -/
def pCompletedDeltaDivisionTorsionEquiv
    (D : DeltaStructure p R) (d : R) (hd : D.IsDistinguished d) (a : σ → R) :
    PCompletedDeltaDivision D d a ≃+*
      PCompletedDeltaPerfection (deltaDivisionTorsionStructure D d a) :=
  RingEquiv.ofBijective (pCompletedDeltaDivisionTorsionMap D d a)
    (pCompletedDeltaDivisionTorsionMap_bijective D d hd a)

/-- 比較同型の順射は旧ねじれ除去商による標準比較射。 -/
@[simp] theorem pCompletedDeltaDivisionTorsionEquiv_toRingHom
    (D : DeltaStructure p R) (d : R) (hd : D.IsDistinguished d) (a : σ → R) :
    (pCompletedDeltaDivisionTorsionEquiv D d hd a).toRingHom =
      pCompletedDeltaDivisionTorsionMap D d a := rfl

/-- 比較同型の逆射もδ射。 -/
theorem pCompletedDeltaDivisionTorsionEquiv_symm_isDeltaHom
    (D : DeltaStructure p R) (d : R) (hd : D.IsDistinguished d) (a : σ → R) :
    (pCompletedDeltaPerfectionStructure (deltaDivisionTorsionStructure D d a)).IsDeltaHom
      (pCompletedDeltaDivisionStructure D d a)
      (pCompletedDeltaDivisionTorsionEquiv D d hd a).symm.toRingHom :=
  DeltaStructure.IsDeltaHom.symm (pCompletedDeltaDivisionTorsionMap_isDeltaHom D d a)

end SerrePositivity.BhattScholze
