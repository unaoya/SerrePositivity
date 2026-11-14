module

public import SerrePositivity.AlgebraicGeometry.SchemeVCover
public import SerrePositivity.AlgebraicGeometry.ValuationProbeExtension
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
概要：固有全射の付値持ち上げを、任意の基底・始域に対して供給する。
方針：分数体上のファイバーの点の剰余体を取り、付値拡大後に固有性の付値判定を使う。
規約：元の固有射の affine 性・Noether 性・有限表示は仮定しない。
使われ方：Rydh 3.10 の固有全射の因子の v 被覆性。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry
universe u

/-- 固有全射は任意の階数の付値環に対する持ち上げを持つ。 -/
theorem isSchemeVCover_of_proper_surjective {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsProper f] [Surjective f] : IsSchemeVCover f := by
  intro V _ _ k
  let F := FractionRing V
  let κ := algebraMap V F
  let t := Spec.map (CommRingCat.ofHom κ) ≫ k
  let T := pullback f t
  obtain ⟨x, _⟩ := (pullback.snd f t).surjective (IsLocalRing.closedPoint F)
  let L := T.residueField x
  let a : Spec (CommRingCat.of L) ⟶ X := T.fromSpecResidueField x ≫ pullback.fst f t
  let c : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of F) :=
    T.fromSpecResidueField x ≫ pullback.snd f t
  let ψ := (Spec.preimage c).hom
  have hψ : Spec.map (CommRingCat.ofHom ψ) = c := Spec.map_preimage c
  have ht : a ≫ f = Spec.map (CommRingCat.ofHom (ψ.comp κ)) ≫ k := by
    dsimp only [a]
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    change c ≫ (Spec.map (CommRingCat.ofHom κ) ≫ k) = _
    rw [← hψ, ← Category.assoc, ← Spec.map_comp]
    rfl
  obtain ⟨W, e, he, heflat⟩ := exists_valuationSubring_extension_of_injective (ψ.comp κ)
    (ψ.injective.comp (IsFractionRing.injective V F))
  have hc : ValuativeCriterion.Existence f := by
    have h : UniversallyClosed f := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  let S : ValuativeCommSq f := {
    R := W
    K := L
    i₁ := a
    i₂ := Spec.map (CommRingCat.ofHom e) ≫ k
    commSq := ⟨by
      rw [ht, ← Category.assoc, ← Spec.map_comp]
      exact congrArg (fun q ↦ Spec.map (CommRingCat.ofHom q) ≫ k) he.symm⟩ }
  obtain ⟨l, _, hl⟩ := (hc S).exists_lift
  exact ⟨CommRingCat.of W, inferInstance, inferInstance, e, l, heflat, hl⟩

end SerrePositivity.AlgebraicGeometry
