module
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.BasedEndBlock
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.BasedCoefficientRestriction
public import SerrePositivity.InfinityCategories.Derived.CoherentBar.Retract.BasedFullEndColumnAction
/-!
概要：零次数の係数列への前合成は、始点保存自己写像による係数押出しに一致する。
方針：全次数の既存の交換式を零次数へ移送し、始点支持のある全係数へ延長する。
規約：全係数の版は始点支持を明示仮定とする。
使われ方：普遍 Hσ の係数自然性を実境界との合成へ移す。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories
open CategoryTheory Limits DifferentialGraded DGNerve SSet
open scoped Simplicial
variable (R : Type u) [CommRing R] (D : Type v) [DGCategory R D] [Small.{u} D]
  {I : SSet.{u}}
  (F : (SSet.uliftFunctor.{max (u + 1) v, u}).obj I ⟶ dgNerve R (RightModule R D))

lemma dgCoherentBarBasedEndColumnAction_push {n : ℕ} (f : ⦋n⦌ ⟶ ⦋n⦌)
    (hf : f.toOrderHom 0 = 0) (s : I _⦋n⦌) (z : DGCoherentBarBasedLabel.{u} n n →₀ R) :
    compose R
      (x := ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F ⟨n, s⟩))
      (y := ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F ⟨n, I.map f.op s⟩))
      (z := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
      (dgCoherentBarBasedEndColumnAction R D F (I.map f.op s) z)
      (dgCoherentBarBasedEndBlock R D F f hf s) rfl =
    dgCoherentBarBasedEndColumnAction R D F s
      (Finsupp.mapDomain (dgCoherentBarBasedLabelPush f hf) z) := by
  have h := dgCoherentBarBasedColumnAction_push R D F f hf s z
  have ht := congrArg (dgCoherentBarEndDegreeTransport R D F s) h
  let M := ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F ⟨n, s⟩)
  let N := ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F ⟨n, I.map f.op s⟩)
  let B := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F)
  have hc := gradedHomTransport_compose (A := R) (D := RightModule R D)
    (x := M) (y := N) (z := B) (x' := M) (y' := N) (z' := B)
    rfl rfl rfl (sub_self (n : ℤ)) (sub_self (n : ℤ)) (sub_self (n : ℤ))
    (dgCoherentBarBasedColumnAction R D F n (I.map f.op s) z)
    (dgCoherentBarBasedBlock R D F f hf s)
    (by omega : ((n : ℤ) - (n : ℤ)) + ((n : ℤ) - (n : ℤ)) = (n : ℤ) - (n : ℤ))
  exact hc.symm.trans ht

lemma dgCoherentBarBasedFullEndColumnAction_push {n : ℕ} (f : ⦋n⦌ ⟶ ⦋n⦌)
    (hf : f.toOrderHom 0 = 0) (s : I _⦋n⦌)
    (z : ((Δ[n] : SSet.{u}) _⦋n⦌) →₀ R) (hz : ∀ a ∈ z.support, a 0 = 0) :
    compose R
      (x := ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F ⟨n, s⟩))
      (y := ForgetEnrichment.to (Complex R) (dgCoherentBarFamily R D F ⟨n, I.map f.op s⟩))
      (z := ForgetEnrichment.to (Complex R) (dgCoherentBarGraded R D F))
      (dgCoherentBarBasedFullEndColumnAction R D F (I.map f.op s) z)
      (dgCoherentBarBasedEndBlock R D F f hf s) rfl =
    dgCoherentBarBasedFullEndColumnAction R D F s
      (Finsupp.mapDomain ((SSet.stdSimplex.map f).app (Opposite.op ⦋n⦌)) z) := by
  have h := dgCoherentBarBasedEndColumnAction_push R D F f hf s
    (z.subtypeDomain (fun a => a 0 = 0))
  have hr := congrArg (dgCoherentBarBasedEndColumnAction R D F s)
    (dgCoherentBarBasedCoefficients_push R f hf z hz)
  exact h.trans hr.symm

end SerrePositivity.InfinityCategories
