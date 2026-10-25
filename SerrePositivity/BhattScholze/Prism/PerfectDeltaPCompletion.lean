module

public import SerrePositivity.BhattScholze.Delta.DeltaAdicLift
public import SerrePositivity.BhattScholze.Delta.DeltaPerfectionUniversal

/-! # 完全δ環の古典的p進完備化

著者公開版Lemma 3.9のp進完備化段階に使うδ環の定理。
逆Frobeniusを古典的完備化に延長し、射の外延性で両逆の等式を証明する。
導来完備化との比較やprismのイデアルの処理は含めない。
-/

@[expose] public noncomputable section
universe u v
namespace SerrePositivity.BhattScholze.DeltaStructure
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- 完全δ環を古典的p進完備化しても完全δ環となる。 -/
theorem IsPerfect.adicCompletion_span_p {D : DeltaStructure p A} (hD : D.IsPerfect) :
    (D.adicCompletion (Ideal.span {(p : A)}) (Ideal.subset_span (by simp))).IsPerfect := by
  let I : Ideal A := Ideal.span {(p : A)}
  have hI : I.FG := Submodule.fg_span (Set.toFinite _)
  have hp : (p : A) ∈ I := Ideal.subset_span (by simp)
  let C := AdicCompletion I A
  let j := algebraMap A C
  let J : Ideal C := Ideal.span {(p : C)}
  let DC := D.adicCompletion I hp
  have hJ : I.map j = J := by simp [I, J, Ideal.map_span, j]
  let : IsAdicComplete I C := AdicCompletion.isAdicComplete hI
  let : IsAdicComplete J C := by
    rw [← hJ]
    exact (IsAdicComplete.map_algebraMap_iff (I := I) (S := C) (M := C)).mpr inferInstance
  let ψ := (D.frobeniusEquiv hD).symm.toRingHom
  have hδj := D.isDeltaHom_adicCompletion I hp
  have hψ : D.IsDeltaHom D ψ := D.frobeniusEquiv_symm_isDeltaHom hD
  have hIJ : I.map (j.comp ψ) ≤ J := by
    simp [I, J, Ideal.map_span]
  obtain ⟨g, hg, _⟩ := D.existsUnique_adicCompletion_lift DC I hp hI J
    (j.comp ψ) (hδj.comp hψ) hIJ
  have hgj (r : A) : g (j r) = j (ψ r) := DFunLike.congr_fun hg.1 r
  have hFj (r : A) : DC.frobeniusLift (j r) = j (D.frobeniusLift r) :=
    (hδj.map_frobeniusLift r).symm
  have hbase : I.map j ≤ J := hJ.le
  have hFG : DC.frobeniusLift.comp g = RingHom.id C := by
    apply adicCompletion_extension_unique I hI J j hbase
    · apply RingHom.ext
      intro r
      change DC.frobeniusLift (g (j r)) = j r
      rw [hgj, hFj]
      change j ((D.frobeniusEquiv hD) ((D.frobeniusEquiv hD).symm r)) = j r
      rw [RingEquiv.apply_symm_apply]
    · rfl
  have hGF : g.comp DC.frobeniusLift = RingHom.id C := by
    apply adicCompletion_extension_unique I hI J j hbase
    · apply RingHom.ext
      intro r
      change g (DC.frobeniusLift (j r)) = j r
      rw [hFj, hgj]
      change j ((D.frobeniusEquiv hD).symm ((D.frobeniusEquiv hD) r)) = j r
      rw [RingEquiv.symm_apply_apply]
    · rfl
  have hleft : Function.LeftInverse g DC.frobeniusLift := fun x ↦ DFunLike.congr_fun hGF x
  have hright : Function.RightInverse g DC.frobeniusLift := fun x ↦ DFunLike.congr_fun hFG x
  exact ⟨hleft.injective, hright.surjective⟩

end SerrePositivity.BhattScholze.DeltaStructure
