module

public import SerrePositivity.BhattScholze.PerfectDeltaPDPrism
public import SerrePositivity.BhattScholze.OrientedPrismHom

/-! # 完全δ環の実PD完備化prismの普遍性

完全試験prismへの基底δ射でdがprismイデアルへ入る場合、唯一のprism射を得る。
生成元の一致ではなく、イデアルの保存を用いる。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open SerrePositivity.DerivedCompletion
variable {p : ℕ} [Fact p.Prime] {A T : Type u} [CommRing A] [CommRing T]

/-- 完全試験prismへdをそのイデアルに送る基底δ射は、実完備化prismへ一意延長する。 -/
theorem existsUnique_perfectDeltaPDPrismHom
    (D : DeltaStructure p A) (hD : D.IsPerfect) (d : A) (hd : D.IsDistinguished d)
    (Q : OrientedPrism p T) (hQ : Q.deltaStructure.IsPerfect)
    (f : A →+* T) (hf : D.IsDeltaHom Q.deltaStructure f) (hdf : f d ∈ Q.ideal) :
    letI := pdCompletionCommRing A p d
    ∃! g : OrientedPrism.Hom (perfectDeltaPDPrism D hD d hd) Q,
      g.toRingHom.comp (pdCompletionUnit A p d) = f := by
  let := pdCompletionCommRing A p d
  let P := perfectDeltaPDPrism D hD d hd
  let j := pdCompletionUnit A p d
  let := Q.isAdicComplete_generator
  let := Q.isAdicComplete_p_of_perfect hQ
  have hspan : Ideal.span {f d} = Q.ideal := by
    have h := hf.map_span_eq_of_distinguished_of_mem_span hd hdf
      (IsAdicComplete.le_jacobson_bot (Ideal.span {Q.generator}) (Ideal.subset_span (by simp)))
      (IsAdicComplete.le_jacobson_bot (Ideal.span {(p : T)}) (Ideal.subset_span (by simp)))
    simpa only [Ideal.map_span, Set.image_singleton, OrientedPrism.ideal] using h
  let : IsAdicComplete (Ideal.span {f d}) T := by
    rw [hspan]
    exact Q.isAdicComplete_generator
  have hdT : IsModuleComplete T (f d) (ModuleCat.of T T) :=
    isModuleComplete_of_isAdicComplete T (f d) (ModuleCat.of T T)
  obtain ⟨g, hg, hu⟩ := existsUnique_deltaPDCompletionHom D d Q.deltaStructure f hf Q.complete_p hdT
  have hideal : P.ideal ≤ Q.ideal.comap g := by
    change Ideal.span {j d} ≤ Q.ideal.comap g
    apply (Ideal.span_singleton_le_iff_mem _).mpr
    change g (j d) ∈ Q.ideal
    have he : g (j d) = f d := RingHom.congr_fun hg.2 d
    rw [he]
    exact hdf
  let G : OrientedPrism.Hom P Q := ⟨g, hg.1, hideal⟩
  refine ⟨G, hg.2, ?_⟩
  intro k hk
  apply OrientedPrism.Hom.ext
  exact hu k.toRingHom ⟨k.map_delta, hk⟩

end SerrePositivity.BhattScholze
