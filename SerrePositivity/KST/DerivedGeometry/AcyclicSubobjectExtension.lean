module

public import SerrePositivity.KST.DerivedGeometry.SmallAcyclicTestSubobject
public import SerrePositivity.KST.DerivedGeometry.ShortExactPullback
public import SerrePositivity.KST.DerivedGeometry.MonoQuasiIsoPushout
public import SerrePositivity.KST.DerivedGeometry.AcyclicMapAttachment

/-!
概要：真の非輪状部分複体を、小さい試験商を持つ真に大きな非輪状部分複体へ拡大する。
方針：非零な非輪状商の試験部分対象を引き戻し、短完全列で非輪状性を証明する。
規約：余核と試験対象の実際の同型も結論として構成する。
使われ方：Stacks Lemma 19.12.3、TT §3・§8、Toën §3.2 の超限分解の後続工程。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w u
open CategoryTheory Limits
namespace SerrePositivity.KST.DerivedGeometry
variable {C : Type u} [Category.{w} C] [Abelian C] [IsGrothendieckAbelian.{w} C]

/--
概要：真の非輪状部分対象には、小さい試験商を持つ真に大きな非輪状部分対象が存在する。
方針：非零商の試験部分対象を pullback し、余核の普遍性で商を比較する。
規約：超限分解の一工程の存在を実際に証明する。
使われ方：Stacks 19.12.3、TT §3 の全ての非輪状複体を尽くす構成。
-/
lemma exists_larger_acyclic_subobject (G : C) (hG : IsSeparator G)
    (M : CochainComplex C ℤ) (hM : M.Acyclic) (S : Subobject M)
    (hS : (S : CochainComplex C ℤ).Acyclic) (hne : S ≠ ⊤) :
    ∃ (S' : Subobject M) (h : S < S') (s : SmallAcyclicTestIndex G),
      (S' : CochainComplex C ℤ).Acyclic ∧
      Nonempty (cokernel (Subobject.ofLE S S' h.le) ≅ smallAcyclicTestFamily G s) := by
  let f := S.arrow
  let q := cokernel.π f
  have hQ : (cokernel f).Acyclic := (mono_quasiIso_iff_acyclic_cokernel f).mp
    (quasiIso_of_acyclic _ _ f hS hM)
  have hnQ : ¬ IsZero (cokernel f) := by
    intro hz
    have : Epi f := Abelian.epi_of_cokernel_π_eq_zero f (hz.eq_zero_of_tgt _)
    have : IsIso f := isIso_of_mono_of_epi _
    exact hne (Subobject.eq_top_of_isIso_arrow S)
  obtain ⟨s, i, hi, hni⟩ := exists_nonzero_smallAcyclicTest_subobject G hG (cokernel f) hQ hnQ
  have : Mono i := hi
  let T := smallAcyclicTestFamily G s
  let j := pullback.fst q i
  let g : (S : CochainComplex C ℤ) ⟶ pullback q i := pullback.lift f 0 (by simp [q])
  let S' := Subobject.mk j
  have hP := shortComplexPullback_shortExact (monoCokernelShortComplex f) i
    (monoCokernelShortComplex_shortExact f)
  have hPA : (pullback q i).Acyclic := hP.acyclic_X₂ hS s.prop.1
  have hg0 : g ≫ pullback.snd q i = 0 := by simp [g]
  have hgi : ¬ IsIso g := by
    intro hg
    have : IsIso g := hg
    have hz : pullback.snd q i = 0 := by
      apply (cancel_epi g).mp
      simpa only [comp_zero] using hg0
    apply hni
    rw [IsZero.iff_id_eq_zero]
    apply (cancel_epi (pullback.snd q i)).mp
    rw [hz, zero_comp, zero_comp]
  have hlt : S < S' := by
    simpa only [Subobject.mk_arrow] using
      (Subobject.mk_lt_mk_of_comm (i₁ := S.arrow) (i₂ := j) g (by simp [g, j, f]) hgi)
  let E : (S' : CochainComplex C ℤ) ≅ pullback q i := Subobject.underlyingIso j
  have hw : Subobject.ofLE S S' hlt.le ≫ E.hom = g := by
    apply (cancel_mono j).mp
    rw [Category.assoc, Subobject.underlyingIso_hom_comp_eq_mk, Subobject.ofLE_arrow]
    simp [g, j, f]
  have : Epi (shortComplexPullback (monoCokernelShortComplex f) i).g := hP.epi_g
  have hp : IsColimit (CokernelCofork.ofπ (pullback.snd q i) hg0) := hP.exact.gIsCokernel
  let Ec : cokernel g ≅ T := (cokernelIsCokernel g).coconePointUniqueUpToIso hp
  let Ei : cokernel (Subobject.ofLE S S' hlt.le) ≅ cokernel g :=
    cokernel.mapIso _ g (Iso.refl _) E (by simpa only [Iso.refl_hom, Category.id_comp] using hw)
  exact ⟨S', hlt, s, fun n => (hPA n).of_iso E.symm, ⟨Ei ≪≫ Ec⟩⟩

end SerrePositivity.KST.DerivedGeometry
