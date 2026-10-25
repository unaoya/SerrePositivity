module

public import SerrePositivity.BhattScholze.Delta.Extension.PDCompletionInterface
public import SerrePositivity.BhattScholze.Delta.Extension.WittTwoPDComplete

/-! # 実際の導来(p,d)完備化H⁰へのδ構造の一意延長

著者公開版Lemma 2.18の完備化への適用部分。
受領F3の環普遍性とW₂の実導来完備性から切断を延長する。
p正則性・古典的完備性・有界ねじれを仮定しない。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open SerrePositivity.DerivedCompletion
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- 実際のH⁰に、標準射をδ射とするδ構造が一意に存在する。 -/
theorem existsUnique_deltaPDCompletionStructure (D : DeltaStructure p A) (d : A) :
    letI := pdCompletionCommRing A p d
    ∃! E : DeltaStructure p (PDCompletionH0 A p d), D.IsDeltaHom E (pdCompletionUnit A p d) := by
  let := pdCompletionCommRing A p d
  let H := PDCompletionH0 A p d
  let j := pdCompletionUnit A p d
  have hpH := pdCompletionH0_self_complete_p A p d
  have hdH := pdCompletionH0_self_complete_d A p d
  obtain ⟨s, hs, hsu⟩ := pdCompletion_existsUnique_ringHom A p d (WittTwo p H)
    (wittTwoBaseMap D j) (wittTwo_isModuleComplete_p D j hpH)
    (wittTwo_isModuleComplete_d D j d hpH hdH)
  have hproj : (wittTwoProjection p H).comp s = RingHom.id H := by
    apply pdCompletionRingHom_ext A p d H j hpH hdH
    · rw [RingHom.comp_assoc, hs]
      apply RingHom.ext
      intro x
      simp only [RingHom.comp_apply, wittTwoProjection_apply, wittTwoBaseMap,
        wittTwoMap_coeff, D.coeff_zero]
    · exact RingHom.id_comp j
  let E : DeltaStructure p H :=
    { sectionHom := s
      coeff_zero := fun x ↦ RingHom.congr_fun hproj x }
  have hE : D.IsDeltaHom E j :=
    (D.isDeltaHom_iff_sectionHom_comp E j).mpr hs.symm
  refine ⟨E, hE, ?_⟩
  intro E' hE'
  have hb : E'.sectionHom.comp j = wittTwoBaseMap D j :=
    ((D.isDeltaHom_iff_sectionHom_comp E' j).mp hE').symm
  have he : E'.sectionHom = s := hsu E'.sectionHom hb
  apply DeltaStructure.ext
  intro x
  exact congrArg (fun z : WittTwo p H ↦ z.coeff 1) (RingHom.congr_fun he x)

/-- 実際の(p,d)完備化H⁰に選んだ唯一のδ構造。 -/
def deltaPDCompletionStructure (D : DeltaStructure p A) (d : A) :
    letI := pdCompletionCommRing A p d
    DeltaStructure p (PDCompletionH0 A p d) :=
  (existsUnique_deltaPDCompletionStructure D d).choose

/-- 元のKoszul標準射は、選んだδ構造へのδ射。 -/
theorem pdCompletionUnit_isDeltaHom (D : DeltaStructure p A) (d : A) :
    letI := pdCompletionCommRing A p d
    D.IsDeltaHom (deltaPDCompletionStructure D d) (pdCompletionUnit A p d) :=
  (existsUnique_deltaPDCompletionStructure D d).choose_spec.1

/-- 標準射がδ射になる任意のδ構造は、選んだ構造に一致する。 -/
theorem deltaPDCompletionStructure_unique (D : DeltaStructure p A) (d : A) :
    letI := pdCompletionCommRing A p d
    ∀ E : DeltaStructure p (PDCompletionH0 A p d),
      D.IsDeltaHom E (pdCompletionUnit A p d) → E = deltaPDCompletionStructure D d :=
  (existsUnique_deltaPDCompletionStructure D d).choose_spec.2

end SerrePositivity.BhattScholze
