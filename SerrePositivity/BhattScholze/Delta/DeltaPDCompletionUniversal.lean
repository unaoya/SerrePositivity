module

public import SerrePositivity.BhattScholze.Delta.DeltaPDCompletion

/-! # 実際の導来(p,d)完備化H⁰のδ普遍性

任意のδ基底・pねじれを許す試験δ環について、実導来完備性を明示して一意延長する。
prism性・perfectoid性・全射性はこの普遍性には含めない。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open SerrePositivity.DerivedCompletion
variable {p : ℕ} [Fact p.Prime] {A T : Type u} [CommRing A] [CommRing T]

/-- 実H⁰からの環延長は、基底δ射の延長なら自動的にδ射になる。 -/
theorem pdCompletionRingHom_isDeltaHom (D : DeltaStructure p A) (d : A)
    (E : DeltaStructure p T) (g : A →+* T) (hg : D.IsDeltaHom E g)
    (hp : IsModuleComplete T (p : T) (ModuleCat.of T T))
    (hd : IsModuleComplete T (g d) (ModuleCat.of T T)) :
    letI := pdCompletionCommRing A p d
    ∀ h : PDCompletionH0 A p d →+* T, h.comp (pdCompletionUnit A p d) = g →
      (deltaPDCompletionStructure D d).IsDeltaHom E h := by
  let := pdCompletionCommRing A p d
  intro h hh
  let H := PDCompletionH0 A p d
  let j := pdCompletionUnit A p d
  let DH := deltaPDCompletionStructure D d
  let F := (wittTwoMap h).comp DH.sectionHom
  let G := E.sectionHom.comp h
  have hj := (D.isDeltaHom_iff_sectionHom_comp DH j).mp (pdCompletionUnit_isDeltaHom D d)
  have hF : F.comp j = wittTwoBaseMap D g := by
    apply RingHom.ext
    intro x
    apply TruncatedWittVector.ext
    intro i
    change (wittTwoMap h (DH.sectionHom (j x))).coeff i =
      (wittTwoMap g (D.sectionHom x)).coeff i
    rw [wittTwoMap_coeff, wittTwoMap_coeff]
    have hn := congrArg (fun z : WittTwo p H ↦ z.coeff i) (RingHom.congr_fun hj x)
    simp only [RingHom.comp_apply] at hn
    rw [← hn, wittTwoMap_coeff]
    exact RingHom.congr_fun hh ((D.sectionHom x).coeff i)
  have hG : G.comp j = wittTwoBaseMap D g := by
    change (E.sectionHom.comp h).comp j = (wittTwoMap g).comp D.sectionHom
    rw [RingHom.comp_assoc, hh]
    exact ((D.isDeltaHom_iff_sectionHom_comp E g).mp hg).symm
  obtain ⟨s, _, hu⟩ := pdCompletion_existsUnique_ringHom A p d (WittTwo p T)
    (wittTwoBaseMap D g) (wittTwo_isModuleComplete_p D g hp)
    (wittTwo_isModuleComplete_d D g d hp hd)
  apply (DH.isDeltaHom_iff_sectionHom_comp E h).mpr
  exact (hu F hF).trans (hu G hG).symm

/-- 任意のp,g(d)実導来完備δ環へ、実H⁰からのδ延長が一意に存在する。 -/
theorem existsUnique_deltaPDCompletionHom (D : DeltaStructure p A) (d : A)
    (E : DeltaStructure p T) (g : A →+* T) (hg : D.IsDeltaHom E g)
    (hp : IsModuleComplete T (p : T) (ModuleCat.of T T))
    (hd : IsModuleComplete T (g d) (ModuleCat.of T T)) :
    letI := pdCompletionCommRing A p d
    ∃! h : PDCompletionH0 A p d →+* T,
      (deltaPDCompletionStructure D d).IsDeltaHom E h ∧ h.comp (pdCompletionUnit A p d) = g := by
  let := pdCompletionCommRing A p d
  obtain ⟨h, hh, hu⟩ := existsUnique_pdCompletionRingHom A p d T g hp hd
  refine ⟨h, ⟨pdCompletionRingHom_isDeltaHom D d E g hg hp hd h hh, hh⟩, ?_⟩
  intro k hk
  exact hu k hk.2

/-- 実H⁰から試験δ環への具体的な一意延長環射。 -/
def deltaPDCompletionLift (D : DeltaStructure p A) (d : A)
    (E : DeltaStructure p T) (g : A →+* T) (hg : D.IsDeltaHom E g)
    (hp : IsModuleComplete T (p : T) (ModuleCat.of T T))
    (hd : IsModuleComplete T (g d) (ModuleCat.of T T)) :
    letI := pdCompletionCommRing A p d
    PDCompletionH0 A p d →+* T :=
  (existsUnique_deltaPDCompletionHom D d E g hg hp hd).choose

/-- 選んだ具体的延長はδ射。 -/
theorem deltaPDCompletionLift_isDeltaHom (D : DeltaStructure p A) (d : A)
    (E : DeltaStructure p T) (g : A →+* T) (hg : D.IsDeltaHom E g)
    (hp : IsModuleComplete T (p : T) (ModuleCat.of T T))
    (hd : IsModuleComplete T (g d) (ModuleCat.of T T)) :
    letI := pdCompletionCommRing A p d
    (deltaPDCompletionStructure D d).IsDeltaHom E (deltaPDCompletionLift D d E g hg hp hd) :=
  (existsUnique_deltaPDCompletionHom D d E g hg hp hd).choose_spec.1.1

/-- 選んだ具体的延長は元のKoszul標準射との合成で基底射gに一致する。 -/
theorem deltaPDCompletionLift_comp_unit (D : DeltaStructure p A) (d : A)
    (E : DeltaStructure p T) (g : A →+* T) (hg : D.IsDeltaHom E g)
    (hp : IsModuleComplete T (p : T) (ModuleCat.of T T))
    (hd : IsModuleComplete T (g d) (ModuleCat.of T T)) :
    letI := pdCompletionCommRing A p d
    (deltaPDCompletionLift D d E g hg hp hd).comp (pdCompletionUnit A p d) = g :=
  (existsUnique_deltaPDCompletionHom D d E g hg hp hd).choose_spec.1.2

end SerrePositivity.BhattScholze
