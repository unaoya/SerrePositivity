module

public import SerrePositivity.BhattScholze.PerfectDeltaPDPrismUniversal
public import SerrePositivity.BhattScholze.PCompletedDeltaDivisionQuotient

/-! # 任意のイデアルの除算からの具体的な完全prism候補

δ除算・p進完備δ完全化・実PD完備化を合成し、完全試験prismへの一意延長を得る。
一般prismの始対象やIsPerfectoidizationはまだ結論しない。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open SerrePositivity.DerivedCompletion
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R]

/-- Jの全元の除算候補を実PD完備化した具体的な環の台。 -/
abbrev PerfectDeltaDivisionPrismCarrier (D : DeltaStructure p R) (d : R) (J : Ideal R) :=
  PDCompletionH0 (PCompletedDeltaDivision D d (fun x : J ↦ (x : R))) p
    (pCompletedDeltaDivisionMap D d (fun x : J ↦ (x : R)) d)

/-- 候補の可換環構造は実PD完備化の環構造。 -/
@[instance_reducible] def perfectDeltaDivisionPrismCommRing
    (D : DeltaStructure p R) (d : R) (J : Ideal R) :
    CommRing (PerfectDeltaDivisionPrismCarrier D d J) :=
  pdCompletionCommRing (PCompletedDeltaDivision D d (fun x : J ↦ (x : R))) p
    (pCompletedDeltaDivisionMap D d (fun x : J ↦ (x : R)) d)

/-- distinguished dの任意イデアル除算から、実完備化上の完全prismを構成する。 -/
def perfectDeltaDivisionPrism (D : DeltaStructure p R) (d : R) (hd : D.IsDistinguished d)
    (J : Ideal R) :
    letI := perfectDeltaDivisionPrismCommRing D d J
    OrientedPrism p (PerfectDeltaDivisionPrismCarrier D d J) := by
  letI := perfectDeltaDivisionPrismCommRing D d J
  exact perfectDeltaPDPrism (pCompletedDeltaDivisionStructure D d (fun x : J ↦ (x : R)))
    (pCompletedDeltaDivision_isPerfect D d (fun x : J ↦ (x : R)))
    (pCompletedDeltaDivisionMap D d (fun x : J ↦ (x : R)) d)
    ((pCompletedDeltaDivisionMap_isDeltaHom D d (fun x : J ↦ (x : R))).map_isDistinguished hd)

/-- 元の環から具体的な完全prism候補への標準射。 -/
def perfectDeltaDivisionPrismMap (D : DeltaStructure p R) (d : R) (J : Ideal R) :
    letI := perfectDeltaDivisionPrismCommRing D d J
    R →+* PerfectDeltaDivisionPrismCarrier D d J :=
  (pdCompletionUnit (PCompletedDeltaDivision D d (fun x : J ↦ (x : R))) p
    (pCompletedDeltaDivisionMap D d (fun x : J ↦ (x : R)) d)).comp
      (pCompletedDeltaDivisionMap D d (fun x : J ↦ (x : R)))

/-- 選択生成元はdの標準像。 -/
@[simp] theorem perfectDeltaDivisionPrism_generator
    (D : DeltaStructure p R) (d : R) (hd : D.IsDistinguished d) (J : Ideal R) :
    letI := perfectDeltaDivisionPrismCommRing D d J
    (perfectDeltaDivisionPrism D d hd J).generator = perfectDeltaDivisionPrismMap D d J d := rfl

/-- 候補のδ構造は完全。 -/
theorem perfectDeltaDivisionPrism_isPerfect
    (D : DeltaStructure p R) (d : R) (hd : D.IsDistinguished d) (J : Ideal R) :
    letI := perfectDeltaDivisionPrismCommRing D d J
    (perfectDeltaDivisionPrism D d hd J).deltaStructure.IsPerfect := by
  let := perfectDeltaDivisionPrismCommRing D d J
  exact perfectDeltaPDPrism_isPerfect
    (pCompletedDeltaDivisionStructure D d (fun x : J ↦ (x : R)))
    (pCompletedDeltaDivision_isPerfect D d (fun x : J ↦ (x : R)))
    (pCompletedDeltaDivisionMap D d (fun x : J ↦ (x : R)) d)
    ((pCompletedDeltaDivisionMap_isDeltaHom D d (fun x : J ↦ (x : R))).map_isDistinguished hd)

/-- 元のδ環から候補への標準射はδ射。 -/
theorem perfectDeltaDivisionPrismMap_isDeltaHom
    (D : DeltaStructure p R) (d : R) (hd : D.IsDistinguished d) (J : Ideal R) :
    letI := perfectDeltaDivisionPrismCommRing D d J
    D.IsDeltaHom (perfectDeltaDivisionPrism D d hd J).deltaStructure
      (perfectDeltaDivisionPrismMap D d J) := by
  let := perfectDeltaDivisionPrismCommRing D d J
  exact (pdCompletionUnit_isDeltaHom
    (pCompletedDeltaDivisionStructure D d (fun x : J ↦ (x : R)))
    (pCompletedDeltaDivisionMap D d (fun x : J ↦ (x : R)) d)).comp
      (pCompletedDeltaDivisionMap_isDeltaHom D d (fun x : J ↦ (x : R)))

/-- 完全試験prismへdとJをそのイデアルに送る基底δ射は、唯一のprism射へ延長する。 -/
theorem existsUnique_perfectDeltaDivisionPrismHom {T : Type u} [CommRing T]
    (D : DeltaStructure p R) (d : R) (hd : D.IsDistinguished d) (J : Ideal R)
    (Q : OrientedPrism p T) (hQ : Q.deltaStructure.IsPerfect)
    (f : R →+* T) (hf : D.IsDeltaHom Q.deltaStructure f)
    (hdf : f d ∈ Q.ideal) (hJ : J ≤ Q.ideal.comap f) :
    letI := perfectDeltaDivisionPrismCommRing D d J
    ∃! g : OrientedPrism.Hom (perfectDeltaDivisionPrism D d hd J) Q,
      g.toRingHom.comp (perfectDeltaDivisionPrismMap D d J) = f := by
  let := perfectDeltaDivisionPrismCommRing D d J
  let a := fun x : J ↦ (x : R)
  let DC := pCompletedDeltaDivisionStructure D d a
  let j := pCompletedDeltaDivisionMap D d a
  let c := pdCompletionUnit (PCompletedDeltaDivision D d a) p (j d)
  have hC := pCompletedDeltaDivision_isPerfect D d a
  have hdist := (pCompletedDeltaDivisionMap_isDeltaHom D d a).map_isDistinguished hd
  obtain ⟨k, hk, hku⟩ := existsUnique_pCompletedDeltaDivisionHom_to_perfectPrism
    D d hd J Q hQ f hf hdf hJ
  have hkd : k (j d) ∈ Q.ideal := by
    have he : k (j d) = f d := RingHom.congr_fun hk.2 d
    rw [he]
    exact hdf
  obtain ⟨g, hg, hgu⟩ := existsUnique_perfectDeltaPDPrismHom DC hC (j d) hdist Q hQ k hk.1 hkd
  refine ⟨g, ?_, ?_⟩
  · change g.toRingHom.comp (c.comp j) = f
    rw [← RingHom.comp_assoc, hg, hk.2]
  · intro l hl
    apply hgu l
    apply hku (l.toRingHom.comp c)
    refine ⟨l.map_delta.comp (pdCompletionUnit_isDeltaHom DC (j d)), ?_⟩
    change (l.toRingHom.comp c).comp j = f
    rw [RingHom.comp_assoc]
    exact hl

end SerrePositivity.BhattScholze
