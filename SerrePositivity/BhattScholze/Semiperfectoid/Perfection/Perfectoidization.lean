module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.BhattScholze.Prism.Perfection.PrismPerfection
public import SerrePositivity.BhattScholze.Semiperfectoid.Perfection.PerfectPrismDivision
public import SerrePositivity.BhattScholze.Prism.Perfectoid.PerfectPrismPerfectoid
public import SerrePositivity.BhattScholze.Prism.Perfectoid.PerfectPrismHomLift
public import SerrePositivity.CommutativeAlgebra.Perfectoid.Defs

/-!
# semiperfectoid 環の perfectoid 化（BS 著者版 Corollary 7.3）

## 概要
完全 prism の商の任意の商の普遍 perfectoid 化、perfectoid 環の任意の商（semiperfectoid 環）の perfectoid 化の存在と普遍性。

## 方針
J/d を割る完全 prism を導来 (p,d) 完備化し、商の普遍性を IsPerfectoidization へ移す。

## 規約
全射性は BS 著者版 Theorem 7.4（Semiperfectoid/Surjectivity/Surjectivity）。

## 使われ方
CLMST の perfectoid イデアル、BS 著者版 Theorem 7.4、§8 の環の結果。
-/

universe u

/-! ## 任意のイデアルの除算からの具体的な完全prism候補

δ除算・p進完備δ完全化・実PD完備化を合成し、完全試験prismへの一意延長を得る。
一般prismの始対象やIsPerfectoidizationはまだ結論しない。
-/

@[expose] public noncomputable section PerfectDeltaDivisionPrism

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open _root_.SerrePositivity.DerivedCompletion
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R]

/-- Jの全元の除算候補を実PD完備化した具体的な環の台。 -/
abbrev Semiperfectoid.PerfectDeltaDivisionPrismCarrier (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p R) (d : R) (J : Ideal R) :=
  PDCompletionH0 (_root_.SerrePositivity.BhattScholze.Semiperfectoid.PCompletedDeltaDivision D d (fun x : J ↦ (x : R))) p
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap D d (fun x : J ↦ (x : R)) d)

/-- 候補の可換環構造は実PD完備化の環構造。 -/
@[instance_reducible] def Semiperfectoid.perfectDeltaDivisionPrismCommRing
    (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p R) (d : R) (J : Ideal R) :
    CommRing (_root_.SerrePositivity.BhattScholze.Semiperfectoid.PerfectDeltaDivisionPrismCarrier D d J) :=
  pdCompletionCommRing (_root_.SerrePositivity.BhattScholze.Semiperfectoid.PCompletedDeltaDivision D d (fun x : J ↦ (x : R))) p
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap D d (fun x : J ↦ (x : R)) d)

/-- distinguished dの任意イデアル除算から、実完備化上の完全prismを構成する。 -/
def Semiperfectoid.perfectDeltaDivisionPrism (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p R) (d : R) (hd : D.IsDistinguished d)
    (J : Ideal R) :
    letI := _root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectDeltaDivisionPrismCommRing D d J
    _root_.SerrePositivity.BhattScholze.OrientedPrism p (_root_.SerrePositivity.BhattScholze.Semiperfectoid.PerfectDeltaDivisionPrismCarrier D d J) := by
  letI := _root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectDeltaDivisionPrismCommRing D d J
  exact _root_.SerrePositivity.BhattScholze.perfectDeltaPDPrism (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionStructure D d (fun x : J ↦ (x : R)))
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivision_isPerfect D d (fun x : J ↦ (x : R)))
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap D d (fun x : J ↦ (x : R)) d)
    ((_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap_isDeltaHom D d (fun x : J ↦ (x : R))).map_isDistinguished hd)

/-- 元の環から具体的な完全prism候補への標準射。 -/
def Semiperfectoid.perfectDeltaDivisionPrismMap (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p R) (d : R) (J : Ideal R) :
    letI := _root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectDeltaDivisionPrismCommRing D d J
    R →+* _root_.SerrePositivity.BhattScholze.Semiperfectoid.PerfectDeltaDivisionPrismCarrier D d J :=
  (pdCompletionUnit (_root_.SerrePositivity.BhattScholze.Semiperfectoid.PCompletedDeltaDivision D d (fun x : J ↦ (x : R))) p
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap D d (fun x : J ↦ (x : R)) d)).comp
      (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap D d (fun x : J ↦ (x : R)))

/-- 選択生成元はdの標準像。 -/
@[simp] theorem Semiperfectoid.perfectDeltaDivisionPrism_generator
    (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p R) (d : R) (hd : D.IsDistinguished d) (J : Ideal R) :
    letI := _root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectDeltaDivisionPrismCommRing D d J
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectDeltaDivisionPrism D d hd J).generator = _root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectDeltaDivisionPrismMap D d J d := rfl

/-- 候補のδ構造は完全。 -/
theorem Semiperfectoid.perfectDeltaDivisionPrism_isPerfect
    (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p R) (d : R) (hd : D.IsDistinguished d) (J : Ideal R) :
    letI := _root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectDeltaDivisionPrismCommRing D d J
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectDeltaDivisionPrism D d hd J).deltaStructure.IsPerfect := by
  let := _root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectDeltaDivisionPrismCommRing D d J
  exact _root_.SerrePositivity.BhattScholze.perfectDeltaPDPrism_isPerfect
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionStructure D d (fun x : J ↦ (x : R)))
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivision_isPerfect D d (fun x : J ↦ (x : R)))
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap D d (fun x : J ↦ (x : R)) d)
    ((_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap_isDeltaHom D d (fun x : J ↦ (x : R))).map_isDistinguished hd)

/-- 元のδ環から候補への標準射はδ射。 -/
theorem Semiperfectoid.perfectDeltaDivisionPrismMap_isDeltaHom
    (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p R) (d : R) (hd : D.IsDistinguished d) (J : Ideal R) :
    letI := _root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectDeltaDivisionPrismCommRing D d J
    D.IsDeltaHom (_root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectDeltaDivisionPrism D d hd J).deltaStructure
      (_root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectDeltaDivisionPrismMap D d J) := by
  let := _root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectDeltaDivisionPrismCommRing D d J
  exact (_root_.SerrePositivity.BhattScholze.pdCompletionUnit_isDeltaHom
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionStructure D d (fun x : J ↦ (x : R)))
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap D d (fun x : J ↦ (x : R)) d)).comp
      (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap_isDeltaHom D d (fun x : J ↦ (x : R)))

/-- 完全試験prismへdとJをそのイデアルに送る基底δ射は、唯一のprism射へ延長する。 -/
theorem Semiperfectoid.existsUnique_perfectDeltaDivisionPrismHom {T : Type u} [CommRing T]
    (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p R) (d : R) (hd : D.IsDistinguished d) (J : Ideal R)
    (Q : _root_.SerrePositivity.BhattScholze.OrientedPrism p T) (hQ : Q.deltaStructure.IsPerfect)
    (f : R →+* T) (hf : D.IsDeltaHom Q.deltaStructure f)
    (hdf : f d ∈ Q.ideal) (hJ : J ≤ Q.ideal.comap f) :
    letI := _root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectDeltaDivisionPrismCommRing D d J
    ∃! g : _root_.SerrePositivity.BhattScholze.OrientedPrism.Hom (_root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectDeltaDivisionPrism D d hd J) Q,
      g.toRingHom.comp (_root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectDeltaDivisionPrismMap D d J) = f := by
  let := _root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectDeltaDivisionPrismCommRing D d J
  let a := fun x : J ↦ (x : R)
  let DC := _root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionStructure D d a
  let j := _root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap D d a
  let c := pdCompletionUnit (_root_.SerrePositivity.BhattScholze.Semiperfectoid.PCompletedDeltaDivision D d a) p (j d)
  have hC := _root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivision_isPerfect D d a
  have hdist := (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap_isDeltaHom D d a).map_isDistinguished hd
  obtain ⟨k, hk, hku⟩ := _root_.SerrePositivity.BhattScholze.Semiperfectoid.existsUnique_pCompletedDeltaDivisionHom_to_perfectPrism
    D d hd J Q hQ f hf hdf hJ
  have hkd : k (j d) ∈ Q.ideal := by
    have he : k (j d) = f d := RingHom.congr_fun hk.2 d
    rw [he]
    exact hdf
  obtain ⟨g, hg, hgu⟩ := _root_.SerrePositivity.BhattScholze.existsUnique_perfectDeltaPDPrismHom DC hC (j d) hdist Q hQ k hk.1 hkd
  refine ⟨g, ?_, ?_⟩
  · change g.toRingHom.comp (c.comp j) = f
    rw [← RingHom.comp_assoc, hg, hk.2]
  · intro l hl
    apply hgu l
    apply hku (l.toRingHom.comp c)
    refine ⟨l.map_delta.comp (_root_.SerrePositivity.BhattScholze.pdCompletionUnit_isDeltaHom DC (j d)), ?_⟩
    change (l.toRingHom.comp c).comp j = f
    rw [RingHom.comp_assoc]
    exact hl

end SerrePositivity.BhattScholze

end PerfectDeltaDivisionPrism

/-! ## 任意の基底商から完全prism候補の標準商への射

具体的なR/Jの射と標準商の古典的p完備性を公開する。
候補商のperfectoid性・IsPerfectoidizationは別工程。
-/

@[expose] public noncomputable section PerfectDeltaDivisionQuotient

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
open _root_.SerrePositivity.DerivedCompletion
variable {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R]

/-- Jの全元の像は、候補prismのイデアルへ入る。 -/
theorem Semiperfectoid.perfectDeltaDivisionPrismMap_ideal_le
    (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p R) (d : R) (hd : D.IsDistinguished d) (J : Ideal R) :
    letI := _root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectDeltaDivisionPrismCommRing D d J
    J ≤ (_root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectDeltaDivisionPrism D d hd J).ideal.comap (_root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectDeltaDivisionPrismMap D d J) := by
  let := _root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectDeltaDivisionPrismCommRing D d J
  intro x hx
  apply Ideal.mem_span_singleton.mpr
  change pdCompletionUnit _ p _ (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap D d (fun y : J ↦ (y : R)) d) ∣
    pdCompletionUnit _ p _ (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap D d (fun y : J ↦ (y : R)) x)
  exact map_dvd (pdCompletionUnit _ p _)
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap_dvd D d (fun y : J ↦ (y : R)) ⟨x, hx⟩)

/-- 任意の基底商R/Jから候補prismの標準商への具体的な射。 -/
def Semiperfectoid.perfectDeltaDivisionQuotientMap
    (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p R) (d : R) (hd : D.IsDistinguished d) (J : Ideal R) :
    letI := _root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectDeltaDivisionPrismCommRing D d J
    R ⧸ J →+* _root_.SerrePositivity.BhattScholze.Semiperfectoid.PerfectDeltaDivisionPrismCarrier D d J ⧸
      (_root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectDeltaDivisionPrism D d hd J).ideal := by
  letI := _root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectDeltaDivisionPrismCommRing D d J
  exact Ideal.quotientMap _ (_root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectDeltaDivisionPrismMap D d J)
    (_root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectDeltaDivisionPrismMap_ideal_le D d hd J)

/-- 標準商射の代表元公式。 -/
@[simp] theorem Semiperfectoid.perfectDeltaDivisionQuotientMap_mk
    (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p R) (d : R) (hd : D.IsDistinguished d) (J : Ideal R) (x : R) :
    letI := _root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectDeltaDivisionPrismCommRing D d J
    _root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectDeltaDivisionQuotientMap D d hd J (Ideal.Quotient.mk J x) =
      Ideal.Quotient.mk _ (_root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectDeltaDivisionPrismMap D d J x) := rfl

/-- 候補prismの標準商は、pねじれを許して古典的p進完備。 -/
theorem Semiperfectoid.perfectDeltaDivisionQuotient_isAdicComplete
    (D : _root_.SerrePositivity.BhattScholze.DeltaStructure p R) (d : R) (hd : D.IsDistinguished d) (J : Ideal R) :
    letI := _root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectDeltaDivisionPrismCommRing D d J
    IsAdicComplete (Ideal.span {(p : _root_.SerrePositivity.BhattScholze.Semiperfectoid.PerfectDeltaDivisionPrismCarrier D d J ⧸
      (_root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectDeltaDivisionPrism D d hd J).ideal)})
      (_root_.SerrePositivity.BhattScholze.Semiperfectoid.PerfectDeltaDivisionPrismCarrier D d J ⧸ (_root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectDeltaDivisionPrism D d hd J).ideal) := by
  let := _root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectDeltaDivisionPrismCommRing D d J
  let P := _root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectDeltaDivisionPrism D d hd J
  have hP := _root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectDeltaDivisionPrism_isPerfect D d hd J
  let := P.isAdicComplete_p_of_perfect hP
  exact hP.distinguished_quotient_isAdicComplete (P.isDistinguished_generator)

end SerrePositivity.BhattScholze

end PerfectDeltaDivisionQuotient

/-! ## 完全prism商の任意の商の普遍perfectoid化

完全試験prismの普遍性を既存IsPerfectoidizationへ移す。
全射性は結論に含めない。実PD完備化を使い、古典的完備化への置換をしない。
-/

@[expose] public noncomputable section PerfectPrismQuotientPerfectoidization

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {A S : Type u} [CommRing A] [CommRing S]

/-- 完全prism基底からの全射商の、具体的な除算prism商への標準射。 -/
def Semiperfectoid.perfectPrismQuotientPerfectoidizationMap
    (P : _root_.SerrePositivity.BhattScholze.OrientedPrism p A) (hP : P.deltaStructure.IsPerfect)
    (r : A →+* S) (hr : Function.Surjective r) :
    letI := _root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectDeltaDivisionPrismCommRing P.deltaStructure P.generator (RingHom.ker r)
    S →+* _root_.SerrePositivity.BhattScholze.Semiperfectoid.PerfectDeltaDivisionPrismCarrier P.deltaStructure P.generator (RingHom.ker r) ⧸
      (_root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectDeltaDivisionPrism P.deltaStructure P.generator
        (P.isDistinguished_generator) (RingHom.ker r)).ideal := by
  let := _root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectDeltaDivisionPrismCommRing P.deltaStructure P.generator (RingHom.ker r)
  let j := _root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectDeltaDivisionPrismMap P.deltaStructure P.generator (RingHom.ker r)
  let Q := _root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectDeltaDivisionPrism P.deltaStructure P.generator
    (P.isDistinguished_generator) (RingHom.ker r)
  exact r.liftOfSurjective hr ⟨(Ideal.Quotient.mk Q.ideal).comp j, by
    intro x hx
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    exact _root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectDeltaDivisionPrismMap_ideal_le P.deltaStructure P.generator
      (P.isDistinguished_generator) (RingHom.ker r) hx⟩

set_option maxHeartbeats 2000000 in
-- 除算 prism の担体（PD 完備化の H⁰）上の単一化は、反復した完備化の環構造（反映から
-- 選択で定まる積）に何度も当たって探索をやり直すので、この証明に限って上限を増やす（B4、11-04）。
/-- 非零完全 prism の商から来る全射に対して、標準射は perfectoid 化を与える
（BS 著者版 Corollary 7.3 第一文の完全 prism の商の場合、序論の Theorem 1.12 (2)）。 -/
theorem Semiperfectoid.perfectPrismQuotientPerfectoidizationMap_isPerfectoidization
    (P : _root_.SerrePositivity.BhattScholze.OrientedPrism p A) (hP : P.deltaStructure.IsPerfect)
    [Fact (¬ IsUnit (p : A ⧸ P.ideal))]
    (r : A →+* S) (hr : Function.Surjective r) (hrd : r P.generator = 0) :
    letI := _root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectDeltaDivisionPrismCommRing P.deltaStructure P.generator (RingHom.ker r)
    _root_.SerrePositivity.IsPerfectoidization p (_root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectPrismQuotientPerfectoidizationMap P hP r hr) := by
  let D := P.deltaStructure
  let d := P.generator
  have hd := P.isDistinguished_generator
  let J := RingHom.ker r
  let H := _root_.SerrePositivity.BhattScholze.Semiperfectoid.PerfectDeltaDivisionPrismCarrier D d J
  let := _root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectDeltaDivisionPrismCommRing D d J
  let Q := _root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectDeltaDivisionPrism D d hd J
  have hQ := _root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectDeltaDivisionPrism_isPerfect D d hd J
  let j := _root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectDeltaDivisionPrismMap D d J
  let C := H ⧸ Q.ideal
  let qC := Ideal.Quotient.mk Q.ideal
  have hjδ := _root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectDeltaDivisionPrismMap_isDeltaHom D d hd J
  have hjI : P.ideal ≤ Q.ideal.comap j := by
    rw [_root_.SerrePositivity.BhattScholze.OrientedPrism.ideal, Ideal.span_singleton_le_iff_mem]
    exact Ideal.mem_span_singleton_self _
  let base : _root_.SerrePositivity.BhattScholze.OrientedPrism.Hom P Q := { j with map_delta := hjδ, ideal_le := hjI }
  let f : S →+* C := _root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectPrismQuotientPerfectoidizationMap P hP r hr
  have hfr : f.comp r = qC.comp j := r.liftOfSurjective_comp hr _
  let s : A ⧸ P.ideal →+* S := Ideal.Quotient.lift _ r (by
    change P.ideal ≤ RingHom.ker r
    rw [_root_.SerrePositivity.BhattScholze.OrientedPrism.ideal, Ideal.span_singleton_le_iff_mem]
    exact hrd)
  have hsr : s.comp (Ideal.Quotient.mk P.ideal) = r := rfl
  refine ⟨Q.quotient_isIntegralPerfectoid hQ, ?_⟩
  intro T _ hT g
  rcases hT with hs | ⟨hpT, hcT, ⟨π, u, hu⟩, hFT, hkerT⟩
  · let := hs
    let l : C →+* T :=
      { toFun := fun _ ↦ 0
        map_one' := Subsingleton.elim _ _
        map_mul' := fun _ _ ↦ Subsingleton.elim _ _
        map_zero' := rfl
        map_add' := fun _ _ ↦ Subsingleton.elim _ _ }
    refine ⟨l, ?_, ?_⟩
    · apply RingHom.ext
      intro x
      exact Subsingleton.elim _ _
    · intro k hk
      apply RingHom.ext
      intro x
      exact Subsingleton.elim _ _
  · let := hcT
    let : Fact (¬ IsUnit (p : T)) := ⟨hpT⟩
    obtain ⟨t, ht, et, het⟩ := _root_.SerrePositivity.BhattScholze.exists_perfectoidTrialPrism T p hFT hkerT π u hu
    let := _root_.SerrePositivity.DerivedCompletion.pdCompletionCommRing (WittVector p (PreTilt T p)) p t
    let QT := _root_.SerrePositivity.BhattScholze.perfectDeltaPDPrism (_root_.SerrePositivity.BhattScholze.wittDeltaStructure p (PreTilt T p))
      (_root_.SerrePositivity.BhattScholze.wittDeltaStructure_isPerfect p (PreTilt T p)) t ht
    have hQT := _root_.SerrePositivity.BhattScholze.perfectDeltaPDPrism_isPerfect (_root_.SerrePositivity.BhattScholze.wittDeltaStructure p (PreTilt T p))
      (_root_.SerrePositivity.BhattScholze.wittDeltaStructure_isPerfect p (PreTilt T p)) t ht
    let : Fact (¬ IsUnit (p : _ ⧸ QT.ideal)) := ⟨fun h ↦ hpT
      (by simpa only [map_natCast] using h.map et.toRingHom)⟩
    let gP := et.symm.toRingHom.comp (g.comp s)
    obtain ⟨F, hF, hFu⟩ := _root_.SerrePositivity.BhattScholze.existsUnique_perfectPrismHomLift P QT hP hQT gP
    have hFJ : J ≤ QT.ideal.comap F.toRingHom := by
      intro x hx
      change F.toRingHom x ∈ QT.ideal
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      have hh := RingHom.congr_fun hF (Ideal.Quotient.mk P.ideal x)
      change Ideal.Quotient.mk QT.ideal (F.toRingHom x) = et.symm (g (r x)) at hh
      rw [show r x = 0 from hx, map_zero, map_zero] at hh
      exact hh
    obtain ⟨K, hK, hKu⟩ := _root_.SerrePositivity.BhattScholze.Semiperfectoid.existsUnique_perfectDeltaDivisionPrismHom D d hd J QT hQT
      F.toRingHom F.map_delta F.map_generator_mem hFJ
    let l := et.toRingHom.comp K.quotientMap
    have hlg : l.comp f = g := by
      apply RingHom.ext
      intro x
      obtain ⟨a, rfl⟩ := hr x
      have hh : f (r a) = qC (j a) := RingHom.congr_fun hfr a
      change et (K.quotientMap (f (r a))) = g (r a)
      rw [hh, _root_.SerrePositivity.BhattScholze.OrientedPrism.Hom.quotientMap_mk]
      have hk : K.toRingHom (j a) = F.toRingHom a := RingHom.congr_fun hK a
      rw [hk]
      have hff := RingHom.congr_fun hF (Ideal.Quotient.mk P.ideal a)
      change Ideal.Quotient.mk QT.ideal (F.toRingHom a) = et.symm (g (r a)) at hff
      rw [hff, et.apply_symm_apply]
    refine ⟨l, hlg, ?_⟩
    intro k hk
    rcases subsingleton_or_nontrivial C with hsub | hn
    · let := hsub
      apply RingHom.ext
      intro x
      rw [Subsingleton.elim x 0, map_zero, map_zero]
    · let := hn
      let : IsAdicComplete (Ideal.span {(p : C)}) C :=
        _root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectDeltaDivisionQuotient_isAdicComplete D d hd J
      have hpC : ¬ IsUnit (p : C) := by
        intro h
        let : Subsingleton C := _root_.SerrePositivity.subsingleton_of_isUnit_natCast_of_isHausdorff p C h
        exact zero_ne_one (Subsingleton.elim (0 : C) 1)
      let : Fact (¬ IsUnit (p : C)) := ⟨hpC⟩
      obtain ⟨L, hL, _⟩ := _root_.SerrePositivity.BhattScholze.existsUnique_perfectPrismHomLift Q QT hQ hQT
        (et.symm.toRingHom.comp k)
      have hLF : L.comp base = F := by
        apply hFu
        apply Ideal.Quotient.ringHom_ext
        apply RingHom.ext
        intro a
        change Ideal.Quotient.mk QT.ideal (L.toRingHom (j a)) = et.symm (g (r a))
        have hll := RingHom.congr_fun hL (qC (j a))
        change Ideal.Quotient.mk QT.ideal (L.toRingHom (j a)) = et.symm (k (qC (j a))) at hll
        rw [hll]
        have hh : f (r a) = qC (j a) := RingHom.congr_fun hfr a
        rw [← hh]
        have hkg : k (f (r a)) = g (r a) := RingHom.congr_fun hk (r a)
        rw [hkg]
      have hLK : L = K := hKu L (congrArg _root_.SerrePositivity.BhattScholze.OrientedPrism.Hom.toRingHom hLF)
      apply RingHom.ext
      intro x
      have hh := RingHom.congr_fun hL x
      change L.quotientMap x = et.symm (k x) at hh
      rw [hLK] at hh
      change k x = et (K.quotientMap x)
      rw [hh, et.apply_symm_apply]

/-- 完全prismの商の任意の全射商には、環として普遍なperfectoid化が存在する（BS 著者版 Corollary 7.3 の第一文の完全 prism の剰余環からの全射商の場合）。 -/
theorem Semiperfectoid.exists_perfectoidization_of_perfectPrism_quotient
    (P : _root_.SerrePositivity.BhattScholze.OrientedPrism p A) (hP : P.deltaStructure.IsPerfect)
    [Fact (¬ IsUnit (p : A ⧸ P.ideal))]
    (r : A →+* S) (hr : Function.Surjective r) (hrd : r P.generator = 0) :
    ∃ (C : Type u) (_ : CommRing C) (f : S →+* C), _root_.SerrePositivity.IsPerfectoidization p f := by
  let := _root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectDeltaDivisionPrismCommRing P.deltaStructure P.generator (RingHom.ker r)
  exact ⟨_, inferInstance, _root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectPrismQuotientPerfectoidizationMap P hP r hr,
    _root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectPrismQuotientPerfectoidizationMap_isPerfectoidization P hP r hr hrd⟩

end SerrePositivity.BhattScholze

end PerfectPrismQuotientPerfectoidization

/-! ## perfectoid環の商の普遍perfectoid化

BS 著者版 Corollary 7.3の存在・普遍性。
δ除算→完全化→実PD完備化の完全試験prismへの普遍性とBS 著者版 Theorem 3.10の対応を合成する。
商の導来p完備性を課した原典入力を公開し、より一般の全射商の入口も分ける。
全射性・B-I・Andréの引用を使わない。
-/

@[expose] public noncomputable section SemiperfectoidPerfectoidization

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime] {R S : Type u} [CommRing R] [CommRing S]

/-- 任意のperfectoid環の全射商には、環として普遍なperfectoid化が存在する（BS 著者版 Corollary 7.3 の第一文の perfectoid 環の全射商の場合）。
導来完備化を構成に組み込むため、源の商の完備性はこの強い入口には不要。 -/
theorem Semiperfectoid.exists_perfectoidization_of_perfectoid_surjective_quotient
    (hR : _root_.SerrePositivity.IsIntegralPerfectoid R p) (q : R →+* S) (hq : Function.Surjective q) :
    ∃ (C : Type u) (_ : CommRing C) (f : S →+* C), _root_.SerrePositivity.IsPerfectoidization p f := by
  rcases hR with hs | ⟨hp, hc, ⟨π, u, hu⟩, hF, hker⟩
  · let := hs
    let : Subsingleton S := q.codomain_trivial
    refine ⟨S, inferInstance, RingHom.id S, Or.inl inferInstance, ?_⟩
    intro T _ hT g
    refine ⟨g, RingHom.comp_id _, ?_⟩
    intro l hl
    simpa only [RingHom.comp_id] using hl
  · let := hc
    let : Fact (¬ IsUnit (p : R)) := ⟨hp⟩
    obtain ⟨d, hd, e, he⟩ := _root_.SerrePositivity.BhattScholze.exists_perfectoidTrialPrism R p hF hker π u hu
    let := _root_.SerrePositivity.DerivedCompletion.pdCompletionCommRing (WittVector p (PreTilt R p)) p d
    let P := _root_.SerrePositivity.BhattScholze.perfectDeltaPDPrism (_root_.SerrePositivity.BhattScholze.wittDeltaStructure p (PreTilt R p))
      (_root_.SerrePositivity.BhattScholze.wittDeltaStructure_isPerfect p (PreTilt R p)) d hd
    have hP := _root_.SerrePositivity.BhattScholze.perfectDeltaPDPrism_isPerfect (_root_.SerrePositivity.BhattScholze.wittDeltaStructure p (PreTilt R p))
      (_root_.SerrePositivity.BhattScholze.wittDeltaStructure_isPerfect p (PreTilt R p)) d hd
    let : Fact (¬ IsUnit (p : _ ⧸ P.ideal)) := ⟨fun h ↦ hp
      (by simpa only [map_natCast] using h.map e.toRingHom)⟩
    let r := q.comp (e.toRingHom.comp (Ideal.Quotient.mk P.ideal))
    have hr : Function.Surjective r := hq.comp (e.surjective.comp Ideal.Quotient.mk_surjective)
    have hrd : r P.generator = 0 := by
      change q (e (Ideal.Quotient.mk P.ideal P.generator)) = 0
      have hz : Ideal.Quotient.mk P.ideal P.generator = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
      rw [hz, map_zero, map_zero]
    exact _root_.SerrePositivity.BhattScholze.Semiperfectoid.exists_perfectoidization_of_perfectPrism_quotient P hP r hr hrd

/-- B3の原典入力：任意perfectoid環の導来p完備な全射商の存在と普遍性（BS 著者版 Corollary 7.3 の第一文、序論の Theorem 1.12 (2)）。
一般のpねじれ商を含む。全射性は別のB4工程。 -/
theorem Semiperfectoid.exists_perfectoidization_of_semiperfectoid_quotient
    (hR : _root_.SerrePositivity.IsIntegralPerfectoid R p) (q : R →+* S) (hq : Function.Surjective q)
    (_hS : _root_.SerrePositivity.DerivedCompletion.IsModuleComplete S (p : S) (ModuleCat.of S S)) :
    ∃ (C : Type u) (_ : CommRing C) (f : S →+* C), _root_.SerrePositivity.IsPerfectoidization p f :=
  _root_.SerrePositivity.BhattScholze.Semiperfectoid.exists_perfectoidization_of_perfectoid_surjective_quotient hR q hq

end SerrePositivity.BhattScholze

end SemiperfectoidPerfectoidization

/-! ## B3で選ぶ任意イデアル商の普遍perfectoid化

一般有限代数の存在入力から独立に対象を選ぶBS接続層。
全射性・冪等性・長さの条件は構成に含めない。
-/

@[expose] public noncomputable section QuotientPerfectoidization

namespace SerrePositivity

variable (R : Type u) [CommRing R] (I : Ideal R) (p : ℕ) [Fact p.Prime]
    (hR : IsIntegralPerfectoid R p)

/-- B3の一般全射商の存在で選ぶperfectoid化。 -/
def BhattScholze.Semiperfectoid.QuotientPerfectoidization : Type u :=
  (_root_.SerrePositivity.BhattScholze.Semiperfectoid.exists_perfectoidization_of_perfectoid_surjective_quotient hR
    (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective).choose

instance : CommRing (_root_.SerrePositivity.BhattScholze.Semiperfectoid.QuotientPerfectoidization R I p hR) :=
  (_root_.SerrePositivity.BhattScholze.Semiperfectoid.exists_perfectoidization_of_perfectoid_surjective_quotient hR
    (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective).choose_spec.choose

/-- 商環からB3の選択対象への標準写像。 -/
def BhattScholze.Semiperfectoid.toQuotientPerfectoidization : R ⧸ I →+* _root_.SerrePositivity.BhattScholze.Semiperfectoid.QuotientPerfectoidization R I p hR :=
  (_root_.SerrePositivity.BhattScholze.Semiperfectoid.exists_perfectoidization_of_perfectoid_surjective_quotient hR
    (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective).choose_spec.choose_spec.choose

/-- B3で選んだ標準写像の存在・普遍性。 -/
theorem BhattScholze.Semiperfectoid.isPerfectoidization_toQuotientPerfectoidization :
    _root_.SerrePositivity.IsPerfectoidization p (_root_.SerrePositivity.BhattScholze.Semiperfectoid.toQuotientPerfectoidization R I p hR) :=
  (_root_.SerrePositivity.BhattScholze.Semiperfectoid.exists_perfectoidization_of_perfectoid_surjective_quotient hR
    (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective).choose_spec.choose_spec.choose_spec

instance : Algebra (R ⧸ I) (_root_.SerrePositivity.BhattScholze.Semiperfectoid.QuotientPerfectoidization R I p hR) :=
  (_root_.SerrePositivity.BhattScholze.Semiperfectoid.toQuotientPerfectoidization R I p hR).toAlgebra

instance : Algebra R (_root_.SerrePositivity.BhattScholze.Semiperfectoid.QuotientPerfectoidization R I p hR) :=
  ((_root_.SerrePositivity.BhattScholze.Semiperfectoid.toQuotientPerfectoidization R I p hR).comp (Ideal.Quotient.mk I)).toAlgebra

instance : IsScalarTower R (R ⧸ I) (_root_.SerrePositivity.BhattScholze.Semiperfectoid.QuotientPerfectoidization R I p hR) :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

/-- 商環の作用は選んだ標準写像による。 -/
theorem BhattScholze.Semiperfectoid.algebraMap_quotientPerfectoidization :
    algebraMap (R ⧸ I) (_root_.SerrePositivity.BhattScholze.Semiperfectoid.QuotientPerfectoidization R I p hR) =
      _root_.SerrePositivity.BhattScholze.Semiperfectoid.toQuotientPerfectoidization R I p hR := rfl

/-- 元環の作用は商写像と標準写像の合成による。 -/
theorem BhattScholze.Semiperfectoid.algebraMap_base_quotientPerfectoidization :
    algebraMap R (_root_.SerrePositivity.BhattScholze.Semiperfectoid.QuotientPerfectoidization R I p hR) =
      (_root_.SerrePositivity.BhattScholze.Semiperfectoid.toQuotientPerfectoidization R I p hR).comp (Ideal.Quotient.mk I) := rfl

/-- 零商の選択対象も零環となる。 -/
theorem BhattScholze.Semiperfectoid.quotientPerfectoidization_subsingleton [Subsingleton (R ⧸ I)] :
    Subsingleton (_root_.SerrePositivity.BhattScholze.Semiperfectoid.QuotientPerfectoidization R I p hR) :=
  (_root_.SerrePositivity.BhattScholze.Semiperfectoid.toQuotientPerfectoidization R I p hR).codomain_trivial

/-- pを含む商では、選択したperfectoid化でもpが零になる。 -/
theorem BhattScholze.Semiperfectoid.quotientPerfectoidization_natCast_eq_zero (hp : (p : R) ∈ I) :
    (p : _root_.SerrePositivity.BhattScholze.Semiperfectoid.QuotientPerfectoidization R I p hR) = 0 := by
  have hq : (p : R ⧸ I) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk I)]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hp
  rw [← map_natCast (_root_.SerrePositivity.BhattScholze.Semiperfectoid.toQuotientPerfectoidization R I p hR), hq, map_zero]

end SerrePositivity

end QuotientPerfectoidization

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Cor 7.3" (partial := special) "Cor 7.3 の S′（根の商）の場合：S′ の prismatic 完全化と perfectoidization の単位を保つ唯一の δ-prism 同型（BS-W17 停止点 5、11-12）。一般の semiperfectoid の場合の存在は本体の Perfectoidization"] _root_.SerrePositivity.BhattScholze.Semiperfectoid.exists_perfectoidization_of_perfectoid_surjective_quotient
attribute [cite BS19 "Cor 7.3" (partial := special) "Cor 7.3 の S′（根の商）の場合：S′ の prismatic 完全化と perfectoidization の単位を保つ唯一の δ-prism 同型（BS-W17 停止点 5、11-12）。一般の semiperfectoid の場合の存在は本体の Perfectoidization"] _root_.SerrePositivity.BhattScholze.Semiperfectoid.exists_perfectoidization_of_semiperfectoid_quotient
attribute [cite BS19 "Thm 1.12" (partial := special) "(1) Prop 7.2（全 prism の中の始対象）は本体になく不要（D37、代数的部分だけ Delta/Division）。(2) Cor 7.3・Thm 7.4 は本体で sorry なし（完全試験 prism への始性で構成、超限構成は経由しない） ／ DOC1 照合：ok 3 件"] _root_.SerrePositivity.BhattScholze.Semiperfectoid.exists_perfectoidization_of_semiperfectoid_quotient
attribute [cite BS19 "Thm 1.12" (partial := special) "(1) Prop 7.2（全 prism の中の始対象）は本体になく不要（D37、代数的部分だけ Delta/Division）。(2) Cor 7.3・Thm 7.4 は本体で sorry なし（完全試験 prism への始性で構成、超限構成は経由しない） ／ DOC1 照合：ok 3 件"] _root_.SerrePositivity.BhattScholze.Semiperfectoid.perfectPrismQuotientPerfectoidizationMap_isPerfectoidization
