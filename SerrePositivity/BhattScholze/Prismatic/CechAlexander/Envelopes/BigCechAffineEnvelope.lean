module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.BhattScholze.Prismatic.CechAlexander.Comparison.BigCechAlexander
import all SerrePositivity.BhattScholze.Prismatic.CechAlexander.Comparison.BigCechAlexander
public import SerrePositivity.BhattScholze.Prismatic.CechAlexander.Comparison.BigCechCompletionLift
public import SerrePositivity.BhattScholze.Prismatic.Envelopes.VariableEnvelope
public import SerrePositivity.BhattScholze.Prismatic.Envelopes.CompletedFreeDeltaBounds
public import SerrePositivity.BhattScholze.Prismatic.Envelopes.CompletedFreeDeltaResidue
import all SerrePositivity.BhattScholze.Prismatic.Envelopes.VariableEnvelope
import all SerrePositivity.HomologicalAlgebra.DerivedCompletion.Principal.CompletionFunctor

/-!
# 大きい affine Čech–Alexander 枠の包

## 概要
完備多項式環の全元を変数とする枠の各項で、prismatic envelope を構成する。

## 方針
第 0 頂点の多項式変数を固定する。他の変数から、その評価を持ち上げた
完備多項式を引く。座標変換後は、変数の部分集合に沿う包の普遍性を使う。

## 規約
持ち上げは各項の選択にのみ使う。関手の射は包の普遍性で決める。

## 使われ方
BS 著者版 Construction 4.18・Remark 4.19 と Theorem 6.4。
-/

public noncomputable section

open CategoryTheory SerrePositivity.DerivedCompletion

universe u

namespace SerrePositivity.BhattScholze.Prismatic

set_option backward.isDefEq.respectTransparency false

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] (P : OrientedPrism p A)
variable (Q : Poly (A ⧸ P.ideal)) (n : ℕ)

local notation "C" => (A ⧸ P.ideal)
local notation "S" => BigCechIndex P Q n
local notation "B" => completedFreeDelta P S
local notation "ΔB" => completedFreeDeltaStructure P S
local notation "ι" => completedFreeDeltaBase P S
local notation "X" => completedFreeDeltaVariable P S
local notation "U" => MvPolynomial (Fin Q.n) A

private def anchor (j : Fin Q.n) : S :=
  (prismPolynomialUnit P (Fin Q.n) (MvPolynomial.X j), 0)

private def otherCoordinates : Set S := (Set.range (anchor P Q n))ᶜ

private def liftCoefficient (q : polyCompletion P Q.n) : CompletedRing p U :=
  (polyCompletionCoefficientQuotient_surjective P Q.n q).choose

private theorem liftCoefficient_spec (q : polyCompletion P Q.n) :
    polyCompletionCoefficientQuotient P Q.n (liftCoefficient P Q q) = q :=
  (polyCompletionCoefficientQuotient_surjective P Q.n q).choose_spec

private def evalAnchorsRaw : U →+* B :=
  MvPolynomial.eval₂Hom ι (fun j => X (anchor P Q n j))

private def evalAnchors : CompletedRing p U →+* B :=
  liftFromPolyCompletion p (evalAnchorsRaw P Q n) (completedFreeDelta_complete_p P S)

private theorem evalAnchors_unit (x : U) :
    evalAnchors P Q n (principalCompletionRingCatUnit p (CommRingCat.of U) x) =
      evalAnchorsRaw P Q n x :=
  RingHom.congr_fun (liftFromPolyCompletion_comp p (evalAnchorsRaw P Q n)
    (completedFreeDelta_complete_p P S)) x

private theorem evalAnchors_ext (g h : B →+* B)
    (hb : g.comp ι = h.comp ι) (hX : ∀ j, g (X (anchor P Q n j)) = h (X (anchor P Q n j))) :
    g.comp (evalAnchors P Q n) = h.comp (evalAnchors P Q n) := by
  have he : g.comp (evalAnchorsRaw P Q n) = h.comp (evalAnchorsRaw P Q n) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      change g (evalAnchorsRaw P Q n (MvPolynomial.C a)) =
        h (evalAnchorsRaw P Q n (MvPolynomial.C a))
      rw [evalAnchorsRaw, MvPolynomial.eval₂Hom_C]
      exact RingHom.congr_fun hb a
    · intro j
      change g (evalAnchorsRaw P Q n (MvPolynomial.X j)) =
        h (evalAnchorsRaw P Q n (MvPolynomial.X j))
      rw [evalAnchorsRaw, MvPolynomial.eval₂Hom_X']
      exact hX j
  have hg := liftFromPolyCompletion_unique p (h.comp (evalAnchorsRaw P Q n))
    (completedFreeDelta_complete_p P S) (g.comp (evalAnchors P Q n)) (by
      rw [RingHom.comp_assoc, show (evalAnchors P Q n).comp
        (principalCompletionRingCatUnit p (CommRingCat.of U)).hom = evalAnchorsRaw P Q n
        from liftFromPolyCompletion_comp p _ _, he])
  have hh := liftFromPolyCompletion_unique p (h.comp (evalAnchorsRaw P Q n))
    (completedFreeDelta_complete_p P S) (h.comp (evalAnchors P Q n)) (by
      rw [RingHom.comp_assoc, show (evalAnchors P Q n).comp
        (principalCompletionRingCatUnit p (CommRingCat.of U)).hom = evalAnchorsRaw P Q n
        from liftFromPolyCompletion_comp p _ _])
  exact hg.trans hh.symm

private def anchorLift (q : polyCompletion P Q.n) : B :=
  evalAnchors P Q n (liftCoefficient P Q q)

private def shiftValue (t : ℤ) (s : S) : B := by
  classical
  exact if s ∈ otherCoordinates P Q n then X s + t • anchorLift P Q n s.1 else X s

private theorem existsUnique_shift (t : ℤ) :
    ∃! g : B →+* B, (ΔB).IsDeltaHom ΔB g ∧ g.comp ι = ι ∧
      ∀ s, g (X s) = shiftValue P Q n t s :=
  existsUnique_completedFreeDeltaHom P S ΔB ι (completedFreeDeltaBase_isDeltaHom P S)
    (completedFreeDelta_complete_p P S) (completedFreeDelta_complete_generator P S)
    (shiftValue P Q n t)

private def shift (t : ℤ) : B →+* B := (existsUnique_shift P Q n t).choose

private theorem shift_spec (t : ℤ) :
    (ΔB).IsDeltaHom ΔB (shift P Q n t) ∧ (shift P Q n t).comp ι = ι ∧
      ∀ s, shift P Q n t (X s) = shiftValue P Q n t s :=
  (existsUnique_shift P Q n t).choose_spec.1

private theorem shift_anchor (t : ℤ) (j : Fin Q.n) :
    shift P Q n t (X (anchor P Q n j)) = X (anchor P Q n j) := by
  classical
  rw [(shift_spec P Q n t).2.2]
  have h : anchor P Q n j ∉ otherCoordinates P Q n := fun h => h ⟨j, rfl⟩
  simp only [shiftValue, ite_eq_right h]

private theorem shift_anchorLift (t : ℤ) (q : polyCompletion P Q.n) :
    shift P Q n t (anchorLift P Q n q) = anchorLift P Q n q := by
  have h := evalAnchors_ext P Q n (shift P Q n t) (RingHom.id _)
    ((shift_spec P Q n t).2.1.trans (RingHom.id_comp _).symm)
    (shift_anchor P Q n t)
  exact RingHom.congr_fun h (liftCoefficient P Q q)

private theorem shift_inverse (t : ℤ) :
    (shift P Q n (-t)).comp (shift P Q n t) = RingHom.id _ := by
  classical
  have ht := shift_spec P Q n t
  have hu := shift_spec P Q n (-t)
  apply completedFreeDeltaHom_ext P S ΔB ι (completedFreeDeltaBase_isDeltaHom P S)
    (completedFreeDelta_complete_p P S) (completedFreeDelta_complete_generator P S)
    (hu.1.comp ht.1) (DeltaStructure.isDeltaHom_id _)
  · rw [RingHom.comp_assoc, ht.2.1, hu.2.1]
  · exact RingHom.id_comp _
  · intro s
    change shift P Q n (-t) (shift P Q n t (X s)) = X s
    rw [ht.2.2]
    by_cases h : s ∈ otherCoordinates P Q n
    · rw [shiftValue, ite_eq_left h, map_add, map_zsmul, shift_anchorLift, hu.2.2,
        shiftValue, ite_eq_left h, neg_smul, neg_add_cancel_right]
    · rw [shiftValue, ite_eq_right h, hu.2.2, shiftValue, ite_eq_right h]

section Target

variable {D : Type u} [CommRing D] (T : OrientedPrism p D) (f : OrientedPrism.Hom P T)
variable (g : completedFreeDelta P (BigCechIndex P Q n) →+* D)
variable (hb : g.comp (completedFreeDeltaBase P (BigCechIndex P Q n)) = f.toRingHom)


private def sectionRaw : MvPolynomial (Fin Q.n) C →+* D ⧸ T.ideal :=
  MvPolynomial.eval₂Hom f.quotientMap fun j =>
    Ideal.Quotient.mk T.ideal (g (X (anchor P Q n j)))

private def anchorSection : polyCompletion P Q.n →+* D ⧸ T.ideal :=
  liftFromPolyCompletion p (sectionRaw P Q n T f g)
    (isModuleComplete_principal_quotient_natCast D p T.generator T.complete_p)

private theorem anchorSection_comp :
    (anchorSection P Q n T f g).comp (prismPolynomialUnit P (Fin Q.n)) =
      sectionRaw P Q n T f g :=
  liftFromPolyCompletion_comp p _ _

private theorem anchorSection_variable (j : Fin Q.n) :
    anchorSection P Q n T f g (anchor P Q n j).1 =
      Ideal.Quotient.mk T.ideal (g (X (anchor P Q n j))) := by
  have h := RingHom.congr_fun (anchorSection_comp P Q n T f g) (MvPolynomial.X j)
  exact h.trans (MvPolynomial.eval₂Hom_X' _ _ _)

include hb in
private theorem anchorLift_mod (q : polyCompletion P Q.n) :
    (Ideal.Quotient.mk T.ideal) (g (anchorLift P Q n q)) = anchorSection P Q n T f g q := by
  let qA := Ideal.Quotient.mk P.ideal
  let w := MvPolynomial.map (σ := Fin Q.n) qA
  let eval := sectionRaw P Q n T f g
  let e := principalCompletionRingCatUnit p (CommRingCat.of U)
  let g₀ := (Ideal.Quotient.mk T.ideal).comp g
  have he : g₀.comp (evalAnchorsRaw P Q n) = eval.comp w := by
    apply MvPolynomial.ringHom_ext
    · intro a
      change (Ideal.Quotient.mk T.ideal) (g (evalAnchorsRaw P Q n (MvPolynomial.C a))) =
        eval (MvPolynomial.map qA (MvPolynomial.C a))
      rw [evalAnchorsRaw, MvPolynomial.eval₂Hom_C, MvPolynomial.map_C]
      simp only [eval, sectionRaw, MvPolynomial.eval₂Hom_C]
      change (Ideal.Quotient.mk T.ideal) ((g.comp ι) a) = f.quotientMap (qA a)
      rw [hb, OrientedPrism.Hom.quotientMap_mk]
    · intro j
      change (Ideal.Quotient.mk T.ideal) (g (evalAnchorsRaw P Q n (MvPolynomial.X j))) =
        eval (MvPolynomial.map qA (MvPolynomial.X j))
      rw [evalAnchorsRaw, MvPolynomial.eval₂Hom_X', MvPolynomial.map_X]
      simp only [eval, sectionRaw, MvPolynomial.eval₂Hom_X']
  have hL : (g₀.comp (evalAnchors P Q n)).comp e.hom = eval.comp w := by
    rw [RingHom.comp_assoc]
    have h : (evalAnchors P Q n).comp e.hom = evalAnchorsRaw P Q n :=
      liftFromPolyCompletion_comp p _ _
    rw [h, he]
  have hR : (anchorSection P Q n T f g).comp
        ((polyCompletionCoefficientQuotient P Q.n).comp e.hom) = eval.comp w := by
    apply RingHom.ext
    intro x
    change anchorSection P Q n T f g (polyCompletionCoefficientQuotient P Q.n (e x)) =
      eval (w x)
    rw [polyCompletionCoefficientQuotient_unit]
    exact RingHom.congr_fun (anchorSection_comp P Q n T f g) _
  let hc := isModuleComplete_principal_quotient_natCast D p T.generator T.complete_p
  have H := (liftFromPolyCompletion_unique p (eval.comp w) hc _ hL).trans
    (liftFromPolyCompletion_unique p (eval.comp w) hc _
      ((RingHom.comp_assoc _ _ _).trans hR)).symm
  have h := RingHom.congr_fun H (liftCoefficient P Q q)
  change (Ideal.Quotient.mk T.ideal) (g (anchorLift P Q n q)) =
    anchorSection P Q n T f g (polyCompletionCoefficientQuotient P Q.n (liftCoefficient P Q q)) at h
  rwa [liftCoefficient_spec] at h

private theorem bigCechEval_surjective : Function.Surjective (bigCechEval Q n) := by
  intro x
  refine ⟨MvPolynomial.X (x, (0 : Fin (n + 1))), ?_⟩
  rw [bigCechEval, MvPolynomial.eval₂Hom_X']

set_option maxHeartbeats 500000 in
-- 核の二つの因子化を完備多項式の単位に沿って照合する。
include hb in
private theorem map_ideal_iff_section :
    (bigCechIdeal P Q n).map g ≤ T.ideal ↔
      ∀ s : S, (Ideal.Quotient.mk T.ideal) (g (X s)) = anchorSection P Q n T f g s.1 := by
  let a := bigCechEval Q n
  let z := (Ideal.Quotient.mk T.ideal).comp (g.comp (bigCechInitial P Q n))
  have hker : (bigCechIdeal P Q n).map g ≤ T.ideal ↔ RingHom.ker a ≤ RingHom.ker z := by
    rw [bigCechIdeal, Ideal.map_map, Ideal.map_le_iff_le_comap]
    constructor <;> intro h x hx
    · exact Ideal.Quotient.eq_zero_iff_mem.mpr (h hx)
    · change (g.comp (bigCechInitial P Q n)) x ∈ T.ideal
      exact Ideal.Quotient.eq_zero_iff_mem.mp (RingHom.mem_ker.mp (h hx))
  rw [hker]
  constructor
  · intro h
    let e := a.liftOfSurjective (bigCechEval_surjective P Q n) ⟨z, h⟩
    have he : e.comp a = z := RingHom.liftOfSurjective_comp _ _ _
    have hX (s : S) : e s.1 = (Ideal.Quotient.mk T.ideal) (g (X s)) := by
      have hs := RingHom.congr_fun he (MvPolynomial.X s)
      change e (bigCechEval Q n (MvPolynomial.X s)) =
        (Ideal.Quotient.mk T.ideal) (g (bigCechInitial P Q n (MvPolynomial.X s))) at hs
      simpa only [bigCechEval, MvPolynomial.eval₂Hom_X', bigCechInitial_X] using hs
    have e_comp : e.comp (prismPolynomialUnit P (Fin Q.n)) = sectionRaw P Q n T f g := by
      apply MvPolynomial.ringHom_ext
      · intro c
        obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective c
        have hh := RingHom.congr_fun he (MvPolynomial.C b)
        change e (bigCechEval Q n (MvPolynomial.C b)) =
          (Ideal.Quotient.mk T.ideal) (g (bigCechInitial P Q n (MvPolynomial.C b))) at hh
        rw [bigCechEval, MvPolynomial.eval₂Hom_C, bigCechInitial_C] at hh
        simp only [RingHom.comp_apply, sectionRaw, MvPolynomial.eval₂Hom_C]
        change e (prismPolynomialUnit P (Fin Q.n) (MvPolynomial.C (Ideal.Quotient.mk P.ideal b))) =
          (Ideal.Quotient.mk T.ideal) ((g.comp ι) b) at hh
        rw [hb, ← OrientedPrism.Hom.quotientMap_mk] at hh
        exact hh
      · intro j
        change e (prismPolynomialUnit P (Fin Q.n) (MvPolynomial.X j)) =
          sectionRaw P Q n T f g (MvPolynomial.X j)
        rw [sectionRaw, MvPolynomial.eval₂Hom_X']
        exact hX (anchor P Q n j)
    have hE : e = anchorSection P Q n T f g :=
      liftFromPolyCompletion_unique p (sectionRaw P Q n T f g)
        (isModuleComplete_principal_quotient_natCast D p T.generator T.complete_p) e e_comp
    intro s
    exact (hX s).symm.trans (RingHom.congr_fun hE s.1)
  · intro h
    have he : (anchorSection P Q n T f g).comp a = z := by
      apply MvPolynomial.ringHom_ext
      · intro b
        change anchorSection P Q n T f g (bigCechEval Q n (MvPolynomial.C b)) =
          (Ideal.Quotient.mk T.ideal) (g (bigCechInitial P Q n (MvPolynomial.C b)))
        rw [bigCechEval, MvPolynomial.eval₂Hom_C, bigCechInitial_C]
        have he := RingHom.congr_fun (anchorSection_comp P Q n T f g)
          (MvPolynomial.C (Ideal.Quotient.mk P.ideal b))
        change anchorSection P Q n T f g (prismPolynomialUnit P (Fin Q.n)
          (MvPolynomial.C (Ideal.Quotient.mk P.ideal b))) = _ at he
        change _ = (Ideal.Quotient.mk T.ideal) ((g.comp ι) b)
        rw [hb, ← OrientedPrism.Hom.quotientMap_mk]
        change anchorSection P Q n T f g (prismPolynomialUnit P (Fin Q.n)
          (MvPolynomial.C (Ideal.Quotient.mk P.ideal b))) = _
        simpa only [sectionRaw, MvPolynomial.eval₂Hom_C] using he
      · intro s
        change anchorSection P Q n T f g (bigCechEval Q n (MvPolynomial.X s)) =
          (Ideal.Quotient.mk T.ideal) (g (bigCechInitial P Q n (MvPolynomial.X s)))
        rw [bigCechEval, MvPolynomial.eval₂Hom_X', bigCechInitial_X, h]
    rw [← he]
    intro a ha
    change anchorSection P Q n T f g (bigCechEval Q n a) = 0
    rw [RingHom.mem_ker.mp ha, map_zero]

end Target

section Envelope

variable (hP : IsBoundedPrism P)

local notation "Z" => otherCoordinates P Q n
local notation "c" => ι P.generator
local notation "hreg" => completedFreeDelta_generator_regular P hP S
local notation "T" => completedFreeDeltaPrism P S hreg
local notation "α" => shift P Q n 1
local notation "β" => shift P Q n (-1)
local notation "v" => variableEnvelopeSubstitution P S Z

private def affineBigUnit : B →+* B := (v).comp α

private theorem affineBigUnit_base : (affineBigUnit P Q n).comp ι = ι := by
  unfold affineBigUnit
  rw [RingHom.comp_assoc, (shift_spec P Q n 1).2.1, variableEnvelopeSubstitution_base]

private theorem affineBigUnit_isDeltaHom : (ΔB).IsDeltaHom ΔB (affineBigUnit P Q n) :=
  (variableEnvelopeSubstitution_spec P S Z).1.comp (shift_spec P Q n 1).1

private def affineBigBase : OrientedPrism.Hom P T :=
  ⟨ι, completedFreeDeltaBase_isDeltaHom P S, by
    change Ideal.span {P.generator} ≤ (T).ideal.comap ι
    rw [Ideal.span_singleton_le_iff_mem]
    change c ∈ (T).ideal
    rw [completedFreeDeltaPrism_ideal]
    exact Ideal.subset_span (Set.mem_singleton _)⟩

private theorem affineBigUnit_ideal :
    (bigCechIdeal P Q n).map (affineBigUnit P Q n) ≤ (T).ideal := by
  classical
  let η := affineBigUnit P Q n
  let f := affineBigBase P Q n hP
  apply (map_ideal_iff_section P Q n T f η (affineBigUnit_base P Q n)).mpr
  intro s
  by_cases hs : s ∈ Z
  · have hX : v (X s) ∈ (T).ideal :=
      (isPrismaticEnvelope_variableSubstitution P S Z hreg).map_le
        (Ideal.mem_map_of_mem v (Ideal.subset_span
          (Set.mem_insert_of_mem _ ⟨⟨s, hs⟩, rfl⟩)))
    have h := anchorLift_mod P Q n T f η (affineBigUnit_base P Q n) s.1
    change Ideal.Quotient.mk (T).ideal (v (α (anchorLift P Q n s.1))) =
      anchorSection P Q n T f η s.1 at h
    rw [shift_anchorLift] at h
    change Ideal.Quotient.mk (T).ideal (v (α (X s))) = anchorSection P Q n T f η s.1
    rw [(shift_spec P Q n 1).2.2, shiftValue, ite_eq_left hs, one_zsmul, map_add, map_add,
      Ideal.Quotient.eq_zero_iff_mem.mpr hX, zero_add]
    exact h
  · have hm : s ∈ Set.range (anchor P Q n) := by
      by_contra h
      exact hs h
    obtain ⟨j, rfl⟩ := hm
    exact (anchorSection_variable P Q n T f η j).symm

private theorem affineBigUnit_spec :
    IsPrismaticEnvelope P ΔB ι (completedFreeDeltaBase_isDeltaHom P S)
      (bigCechIdeal P Q n) (generator_mem_bigCechIdeal P Q n) T (affineBigUnit P Q n) := by
  classical
  let η := affineBigUnit P Q n
  let hV := isPrismaticEnvelope_variableSubstitution P S Z hreg
  have hβα : (β).comp α = RingHom.id _ := by
    exact shift_inverse P Q n 1
  have hαβ : (α).comp β = RingHom.id _ := by
    simpa only [neg_neg] using shift_inverse P Q n (-1)
  refine ⟨affineBigUnit_isDeltaHom P Q n, ?_, ?_, affineBigUnit_ideal P Q n hP, ?_⟩
  · rw [affineBigUnit_base]
    exact (affineBigBase P Q n hP).ideal_le
  · rw [completedFreeDeltaPrism_ideal]
    exact congrArg (fun x : B => Ideal.span {x}) (RingHom.congr_fun (affineBigUnit_base P Q n)
      P.generator).symm
  · intro D _ TD g hg hb hI
    let f : OrientedPrism.Hom P TD :=
      ⟨g.comp ι, hg.comp (completedFreeDeltaBase_isDeltaHom P S), hb⟩
    have hb' : P.ideal ≤ TD.ideal.comap ((g.comp β).comp ι) := by
      rwa [RingHom.comp_assoc, (shift_spec P Q n (-1)).2.1]
    have hI' : (variableIdeal P S Z).map (g.comp β) ≤ TD.ideal := by
      have hs := (map_ideal_iff_section P Q n TD f g rfl).mp hI
      rw [Ideal.map_le_iff_le_comap, variableIdeal, Ideal.span_le]
      rintro x (hx | ⟨s, rfl⟩)
      · obtain rfl := hx
        change ((g.comp β).comp ι) P.generator ∈ TD.ideal
        exact hb' (Ideal.subset_span (Set.mem_singleton _))
      · change g (β (X s.val)) ∈ TD.ideal
        apply Ideal.Quotient.eq_zero_iff_mem.mp
        rw [(shift_spec P Q n (-1)).2.2, shiftValue, ite_eq_left s.property,
          neg_smul, one_zsmul, ← sub_eq_add_neg, map_sub, map_sub,
          hs s.val, anchorLift_mod P Q n TD f g rfl, sub_self]
    obtain ⟨k, hk, hu⟩ := hV.lift TD (g.comp β) (hg.comp (shift_spec P Q n (-1)).1) hb' hI'
    refine ⟨k, ⟨hk.1, ?_⟩, ?_⟩
    · change k.comp ((v).comp α) = g
      rw [← RingHom.comp_assoc, hk.2, RingHom.comp_assoc, hβα, RingHom.comp_id]
    · intro l hl
      apply hu
      refine ⟨hl.1, ?_⟩
      have h := congrArg (fun m : B →+* D => m.comp β) hl.2
      change (l.comp ((v).comp α)).comp β = g.comp β at h
      rwa [← RingHom.comp_assoc α v l, RingHom.comp_assoc β α (l.comp v),
        hαβ, RingHom.comp_id] at h

/-- 有界 prism 上の大きい affine 枠の各項に対する包。 -/
def affineBigCechTerm : BigCechTerm P Q n where
  carrier := B
  prism := T
  unit := affineBigUnit P Q n
  isEnvelope := affineBigUnit_spec P Q n hP

/-- 大きい枠の包は有界 prism。 -/
theorem affineBigCechTerm_bounded : IsBoundedPrism (affineBigCechTerm P Q n hP).prism := by
  change IsBoundedPrism T
  unfold IsBoundedPrism
  rw [completedFreeDeltaPrism_ideal]
  exact completedFreeDelta_residue_bounded P hP S

end Envelope

/-- 有界 prism 上の大きい affine Čech–Alexander 模型。 -/
def bigCechAlexander (hP : IsBoundedPrism P) :
    Poly C ⥤ SerrePositivity.Cosimplicial.CosimplicialAlgebra A :=
  bigCechAlexanderOfTerms P (fun Q n => affineBigCechTerm P Q n hP)

end SerrePositivity.BhattScholze.Prismatic

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite BS19 "Construction 4.18" (partial := component) "大きい枠の Čech–Alexander 模型の項と座標変換（BS-D69 P2）。Δ を計算することは G9・G10 待ち ／ 11-11 更新 ／ 11-12 夜更新（§4 の見直し）"] _root_.SerrePositivity.BhattScholze.Prismatic.affineBigCechTerm
