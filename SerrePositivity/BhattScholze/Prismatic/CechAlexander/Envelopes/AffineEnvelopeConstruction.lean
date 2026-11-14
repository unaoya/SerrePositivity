module

public import SerrePositivity.BhattScholze.Prismatic.CechAlexander.Envelopes.AffineEnvelopeMaps
public import SerrePositivity.BhattScholze.Prismatic.Envelopes.CompletedFreeDeltaResidue
public import SerrePositivity.BhattScholze.Prismatic.Envelopes.VariableEnvelope
import all SerrePositivity.BhattScholze.Prismatic.CechAlexander.Envelopes.AffineEnvelopeMaps

/-!
# affine envelope の差座標

## 概要
第 0 copy を固定して、他の copy を差座標に直す。

## 方針
自由 δ 環の完備化の普遍性で加減の逆写像を作り、指定変数の envelope を移す。

## 使われ方
affine Čech–Alexander 模型（BS 著者版 Remark 4.19）。
-/

public noncomputable section

universe u

open CategoryTheory SerrePositivity.DerivedCompletion

namespace SerrePositivity.BhattScholze.Prismatic

set_option backward.isDefEq.respectTransparency false

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] (P : OrientedPrism p A)
section AffineTerm

variable (r n : ℕ)

local notation "C" => completedFreeDelta P (AffineIndex r n)
local notation "D" => completedFreeDeltaStructure P (AffineIndex r n)
local notation "ι" => completedFreeDeltaBase P (AffineIndex r n)
local notation "X" => completedFreeDeltaVariable P (AffineIndex r n)

private def shiftValue (t : ℤ) (s : (AffineIndex.{u} r n)) : C :=
  if s.down.2 = 0 then X s else X s + t • X ⟨(s.down.1, 0)⟩

private theorem existsUnique_affineShift (t : ℤ) :
    ∃! g : C →+* C, (D).IsDeltaHom D g ∧ g.comp ι = ι ∧
      ∀ s, g (X s) = shiftValue P r n t s :=
  existsUnique_completedFreeDeltaHom P (AffineIndex.{u} r n) D ι (completedFreeDeltaBase_isDeltaHom P (AffineIndex.{u} r n))
    (completedFreeDelta_complete_p P (AffineIndex.{u} r n)) (completedFreeDelta_complete_generator P (AffineIndex.{u} r n))
    (shiftValue P r n t)

private def affineShift (t : ℤ) : C →+* C :=
  (existsUnique_affineShift P r n t).choose

private theorem affineShift_spec (t : ℤ) :
    (D).IsDeltaHom D (affineShift P r n t) ∧ (affineShift P r n t).comp ι = ι ∧
      ∀ s, affineShift P r n t (X s) = shiftValue P r n t s :=
  (existsUnique_affineShift P r n t).choose_spec.1

private theorem affineShift_inverse (t : ℤ) :
    (affineShift P r n (-t)).comp (affineShift P r n t) = RingHom.id C := by
  let f := affineShift P r n t
  let g := affineShift P r n (-t)
  obtain ⟨hfδ, hfB, hfX⟩ := affineShift_spec P r n t
  obtain ⟨hgδ, hgB, hgX⟩ := affineShift_spec P r n (-t)
  apply completedFreeDeltaHom_ext P (AffineIndex.{u} r n) D ι (completedFreeDeltaBase_isDeltaHom P (AffineIndex.{u} r n))
    (completedFreeDelta_complete_p P (AffineIndex.{u} r n)) (completedFreeDelta_complete_generator P (AffineIndex.{u} r n))
    (hgδ.comp hfδ)
  · exact fun _ => rfl
  · rw [RingHom.comp_assoc, hfB, hgB]
  · exact RingHom.id_comp _
  · intro s
    change g (f (X s)) = X s
    have hz : g (X ⟨(s.down.1, 0)⟩) = X ⟨(s.down.1, 0)⟩ := by
      rw [(affineShift_spec P r n (-t)).2.2]
      simp [shiftValue]
    rw [hfX]
    by_cases hs : s.down.2 = 0
    · simpa only [shiftValue, hs, ite_true] using hgX s
    · simp only [shiftValue, hs, ite_false, map_add, map_zsmul, hz]
      rw [hgX]
      simp only [shiftValue, hs, ite_false, neg_smul, neg_add_cancel_right]

private def differenceCoordinates : Set (AffineIndex.{u} r n) := {s | s.down.2 ≠ 0}

private theorem affineShift_difference (j : Fin r) (i : Fin (n + 1)) :
    affineShift P r n 1 (affineVariable P r n j i - affineVariable P r n j 0) =
      if i = 0 then 0 else X ⟨(j, i)⟩ := by
  change affineShift P r n 1 (X ⟨(j, i)⟩ - X ⟨(j, 0)⟩) = _
  rw [map_sub, (affineShift_spec P r n 1).2.2, (affineShift_spec P r n 1).2.2]
  by_cases hi : i = 0 <;> simp [shiftValue, hi]

private theorem affineShift_ideal :
    (affineDifferenceIdeal P r n).map (affineShift P r n 1) =
      variableIdeal P (AffineIndex.{u} r n) (differenceCoordinates r n) := by
  rw [affineDifferenceIdeal, Ideal.map_span, variableIdeal]
  let f := affineShift P r n 1
  have hf : f (ι P.generator) = ι P.generator :=
    RingHom.congr_fun (affineShift_spec P r n 1).2.1 P.generator
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨_, hx, rfl⟩
    rcases hx with hx | ⟨⟨j, i⟩, rfl⟩
    · obtain rfl := Set.mem_singleton_iff.mp hx
      rw [hf]
      exact Ideal.subset_span (Set.mem_insert _ _)
    · rw [affineShift_difference]
      by_cases hi : i = 0
      · rw [ite_eq_left hi]; exact Ideal.zero_mem _
      · rw [ite_eq_right hi]
        exact Ideal.subset_span (Set.mem_insert_of_mem _ ⟨⟨⟨(j, i)⟩, hi⟩, rfl⟩)
  · rw [Ideal.span_le]
    rintro x (hx | ⟨⟨⟨⟨j, i⟩⟩, hi⟩, rfl⟩)
    · obtain rfl := Set.mem_singleton_iff.mp hx
      exact Ideal.subset_span ⟨_, Set.mem_insert _ _, hf⟩
    · apply Ideal.subset_span
      refine ⟨_, Set.mem_insert_of_mem _ ⟨(j, i), rfl⟩, ?_⟩
      change f (affineVariable P r n j i - affineVariable P r n j 0) = X ⟨(j, i)⟩
      rw [affineShift_difference, ite_eq_right hi]

private def affineEnvelopeUnit : C →+* C :=
  (variableEnvelopeSubstitution P (AffineIndex.{u} r n) (differenceCoordinates r n)).comp (affineShift P r n 1)

private theorem affineEnvelopeUnit_base : (affineEnvelopeUnit P r n).comp ι = ι := by
  unfold affineEnvelopeUnit
  rw [RingHom.comp_assoc, (affineShift_spec P r n 1).2.1, variableEnvelopeSubstitution_base]

private theorem affineDifferenceIdeal_generator :
    ι P.generator ∈ affineDifferenceIdeal P r n := by
  unfold affineDifferenceIdeal
  exact Ideal.subset_span (Set.mem_insert _ _)

private theorem affineEnvelopeUnit_spec (hreg : Function.Injective (ι P.generator * ·)) :
    IsPrismaticEnvelope P D ι (completedFreeDeltaBase_isDeltaHom P (AffineIndex.{u} r n))
      (affineDifferenceIdeal P r n) (affineDifferenceIdeal_generator P r n)
      (completedFreeDeltaPrism P (AffineIndex.{u} r n) hreg) (affineEnvelopeUnit P r n) := by
  let α := affineShift P r n 1
  let β := affineShift P r n (-1)
  let η := variableEnvelopeSubstitution P (AffineIndex.{u} r n) (differenceCoordinates r n)
  have hβα : β.comp α = RingHom.id C := by simpa [α, β] using affineShift_inverse P r n 1
  have hαβ : α.comp β = RingHom.id C := by simpa [α, β] using affineShift_inverse P r n (-1)
  have hα := affineShift_spec P r n 1
  have hβ := affineShift_spec P r n (-1)
  have hη := isPrismaticEnvelope_variableSubstitution P (AffineIndex.{u} r n) (differenceCoordinates r n) hreg
  refine ⟨hη.isDeltaHom.comp hα.1, ?_, ?_, ?_, ?_⟩
  · simpa only [affineEnvelopeUnit_base, variableEnvelopeSubstitution_base] using hη.base_hom
  · rw [hη.ideal_eq]
    have h := RingHom.congr_fun (affineEnvelopeUnit_base P r n) P.generator
    have h' := RingHom.congr_fun
      (variableEnvelopeSubstitution_base P (AffineIndex.{u} r n) (differenceCoordinates r n)) P.generator
    change (affineEnvelopeUnit P r n) (ι P.generator) = ι P.generator at h
    change η (ι P.generator) = ι P.generator at h'
    rw [h, h']
  · unfold affineEnvelopeUnit
    rw [← Ideal.map_map, affineShift_ideal]
    exact hη.map_le
  · intro B _ Q g hg hb hI
    have hb' : P.ideal ≤ Q.ideal.comap ((g.comp β).comp ι) := by
      rwa [RingHom.comp_assoc, hβ.2.1]
    have hI' : (variableIdeal P (AffineIndex.{u} r n) (differenceCoordinates r n)).map (g.comp β) ≤ Q.ideal := by
      rw [← affineShift_ideal, Ideal.map_map]
      change (affineDifferenceIdeal P r n).map ((g.comp β).comp α) ≤ Q.ideal
      rwa [RingHom.comp_assoc, hβα, RingHom.comp_id]
    obtain ⟨k, hk, hu⟩ := hη.lift Q (g.comp β) (hg.comp hβ.1) hb' hI'
    refine ⟨k, ⟨hk.1, ?_⟩, ?_⟩
    · change k.comp (η.comp α) = g
      rw [← RingHom.comp_assoc, hk.2, RingHom.comp_assoc, hβα, RingHom.comp_id]
    · intro l hl
      apply hu
      refine ⟨hl.1, ?_⟩
      have h := congrArg (fun f : C →+* B => f.comp β) hl.2
      change (l.comp (η.comp α)).comp β = g.comp β at h
      rwa [← RingHom.comp_assoc α η l, RingHom.comp_assoc β α (l.comp η),
        hαβ, RingHom.comp_id] at h

private theorem exists_affineSection {B : Type u} [CommRing B] (Q : OrientedPrism p B)
    (f : OrientedPrism.Hom P Q) (x : Fin r → B ⧸ Q.ideal) :
    ∃ sec : prismPolynomialCompletion P (Fin r) →+* B ⧸ Q.ideal,
      sec.comp (algebraMap (A ⧸ P.ideal) _) = f.quotientMap ∧
      ∀ j, sec (prismPolynomialUnit P (Fin r) (MvPolynomial.X j)) = x j := by
  let R := MvPolynomial (Fin r) (A ⧸ P.ideal)
  let T := B ⧸ Q.ideal
  let e : R →+* T := MvPolynomial.eval₂Hom f.quotientMap x
  let := e.toAlgebra
  have hT : IsModuleComplete R (p : R) (ModuleCat.of R T) := by
    apply (isModuleComplete_algebraMap_iff R T (p : R) T).mp
    change IsModuleComplete T (e (p : R)) (ModuleCat.of T T)
    rw [map_natCast]
    exact isModuleComplete_principal_quotient_natCast B p Q.generator Q.complete_p
  obtain ⟨sec, hsec, _⟩ := principalCompletion_existsUnique_ringHom R (p : R) T e hT
  change sec.comp (prismPolynomialUnit P (Fin r)) = e at hsec
  refine ⟨sec, ?_, ?_⟩
  · change sec.comp ((prismPolynomialUnit P (Fin r)).comp MvPolynomial.C) = _
    rw [← RingHom.comp_assoc, hsec]
    exact RingHom.ext (fun x => MvPolynomial.eval₂Hom_C _ _ x)
  · intro j
    change (sec.comp (prismPolynomialUnit P (Fin r))) (MvPolynomial.X j) = _
    rw [hsec]
    exact MvPolynomial.eval₂Hom_X' _ _ _

private theorem affineEnvelope_small {κ : Cardinal.{u}}
    (hk : cutoff A (prismPolynomialCompletion P (Fin r)) ≤ κ) :
    Cardinal.mk C ≤ κ := by
  apply (cardinal_envelope_le P (AffineIndex.{u} r n)).trans
  apply le_trans _ hk
  unfold cutoff
  apply Cardinal.power_le_power_right
  have hS : Cardinal.mk (AffineIndex.{u} r n) ≤ Cardinal.aleph0 := Cardinal.mk_le_aleph0
  have he : Cardinal.mk (AffineIndex.{u} r n) + Cardinal.aleph0 = Cardinal.aleph0 := by
    rw [Cardinal.add_eq_max' le_rfl, max_eq_right hS]
  rw [add_assoc, he, add_assoc]
  gcongr
  exact self_le_add_left _ _

private def affineEnvelopeTermAux (hP : IsBoundedPrism P) (κ : Cardinal.{u})
    (hk : cutoff A (prismPolynomialCompletion P (Fin r)) ≤ κ) : AffineEnvelopeTerm P r n κ := by
  let hreg := completedFreeDelta_generator_regular P hP (AffineIndex.{u} r n)
  let Q := completedFreeDeltaPrism P (AffineIndex.{u} r n) hreg
  let η := affineEnvelopeUnit P r n
  have hη := affineEnvelopeUnit_spec P r n hreg
  have hB : IsBoundedPrism Q := by
    unfold IsBoundedPrism
    rw [completedFreeDeltaPrism_ideal]
    exact completedFreeDelta_residue_bounded P hP (AffineIndex.{u} r n)
  let f : OrientedPrism.Hom P Q := ⟨η.comp ι,
    hη.isDeltaHom.comp (completedFreeDeltaBase_isDeltaHom P (AffineIndex.{u} r n)), hη.base_hom⟩
  let E := exists_affineSection P r Q f
    (fun j => Ideal.Quotient.mk Q.ideal (η (affineVariable P r n j 0)))
  exact ⟨⟨C, Q, hB, f, E.choose, E.choose_spec.1, affineEnvelope_small P r n hk⟩,
    η, hη, rfl, E.choose_spec.2⟩

end AffineTerm

/-- 概要：affine Čech–Alexander 模型の次数 n の envelope（BS 著者版 Remark 4.19）。
方針：差座標で自由変数の envelope を作り、第 0 copy で剰余への構造射を指定する。
規約：基底は剰余環上の完備多項式環。
使われ方：`cechAlexanderAffine` の各項。 -/
def affineEnvelopeTerm (hP : IsBoundedPrism P) (r n : ℕ) (κ : Cardinal.{u})
    (hk : cutoff A (prismPolynomialCompletion P (Fin r)) ≤ κ) : AffineEnvelopeTerm P r n κ :=
  affineEnvelopeTermAux P r n hP κ hk

open scoped Simplicial in
/-- 完備多項式環の小さい affine Čech–Alexander 模型。 -/
def cechAlexanderAffine (hP : IsBoundedPrism P) (r : ℕ) (κ : Cardinal.{u})
    (hk : cutoff A (prismPolynomialCompletion P (Fin r)) ≤ κ) :
    CosimplicialObject (PrismOver P (prismPolynomialCompletion P (Fin r)) κ) :=
  cechAlexanderOfAffineTerms P (fun n => affineEnvelopeTerm P hP r n κ hk)

/-- affine Čech–Alexander 模型を基底上の余単体的可換代数として読む。 -/
def polyCosimplicialAlgebra (hP : IsBoundedPrism P) (r : ℕ) :
    SerrePositivity.Cosimplicial.CosimplicialAlgebra A :=
  polyCosimplicialAlgebraOfAffineTerms P (fun n =>
    affineEnvelopeTerm P hP r n (polyCutoff P r) le_rfl)

end SerrePositivity.BhattScholze.Prismatic
