module
public import SerrePositivity.DifferentialGraded.Complexes.ConeHom
public import SerrePositivity.DifferentialGraded.Complexes.Cells

/-! # 合成が零となる射のconeからの延長 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Limits HomologicalComplex CochainComplex HomComplex
variable {A : Type u} [CommRing A]

def complexConeDesc {P Q T : Complex A} (f : P ⟶ Q) (q : Q ⟶ T) (h : f ≫ q = 0) :
    mappingCone f ⟶ T := mappingCone.desc f 0 q (by simp [h])

lemma complexConeDesc_f {P Q T : Complex A} (f : P ⟶ Q) (q : Q ⟶ T) (h : f ≫ q = 0)
    (i : ℤ) : (complexConeDesc f q h).f i =
      (mappingCone.snd f).v i i (add_zero i) ≫ q.f i := by
  rw [complexConeDesc, mappingCone.desc_f _ _ _ _ i (i + 1) rfl,
    Cochain.zero_v, comp_zero, zero_add]

lemma complexConeDesc_ofHom {P Q T : Complex A} (f : P ⟶ Q) (q : Q ⟶ T) (h : f ≫ q = 0) :
    Cochain.ofHom (complexConeDesc f q h) =
      (mappingCone.snd f).comp (Cochain.ofHom q) (zero_add 0) := by
  apply Cochain.ext₀
  intro i
  rw [Cochain.ofHom_v, complexConeDesc_f, Cochain.comp_zero_cochain_v, Cochain.ofHom_v]

lemma complexConeDesc_inr {P Q T : Complex A} (f : P ⟶ Q) (q : Q ⟶ T) (h : f ≫ q = 0) :
    mappingCone.inr f ≫ complexConeDesc f q h = q := mappingCone.inr_desc _ _ _ _

/-- coneの全次数対角作用と零cochain延長の整合性。 -/
lemma coneMapCochain_desc {P Q T P' Q' T' : Complex A}
    (f : P ⟶ Q) (g : P' ⟶ Q') (q : Q ⟶ T) (q' : Q' ⟶ T')
    (hq : f ≫ q = 0) (hq' : g ≫ q' = 0) {p : ℤ}
    (a : Cochain P P' p) (b : Cochain Q Q' p) (c : Cochain T T' p)
    (hb : b.comp (Cochain.ofHom q') (add_zero p) =
      (Cochain.ofHom q).comp c (zero_add p)) :
    (coneMapCochain f g a b).comp (Cochain.ofHom (complexConeDesc g q' hq')) (add_zero p) =
      (Cochain.ofHom (complexConeDesc f q hq)).comp c (zero_add p) := by
  rw [complexConeDesc_ofHom, complexConeDesc_ofHom,
    ← Cochain.comp_assoc_of_second_is_zero_cochain, coneMapCochain_snd,
    Cochain.comp_assoc_of_first_is_zero_cochain, hb,
    ← Cochain.comp_assoc_of_second_is_zero_cochain]

/-- source cycleの像を消す具体的な境界の証人。 -/
def complexConeBoundaryWitness {P Q : Complex A} (f : P ⟶ Q) (n : ℤ)
    (z : complexCycles A P (n + 1)) : (mappingCone f).X n :=
  homotopyCofiber.inlX f (n + 1) n rfl z.val

lemma complexConeBoundaryWitness_d {P Q : Complex A} (f : P ⟶ Q) (n : ℤ)
    (z : complexCycles A P (n + 1)) :
    (mappingCone f).d n (n + 1) (complexConeBoundaryWitness f n z) =
      (mappingCone.inr f).f (n + 1) (f.f (n + 1) z.val) := by
  let t := homotopyCofiber.inlX f (n + 1) n rfl z.val
  have h := congrArg (fun k => k z.val)
    (homotopyCofiber.inlX_d f n (n + 1) (n + 1 + 1) rfl rfl)
  change homotopyCofiber.d f n (n + 1) t =
    -homotopyCofiber.inlX f (n + 1 + 1) (n + 1) rfl (P.d (n + 1) (n + 1 + 1) z.val) +
      homotopyCofiber.inrX f (n + 1) (f.f (n + 1) z.val) at h
  rw [z.property, map_zero, neg_zero, zero_add] at h
  exact h

/-- 零cochainによるcone延長は、この境界の証人を零に送る。 -/
lemma complexConeBoundaryWitness_desc {P Q T : Complex A} (f : P ⟶ Q) (q : Q ⟶ T)
    (h : f ≫ q = 0) (n : ℤ) (z : complexCycles A P (n + 1)) :
    (complexConeDesc f q h).f n (complexConeBoundaryWitness f n z) = 0 := by
  have hv := congrArg (fun k => k z.val)
    (mappingCone.inl_v_desc_f f 0 q (by simp [h]) (n + 1) n (by omega))
  exact hv

/-- sourceのcycleの像は標準coneで境界となる。 -/
lemma complexCone_inl_boundary {P Q : Complex A} (f : P ⟶ Q) (n : ℤ)
    (z : complexCycles A P (n + 1)) :
    ∃ t : (mappingCone f).X n, (mappingCone f).d n (n + 1) t =
      (mappingCone.inr f).f (n + 1) (f.f (n + 1) z.val) :=
  ⟨complexConeBoundaryWitness f n z, complexConeBoundaryWitness_d f n z⟩

end SerrePositivity.DifferentialGraded
