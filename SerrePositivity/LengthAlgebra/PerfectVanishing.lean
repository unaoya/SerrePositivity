module

public import SerrePositivity.LengthAlgebra.PerfectHomology
public import SerrePositivity.PerfectComplex.KoszulTower
public import SerrePositivity.PerfectComplex.KoszulAmplitude

/-! # 支持つき有限射影複体の消滅

消滅には有限長さの商でなく大きな商を用い、長さの有限性を要求しない。
(Supp) はスカラーの零ホモトピー、(Kosₘ) は環自身の Koszul 消滅と項の振幅から
確認し、結論を共通の反復錐定理から得る。
-/

@[expose] public section

universe u

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.LengthAlgebra

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

variable {R : Type u} [CommRing R] {J : Ideal R} (lam : NormalizedLength R J)
  (hfg : J.FG) {e : ℕ} (z : Fin e → R)
  (hJ : J ≤ (Ideal.span (Set.range z)).radical)

include hfg hJ in
lemma perfectModuleHomology_powTorsion (X : SupportedPerfectHomotopy z) (q : ℤ) :
    powTorsionModule J ((perfectModuleHomology z q).obj X) := by
  obtain ⟨⟨X, hX⟩, hz⟩ := X
  obtain ⟨P : CochainComplex _ _, rfl⟩ := X.quotient_obj_surjective
  have hP := (perfectHomotopyProperty_quotient R P).mp hX
  have hs := (perfectHomotopyObj_supported_iff z P hP).mp hz
  apply (powTorsionModule J).prop_of_iso
    ((HomotopyCategory.homologyFunctorFactors _ _ q).app P).symm
  exact supported_homology_isPowTorsion hfg hJ hs q

/-- 有限性を仮定せず、ホモロジーを冪ねじれ加群の圏へ送る。 -/
noncomputable def perfectTorsionHomology (q : ℤ) :
    SupportedPerfectHomotopy z ⥤ PowTorsionModule J :=
  (powTorsionModule J).lift (perfectModuleHomology z q)
    (fun X ↦ perfectModuleHomology_powTorsion hfg z hJ X q)

instance perfectTorsionHomology_additive (q : ℤ) :
    (perfectTorsionHomology hfg z hJ q).Additive := by
  dsimp only [perfectTorsionHomology]
  infer_instance

instance perfectTorsionHomology_isHomological (q : ℤ) :
    (perfectTorsionHomology hfg z hJ q).IsHomological where
  exact T hT := by
    apply (ShortComplex.exact_map_iff_of_faithful _ (powTorsionModule J).ι).mp
    exact (perfectModuleHomology z q).map_distinguished_exact T hT

/-- 大きな長さの商に値をもつ実際のホモロジー関手。 -/
noncomputable def perfectLengthHomology (q : ℤ) :
    SupportedPerfectHomotopy z ⥤ LengthQuotient lam :=
  perfectTorsionHomology hfg z hJ q ⋙ lengthQuotientFunctor lam

instance perfectLengthHomology_additive (q : ℤ) :
    (perfectLengthHomology lam hfg z hJ q).Additive := by
  dsimp only [perfectLengthHomology]
  infer_instance

instance perfectLengthHomology_isHomological (q : ℤ) :
    (perfectLengthHomology lam hfg z hJ q).IsHomological where
  exact T hT := ((perfectTorsionHomology hfg z hJ q).map_distinguished_exact T hT).map
    (lengthQuotientFunctor lam)

noncomputable def perfectLengthHomologyShiftIso (q : ℤ) :
    shiftFunctor _ q ⋙ perfectLengthHomology lam hfg z hJ 0 ≅
      perfectLengthHomology lam hfg z hJ q := by
  let G := supportedPerfectInclusion z ⋙ perfectHomotopyInclusion R
  let H := HomotopyCategory.homologyFunctor (ModuleCat.{u} R) (.up ℤ) 0
  let i : shiftFunctor _ q ⋙ perfectModuleHomology z 0 ≅ perfectModuleHomology z q :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (G.commShiftIso q) H ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft G (H.isoShift q)
  let j : shiftFunctor _ q ⋙ perfectTorsionHomology hfg z hJ 0 ≅
      perfectTorsionHomology hfg z hJ q :=
    NatIso.ofComponents (fun X ↦ ObjectProperty.isoMk _ (i.app X)) (fun f ↦ by
      apply ObjectProperty.hom_ext
      exact i.hom.naturality f)
  exact Functor.isoWhiskerRight j (lengthQuotientFunctor lam)

noncomputable instance perfectLengthHomology_shiftSequence :
    (perfectLengthHomology lam hfg z hJ 0).ShiftSequence ℤ :=
  Functor.ShiftSequence.tautological _ ℤ

/-- 商で零であることと、元のホモロジーの長さが零であることの一致。 -/
lemma perfectLengthHomology_isZero_iff
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (hP : strictlyPerfectComplex R P)
    (hs : IsSupported z P) (q : ℤ) :
    IsZero ((perfectLengthHomology lam hfg z hJ q).obj
      ⟨perfectHomotopyObj R P hP, (perfectHomotopyObj_supported_iff z P hP).mpr hs⟩) ↔
      lam.len (P.homology q) = 0 := by
  rw [← extendedQuotientLength_eq_zero_iff]
  change lam.len ((HomotopyCategory.homologyFunctor (ModuleCat.{u} R) (.up ℤ) q).obj
    ((HomotopyCategory.quotient (ModuleCat.{u} R) (.up ℤ)).obj P)) = 0 ↔ _
  have h := lam.len_congr _ _
    (((HomotopyCategory.homologyFunctorFactors _ _ q).app P).toLinearEquiv)
  exact ⟨fun hz ↦ h.symm.trans hz, fun hz ↦ h.trans hz⟩

/-- 有限個のスカラーを自然数添字に延長する。指定された範囲の外は使わない。 -/
def koszulScalars (k : ℕ) : R := if hk : k < e then z ⟨k, hk⟩ else 0

@[simp] lemma koszulScalars_fin (j : Fin e) : koszulScalars z j = z j := by
  simp [koszulScalars, j.isLt]

include hfg hJ in
/-- 有限射影複体の新交叉型消滅。(Supp) と (Kosₘ) を確認した後は共通定理を使う。
長さの有限性、局所性、ネーター性、平坦性はいずれも仮定しない。 -/
theorem lambdaHomology_projective_vanishing
    (hzero : ∀ i : ℕ, 0 < i → lam.len (koszulHomologySelf z i) = 0)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (hP : strictlyPerfectComplex R P)
    (hx : ∀ j, Nonempty (Homotopy (smulId (z j) P) 0))
    (a b : ℤ) (hbound : ∀ q, q < a ∨ b < q → IsZero (P.X q))
    (q : ℤ) (hq : q < a + e ∨ b < q) : lam.len (P.homology q) = 0 := by
  have hs : IsSupported z P := ⟨1, fun j ↦ by simpa only [pow_one, smulId] using hx j⟩
  let x := koszulScalars z
  let X := perfectKoszulObj z x P hP hs
  let T := perfectKoszulTriangle z x P hP hs
  let F := perfectLengthHomology lam hfg z hJ 0
  have hS : ∀ k < e, Triangle.mk (x k • 𝟙 (X k)) (T k).mor₂ (T k).mor₃ ∈ distTriang _ :=
    fun k _ ↦ perfectKoszulTriangle_mk_distinguished z x P hP hs k
  have hnull : ∀ j < e, x j • 𝟙 (X 0) = 0 := by
    intro j hj
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    exact (nonempty_homotopy_smul_id_zero_iff _ P).mp
      (by simpa [x, koszulScalars, hj, smulId] using hx ⟨j, hj⟩)
  have hT := iteratedScalarCone_zero_triangles X (fun k ↦ (T k).mor₂)
    (fun k ↦ (T k).mor₃) e x hS hnull
  have hKos (i : ℤ) (hi : i < a ∨ b < i) : IsZero ((F.shift i).obj (X e)) := by
    apply IsZero.of_iso _ ((perfectLengthHomologyShiftIso lam hfg z hJ i).app (X e))
    apply (perfectLengthHomology_isZero_iff lam hfg z hJ _ _ (hs.koszulComplexOn _) i).mpr
    have heq : (fun j : Fin e ↦ x j) = z := funext (koszulScalars_fin z)
    change lam.len ((koszulComplexOn (fun j : Fin e ↦ x j) P).homology i) = 0
    rw [heq]
    exact lambdaHomology_koszul_projective_amplitude lam hfg z hJ hzero P
      (fun q ↦ (hP.2 q).1) (fun q ↦ (hP.2 q).2) a b hbound i hi
  have hv := iteratedZeroCone_vanishing X (fun k ↦ (T k).mor₂) (fun k ↦ (T k).mor₃)
    e hT F a b hKos q hq
  apply (perfectLengthHomology_isZero_iff lam hfg z hJ P hP hs q).mp
  exact hv.of_iso ((perfectLengthHomologyShiftIso lam hfg z hJ q).app (X 0)).symm

end SerrePositivity.LengthAlgebra
