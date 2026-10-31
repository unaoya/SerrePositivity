module

public import SerrePositivity.PerfectComplex.Perfect.HomotopyCategory
public import SerrePositivity.LengthAlgebra.Koszul
public import SerrePositivity.CategoryTheory.Euler
public import Mathlib.Algebra.Homology.HomotopyCategory.HomologicalFunctor
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence
public import SerrePositivity.PerfectComplex.KoszulTower
public import SerrePositivity.PerfectComplex.KoszulLength
public import SerrePositivity.PerfectComplex.Perfect.FreeComparison

/-! # 有限射影複体の正規化 Euler 評価

## 概要

有限射影複体のホモロジーを有限長さの Serre 商へ送って共通の Euler 評価を作り、台つき有限射影複体の消滅（スカラーの零ホモトピーと環自身の Koszul 消滅から、反復錐の定理で）と、係数変更による Euler 評価を与える。

## 方針

消滅には有限長さの商ではなく大きな商を使い、長さの有限性を要求しない。

## 規約

Koszul の条件と台の条件は明示的な仮定として受け取る。

## 使われ方

`LengthAlgebra/KoszulFormula`、IntersectionMultiplicity/ParameterQuotient、Paper の §4。
-/

@[expose] public noncomputable section

universe u

section PerfectHomologyPart

namespace SerrePositivity.LengthAlgebra

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

variable {R : Type u} [CommRing R] {J : Ideal R} (lam : NormalizedLength R J)
  (hfg : J.FG) {e : ℕ} (z : Fin e → R)
  (hJ : J ≤ (Ideal.span (Set.range z)).radical) (hfin : KoszulFinite lam z)

/-- 支持つき有限射影複体の通常のホモロジー関手。 -/
noncomputable abbrev perfectModuleHomology (q : ℤ) :
    SupportedPerfectHomotopy z ⥤ ModuleCat.{u} R :=
  supportedPerfectInclusion z ⋙ perfectHomotopyInclusion R ⋙
    HomotopyCategory.homologyFunctor _ _ q

include hfg hJ hfin in
/-- 支持と Koszul 有限性によって、評価先を有限長さの冪ねじれ加群に制限できる。 -/
lemma perfectModuleHomology_mem (X : SupportedPerfectHomotopy z) (q : ℤ) :
    finiteLengthTorsion lam ((perfectModuleHomology z q).obj X) := by
  obtain ⟨⟨X, hX⟩, hz⟩ := X
  obtain ⟨P : CochainComplex _ _, rfl⟩ := X.quotient_obj_surjective
  have hP := (perfectHomotopyProperty_quotient R P).mp hX
  have hs : IsSupported z P := (perfectHomotopyObj_supported_iff z P hP).mp hz
  apply (finiteLengthTorsion lam).prop_of_iso
    ((HomotopyCategory.homologyFunctorFactors _ _ q).app P).symm
  apply homology_mem_finiteLengthTorsion lam z hfg hJ hfin P
    (fun q ↦ (hP.2 q).1) (fun q ↦ (hP.2 q).2) _ hs q
  obtain ⟨a, b, ha, hb⟩ := hP.1
  exact ⟨a, b, fun q hq ↦ hq.elim (fun h ↦ P.isZero_of_isStrictlyGE a q h)
    (fun h ↦ P.isZero_of_isStrictlyLE b q h)⟩

/-- 有限長さの冪ねじれ加群に値をもつホモロジー関手。 -/
noncomputable def perfectFiniteHomology (q : ℤ) :
    SupportedPerfectHomotopy z ⥤ FiniteLengthTorsion lam :=
  (finiteLengthTorsion lam).lift (perfectModuleHomology z q)
    (fun X ↦ perfectModuleHomology_mem lam hfg z hJ hfin X q)

instance perfectFiniteHomology_additive (q : ℤ) :
    (perfectFiniteHomology lam hfg z hJ hfin q).Additive := by
  dsimp only [perfectFiniteHomology]
  infer_instance

instance perfectFiniteHomology_isHomological (q : ℤ) :
    (perfectFiniteHomology lam hfg z hJ hfin q).IsHomological where
  exact T hT := by
    apply (ShortComplex.exact_map_iff_of_faithful _ (finiteLengthTorsion lam).ι).mp
    exact (perfectModuleHomology z q).map_distinguished_exact T hT

/-- 有限長さの商に値をもつホモロジー関手。 -/
noncomputable def perfectQuotientHomology (q : ℤ) :
    SupportedPerfectHomotopy z ⥤ FiniteLengthQuotient lam :=
  perfectFiniteHomology lam hfg z hJ hfin q ⋙ finiteLengthQuotientFunctor lam

instance perfectQuotientHomology_additive (q : ℤ) :
    (perfectQuotientHomology lam hfg z hJ hfin q).Additive := by
  dsimp only [perfectQuotientHomology]
  infer_instance

instance perfectQuotientHomology_isHomological (q : ℤ) :
    (perfectQuotientHomology lam hfg z hJ hfin q).IsHomological where
  exact T hT :=
    ((perfectFiniteHomology lam hfg z hJ hfin q).map_distinguished_exact T hT).map
      (finiteLengthQuotientFunctor lam)

/-- 第零次関手のシフトと、各次数のホモロジーの自然同型。 -/
noncomputable def perfectQuotientHomologyShiftIso (q : ℤ) :
    shiftFunctor _ q ⋙ perfectQuotientHomology lam hfg z hJ hfin 0 ≅
      perfectQuotientHomology lam hfg z hJ hfin q := by
  let G := supportedPerfectInclusion z ⋙ perfectHomotopyInclusion R
  let H := HomotopyCategory.homologyFunctor (ModuleCat.{u} R) (.up ℤ) 0
  let i : shiftFunctor _ q ⋙ perfectModuleHomology z 0 ≅ perfectModuleHomology z q :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (G.commShiftIso q) H ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft G (H.isoShift q)
  let j : shiftFunctor _ q ⋙ perfectFiniteHomology lam hfg z hJ hfin 0 ≅
      perfectFiniteHomology lam hfg z hJ hfin q :=
    NatIso.ofComponents (fun X ↦ ObjectProperty.isoMk _ (i.app X)) (fun f ↦ by
      apply ObjectProperty.hom_ext
      exact i.hom.naturality f)
  exact Functor.isoWhiskerRight j (finiteLengthQuotientFunctor lam)

/-- 各対象ごとの有界性。圏全体に共通の振幅は要求しない。 -/
lemma perfectQuotientHomology_bounded (X : SupportedPerfectHomotopy z) :
    ∃ a b : ℤ, ∀ q, q < a ∨ b < q →
      IsZero ((perfectQuotientHomology lam hfg z hJ hfin q).obj X) := by
  obtain ⟨⟨X, hX⟩, hz⟩ := X
  obtain ⟨P : CochainComplex _ _, rfl⟩ := X.quotient_obj_surjective
  obtain ⟨⟨a, b, ha, hb⟩, hp⟩ := (perfectHomotopyProperty_quotient R P).mp hX
  refine ⟨a, b, fun q hq ↦ ?_⟩
  apply (finiteLengthQuotientFunctor lam).map_isZero
  rw [IsZero.iff_id_eq_zero]
  apply ObjectProperty.hom_ext
  exact ((isZero_homology_of_isZero_X P q
    (hq.elim (fun h ↦ P.isZero_of_isStrictlyGE a q h)
      (fun h ↦ P.isZero_of_isStrictlyLE b q h))).of_iso
      ((HomotopyCategory.homologyFunctorFactors _ _ q).app P)).eq_of_src _ _

noncomputable instance perfectQuotientHomology_shiftSequence :
    (perfectQuotientHomology lam hfg z hJ hfin 0).ShiftSequence ℤ :=
  Functor.ShiftSequence.tautological _ ℤ

/-- 共通 Euler 評価に渡すシフト列の有界性。 -/
lemma perfectQuotientHomology_shift_bounded (X : SupportedPerfectHomotopy z) :
    ∃ a b : ℤ, ∀ q, q < a ∨ b < q →
      IsZero (((perfectQuotientHomology lam hfg z hJ hfin 0).shift q).obj X) := by
  obtain ⟨a, b, hab⟩ := perfectQuotientHomology_bounded lam hfg z hJ hfin X
  exact ⟨a, b, fun q hq ↦ (hab q hq).of_iso
    ((perfectQuotientHomologyShiftIso lam hfg z hJ hfin q).app X)⟩

/-- 有限射影版の Euler 評価は共通のホモロジー的 Euler 評価で定義する。 -/
noncomputable def perfectEuler (X : SupportedPerfectHomotopy z) : ℝ :=
  homologicalEuler (quotientLength lam) (perfectQuotientHomology lam hfg z hJ hfin 0) X

/-- 共通の三角加法性により得られる Euler 準同型。 -/
noncomputable def perfectEulerK0 : TriangulatedK0 (SupportedPerfectHomotopy z) →+ ℝ :=
  homologicalEulerK0 (quotientLength lam) (quotientLength_iso lam) (quotientLength_add lam)
    (perfectQuotientHomology lam hfg z hJ hfin 0)
    (fun X hX ↦ (quotientLength_eq_zero_iff lam X).mpr hX)
    (perfectQuotientHomology_shift_bounded lam hfg z hJ hfin)

@[simp] lemma perfectEulerK0_mk (X : SupportedPerfectHomotopy z) :
    perfectEulerK0 lam hfg z hJ hfin (TriangulatedK0.mk X) =
      perfectEuler lam hfg z hJ hfin X := homologicalEulerK0_mk ..

/-- 代表複体上で、新しい評価は従来のホモロジーの交代和と一致する。 -/
lemma perfectEuler_eq_lambdaEuler (X : SupportedPerfectHomotopy z) :
    perfectEuler lam hfg z hJ hfin X = lambdaEuler lam X.obj.obj.as := by
  unfold perfectEuler homologicalEuler lambdaEuler
  simp only [zsmul_eq_mul]
  congr 1
  funext q
  congr 1
  refine (quotientLength_iso lam
    ((perfectQuotientHomologyShiftIso lam hfg z hJ hfin q).app X)).trans ?_
  exact congrArg ENNReal.toReal (lam.len_congr _ _
    ((HomotopyCategory.homologyFunctorFactors _ _ q).app X.obj.obj.as).toLinearEquiv)

end SerrePositivity.LengthAlgebra

end PerfectHomologyPart

section PerfectVanishingPart

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

end PerfectVanishingPart

section PerfectBaseChangePart

namespace SerrePositivity.LengthAlgebra

open CategoryTheory CategoryTheory.Limits

variable {R C : Type u} [CommRing R] [CommRing C] (φ : R →+* C)
  {J : Ideal C} (lam : NormalizedLength C J) (hfg : J.FG)
  {e : ℕ} (z : Fin e → R)
  (hJ : J ≤ (Ideal.span (Set.range (φ ∘ z))).radical)
  (hfin : KoszulFinite lam (φ ∘ z))

/-- 三角関手による共通 Euler 評価の引き戻し。 -/
noncomputable def perfectBaseChangeEulerK0 : TriangulatedK0 (SupportedPerfectHomotopy z) →+ ℝ :=
  (perfectEulerK0 lam hfg (φ ∘ z) hJ hfin).comp
    (TriangulatedK0.map (supportedPerfectChangeRing φ z))

/-- 有限自由モデル上でも、新しい Euler 評価は従来の `chiLam` を再現する。 -/
@[simp] lemma perfectBaseChangeEulerK0_free (P : PerfSupp R z) :
    perfectBaseChangeEulerK0 φ lam hfg z hJ hfin
      (TriangulatedK0.mk (perfSuppHomotopyObj P)) = chiLam lam φ P.1 := by
  simp only [perfectBaseChangeEulerK0, AddMonoidHom.comp_apply, TriangulatedK0.map_mk,
    perfectEulerK0_mk]
  exact perfectEuler_eq_lambdaEuler lam hfg (φ ∘ z) hJ hfin _

/-- 旧有限自由 K₀ 上の評価も、共通 Euler 評価から比較写像で引き戻す。 -/
noncomputable def freeBaseChangeEulerK0 : K0Supported R z →+ ℝ :=
  (perfectBaseChangeEulerK0 φ lam hfg z hJ hfin).comp freeToPerfectK0

@[simp] lemma freeBaseChangeEulerK0_mk (P : PerfSupp R z) :
    freeBaseChangeEulerK0 φ lam hfg z hJ hfin (K0.mk P) = chiLam lam φ P.1 := by
  simp [freeBaseChangeEulerK0]

/-- 三角関手の合成に関する自然同型は、Euler 評価の合成にも降りる。 -/
lemma perfectBaseChangeEulerK0_comp {A : Type u} [CommRing A] (α : A →+* R)
    {n : ℕ} (w : Fin n → A)
    (hJ' : J ≤ (Ideal.span (Set.range (φ ∘ α ∘ w))).radical)
    (hfin' : KoszulFinite lam (φ ∘ α ∘ w)) :
    (perfectBaseChangeEulerK0 φ lam hfg (α ∘ w) hJ' hfin').comp
      (TriangulatedK0.map (supportedPerfectChangeRing α w)) =
        perfectBaseChangeEulerK0 (φ.comp α) lam hfg w hJ' hfin' := by
  dsimp only [perfectBaseChangeEulerK0]
  rw [AddMonoidHom.comp_assoc, ← TriangulatedK0.map_comp]
  rw [TriangulatedK0.map_natIso _ (supportedPerfectChangeRingCompIso α w φ)]
  rfl

/-- 恒等係数変更後の評価は、元の Euler 評価そのものである。 -/
lemma perfectBaseChangeEulerK0_id {I : Ideal R} (mu : NormalizedLength R I) (hIfg : I.FG)
    (hI : I ≤ (Ideal.span (Set.range z)).radical) (hfinite : KoszulFinite mu z) :
    perfectBaseChangeEulerK0 (RingHom.id R) mu hIfg z hI hfinite =
      perfectEulerK0 mu hIfg z hI hfinite := by
  dsimp only [perfectBaseChangeEulerK0]
  rw [TriangulatedK0.map_natIso _ (supportedPerfectChangeRingIdIso z), TriangulatedK0.map_id,
    AddMonoidHom.comp_id]
  rfl

end SerrePositivity.LengthAlgebra

end PerfectBaseChangePart
