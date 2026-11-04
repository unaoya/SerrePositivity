module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ComplexCompletion.Basic
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Tower.HolimModel
public import SerrePositivity.HomologicalAlgebra.Complex.Cone
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Koszul.Tower
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-! # 複体の塔の射とホモトピー逆極限の関手性

## 概要

任意の両立する塔の射が holim の写像 `complexTowerHomotopyLimitMap` を誘導することを示し、表示同型・標準射影・持ち上げとの両立（自然性）を与える。塔の短完全列は holim の短完全列を与える（`complexTowerHomotopyLimitShortComplex_shortExact`）。

## 方針

差分の錐とシフトへ射を移し、holim の二成分表示で各次数の完全性を直接示す。通常の逆極限の完全性や lim¹ の消滅は仮定しない。

## 規約

TowerProjection は KoszulTower・TowerUnit の上にあるので別ファイルのまま。

## 使われ方

導来完備化の比較、`Tower/Milnor`。
-/

@[expose] public noncomputable section

universe u

section TowerMapPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable (R : Type u) [CommRing R]
variable {K L : ℕ → CochainComplex (ModuleCat.{u} R) ℤ}
    (t : ∀ n, K (n + 1) ⟶ K n) (s : ∀ n, L (n + 1) ⟶ L n)
    (g : ∀ n, K n ⟶ L n) (hg : ∀ n, t n ≫ g n = g (n + 1) ≫ s n)

/-- 塔の任意の射を、直積上の差分のArrow射へ移す。 -/
def complexTowerDifferenceArrowMap :
    Arrow.mk (complexTowerDifference R K t) ⟶ Arrow.mk (complexTowerDifference R L s) :=
  Arrow.homMk (complexTowerProductMap R g) (complexTowerProductMap R g)
    (complexTowerDifference_naturality R t s g hg)

/-- 任意の両立する射は、具体的なholimモデルの射を与える。 -/
def complexTowerHomotopyLimitMap :
    complexTowerHomotopyLimit R K t ⟶ complexTowerHomotopyLimit R L s :=
  ((cochainMappingConeFunctor R).map (complexTowerDifferenceArrowMap R t s g hg))⟦(-1 : ℤ)⟧'

/-- 直積の各項の写像を成分ごとに計算する。 -/
theorem complexProductDegreeEquiv_map (i : ℤ) (x : (piObj K).X i) (k : ℕ) :
    complexProductDegreeEquiv R L i ((complexTowerProductMap R g).f i x) k =
      (g k).f i (complexProductDegreeEquiv R K i x k) := by
  simp only [complexProductDegreeEquiv_apply]
  exact congrArg (fun f ↦ (f.f i).hom x) (complexTowerProductMap_projection R g k)

/-- holimの射とシフトの各項の同型は可換する。 -/
theorem complexTowerHomotopyLimitDegreeIso_map (m n : ℤ) (h : m + 1 = n)
    (x : (complexTowerHomotopyLimit R K t).X n) :
    (CochainComplex.shiftFunctorObjXIso
      (CochainComplex.mappingCone (complexTowerDifference R L s)) (-1) n m (by omega)).hom
        ((complexTowerHomotopyLimitMap R t s g hg).f n x) =
      ((cochainMappingConeFunctor R).map (complexTowerDifferenceArrowMap R t s g hg)).f m
        ((CochainComplex.shiftFunctorObjXIso
          (CochainComplex.mappingCone (complexTowerDifference R K t))
          (-1) n m (by omega)).hom x) := by
  have hm : m = n + (-1) := by omega
  subst m
  simp [complexTowerHomotopyLimitMap, CochainComplex.shiftFunctorObjXIso]
  rfl

/-- holimの射の第1成分は、同じ次数の段ごとの射。 -/
theorem complexTowerHomotopyLimitDegreeEquiv_map_fst (m n : ℤ) (h : m + 1 = n)
    (x : (complexTowerHomotopyLimit R K t).X n) (k : ℕ) :
    (complexTowerHomotopyLimitDegreeEquiv R L s m n h
      ((complexTowerHomotopyLimitMap R t s g hg).f n x)).1 k =
        (g k).f n ((complexTowerHomotopyLimitDegreeEquiv R K t m n h x).1 k) := by
  rw [complexTowerHomotopyLimitDegreeEquiv_fst, complexTowerHomotopyLimitDegreeEquiv_fst,
    complexTowerHomotopyLimitDegreeIso_map R t s g hg m n h]
  let y := (CochainComplex.shiftFunctorObjXIso
    (CochainComplex.mappingCone (complexTowerDifference R K t)) (-1) n m (by omega)).hom x
  have hh := congrArg (fun f ↦ f.hom y)
    (moduleConeArrowMap_fst (complexTowerDifference R K t) (complexTowerDifference R L s)
      (complexTowerDifferenceArrowMap R t s g hg) m n h)
  change homotopyCofiber.fstX (complexTowerDifference R L s) m n h
      (((cochainMappingConeFunctor R).map
        (complexTowerDifferenceArrowMap R t s g hg)).f m y) =
    (complexTowerProductMap R g).f n
      (homotopyCofiber.fstX (complexTowerDifference R K t) m n h y) at hh
  rw [hh, complexProductDegreeEquiv_map]

/-- holimの射の第2成分は、一つ前の次数の段ごとの射。 -/
theorem complexTowerHomotopyLimitDegreeEquiv_map_snd (m n : ℤ) (h : m + 1 = n)
    (x : (complexTowerHomotopyLimit R K t).X n) (k : ℕ) :
    (complexTowerHomotopyLimitDegreeEquiv R L s m n h
      ((complexTowerHomotopyLimitMap R t s g hg).f n x)).2 k =
        (g k).f m ((complexTowerHomotopyLimitDegreeEquiv R K t m n h x).2 k) := by
  rw [complexTowerHomotopyLimitDegreeEquiv_snd, complexTowerHomotopyLimitDegreeEquiv_snd,
    complexTowerHomotopyLimitDegreeIso_map R t s g hg m n h]
  let y := (CochainComplex.shiftFunctorObjXIso
    (CochainComplex.mappingCone (complexTowerDifference R K t)) (-1) n m (by omega)).hom x
  have hh := congrArg (fun f ↦ f.hom y)
    (moduleConeArrowMap_snd (complexTowerDifference R K t) (complexTowerDifference R L s)
      (complexTowerDifferenceArrowMap R t s g hg) m)
  change homotopyCofiber.sndX (complexTowerDifference R L s) m
      (((cochainMappingConeFunctor R).map
        (complexTowerDifferenceArrowMap R t s g hg)).f m y) =
    (complexTowerProductMap R g).f m (homotopyCofiber.sndX (complexTowerDifference R K t) m y) at hh
  rw [hh, complexProductDegreeEquiv_map]

/-- 差分を消す標準持ち上げは、塔の任意の両立する射と可換する。 -/
theorem complexTowerHomotopyLimitLift_map
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (α : P ⟶ piObj K) (hα : α ≫ complexTowerDifference R K t = 0)
    (β : P ⟶ piObj L) (hβ : β ≫ complexTowerDifference R L s = 0)
    (hαβ : α ≫ complexTowerProductMap R g = β) :
    complexTowerHomotopyLimitLift R K t P α hα ≫
      complexTowerHomotopyLimitMap R t s g hg =
        complexTowerHomotopyLimitLift R L s P β hβ := by
  dsimp only [complexTowerHomotopyLimitMap]
  open CochainComplex.HomComplex in
  apply (Cocycle.equivHomShift (K := P)
    (L := CochainComplex.mappingCone (complexTowerDifference R L s)) (n := (-1 : ℤ))).injective
  rw [CochainComplex.HomComplex.Cocycle.equivHomShift_comp_shift (n := (-1 : ℤ))]
  apply Subtype.ext
  simp only [complexTowerHomotopyLimitLift,
    CochainComplex.HomComplex.Cocycle.postcomp, CochainComplex.HomComplex.Cocycle.mk_coe]
  erw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  simp only [CochainComplex.mappingCone.liftCocycle_coe,
    CochainComplex.HomComplex.Cocycle.ofHom_coe, CochainComplex.mappingCone.liftCochain,
    CochainComplex.HomComplex.Cochain.zero_comp, add_zero]
  rw [CochainComplex.HomComplex.Cochain.comp_assoc_of_first_is_zero_cochain]
  erw [cochainMappingConeFunctor_inl]
  simp only [← CochainComplex.HomComplex.Cochain.comp_assoc_of_first_is_zero_cochain]
  erw [← CochainComplex.HomComplex.Cochain.ofHom_comp]
  change (CochainComplex.HomComplex.Cochain.ofHom
    (α ≫ complexTowerProductMap R g)).comp _ _ = _
  rw [hαβ]
  rfl

/-- 各段への両立する標準射の持ち上げと、holimの射の比較。 -/
theorem complexTowerCompatibleLift_map (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (α : ∀ n, P ⟶ K n) (hα : ∀ n, α (n + 1) ≫ t n = α n)
    (β : ∀ n, P ⟶ L n) (hβ : ∀ n, β (n + 1) ≫ s n = β n)
    (hαβ : ∀ n, α n ≫ g n = β n) :
    complexTowerCompatibleLift R K t P α hα ≫
      complexTowerHomotopyLimitMap R t s g hg = complexTowerCompatibleLift R L s P β hβ := by
  apply complexTowerHomotopyLimitLift_map
  apply Pi.hom_ext
  intro n
  rw [Category.assoc, complexTowerProductMap_projection, ← Category.assoc,
    Pi.lift_comp_π, Pi.lift_comp_π, hαβ]

end SerrePositivity.DerivedCompletion

end TowerMapPart

section TowerIsoProjectionPart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits CategoryTheory.Category
open HomologicalComplex.homotopyCofiber
variable (R : Type u) [CommRing R]
variable {K L : ℕ → CochainComplex (ModuleCat.{u} R) ℤ}
    (t : ∀ n, K (n + 1) ⟶ K n) (s : ∀ n, L (n + 1) ⟶ L n)
    (e : ∀ n, K n ≅ L n) (he : ∀ n, t n ≫ (e n).hom = (e (n + 1)).hom ≫ s n)

/-- 標準射影の零次数成分は、外側の錐の第1射影。 -/
theorem complexTowerProjection_fst_zero :
    (complexTowerProjection R K t).f 0 =
      fstX (complexTowerDifference R K t) (-1) 0 (by decide) := by
  simp [complexTowerProjection, CochainComplex.mappingCocone.fst,
    CochainComplex.HomComplex.Cochain.leftShift, CochainComplex.shiftFunctorObjXIso,
    CochainComplex.mappingCone.fst]

/-- 塔の比較は、外側の錐の零次数の第1射影を保つ。 -/
theorem complexTowerHomotopyLimitIso_fst_zero :
    (complexTowerHomotopyLimitIso R t s e he).hom.f 0 ≫
      fstX (complexTowerDifference R L s) (-1) 0 (by decide) =
    fstX (complexTowerDifference R K t) (-1) 0 (by decide) ≫
      (complexTowerProductIso R e).hom.f 0 := by
  change (mapArrowHom (complexTowerDifference R K t) (complexTowerDifference R L s)
    (fun j ↦ ⟨j - 1, by simp⟩) (complexTowerDifferenceIso R t s e he).hom).f (-1) ≫ _ = _
  exact moduleConeArrowMap_fst _ _ _ (-1) 0 (by decide)

/-- 塔の比較は、外側の錐の零次数の第2射影を保つ。 -/
theorem complexTowerHomotopyLimitIso_snd_zero :
    (complexTowerHomotopyLimitIso R t s e he).hom.f 0 ≫
      sndX (complexTowerDifference R L s) (-1) =
    sndX (complexTowerDifference R K t) (-1) ≫ (complexTowerProductIso R e).hom.f (-1) := by
  change (mapArrowHom (complexTowerDifference R K t) (complexTowerDifference R L s)
    (fun j ↦ ⟨j - 1, by simp⟩) (complexTowerDifferenceIso R t s e he).hom).f (-1) ≫ _ = _
  exact moduleConeArrowMap_snd _ _ _ (-1)

end SerrePositivity.DerivedCompletion

end TowerIsoProjectionPart

section TowerIsoMapCompatibilityPart

namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits
variable (R : Type u) [CommRing R]
    {K L : ℕ → CochainComplex (ModuleCat.{u} R) ℤ}
    (t : ∀ n, K (n + 1) ⟶ K n) (s : ∀ n, L (n + 1) ⟶ L n)
    (e : ∀ n, K n ≅ L n)
    (he : ∀ n, t n ≫ (e n).hom = (e (n + 1)).hom ≫ s n)

/-- The original map on holims is exactly the hom of the existing comparison iso. -/
lemma complexTowerHomotopyLimitMap_eq_iso_hom :
    complexTowerHomotopyLimitMap R t s (fun n => (e n).hom) he =
      (complexTowerHomotopyLimitIso R t s e he).hom := rfl

/-- Transporting a compatible lift through a tower iso keeps all original maps. -/
lemma complexTowerCompatibleLift_iso
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (α : ∀ n, P ⟶ K n) (hα : ∀ n, α (n + 1) ≫ t n = α n)
    (β : ∀ n, P ⟶ L n) (hβ : ∀ n, β (n + 1) ≫ s n = β n)
    (hαβ : ∀ n, α n ≫ (e n).hom = β n) :
    complexTowerCompatibleLift R K t P α hα ≫
      (complexTowerHomotopyLimitIso R t s e he).hom =
        complexTowerCompatibleLift R L s P β hβ := by
  rw [← complexTowerHomotopyLimitMap_eq_iso_hom]
  exact complexTowerCompatibleLift_map R t s (fun n => (e n).hom) he P α hα β hβ hαβ

end SerrePositivity.DerivedCompletion

end TowerIsoMapCompatibilityPart

section TowerLiftNaturalityPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits CochainComplex.HomComplex
variable (R : Type u) [CommRing R]
    (K : ℕ → CochainComplex (ModuleCat.{u} R) ℤ) (t : ∀ n, K (n + 1) ⟶ K n)

/-- Precomposing a zero-difference map precomposes its original cone lift. -/
lemma complexTowerHomotopyLimitLift_precomp
    {P Q : CochainComplex (ModuleCat.{u} R) ℤ} (f : P ⟶ Q)
    (β : Q ⟶ piObj K) (hβ : β ≫ complexTowerDifference R K t = 0) :
    f ≫ complexTowerHomotopyLimitLift R K t Q β hβ =
      complexTowerHomotopyLimitLift R K t P (f ≫ β)
        (by rw [Category.assoc, hβ, comp_zero]) := by
  apply (Cocycle.equivHomShift (K := P)
    (L := CochainComplex.mappingCone (complexTowerDifference R K t)) (n := (-1 : ℤ))).injective
  rw [Cocycle.equivHomShift_comp (n := (-1 : ℤ))]
  apply Subtype.ext
  simp only [complexTowerHomotopyLimitLift, Cocycle.precomp, Cocycle.mk_coe]
  erw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply]
  simp only [CochainComplex.mappingCone.liftCocycle_coe, Cocycle.ofHom_coe,
    CochainComplex.mappingCone.liftCochain, Cochain.zero_comp, add_zero]
  rw [← Cochain.comp_assoc_of_first_is_zero_cochain]
  erw [← Cochain.ofHom_comp]

/-- The compatible lift keeps the original maps under source precomposition. -/
lemma complexTowerCompatibleLift_precomp
    {P Q : CochainComplex (ModuleCat.{u} R) ℤ} (f : P ⟶ Q)
    (β : ∀ n, Q ⟶ K n) (hβ : ∀ n, β (n + 1) ≫ t n = β n) :
    f ≫ complexTowerCompatibleLift R K t Q β hβ =
      complexTowerCompatibleLift R K t P (fun n => f ≫ β n)
        (by intro n; rw [Category.assoc, hβ]) := by
  unfold complexTowerCompatibleLift
  rw [complexTowerHomotopyLimitLift_precomp]
  congr 1
  apply Pi.hom_ext
  intro n
  simp only [Category.assoc, Pi.lift_comp_π]

/-- Naturality for simultaneous changes of the source and the tower. -/
lemma complexTowerCompatibleLift_naturality
    {L : ℕ → CochainComplex (ModuleCat.{u} R) ℤ} (s : ∀ n, L (n + 1) ⟶ L n)
    (g : ∀ n, K n ⟶ L n) (hg : ∀ n, t n ≫ g n = g (n + 1) ≫ s n)
    {P Q : CochainComplex (ModuleCat.{u} R) ℤ} (f : P ⟶ Q)
    (α : ∀ n, P ⟶ K n) (hα : ∀ n, α (n + 1) ≫ t n = α n)
    (β : ∀ n, Q ⟶ L n) (hβ : ∀ n, β (n + 1) ≫ s n = β n)
    (h : ∀ n, α n ≫ g n = f ≫ β n) :
    complexTowerCompatibleLift R K t P α hα ≫
      complexTowerHomotopyLimitMap R t s g hg =
        f ≫ complexTowerCompatibleLift R L s Q β hβ := by
  rw [complexTowerCompatibleLift_precomp]
  exact complexTowerCompatibleLift_map R t s g hg P α hα _ _ h

end SerrePositivity.DerivedCompletion

end TowerLiftNaturalityPart

section TowerExactPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits HomologicalComplex
variable (R : Type u) [CommRing R]
variable {K L M : ℕ → CochainComplex (ModuleCat.{u} R) ℤ}
    (t : ∀ n, K (n + 1) ⟶ K n) (s : ∀ n, L (n + 1) ⟶ L n)
    (u : ∀ n, M (n + 1) ⟶ M n)
    (f : ∀ n, K n ⟶ L n) (g : ∀ n, L n ⟶ M n)
    (hf : ∀ n, t n ≫ f n = f (n + 1) ≫ s n)
    (hg : ∀ n, s n ≫ g n = g (n + 1) ≫ u n)
    (hfg : ∀ n, f n ≫ g n = 0)

include hfg in
/-- 各段の零合成は、holimの実際の写像の零合成を与える。 -/
theorem complexTowerHomotopyLimitMap_comp_zero :
    complexTowerHomotopyLimitMap R t s f hf ≫
      complexTowerHomotopyLimitMap R s u g hg = 0 := by
  apply HomologicalComplex.hom_ext
  intro i
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply (complexTowerHomotopyLimitDegreeEquiv R M u (i - 1) i (by omega)).injective
  apply Prod.ext
  · funext k
    simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
      HomologicalComplex.zero_f, ModuleCat.hom_zero, LinearMap.zero_apply, map_zero,
      Prod.fst_zero, Pi.zero_apply]
    rw [complexTowerHomotopyLimitDegreeEquiv_map_fst,
      complexTowerHomotopyLimitDegreeEquiv_map_fst]
    exact congrArg (fun q ↦ (q.f i).hom
      ((complexTowerHomotopyLimitDegreeEquiv R K t (i - 1) i (by omega) x).1 k)) (hfg k)
  · funext k
    simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
      HomologicalComplex.zero_f, ModuleCat.hom_zero, LinearMap.zero_apply, map_zero,
      Prod.snd_zero, Pi.zero_apply]
    rw [complexTowerHomotopyLimitDegreeEquiv_map_snd,
      complexTowerHomotopyLimitDegreeEquiv_map_snd]
    exact congrArg (fun q ↦ (q.f (i - 1)).hom
      ((complexTowerHomotopyLimitDegreeEquiv R K t (i - 1) i (by omega) x).2 k)) (hfg k)

/-- 塔の短複体のholimを、実際の複体の短複体として構成する。 -/
def complexTowerHomotopyLimitShortComplex : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ) :=
  ShortComplex.mk (complexTowerHomotopyLimitMap R t s f hf)
    (complexTowerHomotopyLimitMap R s u g hg)
    (complexTowerHomotopyLimitMap_comp_zero R t s u f g hf hg hfg)

/-- 各段が短完全なら、差分の錐とシフトによるholimの短複体も短完全。 -/
theorem complexTowerHomotopyLimitShortComplex_shortExact
    (hS : ∀ k, (ShortComplex.mk (f k) (g k) (hfg k)).ShortExact) :
    (complexTowerHomotopyLimitShortComplex R t s u f g hf hg hfg).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro i
  change (ShortComplex.mk
    ((complexTowerHomotopyLimitMap R t s f hf).f i)
    ((complexTowerHomotopyLimitMap R s u g hg).f i)
    (congrArg (fun q ↦ q.f i)
      (complexTowerHomotopyLimitMap_comp_zero R t s u f g hf hg hfg))).ShortExact
  have hs (k : ℕ) (j : ℤ) :
      ((ShortComplex.mk (f k) (g k) (hfg k)).map
        (HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) j)).ShortExact :=
    (hS k).map_of_exact (HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) j)
  have hfinj (k : ℕ) (j : ℤ) : Function.Injective ((f k).f j) :=
    (ModuleCat.mono_iff_injective _).mp (hs k j).mono_f
  have hgsurj (k : ℕ) (j : ℤ) : Function.Surjective ((g k).f j) :=
    (ModuleCat.epi_iff_surjective _).mp (hs k j).epi_g
  have hexact (k : ℕ) (j : ℤ) (y : (L k).X j) (hy : (g k).f j y = 0) :
      ∃ x, (f k).f j x = y :=
    (ShortComplex.moduleCat_exact_iff _).mp (hs k j).exact y hy
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · apply (ShortComplex.moduleCat_exact_iff _).mpr
    intro y hy
    let v := complexTowerHomotopyLimitDegreeEquiv R L s (i - 1) i (by omega) y
    have hv₁ (k : ℕ) : (g k).f i (v.1 k) = 0 := by
      have h := congrArg (fun z ↦
        (complexTowerHomotopyLimitDegreeEquiv R M u (i - 1) i (by omega) z).1 k) hy
      simpa only [complexTowerHomotopyLimitDegreeEquiv_map_fst, map_zero,
        Prod.fst_zero, Pi.zero_apply] using h
    have hv₂ (k : ℕ) : (g k).f (i - 1) (v.2 k) = 0 := by
      have h := congrArg (fun z ↦
        (complexTowerHomotopyLimitDegreeEquiv R M u (i - 1) i (by omega) z).2 k) hy
      simpa only [complexTowerHomotopyLimitDegreeEquiv_map_snd, map_zero,
        Prod.snd_zero, Pi.zero_apply] using h
    choose x₁ hx₁ using fun k ↦ hexact k i (v.1 k) (hv₁ k)
    choose x₂ hx₂ using fun k ↦ hexact k (i - 1) (v.2 k) (hv₂ k)
    refine ⟨(complexTowerHomotopyLimitDegreeEquiv R K t (i - 1) i (by omega)).symm (x₁, x₂), ?_⟩
    apply (complexTowerHomotopyLimitDegreeEquiv R L s (i - 1) i (by omega)).injective
    apply Prod.ext
    · funext k
      rw [complexTowerHomotopyLimitDegreeEquiv_map_fst, LinearEquiv.apply_symm_apply]
      exact hx₁ k
    · funext k
      rw [complexTowerHomotopyLimitDegreeEquiv_map_snd, LinearEquiv.apply_symm_apply]
      exact hx₂ k
  · apply (ModuleCat.mono_iff_injective _).mpr
    intro x y hxy
    apply (complexTowerHomotopyLimitDegreeEquiv R K t (i - 1) i (by omega)).injective
    apply Prod.ext
    · funext k
      apply hfinj k i
      have h := congrArg (fun z ↦
        (complexTowerHomotopyLimitDegreeEquiv R L s (i - 1) i (by omega) z).1 k) hxy
      simpa only [complexTowerHomotopyLimitDegreeEquiv_map_fst] using h
    · funext k
      apply hfinj k (i - 1)
      have h := congrArg (fun z ↦
        (complexTowerHomotopyLimitDegreeEquiv R L s (i - 1) i (by omega) z).2 k) hxy
      simpa only [complexTowerHomotopyLimitDegreeEquiv_map_snd] using h
  · apply (ModuleCat.epi_iff_surjective _).mpr
    intro y
    let v := complexTowerHomotopyLimitDegreeEquiv R M u (i - 1) i (by omega) y
    choose x₁ hx₁ using fun k ↦ hgsurj k i (v.1 k)
    choose x₂ hx₂ using fun k ↦ hgsurj k (i - 1) (v.2 k)
    refine ⟨(complexTowerHomotopyLimitDegreeEquiv R L s (i - 1) i (by omega)).symm (x₁, x₂), ?_⟩
    apply (complexTowerHomotopyLimitDegreeEquiv R M u (i - 1) i (by omega)).injective
    apply Prod.ext
    · funext k
      rw [complexTowerHomotopyLimitDegreeEquiv_map_fst, LinearEquiv.apply_symm_apply]
      exact hx₁ k
    · funext k
      rw [complexTowerHomotopyLimitDegreeEquiv_map_snd, LinearEquiv.apply_symm_apply]
      exact hx₂ k

end SerrePositivity.DerivedCompletion

end TowerExactPart
