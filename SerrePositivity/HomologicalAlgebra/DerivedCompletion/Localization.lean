module

public import SerrePositivity.CommutativeAlgebra.Adic.Telescope
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleResolution
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import SerrePositivity.HomologicalAlgebra.HomComplexCone
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Tower.HolimModel
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Tower.Milnor
public import SerrePositivity.CommutativeAlgebra.Adic.Principal
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ComplexCompletion

/-! # 主元の局所化の自由分解と a 倍の塔

## 概要

主元 a を反転する局所化の telescope を長さ一の自由分解（二項の K 射影的な複体）として登録し、完備性の定義に現れる局所化からの射が、この分解からの Hom 複体のコホモロジーで計算できることを示す。Hom 複体を a 倍を遷移とする塔の holim と同一視し、a がその holim 上で可逆であること（Milnor 列の lim と lim¹ の両方で、シフトが a 倍を反転する）を示す。

## 方針

分解からの Hom 複体の列座標を明示し、塔の holim の二成分表示と比べる。可逆性は短い五項補題による。

## 規約

`scalarComplexTowerHomotopyLimit` は導来完備性の判定に使う名前なので残す。

## 使われ方

導来完備性の判定（`IsModuleComplete`）と導来完備化。
-/

@[expose] public noncomputable section

universe u

section LocalizationPresentationPart

namespace SerrePositivity.DerivedCompletion
open CategoryTheory
variable (R : Type u) [CommRing R]

/-- 主元を反転する局所化のtelescope短複体。 -/
def localizationPresentation (f : R) : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.mk (ModuleCat.ofHom (localizationTelescopeMap R f))
    (ModuleCat.ofHom (localizationTelescopeToAway R f)) (by
      apply ModuleCat.hom_ext
      exact localizationTelescope_comp_eq_zero R f)

/-- 自由telescopeは短完全列を与える。 -/
theorem localizationPresentation_shortExact (f : R) :
    (localizationPresentation R f).ShortExact where
  exact := (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mpr
    (localizationTelescope_range_eq_ker R f)
  mono_f := (ModuleCat.mono_iff_injective _).mpr
    (localizationTelescopeMap_injective R f)
  epi_g := (ModuleCat.epi_iff_surjective _).mpr
    (localizationTelescopeToAway_surjective R f)

instance localizationPresentation_projective_X₁ (f : R) :
    Projective (localizationPresentation R f).X₁ := by
  change Projective (ModuleCat.of R (ℕ →₀ R))
  infer_instance

instance localizationPresentation_projective_X₂ (f : R) :
    Projective (localizationPresentation R f).X₂ := by
  change Projective (ModuleCat.of R (ℕ →₀ R))
  infer_instance

/-- 局所化からのExtは、次数二以上で消滅する。 -/
theorem localization_ext_eq_zero (f : R) (M : ModuleCat.{u} R) (n : ℕ)
    (e : CategoryTheory.Abelian.Ext (ModuleCat.of R (Localization.Away f)) M (n + 2)) :
    e = 0 := by
  let S := localizationPresentation R f
  have hS := localizationPresentation_shortExact R f
  obtain ⟨x, hx⟩ := CategoryTheory.Abelian.Ext.contravariant_sequence_exact₃ hS M e
    (CategoryTheory.Abelian.Ext.eq_zero_of_projective _) (n₀ := n + 1) (by omega)
  rw [← hx, CategoryTheory.Abelian.Ext.eq_zero_of_projective x]
  simp
  rfl

/-- Ext¹の消滅は、自由分解の差分写像に沿うExt⁰の全射性と同値。 -/
theorem localization_ext_one_subsingleton_iff (f : R) (M : ModuleCat.{u} R) :
    Subsingleton (CategoryTheory.Abelian.Ext (ModuleCat.of R (Localization.Away f)) M 1) ↔
      Function.Surjective
        ((CategoryTheory.Abelian.Ext.mk₀ (localizationPresentation R f).f).precomp M
          (add_zero 0)) :=
  CategoryTheory.Abelian.Ext.one_subsingleton_iff_of_projective M _
    (localizationPresentation_shortExact R f) inferInstance

end SerrePositivity.DerivedCompletion

end LocalizationPresentationPart

section LocalizationResolutionPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits CategoryTheory.Localization HomologicalComplex
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R]

/-- 局所化の自由presentationを零次数複体の短完全列へ移したもの。 -/
def localizationPresentationComplex (a : R) :
    ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ) :=
  (localizationPresentation R a).map (CochainComplex.singleFunctor (ModuleCat R) 0)

/-- 零次数複体へ移しても局所化のpresentationは短完全。 -/
theorem localizationPresentationComplex_shortExact (a : R) :
    (localizationPresentationComplex R a).ShortExact :=
  (localizationPresentation_shortExact R a).map_of_exact _

/-- 主元局所化の、自由telescopeの差分の錐による二項分解。 -/
def localizationResolutionComplex (a : R) : CochainComplex (ModuleCat.{u} R) ℤ :=
  CochainComplex.mappingCone (localizationPresentationComplex R a).f

/-- 二項分解は正次数で零。 -/
instance localizationResolutionComplex_isStrictlyLE (a : R) :
    (localizationResolutionComplex R a).IsStrictlyLE 0 := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  rw [localizationResolutionComplex, CochainComplex.mappingCone.isZero_X_iff]
  exact ⟨HomologicalComplex.isZero_single_obj_X _ 0 _ (i + 1) (by omega),
    HomologicalComplex.isZero_single_obj_X _ 0 _ i (by omega)⟩

/-- 二項分解の各項は射影的。 -/
instance localizationResolutionComplex_projective (a : R) (i : ℤ) :
    Projective ((localizationResolutionComplex R a).X i) := by
  have : Projective (((localizationPresentationComplex R a).X₁).X (i + 1)) := by
    change Projective (((CochainComplex.singleFunctor (ModuleCat R) 0).obj
      (localizationPresentation R a).X₁).X (i + 1))
    infer_instance
  have : Projective (((localizationPresentationComplex R a).X₂).X i) := by
    change Projective (((CochainComplex.singleFunctor (ModuleCat R) 0).obj
      (localizationPresentation R a).X₂).X i)
    infer_instance
  exact Projective.of_iso
    (homotopyCofiber.XIsoBiprod (localizationPresentationComplex R a).f i (i + 1) rfl).symm
    inferInstance

/-- 局所化の二項自由分解はK射影的。 -/
instance localizationResolutionComplex_isKProjective (a : R) :
    (localizationResolutionComplex R a).IsKProjective :=
  CochainComplex.isKProjective_of_projective _ 0

/-- 二項自由分解の、局所化を零次数に置く複体への標準増大射。 -/
def localizationResolutionAugmentation (a : R) :
    localizationResolutionComplex R a ⟶
      (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj
        (ModuleCat.of R (Localization.Away a)) :=
  CochainComplex.mappingCone.descShortComplex (localizationPresentationComplex R a)

/-- 標準増大射は準同型同値。 -/
instance localizationResolutionAugmentation_quasiIso (a : R) :
    QuasiIso (localizationResolutionAugmentation R a) :=
  CochainComplex.mappingCone.quasiIso_descShortComplex
    (localizationPresentationComplex_shortExact R a)

/-- 二項自由分解の実導来像は、標準の局所化対象に一致する。 -/
def localizationResolutionDerivedIso (a : R) :
    DerivedCategory.Q.obj (localizationResolutionComplex R a) ≅ localizationObject R a :=
  asIso (DerivedCategory.Q.map (localizationResolutionAugmentation R a))

/-- 二項自由分解からのHom複体のコホモロジーは、局所化対象からの導来射に一致する。 -/
def localizationResolutionHomologyEquiv (a : R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (i : ℤ) :
    (CochainComplex.linearHomComplex R (localizationResolutionComplex R a) K).homology i ≃
      ShiftedHom (localizationObject R a) (DerivedCategory.Q.obj K) i := by
  letI : HasSmallLocalizedShiftedHom.{u + 1}
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)) ℤ
      (localizationResolutionComplex R a) K := fun m n ↦
    hasSmallLocalizedHom_of_isLocalization
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))
      (DerivedCategory.Q (C := ModuleCat R))
      (X := (localizationResolutionComplex R a)⟦m⟧) (Y := K⟦n⟧)
  exact (CochainComplex.HomComplex.homologyLinearEquiv R _ K i).toEquiv |>.trans
    ((CochainComplex.HomComplex.CohomologyClass.equivOfIsKProjective.{u + 1}
      (K := localizationResolutionComplex R a) (L := K) (n := i)).trans
      ((SmallShiftedHom.equiv _ DerivedCategory.Q).trans
        (Iso.homCongr (localizationResolutionDerivedIso R a) (Iso.refl _))))

/-- 完備複体への線形Hom複体のコホモロジーは全次数で零。 -/
theorem localizationResolutionHomology_subsingleton (a : R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : IsComplete R a (DerivedCategory.Q.obj K)) (i : ℤ) :
    Subsingleton
      ((CochainComplex.linearHomComplex R (localizationResolutionComplex R a) K).homology i) := by
  let : Subsingleton (ShiftedHom (localizationObject R a) (DerivedCategory.Q.obj K) i) :=
    ⟨fun x y ↦ (hK i x).trans (hK i y).symm⟩
  exact (localizationResolutionHomologyEquiv R a K i).injective.subsingleton

/-- 完備性は、二項自由分解からの線形Hom複体の全コホモロジーの消滅と同値。 -/
theorem isComplete_iff_localizationResolutionHomology_subsingleton (a : R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    IsComplete R a (DerivedCategory.Q.obj K) ↔
      ∀ i : ℤ, Subsingleton
        ((CochainComplex.linearHomComplex R (localizationResolutionComplex R a) K).homology i) := by
  constructor
  · exact localizationResolutionHomology_subsingleton R a K
  · intro h i x
    let := h i
    have : Subsingleton (ShiftedHom (localizationObject R a) (DerivedCategory.Q.obj K) i) :=
      (localizationResolutionHomologyEquiv R a K i).symm.injective.subsingleton
    exact Subsingleton.elim _ _

/-- 完備性の定義と、具体的な線形Hom複体の非輪状性の比較。 -/
theorem isComplete_iff_localizationResolutionHom_acyclic (a : R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    IsComplete R a (DerivedCategory.Q.obj K) ↔
      (CochainComplex.linearHomComplex R (localizationResolutionComplex R a) K).Acyclic := by
  rw [isComplete_iff_localizationResolutionHomology_subsingleton, acyclic_iff]
  apply forall_congr'
  intro i
  rw [exactAt_iff_isZero_homology, ModuleCat.isZero_iff_subsingleton]

end SerrePositivity.DerivedCompletion

end LocalizationResolutionPart

section LocalizationHomCoordinatesPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory HomologicalComplex CochainComplex.HomComplex
variable (R : Type u) [CommRing R]

/-- 自由telescopeを零次数に置いた複体からのcochainを、自由基底で評価する。 -/
def localizationFreeCochainEquiv (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ) :
    Cochain ((CochainComplex.singleFunctor (ModuleCat R) 0).obj
      (ModuleCat.of R (LocalizationTelescopeFree R))) K n ≃ₗ[R] (ℕ → K.X n) :=
  Cochain.fromSingleLinearEquiv (zero_add n) ≪≫ₗ
    ModuleCat.homLinearEquiv ≪≫ₗ localizationTelescopeHomEquiv R (K.X n)

/-- 自由基底の評価を、零次数から作った標準cochainについて計算する。 -/
@[simp] theorem localizationFreeCochainEquiv_fromSingleMk
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ)
    (f : ModuleCat.of R (LocalizationTelescopeFree R) ⟶ K.X n) :
    localizationFreeCochainEquiv R K n (Cochain.fromSingleMk f (zero_add n)) =
      localizationTelescopeHomEquiv R (K.X n) f.hom := by
  simp [localizationFreeCochainEquiv, Cochain.fromSingleLinearEquiv]
  rfl

/-- 自由基底の評価は、Hom複体の微分をKの成分ごとの微分へ移す。 -/
theorem localizationFreeCochainEquiv_δ (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (n p : ℤ) (x : Cochain ((CochainComplex.singleFunctor (ModuleCat R) 0).obj
      (ModuleCat.of R (LocalizationTelescopeFree R))) K n) :
    localizationFreeCochainEquiv R K p (δ n p x) =
      fun k ↦ K.d n p (localizationFreeCochainEquiv R K n x k) := by
  obtain ⟨f, rfl⟩ := Cochain.fromSingleMk_surjective x n (zero_add n)
  rw [Cochain.δ_fromSingleMk f (zero_add n) p p (zero_add p)]
  rw [localizationFreeCochainEquiv_fromSingleMk, localizationFreeCochainEquiv_fromSingleMk]
  rfl

/-- Telescopeの差分に沿う前合成は、列のa進差分へ移る。 -/
theorem localizationFreeCochainEquiv_precomp (a : R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℤ)
    (x : Cochain ((CochainComplex.singleFunctor (ModuleCat R) 0).obj
      (ModuleCat.of R (LocalizationTelescopeFree R))) K n) :
    localizationFreeCochainEquiv R K n
      ((Cochain.ofHom (localizationPresentationComplex R a).f).comp x (zero_add n)) =
        adicRecurrenceMap a (localizationFreeCochainEquiv R K n x) := by
  obtain ⟨f, rfl⟩ := Cochain.fromSingleMk_surjective x n (zero_add n)
  change localizationFreeCochainEquiv R K n
    ((Cochain.ofHom ((CochainComplex.singleFunctor (ModuleCat R) 0).map
      (ModuleCat.ofHom (localizationTelescopeMap R a)))).comp
        (Cochain.fromSingleMk f (zero_add n)) (zero_add n)) = _
  rw [← Cochain.fromSingleMk_precomp]
  rw [localizationFreeCochainEquiv_fromSingleMk, localizationFreeCochainEquiv_fromSingleMk]
  exact localizationTelescopeHomEquiv_comp R a (K.X n) f.hom

/-- 二項自由分解からのHomの次数n成分を、隣接二次数の列の組へ同定する。 -/
def localizationResolutionCochainEquiv (a : R) (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (m n : ℤ) (h : m + 1 = n) :
    Cochain (localizationResolutionComplex R a) K n ≃ₗ[R]
      (ℕ → K.X m) × (ℕ → K.X n) :=
  mappingConeSourceCochainEquiv R (localizationPresentationComplex R a).f K m n h ≪≫ₗ
    (localizationFreeCochainEquiv R K m).prodCongr (localizationFreeCochainEquiv R K n)

/-- 列の二成分から、元のHom複体のcochainを組み立てる。 -/
theorem localizationResolutionCochainEquiv_symm_apply (a : R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (m n : ℤ) (h : m + 1 = n)
    (α : ℕ → K.X m) (β : ℕ → K.X n) :
    (localizationResolutionCochainEquiv R a K m n h).symm (α, β) =
      (mappingConeSourceCochainEquiv R (localizationPresentationComplex R a).f K m n h).symm
        ((localizationFreeCochainEquiv R K m).symm α,
          (localizationFreeCochainEquiv R K n).symm β) := rfl

/-- 列表示でのHom複体の微分。符号付きのa進差分を含む。 -/
theorem localizationResolutionCochainEquiv_symm_δ (a : R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (m n p : ℤ)
    (h : m + 1 = n) (h' : n + 1 = p) (α : ℕ → K.X m) (β : ℕ → K.X n) :
    δ n p ((localizationResolutionCochainEquiv R a K m n h).symm (α, β)) =
      (localizationResolutionCochainEquiv R a K n p h').symm
        ((fun k ↦ K.d m n (α k)) + p.negOnePow • adicRecurrenceMap a β,
          fun k ↦ K.d n p (β k)) := by
  rw [localizationResolutionCochainEquiv_symm_apply,
    mappingConeSourceCochainEquiv_symm_δ R (localizationPresentationComplex R a).f K m n p h h',
    localizationResolutionCochainEquiv_symm_apply]
  congr 1
  apply Prod.ext
  · apply (localizationFreeCochainEquiv R K n).injective
    simp [localizationFreeCochainEquiv_δ, localizationFreeCochainEquiv_precomp,
      Units.smul_def]
  · apply (localizationFreeCochainEquiv R K p).injective
    simp [localizationFreeCochainEquiv_δ]

end SerrePositivity.DerivedCompletion

end LocalizationHomCoordinatesPart

section LocalizationTowerComparisonPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits HomologicalComplex CochainComplex.HomComplex
open scoped ZeroObject
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R]

/-- 同じ複体をa倍で結ぶ塔のホモトピー逆極限。 -/
abbrev scalarComplexTowerHomotopyLimit (a : R) (K : CochainComplex (ModuleCat.{u} R) ℤ) :=
  complexTowerHomotopyLimit R (constantComplexTower R K) (fun _ ↦ smulId a K)

/-- 自由分解からのHomの各項と、a倍遷移の塔のholimの各項との符号付き同型。 -/
def localizationHomTowerDegreeEquiv (a : R) (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (m n : ℤ) (h : m + 1 = n) :
    (CochainComplex.linearHomComplex R (localizationResolutionComplex R a) K).X n ≃ₗ[R]
      (scalarComplexTowerHomotopyLimit R a K).X n :=
  localizationResolutionCochainEquiv R a K m n h ≪≫ₗ
    LinearEquiv.prodComm R _ _ ≪≫ₗ
      (LinearEquiv.refl R _).prodCongr
        (DistribMulAction.toLinearEquiv R (ℕ → K.X m) (n + 1).negOnePow) ≪≫ₗ
          (complexTowerHomotopyLimitDegreeEquiv R (constantComplexTower R K)
            (fun _ ↦ smulId a K) m n h).symm

/-- 比較は二成分の交換と、前の次数に対する(-1)^(n+1)倍である。 -/
theorem localizationHomTowerDegreeEquiv_coordinates (a : R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (m n : ℤ) (h : m + 1 = n)
    (x : Cochain (localizationResolutionComplex R a) K n) :
    complexTowerHomotopyLimitDegreeEquiv R (constantComplexTower R K)
      (fun _ ↦ smulId a K) m n h (localizationHomTowerDegreeEquiv R a K m n h x) =
        ((localizationResolutionCochainEquiv R a K m n h x).2,
          (n + 1).negOnePow • (localizationResolutionCochainEquiv R a K m n h x).1) := by
  change (complexTowerHomotopyLimitDegreeEquiv R (constantComplexTower R K)
    (fun _ ↦ smulId a K) m n h)
      ((complexTowerHomotopyLimitDegreeEquiv R (constantComplexTower R K)
        (fun _ ↦ smulId a K) m n h).symm _) = _
  exact LinearEquiv.apply_symm_apply _ _

/-- 各項の符号付き同型は、実際の二つの複体の微分を保つ。 -/
theorem localizationHomTowerDegreeEquiv_d (a : R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (m n p : ℤ)
    (h : m + 1 = n) (h' : n + 1 = p)
    (x : Cochain (localizationResolutionComplex R a) K n) :
    (scalarComplexTowerHomotopyLimit R a K).d n p
        (localizationHomTowerDegreeEquiv R a K m n h x) =
      localizationHomTowerDegreeEquiv R a K n p h' (δ n p x) := by
  obtain ⟨⟨α, β⟩, rfl⟩ := (localizationResolutionCochainEquiv R a K m n h).symm.surjective x
  apply (complexTowerHomotopyLimitDegreeEquiv R (constantComplexTower R K)
    (fun _ ↦ smulId a K) n p h').injective
  rw [localizationResolutionCochainEquiv_symm_δ R a K m n p h h']
  simp only [localizationHomTowerDegreeEquiv_coordinates, LinearEquiv.apply_symm_apply]
  apply Prod.ext
  · funext k
    rw [complexTowerHomotopyLimitDegreeEquiv_d_fst R _ _ m n p h h']
    simp only [localizationHomTowerDegreeEquiv_coordinates, LinearEquiv.apply_symm_apply]
  · funext k
    rw [complexTowerHomotopyLimitDegreeEquiv_d_snd R _ _ m n p h h']
    simp only [localizationHomTowerDegreeEquiv_coordinates, LinearEquiv.apply_symm_apply]
    change -(β k - a • β (k + 1)) - K.d m n ((n + 1).negOnePow • α k) =
      (p + 1).negOnePow •
        (K.d m n (α k) + p.negOnePow • (β k - a • β (k + 1)))
    have hd : K.d m n ((n + 1).negOnePow • α k) =
        (n + 1).negOnePow • K.d m n (α k) := by
      simp [Units.smul_def]
    rw [hd, h']
    simp only [Int.negOnePow_succ, Units.neg_smul, smul_add, smul_smul,
      neg_mul, Int.units_mul_self, one_smul]
    abel

/-- 局所化の自由分解からの線形Hom複体と、a倍遷移の塔のholimの実際の複体同型。 -/
def localizationHomTowerIso (a : R) (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    CochainComplex.linearHomComplex R (localizationResolutionComplex R a) K ≅
      scalarComplexTowerHomotopyLimit R a K :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n ↦ (localizationHomTowerDegreeEquiv R a K (n - 1) n (by omega)).toModuleIso)
    (by
      intro n p h
      change n + 1 = p at h
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change (scalarComplexTowerHomotopyLimit R a K).d n p
          (localizationHomTowerDegreeEquiv R a K (n - 1) n (by omega) x) =
        localizationHomTowerDegreeEquiv R a K (p - 1) p (by omega) (δ n p x)
      simpa only [show p - 1 = n by omega] using
        localizationHomTowerDegreeEquiv_d R a K (n - 1) n p (by omega) h x)

/-- 完備対象では、a倍遷移の塔のholimは非輪状。 -/
theorem scalarComplexTowerHomotopyLimit_acyclic_of_isComplete (a : R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : IsComplete R a (DerivedCategory.Q.obj K)) :
    (scalarComplexTowerHomotopyLimit R a K).Acyclic := by
  have h := (isComplete_iff_localizationResolutionHom_acyclic R a K).mp hK
  intro i
  exact (quasiIsoAt_iff_exactAt (localizationHomTowerIso R a K).hom i (h i)).mp inferInstance

/-- a倍遷移の塔のholimの非輪状性は、元の実導来完備性と同値。 -/
theorem isComplete_iff_scalarComplexTowerHomotopyLimit_acyclic (a : R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    IsComplete R a (DerivedCategory.Q.obj K) ↔
      (scalarComplexTowerHomotopyLimit R a K).Acyclic := by
  constructor
  · exact scalarComplexTowerHomotopyLimit_acyclic_of_isComplete R a K
  · intro h
    apply (isComplete_iff_localizationResolutionHom_acyclic R a K).mpr
    intro i
    exact (quasiIsoAt_iff_exactAt (localizationHomTowerIso R a K).inv i (h i)).mp inferInstance

/-- 完備複体のa倍遷移の塔は、実導来圏で零対象となる。 -/
theorem scalarComplexTowerHomotopyLimitObject_isZero_of_isComplete (a : R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : IsComplete R a (DerivedCategory.Q.obj K)) :
    CategoryTheory.Limits.IsZero
      (DerivedCategory.Q.obj (scalarComplexTowerHomotopyLimit R a K)) := by
  have h := scalarComplexTowerHomotopyLimit_acyclic_of_isComplete R a K hK
  have hz := HomologicalComplex.acyclic_of_isZero
    (0 : CochainComplex (ModuleCat.{u} R) ℤ)
    (CategoryTheory.Limits.isZero_zero (CochainComplex (ModuleCat.{u} R) ℤ))
  have : QuasiIso (0 : scalarComplexTowerHomotopyLimit R a K ⟶ 0) := by
    rw [quasiIso_iff]
    intro i
    exact (quasiIsoAt_iff_exactAt _ i (h i)).mpr (hz i)
  exact (DerivedCategory.Q.map_isZero (CategoryTheory.Limits.isZero_zero _)).of_iso
    (asIso (DerivedCategory.Q.map (0 : scalarComplexTowerHomotopyLimit R a K ⟶ 0)))

end SerrePositivity.DerivedCompletion

end LocalizationTowerComparisonPart

section ScalarTowerInversionPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R] (a : R) (K : CochainComplex (ModuleCat.{u} R) ℤ)

/-- On homology, the scalar-transition difference is the ordinary scalar recurrence. -/
lemma scalarComplexTowerHomologyDifference (i : ℤ) :
    complexTowerHomologyDifference R (constantComplexTower R K) (fun _ => smulId a K) i =
      adicRecurrenceMap (M := K.homology i) a := by
  apply LinearMap.ext
  intro x
  funext n
  change x n - homologyMap (smulId a K) i (x (n + 1)) = x n - a • x (n + 1)
  rw [smulId, homologyMap_smul, homologyMap_id]
  rfl

/-- Multiplication by the scalar is invertible on each homology group of the scalar holim. -/
lemma scalarComplexTowerHomotopyLimit_homology_smul_isIso (i : ℤ) :
    IsIso (a • 𝟙 (ModuleCat.of R ((scalarComplexTowerHomotopyLimit R a K).homology i))) := by
  let S := complexTowerMilnorSequence R (constantComplexTower R K) (fun _ => smulId a K) i
  let φ : S ⟶ S :=
    { τ₁ := a • 𝟙 S.X₁
      τ₂ := a • 𝟙 S.X₂
      τ₃ := a • 𝟙 S.X₃
      comm₁₂ := by simp
      comm₂₃ := by simp }
  have h₁ : IsIso φ.τ₁ := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    change Function.Bijective (fun x : complexTowerHomologyLimOne R
      (constantComplexTower R K) (fun _ => smulId a K) (i - 1) => a • x)
    have h (d : (ℕ → K.homology (i - 1)) →ₗ[R] (ℕ → K.homology (i - 1)))
        (hd : d = adicRecurrenceMap a) :
        Function.Bijective (fun x : (ℕ → K.homology (i - 1)) ⧸ d.range => a • x) := by
      subst d
      exact (adicRecurrenceCokernelScalarEquiv (M := K.homology (i - 1)) a).bijective
    exact h _ (scalarComplexTowerHomologyDifference R a K (i - 1))
  have h₃ : IsIso φ.τ₃ := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    change Function.Bijective (fun x : (complexTowerHomologyDifference R
      (constantComplexTower R K) (fun _ => smulId a K) i).ker => a • x)
    rw [scalarComplexTowerHomologyDifference]
    exact (adicRecurrenceKernelScalarEquiv (M := K.homology i) a).bijective
  have := h₁
  have := h₃
  exact ShortComplex.isIso₂_of_shortExact_of_isIso₁₃ φ
    (complexTowerMilnorSequence_shortExact R _ _ i)
    (complexTowerMilnorSequence_shortExact R _ _ i)

/-- Multiplication by the scalar is a quasi-isomorphism on the actual scalar holim complex. -/
lemma scalarComplexTowerHomotopyLimit_smul_quasiIso :
    QuasiIso (smulId a (scalarComplexTowerHomotopyLimit R a K)) := by
  rw [quasiIso_iff]
  intro i
  rw [quasiIsoAt_iff_isIso_homologyMap, smulId, homologyMap_smul, homologyMap_id]
  exact scalarComplexTowerHomotopyLimit_homology_smul_isIso R a K i

/-- Every nonnegative scalar power is a quasi-isomorphism on the scalar holim. -/
lemma scalarComplexTowerHomotopyLimit_pow_smul_quasiIso (n : ℕ) :
    QuasiIso (smulId (a ^ n) (scalarComplexTowerHomotopyLimit R a K)) := by
  induction n with
  | zero =>
    simp only [pow_zero, smulId, one_smul]
    infer_instance
  | succ n ih =>
    have he : smulId (a ^ (n + 1)) (scalarComplexTowerHomotopyLimit R a K) =
        smulId (a ^ n) (scalarComplexTowerHomotopyLimit R a K) ≫
          smulId a (scalarComplexTowerHomotopyLimit R a K) := by
      simp [smulId, pow_succ, smul_smul, mul_comm]
    rw [he]
    have := ih
    have := scalarComplexTowerHomotopyLimit_smul_quasiIso R a K
    infer_instance

/-- All power-Koszul quotients of the residual scalar holim vanish in the derived category. -/
lemma scalarComplexTowerHomotopyLimit_koszul_isZero (n : ℕ) :
    IsZero (DerivedCategory.Q.obj
      (complexPowerKoszulStage R a (scalarComplexTowerHomotopyLimit R a K) n)) := by
  have := scalarComplexTowerHomotopyLimit_pow_smul_quasiIso R a K n
  exact (CategoryTheory.Pretriangulated.Triangle.isZero₃_iff_isIso₁
    (DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle
      (smulId (a ^ n) (scalarComplexTowerHomotopyLimit R a K))))
    (DerivedCategory.mappingCone_triangle_distinguished _)).mpr (by
      change IsIso (DerivedCategory.Q.map (smulId (a ^ n) (scalarComplexTowerHomotopyLimit R a K)))
      infer_instance)

end SerrePositivity.DerivedCompletion

end ScalarTowerInversionPart
