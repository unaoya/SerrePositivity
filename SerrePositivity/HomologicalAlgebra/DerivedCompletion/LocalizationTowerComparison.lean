module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.LocalizationHomCoordinates
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.TowerCoordinates
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ConstantTower

/-! # 局所化の自由分解からのHomとa倍遷移の塔の比較 -/

@[expose] public noncomputable section
universe u
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
