module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.TowerComplete
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.TowerProjection

/-! # 任意複体の主元Koszul完備化の具体的な関手

各段Cone(aⁿ:K→K)の塔を作り、既存の複体の直積と差分の錐によるholimを使う。
有界性・射影性・各項の通常完備性は要求しない。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits HomologicalComplex
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R]

/-- 任意の複体の第n主元Koszul剰余。環商による導来底変換とは区別する。 -/
abbrev complexPowerKoszulStage (a : R) (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℕ) :=
  CochainComplex.mappingCone (smulId (a ^ n) K)

/-- 冪を一段下げる標準のKoszul遷移。 -/
def complexPowerKoszulTransition (a : R) (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℕ) :
    complexPowerKoszulStage R a K (n + 1) ⟶ complexPowerKoszulStage R a K n :=
  homotopyCofiber.mapArrowHom (smulId (a ^ (n + 1)) K) (smulId (a ^ n) K)
    (fun j ↦ ⟨j - 1, by simp⟩)
    (Arrow.homMk (a • 𝟙 K) (𝟙 K) (by simp [smulId, smul_smul, pow_succ, mul_comm]))

/-- 遷移写像は係数複体の射に自然。 -/
@[reassoc] theorem complexPowerKoszulTransition_naturality (a : R)
    {K L : CochainComplex (ModuleCat.{u} R) ℤ} (f : K ⟶ L) (n : ℕ) :
    (scalarConeFunctor (a ^ (n + 1))).map f ≫ complexPowerKoszulTransition R a L n =
      complexPowerKoszulTransition R a K n ≫ (scalarConeFunctor (a ^ n)).map f := by
  dsimp only [scalarConeFunctor, complexPowerKoszulTransition]
  rw [← homotopyCofiber.mapArrowHom_comp, ← homotopyCofiber.mapArrowHom_comp]
  congr 1
  ext <;> simp

/-- 任意複体の主元Koszul段の可算直積を関手として構成する。 -/
def complexPowerKoszulProductFunctor (a : R) :
    CochainComplex (ModuleCat.{u} R) ℤ ⥤ CochainComplex (ModuleCat.{u} R) ℤ where
  obj K := piObj (complexPowerKoszulStage R a K)
  map {K L} f := complexTowerProductMap R
    (K := complexPowerKoszulStage R a K) (L := complexPowerKoszulStage R a L)
    (fun n ↦ (scalarConeFunctor (a ^ n)).map f)
  map_id K := by
    apply Pi.hom_ext
    intro n
    simp only [complexTowerProductMap_projection, CategoryTheory.Functor.map_id]
    exact Category.comp_id _
  map_comp f g := by
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, complexTowerProductMap_projection,
      CategoryTheory.Functor.map_comp]
    simp only [← Category.assoc]
    rw [complexTowerProductMap_projection]

/-- 直積上の差分を、Arrow圏に値を持つ関手としてまとめる。 -/
def complexPowerKoszulDifferenceFunctor (a : R) :
    CochainComplex (ModuleCat.{u} R) ℤ ⥤ Arrow (CochainComplex (ModuleCat.{u} R) ℤ) where
  obj K := Arrow.mk (complexTowerDifference R (complexPowerKoszulStage R a K)
    (complexPowerKoszulTransition R a K))
  map {K L} f := Arrow.homMk ((complexPowerKoszulProductFunctor R a).map f)
    ((complexPowerKoszulProductFunctor R a).map f)
    (complexTowerDifference_naturality R _ _ _
      (fun n ↦ (complexPowerKoszulTransition_naturality R a f n).symm))
  map_id K := by
    apply Arrow.hom_ext <;> exact (complexPowerKoszulProductFunctor R a).map_id K
  map_comp f g := by
    apply Arrow.hom_ext <;> exact (complexPowerKoszulProductFunctor R a).map_comp f g

/-- Arrow圏上の標準の写像錐関手。 -/
def cochainMappingConeFunctor :
    Arrow (CochainComplex (ModuleCat.{u} R) ℤ) ⥤ CochainComplex (ModuleCat.{u} R) ℤ where
  obj X := CochainComplex.mappingCone X.hom
  map f := homotopyCofiber.mapArrowHom _ _ (fun j ↦ ⟨j - 1, by simp⟩) f
  map_id X := homotopyCofiber.mapArrowHom_id X.hom (fun j ↦ ⟨j - 1, by simp⟩)
  map_comp f g := homotopyCofiber.mapArrowHom_comp _ _ _ (fun j ↦ ⟨j - 1, by simp⟩) f g

/-- 任意複体の主元Koszul完備化の具体的な複体関手。 -/
def complexCompletionFunctor (a : R) :
    CochainComplex (ModuleCat.{u} R) ℤ ⥤ CochainComplex (ModuleCat.{u} R) ℤ :=
  complexPowerKoszulDifferenceFunctor R a ⋙ cochainMappingConeFunctor R ⋙
    shiftFunctor _ (-1 : ℤ)

/-- 完備化候補の標準の実導来対象。 -/
def complexCompletionObject (a : R) (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    ConcreteDerivedCategory R := DerivedCategory.Q.obj ((complexCompletionFunctor R a).obj K)

/-- 各段の座標の零ホモトピーにより、一般複体の各Koszul剰余は導来完備。 -/
theorem complexPowerKoszulStage_isComplete (a : R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℕ) :
    IsComplete R a (DerivedCategory.Q.obj (complexPowerKoszulStage R a K n)) :=
  isComplete_Q_of_scalar_pow_nullHomotopic R a _ n (scalarConeCoordinateNullHomotopy (a ^ n) K)

/-- 完備化候補は、実際の導来圏でa完備である。 -/
theorem complexCompletionObject_isComplete (a : R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) : IsComplete R a (complexCompletionObject R a K) :=
  isComplete_complexTowerHomotopyLimitObject_of_stages R a
    (complexPowerKoszulStage R a K) (complexPowerKoszulTransition R a K)
    (complexPowerKoszulStage_isComplete R a K)

/-- 各段への標準包含はKoszul遷移と両立する。 -/
theorem complexPowerKoszulInclusion_compatible (a : R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℕ) :
    CochainComplex.mappingCone.inr (smulId (a ^ (n + 1)) K) ≫
      complexPowerKoszulTransition R a K n =
        CochainComplex.mappingCone.inr (smulId (a ^ n) K) := by
  simp [CochainComplex.mappingCone.inr, complexPowerKoszulTransition,
    homotopyCofiber.mapArrowHom, homotopyCofiber.inr_desc]

/-- 任意複体からKoszul冪塔のホモトピー逆極限への標準射。 -/
def complexCompletionUnit (a : R) (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    K ⟶ (complexCompletionFunctor R a).obj K :=
  complexTowerCompatibleLift R _ _ K
    (fun n ↦ CochainComplex.mappingCone.inr (smulId (a ^ n) K))
    (complexPowerKoszulInclusion_compatible R a K)

/-- 標準射は各Koszul段への包含を復元する。 -/
theorem complexCompletionUnit_comp_projection (a : R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (n : ℕ) :
    complexCompletionUnit R a K ≫
      complexTowerProjection R (complexPowerKoszulStage R a K)
        (complexPowerKoszulTransition R a K) ≫
          Pi.π (complexPowerKoszulStage R a K) n =
            CochainComplex.mappingCone.inr (smulId (a ^ n) K) := by
  rw [← Category.assoc, complexCompletionUnit,
    complexTowerCompatibleLift_comp_projection, Pi.lift_comp_π]

/-- 標準射を実導来圏へ移す。 -/
def complexCompletionUnitObject (a : R) (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    DerivedCategory.Q.obj K ⟶ complexCompletionObject R a K :=
  DerivedCategory.Q.map (complexCompletionUnit R a K)

end SerrePositivity.DerivedCompletion
