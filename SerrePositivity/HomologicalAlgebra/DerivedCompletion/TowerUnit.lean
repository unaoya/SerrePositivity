module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.KoszulTower
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift

/-! # 両立する写像からホモトピー逆極限への標準写像

厳密に両立するKoszul複体への包含から、実際のmapping coneへ写像を構成する。
H⁰の環構造や導来完備性はまだ仮定・主張しない。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits CategoryTheory.Preadditive
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R]

/-- 差分写像との合成が零となる写像を、実際のホモトピー逆極限へ持ち上げる。 -/
def complexTowerHomotopyLimitLift
    (K : ℕ → CochainComplex (ModuleCat.{u} R) ℤ) (t : ∀ n, K (n + 1) ⟶ K n)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (g : P ⟶ piObj K)
    (hg : g ≫ complexTowerDifference R K t = 0) :
    P ⟶ complexTowerHomotopyLimit R K t :=
  (CochainComplex.HomComplex.Cocycle.equivHomShift).symm
    (CochainComplex.mappingCone.liftCocycle (complexTowerDifference R K t)
      (CochainComplex.HomComplex.Cocycle.ofHom g) 0 (show (-1 : ℤ) + 1 = 0 by norm_num) (by
        simp only [CochainComplex.HomComplex.δ_zero, zero_add,
          CochainComplex.HomComplex.Cocycle.ofHom_coe,
          ← CochainComplex.HomComplex.Cochain.ofHom_comp, hg,
          CochainComplex.HomComplex.Cochain.ofHom_zero]))

/-- 持ち上げのmapping coneへの第1成分は、指定した写像そのもの。 -/
theorem complexTowerHomotopyLimitLift_fst
    (K : ℕ → CochainComplex (ModuleCat.{u} R) ℤ) (t : ∀ n, K (n + 1) ⟶ K n)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (g : P ⟶ piObj K)
    (hg : g ≫ complexTowerDifference R K t = 0) :
    ((CochainComplex.HomComplex.Cocycle.equivHomShift
      (complexTowerHomotopyLimitLift R K t P g hg)).1).comp
        (CochainComplex.mappingCone.fst (complexTowerDifference R K t)).1
          (show (-1 : ℤ) + 1 = 0 by norm_num) = CochainComplex.HomComplex.Cochain.ofHom g := by
  simp [complexTowerHomotopyLimitLift]

/-- 持ち上げのmapping coneへの第2成分は零。 -/
theorem complexTowerHomotopyLimitLift_snd
    (K : ℕ → CochainComplex (ModuleCat.{u} R) ℤ) (t : ∀ n, K (n + 1) ⟶ K n)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (g : P ⟶ piObj K)
    (hg : g ≫ complexTowerDifference R K t = 0) :
    ((CochainComplex.HomComplex.Cocycle.equivHomShift
      (complexTowerHomotopyLimitLift R K t P g hg)).1).comp
        (CochainComplex.mappingCone.snd (complexTowerDifference R K t))
          (add_zero (-1 : ℤ)) = 0 := by
  simp [complexTowerHomotopyLimitLift]

/-- 隣接段に関して両立する写像の族をホモトピー逆極限へ移す。 -/
def complexTowerCompatibleLift
    (K : ℕ → CochainComplex (ModuleCat.{u} R) ℤ) (t : ∀ n, K (n + 1) ⟶ K n)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (g : ∀ n, P ⟶ K n)
    (hg : ∀ n, g (n + 1) ≫ t n = g n) : P ⟶ complexTowerHomotopyLimit R K t :=
  complexTowerHomotopyLimitLift R K t P (Pi.lift g) (by
    apply Pi.hom_ext
    intro n
    simp only [assoc, complexTowerDifference_projection, comp_sub, Pi.lift_comp_π, zero_comp]
    rw [← assoc, Pi.lift_comp_π, hg, sub_self])

/-- 標準持ち上げを各段へ射影すると、指定した写像に戻る。 -/
theorem complexTowerCompatibleLift_projection
    (K : ℕ → CochainComplex (ModuleCat.{u} R) ℤ) (t : ∀ n, K (n + 1) ⟶ K n)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (g : ∀ n, P ⟶ K n)
    (hg : ∀ n, g (n + 1) ≫ t n = g n) (n : ℕ) :
    (((CochainComplex.HomComplex.Cocycle.equivHomShift
      (complexTowerCompatibleLift R K t P g hg)).1).comp
        (CochainComplex.mappingCone.fst (complexTowerDifference R K t)).1
          (show (-1 : ℤ) + 1 = 0 by norm_num)).comp
            (CochainComplex.HomComplex.Cochain.ofHom (Pi.π K n)) (zero_add 0) =
              CochainComplex.HomComplex.Cochain.ofHom (g n) := by
  simp only [complexTowerCompatibleLift, complexTowerHomotopyLimitLift_fst,
    ← CochainComplex.HomComplex.Cochain.ofHom_comp, Pi.lift_comp_π]

/-- 環を零次数に置いた複体からKoszul複体への包含。 -/
def koszulComplexInclusion : {e : ℕ} → (a : Fin e → R) →
    ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R) ⟶
      koszulComplex a)
  | 0, _ => 𝟙 _
  | e + 1, a => koszulComplexInclusion (Fin.init a) ≫
    CochainComplex.mappingCone.inr (smulId (a (Fin.last e)) (koszulComplex (Fin.init a)))

/-- 座標を倍数へ変えるKoszul写像は、零次数環からの包含と可換する。 -/
theorem koszulComplexInclusion_mapOfMul : ∀ {e : ℕ} (a b c : Fin e → R)
    (h : ∀ i, a i = b i * c i),
    koszulComplexInclusion R a ≫ koszulComplexMapOfMul R a b c h =
      koszulComplexInclusion R b
  | 0, _, _, _, _ => by simp [koszulComplexInclusion, koszulComplexMapOfMul, koszulComplex]
  | e + 1, a, b, c, h => by
    simp only [koszulComplexInclusion, koszulComplexMapOfMul]
    simp only [assoc, CochainComplex.mappingCone.inr,
      HomologicalComplex.homotopyCofiber.mapArrowHom,
      HomologicalComplex.homotopyCofiber.inr_desc, Arrow.homMk_right]
    rw [← assoc, koszulComplexInclusion_mapOfMul]

/-- 各冪のKoszul複体への包含は、逆系の遷移と可換する。 -/
theorem powerKoszulInclusion_compatible {e : ℕ} (a : Fin e → R) (n : ℕ) :
    koszulComplexInclusion R (fun i ↦ a i ^ (n + 1)) ≫ powerKoszulTransition R a n =
      koszulComplexInclusion R (fun i ↦ a i ^ n) :=
  koszulComplexInclusion_mapOfMul R _ _ _ _

/-- Koszul逆系による完備化の候補複体への標準写像。 -/
def koszulCompletionUnit {e : ℕ} (a : Fin e → R) :
    (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R) ⟶
      koszulCompletionComplex R a :=
  complexTowerCompatibleLift R _ _ _ (fun n ↦ koszulComplexInclusion R (fun i ↦ a i ^ n))
    (powerKoszulInclusion_compatible R a)

/-- 標準写像を実際の導来圏へ移す。 -/
def koszulCompletionUnitObject {e : ℕ} (a : Fin e → R) :
    (moduleObjectFunctor R).obj (ModuleCat.of R R) ⟶ koszulCompletionObject R a :=
  DerivedCategory.Q.map (koszulCompletionUnit R a)

end SerrePositivity.DerivedCompletion
