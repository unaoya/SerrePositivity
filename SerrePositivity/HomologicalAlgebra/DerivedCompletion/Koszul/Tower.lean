module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Tower.HolimModel
public import SerrePositivity.CommutativeAlgebra.Koszul.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexShift
public import SerrePositivity.CommutativeAlgebra.Koszul.Resolution
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ConeAPI

/-! # 元の冪の Koszul 複体の塔と H⁰

## 概要

指定した元の各冪の Koszul 複体と、冪を一段下げる鎖写像の逆系（`powerKoszulTower`）を作り、その直積と差分の錐から完備化の候補 `koszulCompletionComplex` を作る。標準の包含が誘導する H⁰ の全射とその核を計算して各段の H⁰ を商環と同定し、遷移が商環の標準の遷移と一致することを示す。両立する写像からホモトピー逆極限への標準写像と、その標準射影（連結射の符号を含む）を与える。

## 方針

各冪の段を Mathlib の写像錐で作り、H⁰ の同定は標準の包含で正規化する。正則性は仮定しない。

## 規約

導来完備性は `Koszul/Complete`、H⁰ の環構造と普遍性は `Principal/*`・`Pair/*`。旧 `KoszulTower`・`KoszulCanonicalZero`・`KoszulStageZero`・`TowerUnit`・`TowerProjection`。

## 使われ方

`Koszul/Complete`・`Koszul/Milnor`、`ComplexCompletion/*`、`Principal/*`・`Pair/*`。
-/

@[expose] public noncomputable section

universe u

section KoszulTowerPart

namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Category CategoryTheory.Preadditive
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R]

/-- 各座標を指定した倍数へ変えるKoszul複体の写像。 -/
def koszulComplexMapOfMul : {e : ℕ} → (a b c : Fin e → R) →
    (∀ i, a i = b i * c i) → (koszulComplex a ⟶ koszulComplex b)
  | 0, _, _, _, _ => 𝟙 _
  | e + 1, a, b, c, h =>
    let g := koszulComplexMapOfMul (Fin.init a) (Fin.init b) (Fin.init c)
      (fun i ↦ h i.castSucc)
    HomologicalComplex.homotopyCofiber.mapArrowHom
      (smulId (a (Fin.last e)) (koszulComplex (Fin.init a)))
      (smulId (b (Fin.last e)) (koszulComplex (Fin.init b))) (fun j ↦ ⟨j - 1, by simp⟩)
      (Arrow.homMk (c (Fin.last e) • g) g (by
        change (c (Fin.last e) • g) ≫ (b (Fin.last e) • 𝟙 _) =
          (a (Fin.last e) • 𝟙 _) ≫ g
        simp only [Linear.comp_smul, Linear.smul_comp, id_comp, comp_id, smul_smul, h]))

/-- 指定した元の列の各冪を取ったKoszul複体の逆系。 -/
def powerKoszulTower {e : ℕ} (a : Fin e → R) (n : ℕ) :
    CochainComplex (ModuleCat.{u} R) ℤ := koszulComplex (fun i ↦ a i ^ n)

/-- 冪を一段下げるKoszul複体の鎖写像。 -/
def powerKoszulTransition {e : ℕ} (a : Fin e → R) (n : ℕ) :
    powerKoszulTower R a (n + 1) ⟶ powerKoszulTower R a n :=
  koszulComplexMapOfMul R (fun i ↦ a i ^ (n + 1)) (fun i ↦ a i ^ n) a
    (fun i ↦ pow_succ (a i) n)

/-- 冪のKoszul複体のホモトピー逆極限による完備化の候補モデル。 -/
def koszulCompletionComplex {e : ℕ} (a : Fin e → R) :
    CochainComplex (ModuleCat.{u} R) ℤ :=
  complexTowerHomotopyLimit R (powerKoszulTower R a) (powerKoszulTransition R a)

/-- 上の候補モデルを標準導来圏へ移した対象。 -/
def koszulCompletionObject {e : ℕ} (a : Fin e → R) : ConcreteDerivedCategory R :=
  DerivedCategory.Q.obj (koszulCompletionComplex R a)

end SerrePositivity.DerivedCompletion

end KoszulTowerPart

section TowerUnitPart

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

end TowerUnitPart

section KoszulCanonicalZeroPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
variable (R : Type u) [CommRing R]

/-- 零次数環からKoszulのH⁰への標準写像。 -/
def koszulH0Unit {e : ℕ} (a : Fin e → R) : R →ₗ[R] (koszulComplex a).homology 0 :=
  (HomologicalComplex.homologyMap (koszulComplexInclusion R a) 0).hom.comp
    (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0
      (ModuleCat.of R R)).inv.hom

/-- 一座標増やしたときの標準写像の式。 -/
theorem koszulH0Unit_succ {e : ℕ} (a : Fin (e + 1) → R) :
    koszulH0Unit R a =
      (HomologicalComplex.homologyMap (CochainComplex.mappingCone.inr
        (smulId (a (Fin.last e)) (koszulComplex (Fin.init a)))) 0).hom.comp
          (koszulH0Unit R (Fin.init a)) := by
  simp only [koszulH0Unit, koszulComplexInclusion, HomologicalComplex.homologyMap_comp,
    ModuleCat.hom_comp, LinearMap.comp_assoc]

/-- KoszulのH⁰は、標準包含の像で生成される。 -/
theorem koszulH0Unit_surjective : ∀ {e : ℕ} (a : Fin e → R),
    Function.Surjective (koszulH0Unit R a)
  | 0, a => by
    simp only [koszulH0Unit, koszulComplexInclusion, HomologicalComplex.homologyMap_id,
      ModuleCat.hom_id, LinearMap.id_comp]
    exact (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0
      (ModuleCat.of R R)).toLinearEquiv.symm.surjective
  | e + 1, a => by
    have h1 := koszulComplex_isZero_homology_of_pos (Fin.init a) 1 one_pos
    have h3 := Cone.exact₃ (smulId (a (Fin.last e)) (koszulComplex (Fin.init a))) 0 1 rfl
    have hj := h3.epi_f (h1.eq_zero_of_tgt _)
    rw [koszulH0Unit_succ]
    exact ((ModuleCat.epi_iff_surjective _).mp hj).comp
      (koszulH0Unit_surjective (Fin.init a))

private theorem ker_comp_of_scalar_range
    {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (u : R →ₗ[R] M) (hu : Function.Surjective u) (j : M →ₗ[R] N) (a : R)
    (hj : LinearMap.range (a • LinearMap.id : M →ₗ[R] M) = j.ker) :
    (j.comp u).ker = u.ker ⊔ Submodule.span R {a} := by
  apply le_antisymm
  · intro r hr
    have hur : u r ∈ LinearMap.range (a • LinearMap.id : M →ₗ[R] M) := by
      rw [hj]
      exact hr
    obtain ⟨m, hm⟩ := hur
    obtain ⟨s, hs⟩ := hu m
    have hdiff : r - a * s ∈ u.ker := by
      change u (r - a * s) = 0
      rw [map_sub, show a * s = a • s from rfl, map_smul, hs]
      change u r - a • m = 0
      rw [show a • m = u r from hm, sub_self]
    have hprod : a * s ∈ Submodule.span R {a} := by
      exact Submodule.mem_span_singleton.mpr ⟨s, by simp [smul_eq_mul, mul_comm]⟩
    exact sub_add_cancel r (a * s) ▸ (u.ker ⊔ Submodule.span R {a}).add_mem
      ((show u.ker ≤ u.ker ⊔ Submodule.span R {a} from le_sup_left) hdiff)
      ((show Submodule.span R {a} ≤ u.ker ⊔ Submodule.span R {a} from le_sup_right) hprod)
  · apply sup_le
    · intro r hr
      change j (u r) = 0
      rw [show u r = 0 from hr, map_zero]
    · apply Submodule.span_le.mpr
      intro r hr
      rw [Set.mem_singleton_iff] at hr
      subst r
      change u a ∈ j.ker
      rw [← hj]
      refine ⟨u 1, ?_⟩
      change a • u 1 = u a
      rw [← map_smul, smul_eq_mul, mul_one]

/-- 標準包含からH⁰への写像の核は、列の生成イデアル。 -/
theorem koszulH0Unit_ker : ∀ {e : ℕ} (a : Fin e → R),
    (koszulH0Unit R a).ker = Ideal.span (Set.range a)
  | 0, a => by
    rw [Set.range_eq_empty, Ideal.span_empty]
    apply LinearMap.ker_eq_bot.mpr
    simp only [koszulH0Unit, koszulComplexInclusion, HomologicalComplex.homologyMap_id,
      ModuleCat.hom_id, LinearMap.id_comp]
    exact (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0
      (ModuleCat.of R R)).toLinearEquiv.symm.injective
  | e + 1, a => by
    have h2 := Cone.exact₂ (smulId (a (Fin.last e)) (koszulComplex (Fin.init a))) 0
    have hrk := (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mp h2
    have hmap : HomologicalComplex.homologyMap
        (smulId (a (Fin.last e)) (koszulComplex (Fin.init a))) 0 =
      a (Fin.last e) • 𝟙 ((koszulComplex (Fin.init a)).homology 0) := by
      rw [smulId, homologyMap_smul, HomologicalComplex.homologyMap_id]
    change (HomologicalComplex.homologyMap
      (smulId (a (Fin.last e)) (koszulComplex (Fin.init a))) 0).hom.range =
      (HomologicalComplex.homologyMap (CochainComplex.mappingCone.inr
        (smulId (a (Fin.last e)) (koszulComplex (Fin.init a)))) 0).hom.ker at hrk
    rw [hmap] at hrk
    rw [koszulH0Unit_succ, ker_comp_of_scalar_range R _
      (koszulH0Unit_surjective R (Fin.init a)) _ _ hrk, koszulH0Unit_ker]
    have hrange : Set.range a = insert (a (Fin.last e)) (Set.range (Fin.init a)) := by
      have h := Fin.range_snoc (Fin.init a) (a (Fin.last e))
      rwa [Fin.snoc_init_self] at h
    rw [hrange]
    change _ = Submodule.span R _
    rw [Submodule.span_insert, sup_comm]

/-- 標準包含の像を商の標準元へ送る、正規化されたH⁰の同型。 -/
def koszulCanonicalH0Equiv {e : ℕ} (a : Fin e → R) :
    (koszulComplex a).homology 0 ≃ₗ[R] R ⧸ Ideal.span (Set.range a) :=
  (LinearMap.quotKerEquivOfSurjective (koszulH0Unit R a)
    (koszulH0Unit_surjective R a)).symm.trans
      (Submodule.quotEquivOfEq _ _ (koszulH0Unit_ker R a))

@[simp] theorem koszulCanonicalH0Equiv_unit {e : ℕ} (a : Fin e → R) (r : R) :
    koszulCanonicalH0Equiv R a (koszulH0Unit R a r) = Ideal.Quotient.mk _ r := by
  simp only [koszulCanonicalH0Equiv, LinearEquiv.trans_apply,
    LinearMap.quotKerEquivOfSurjective_symm_apply]
  exact Submodule.quotEquivOfEq_mk _ _ _ r

/-- 座標の倍数によるKoszul写像は標準包含を保つ。 -/
theorem koszulH0Unit_mapOfMul {e : ℕ} (a b c : Fin e → R)
    (h : ∀ i, a i = b i * c i) (r : R) :
    (HomologicalComplex.homologyMap (koszulComplexMapOfMul R a b c h) 0).hom
      (koszulH0Unit R a r) = koszulH0Unit R b r := by
  have hcomp := congrArg (fun f ↦ HomologicalComplex.homologyMap f 0)
    (koszulComplexInclusion_mapOfMul R a b c h)
  rw [HomologicalComplex.homologyMap_comp] at hcomp
  exact LinearMap.congr_fun (congrArg (fun f ↦ f.hom.comp
    (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0
      (ModuleCat.of R R)).inv.hom) hcomp) r

end SerrePositivity.DerivedCompletion

end KoszulCanonicalZeroPart

section KoszulStageZeroPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory
variable (R : Type u) [CommRing R]

/-- 各元のn乗で生成されるイデアル。一般のイデアル冪と区別する。 -/
def powerKoszulIdeal {e : ℕ} (a : Fin e → R) (n : ℕ) : Ideal R :=
  Ideal.span (Set.range (fun i ↦ a i ^ n))

/-- 各段のH⁰の商加群との同型。正則性やねじれの有界性は不要。
標準包含の像を商の標準元に送る同型を使用する。 -/
def powerKoszulStageH0Equiv {e : ℕ} (a : Fin e → R) (n : ℕ) :
    (powerKoszulTower R a n).homology 0 ≃ₗ[R] R ⧸ powerKoszulIdeal R a n :=
  koszulCanonicalH0Equiv R (fun i ↦ a i ^ n)

@[simp] theorem powerKoszulStageH0Equiv_unit {e : ℕ} (a : Fin e → R) (n : ℕ) (r : R) :
    powerKoszulStageH0Equiv R a n (koszulH0Unit R (fun i ↦ a i ^ n) r) =
      Ideal.Quotient.mk _ r := koszulCanonicalH0Equiv_unit R _ r

/-- 元の冪を進めると、生成されるイデアルは小さくなる。 -/
theorem powerKoszulIdeal_antitone {e : ℕ} (a : Fin e → R) :
    Antitone (powerKoszulIdeal R a) := by
  intro m n hmn
  apply Ideal.span_le.mpr
  rintro z ⟨i, rfl⟩
  change a i ^ n ∈ powerKoszulIdeal R a m
  have heq : n = m + (n - m) := (Nat.add_sub_of_le hmn).symm
  rw [heq, pow_add]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_range_self i))

/-- 冪による商環の標準的な遷移写像。 -/
def powerKoszulQuotientTransition {e : ℕ} (a : Fin e → R) (n : ℕ) :
    R ⧸ powerKoszulIdeal R a (n + 1) →+* R ⧸ powerKoszulIdeal R a n :=
  Ideal.Quotient.factor (powerKoszulIdeal_antitone R a (Nat.le_succ n))

@[simp] theorem powerKoszulQuotientTransition_mk {e : ℕ} (a : Fin e → R) (n : ℕ) (r : R) :
    powerKoszulQuotientTransition R a n (Ideal.Quotient.mk _ r) =
      Ideal.Quotient.mk _ r := rfl

/-- 商環の遷移は全射。高次Koszulホモロジーの遷移にはこの結論を使用しない。 -/
theorem powerKoszulQuotientTransition_surjective {e : ℕ} (a : Fin e → R) (n : ℕ) :
    Function.Surjective (powerKoszulQuotientTransition R a n) :=
  Ideal.Quotient.factor_surjective _

/-- KoszulのH⁰遷移は、正規化された同定の下で商環の標準遷移と一致する。 -/
theorem powerKoszulStageH0Equiv_transition {e : ℕ} (a : Fin e → R) (n : ℕ)
    (x : (powerKoszulTower R a (n + 1)).homology 0) :
    powerKoszulStageH0Equiv R a n
      ((HomologicalComplex.homologyMap (powerKoszulTransition R a n) 0).hom x) =
      powerKoszulQuotientTransition R a n
        (powerKoszulStageH0Equiv R a (n + 1) x) := by
  obtain ⟨r, rfl⟩ := koszulH0Unit_surjective R (fun i ↦ a i ^ (n + 1)) x
  change koszulCanonicalH0Equiv R (fun i ↦ a i ^ n)
    ((HomologicalComplex.homologyMap (koszulComplexMapOfMul R
      (fun i ↦ a i ^ (n + 1)) (fun i ↦ a i ^ n) a
      (fun i ↦ pow_succ (a i) n)) 0).hom
      (koszulH0Unit R (fun i ↦ a i ^ (n + 1)) r)) =
    powerKoszulQuotientTransition R a n
      (koszulCanonicalH0Equiv R (fun i ↦ a i ^ (n + 1))
        (koszulH0Unit R (fun i ↦ a i ^ (n + 1)) r))
  rw [koszulH0Unit_mapOfMul, koszulCanonicalH0Equiv_unit, koszulCanonicalH0Equiv_unit]
  rfl

/-- H⁰に誘導されるKoszul遷移は全射。負次数についての主張ではない。 -/
theorem powerKoszulTransition_homology_zero_surjective {e : ℕ} (a : Fin e → R) (n : ℕ) :
    Function.Surjective (HomologicalComplex.homologyMap
      (powerKoszulTransition R a n) 0).hom := by
  intro x
  obtain ⟨r, rfl⟩ := koszulH0Unit_surjective R (fun i ↦ a i ^ n) x
  refine ⟨koszulH0Unit R (fun i ↦ a i ^ (n + 1)) r, ?_⟩
  exact koszulH0Unit_mapOfMul R _ _ _ _ r

end SerrePositivity.DerivedCompletion

end KoszulStageZeroPart

section TowerProjectionPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
variable (R : Type u) [CommRing R]

/-- ホモトピー逆極限の候補から直積への、元を保つ標準射影。 -/
def complexTowerProjection
    (K : ℕ → CochainComplex (ModuleCat.{u} R) ℤ) (t : ∀ n, K (n + 1) ⟶ K n) :
    complexTowerHomotopyLimit R K t ⟶ piObj K :=
  CochainComplex.mappingCocone.fst (complexTowerDifference R K t)

/-- 差分を消す持ち上げは、標準射影によって元の写像へ戻る。 -/
theorem complexTowerHomotopyLimitLift_projection
    (K : ℕ → CochainComplex (ModuleCat.{u} R) ℤ) (t : ∀ n, K (n + 1) ⟶ K n)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (g : P ⟶ piObj K)
    (hg : g ≫ complexTowerDifference R K t = 0) :
    complexTowerHomotopyLimitLift R K t P g hg ≫ complexTowerProjection R K t = g := by
  apply HomologicalComplex.hom_ext
  intro i
  have h := congrArg (fun γ ↦ γ.v i i (add_zero i))
    (complexTowerHomotopyLimitLift_fst R K t P g hg)
  simp only [CochainComplex.HomComplex.Cochain.comp_v
    (n₁ := -1) (n₂ := 1) (n₁₂ := 0) _ _ _ i (i + -1) i rfl (by omega)] at h
  change ((CochainComplex.HomComplex.Cochain.ofHom
    (complexTowerHomotopyLimitLift R K t P g hg)).rightUnshift (-1) (zero_add _)).v
      i (i + -1) rfl ≫
        (CochainComplex.mappingCone.fst (complexTowerDifference R K t)).1.v
          (i + -1) i (by omega) = g.f i at h
  rw [CochainComplex.HomComplex.Cochain.rightUnshift_v _ _ _ i (i + -1) rfl
    i (add_zero i)] at h
  simpa [complexTowerProjection, CochainComplex.mappingCocone.fst,
    CochainComplex.HomComplex.Cochain.leftShift,
    CochainComplex.shiftFunctorObjXIso] using h

/-- 両立する写像の持ち上げと標準射影の合成。 -/
theorem complexTowerCompatibleLift_comp_projection
    (K : ℕ → CochainComplex (ModuleCat.{u} R) ℤ) (t : ∀ n, K (n + 1) ⟶ K n)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (g : ∀ n, P ⟶ K n)
    (hg : ∀ n, g (n + 1) ≫ t n = g n) :
    complexTowerCompatibleLift R K t P g hg ≫ complexTowerProjection R K t = Pi.lift g :=
  complexTowerHomotopyLimitLift_projection R K t P _ _

/-- Milnor列の連結射は、標準射影のホモロジー写像の負。 -/
theorem complexTowerHomologyBoundary_eq_neg_projection
    (K : ℕ → CochainComplex (ModuleCat.{u} R) ℤ) (t : ∀ n, K (n + 1) ⟶ K n)
    (i : ℤ) (x : (complexTowerHomotopyLimit R K t).homology i) :
    complexTowerHomologyBoundary R K t i x =
      -complexProductHomologyEquiv R K i
        (HomologicalComplex.homologyMap (complexTowerProjection R K t) i x) := by
  have h := congrArg (fun f ↦ f.hom x)
    (coneShiftBoundary_eq_neg_fst R (complexTowerDifference R K t) i)
  exact (congrArg (complexProductHomologyEquiv R K i) h).trans (map_neg _ _)

/-- Koszulの標準包含は、各段への実際の射影によって元の包含へ戻る。 -/
theorem koszulCompletionUnit_comp_projection {e : ℕ} (a : Fin e → R) (n : ℕ) :
    koszulCompletionUnit R a ≫
      complexTowerProjection R (powerKoszulTower R a) (powerKoszulTransition R a) ≫
        Pi.π (powerKoszulTower R a) n = koszulComplexInclusion R (fun i ↦ a i ^ n) := by
  rw [← assoc]
  rw [koszulCompletionUnit, complexTowerCompatibleLift_comp_projection, Pi.lift_comp_π]

end SerrePositivity.DerivedCompletion

end TowerProjectionPart
