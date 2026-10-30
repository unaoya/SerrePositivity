module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModuleTower
public import SerrePositivity.HomologicalAlgebra.Complex.ConeLES
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import SerrePositivity.HomologicalAlgebra.Complex.Cone
public import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence

/-! # 複体の可算逆系のホモトピー逆極限のモデル

## 概要

加群の cochain 複体の可算逆系（塔）について、直積上の「恒等写像 − 遷移写像」の写像錐を一段シフトしたもの `complexTowerHomotopyLimit` をホモトピー逆極限（holim）のモデルとして作る。塔の表示同型による比較、直積のホモロジーが成分のホモロジーの直積であること、直積へのホモトピーの組み立て、holim の各項の二成分表示と微分を与え、差分の錐の長完全列を成分ホモロジーの直積の差分へ移す。

## 方針

holim は完備性を仮定せず実際の複体として作る。直積のホモロジーはサイクルと境界の代表元を成分ごとに選んで比べるので、遷移の全射性は要らない。

## 規約

負次数の差分の余核は保持し、通常の逆極限と無条件には同一視しない。`shortComplexZero` などルート直下の一般的な名前は private か名前空間へ移す候補（refactor-plan §3.5.4）。

## 使われ方

`Tower/Maps`・`Tower/Milnor`、導来完備化（ComplexCompletion）、Koszul の塔。
-/

@[expose] public noncomputable section

universe u

section TowerComplexPart

namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits CategoryTheory.Category CategoryTheory.Preadditive
attribute [local instance] HasDerivedCategory.standard
variable (R : Type u) [CommRing R]
    (K : ℕ → CochainComplex (ModuleCat.{u} R) ℤ) (t : ∀ n, K (n + 1) ⟶ K n)

/-- 逆系の直積上の一段の遷移写像。 -/
def complexTowerShift : piObj K ⟶ piObj K :=
  Pi.lift (fun n ↦ Pi.π K (n + 1) ≫ t n)

/-- 複体の直積上の差分写像。 -/
def complexTowerDifference : piObj K ⟶ piObj K := 𝟙 _ - complexTowerShift R K t

/-- 差分写像の各射影を具体的に計算する。 -/
theorem complexTowerDifference_projection (n : ℕ) :
    complexTowerDifference R K t ≫ Pi.π K n = Pi.π K n - Pi.π K (n + 1) ≫ t n := by
  simp only [complexTowerDifference, complexTowerShift, sub_comp, id_comp, Pi.lift_comp_π]

/-- 可算逆系のホモトピー逆極限の、実際のmapping coneによるモデル。 -/
def complexTowerHomotopyLimit : CochainComplex (ModuleCat.{u} R) ℤ :=
  (CochainComplex.mappingCone (complexTowerDifference R K t))⟦(-1 : ℤ)⟧

/-- 上の複体を標準的な実導来圏へ移した対象。 -/
def complexTowerHomotopyLimitObject : ConcreteDerivedCategory R :=
  DerivedCategory.Q.obj (complexTowerHomotopyLimit R K t)

variable {K} {L : ℕ → CochainComplex (ModuleCat.{u} R) ℤ}

/-- 各段の写像から直積の写像を構成する。 -/
def complexTowerProductMap (g : ∀ n, K n ⟶ L n) : piObj K ⟶ piObj L :=
  Pi.lift (fun n ↦ Pi.π K n ≫ g n)

/-- 直積の写像を射影で計算する。 -/
theorem complexTowerProductMap_projection (g : ∀ n, K n ⟶ L n) (n : ℕ) :
    complexTowerProductMap R g ≫ Pi.π L n = Pi.π K n ≫ g n := by
  simp only [complexTowerProductMap, Pi.lift_comp_π]

/-- 逆系の写像と差分写像は可換する。 -/
theorem complexTowerDifference_naturality (s : ∀ n, L (n + 1) ⟶ L n)
    (g : ∀ n, K n ⟶ L n) (hg : ∀ n, t n ≫ g n = g (n + 1) ≫ s n) :
    complexTowerProductMap R g ≫ complexTowerDifference R L s =
      complexTowerDifference R K t ≫ complexTowerProductMap R g := by
  apply Pi.hom_ext
  intro n
  simp only [assoc, complexTowerDifference_projection, comp_sub,
    complexTowerProductMap_projection]
  rw [← assoc, complexTowerProductMap_projection, assoc, ← hg]
  conv_rhs => rw [← assoc, complexTowerDifference_projection, sub_comp]
  rw [assoc]

end SerrePositivity.DerivedCompletion

end TowerComplexPart

section TowerIsoPart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits CategoryTheory.Category
variable (R : Type u) [CommRing R]
variable {K L : ℕ → CochainComplex (ModuleCat.{u} R) ℤ}

/-- 各段の同型から、複体の直積の同型を構成する。 -/
def complexTowerProductIso (e : ∀ n, K n ≅ L n) : piObj K ≅ piObj L where
  hom := complexTowerProductMap R (fun n ↦ (e n).hom)
  inv := complexTowerProductMap R (fun n ↦ (e n).inv)
  hom_inv_id := by
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, complexTowerProductMap_projection]
    rw [← Category.assoc, complexTowerProductMap_projection, Category.assoc,
      Iso.hom_inv_id, Category.comp_id, Category.id_comp]
  inv_hom_id := by
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, complexTowerProductMap_projection]
    rw [← Category.assoc, complexTowerProductMap_projection, Category.assoc,
      Iso.inv_hom_id, Category.comp_id, Category.id_comp]

/-- 遷移を保つ各段の同型は、差分写像の矢印の同型を与える。 -/
def complexTowerDifferenceIso (t : ∀ n, K (n + 1) ⟶ K n) (s : ∀ n, L (n + 1) ⟶ L n)
    (e : ∀ n, K n ≅ L n) (he : ∀ n, t n ≫ (e n).hom = (e (n + 1)).hom ≫ s n) :
    Arrow.mk (complexTowerDifference R K t) ≅ Arrow.mk (complexTowerDifference R L s) :=
  Arrow.isoMk (complexTowerProductIso R e) (complexTowerProductIso R e)
    (complexTowerDifference_naturality R t s (fun n ↦ (e n).hom) he)

/-- 遷移を保つ各段の表示同型は、実際のmapping coneとシフトを含む同型を与える。 -/
def complexTowerHomotopyLimitIso
    (t : ∀ n, K (n + 1) ⟶ K n) (s : ∀ n, L (n + 1) ⟶ L n)
    (e : ∀ n, K n ≅ L n) (he : ∀ n, t n ≫ (e n).hom = (e (n + 1)).hom ≫ s n) :
    complexTowerHomotopyLimit R K t ≅ complexTowerHomotopyLimit R L s :=
  (shiftFunctor (CochainComplex (ModuleCat.{u} R) ℤ) (-1 : ℤ)).mapIso
    (HomologicalComplex.homotopyCofiber.mapArrowIso _ _ (fun j ↦ ⟨j - 1, by simp⟩)
      (complexTowerDifferenceIso R t s e he))

end SerrePositivity.DerivedCompletion

end TowerIsoPart

section ProductHomologyPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits CategoryTheory.Category
variable (R : Type u) [CommRing R]
    (K : ℕ → CochainComplex (ModuleCat.{u} R) ℤ)

/-- 複体の直積の各次数を、成分の項の直積へ同定する。 -/
def complexProductDegreeEquiv (i : ℤ) :
    (piObj K).X i ≃ₗ[R] ∀ n, (K n).X i :=
  ((PreservesProduct.iso (HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) i) K)
    ≪≫ ModuleCat.piIsoPi (fun n ↦ (K n).X i)).toLinearEquiv

@[simp] theorem complexProductDegreeEquiv_apply (i : ℤ) (x : (piObj K).X i) (n : ℕ) :
    complexProductDegreeEquiv R K i x n = (Pi.π K n).f i x := by
  have h := ModuleCat.piIsoPi_hom_ker_subtype (fun n ↦ (K n).X i) n
  have h' := piComparison_comp_π
    (HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) i) K n
  exact congrArg (fun f ↦ f.hom x) ((congrArg
    (fun f ↦ (PreservesProduct.iso
      (HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) i) K).hom ≫ f) h).trans h')

/-- 直積のホモロジーから各成分のホモロジーへの標準比較写像。 -/
def complexProductHomologyMap (i : ℤ) :
    (piObj K).homology i →ₗ[R] ∀ n, (K n).homology i :=
  LinearMap.pi (fun n ↦ (HomologicalComplex.homologyMap (Pi.π K n) i).hom)

/-- 各成分のホモロジー類は、直積の一つのサイクルで表せる。 -/
theorem complexProductHomologyMap_surjective (i : ℤ) :
    Function.Surjective (complexProductHomologyMap R K i) := by
  intro x
  have hrep : ∀ n, ∃ z : (K n).cycles i, (K n).homologyπ i z = x n :=
    fun n ↦ (ModuleCat.epi_iff_surjective ((K n).homologyπ i)).mp inferInstance (x n)
  choose z hz using hrep
  let y := (complexProductDegreeEquiv R K i).symm (fun n ↦ (K n).iCycles i (z n))
  have hy : ∀ n, (Pi.π K n).f i y = (K n).iCycles i (z n) := by
    intro n
    rw [← complexProductDegreeEquiv_apply]
    exact congrFun ((complexProductDegreeEquiv R K i).apply_symm_apply _) n
  let j := (ComplexShape.up ℤ).next i
  have hdy : (piObj K).d i j y = 0 := by
    apply (complexProductDegreeEquiv R K j).injective
    ext n
    simp only [complexProductDegreeEquiv_apply, map_zero]
    have hcomm := congrArg (fun f ↦ f.hom y) ((Pi.π K n).comm i j)
    change (K n).d i j ((Pi.π K n).f i y) =
      (Pi.π K n).f j ((piObj K).d i j y) at hcomm
    rw [← hcomm, hy]
    exact congrArg (fun f ↦ f.hom (z n)) ((K n).iCycles_d i j)
  let y' : (piObj K).cycles i := ((piObj K).sc i).cyclesMk y hdy
  have hy' : ∀ n, HomologicalComplex.cyclesMap (Pi.π K n) i y' = z n := by
    intro n
    apply (ModuleCat.mono_iff_injective ((K n).iCycles i)).mp inferInstance
    have h := congrArg (fun f ↦ f.hom y') (HomologicalComplex.cyclesMap_i (Pi.π K n) i)
    change (K n).iCycles i (HomologicalComplex.cyclesMap (Pi.π K n) i y') =
      (Pi.π K n).f i ((piObj K).iCycles i y') at h
    have hyy : (piObj K).iCycles i y' = y := ((piObj K).sc i).i_cyclesMk y hdy
    rw [h, hyy, hy]
  refine ⟨(piObj K).homologyπ i y', ?_⟩
  ext n
  change HomologicalComplex.homologyMap (Pi.π K n) i ((piObj K).homologyπ i y') = x n
  have h := congrArg (fun f ↦ f.hom y')
    (HomologicalComplex.homologyπ_naturality (Pi.π K n) i)
  change HomologicalComplex.homologyMap (Pi.π K n) i ((piObj K).homologyπ i y') =
    (K n).homologyπ i (HomologicalComplex.cyclesMap (Pi.π K n) i y') at h
  rw [h, hy', hz]

/-- 各成分で境界になる直積のサイクルは、直積でも境界になる。 -/
theorem complexProductHomologyMap_injective (i : ℤ) :
    Function.Injective (complexProductHomologyMap R K i) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective ((piObj K).homologyπ i)).mp inferInstance x
  let j := (ComplexShape.up ℤ).prev i
  have hb : ∀ n, ∃ b : (K n).X j,
      (K n).toCycles j i b = HomologicalComplex.cyclesMap (Pi.π K n) i z := by
    intro n
    let S := (K n).sc i
    let E := ShortComplex.mk S.toCycles S.homologyπ S.toCycles_comp_homologyπ
    have hE : E.Exact := E.exact_of_g_is_cokernel S.homologyIsCokernel
    have hz : (K n).homologyπ i (HomologicalComplex.cyclesMap (Pi.π K n) i z) = 0 := by
      have h := congrArg (fun f ↦ f.hom z)
        (HomologicalComplex.homologyπ_naturality (Pi.π K n) i)
      exact h.symm.trans (congrFun hx n)
    exact E.moduleCat_exact_iff.mp hE _ hz
  choose b hb using hb
  let y := (complexProductDegreeEquiv R K j).symm b
  have hy : ∀ n, (Pi.π K n).f j y = b n := by
    intro n
    rw [← complexProductDegreeEquiv_apply]
    exact congrFun ((complexProductDegreeEquiv R K j).apply_symm_apply _) n
  have hboundary : (piObj K).toCycles j i y = z := by
    apply (ModuleCat.mono_iff_injective ((piObj K).iCycles i)).mp inferInstance
    apply (complexProductDegreeEquiv R K i).injective
    ext n
    simp only [complexProductDegreeEquiv_apply]
    have h₁ := congrArg (fun f ↦ f.hom y) ((piObj K).toCycles_i j i)
    have h₂ := congrArg (fun f ↦ f.hom y) ((Pi.π K n).comm j i)
    have h₃ := congrArg (fun f ↦ f.hom z) (HomologicalComplex.cyclesMap_i (Pi.π K n) i)
    have h₄ := congrArg (fun f ↦ f.hom (b n)) ((K n).toCycles_i j i)
    have h₅ := congrArg (fun w ↦ (K n).iCycles i w) (hb n)
    change (K n).d j i ((Pi.π K n).f j y) =
      (Pi.π K n).f i ((piObj K).d j i y) at h₂
    change (piObj K).iCycles i ((piObj K).toCycles j i y) = (piObj K).d j i y at h₁
    change (K n).iCycles i (HomologicalComplex.cyclesMap (Pi.π K n) i z) =
      (Pi.π K n).f i ((piObj K).iCycles i z) at h₃
    change (K n).iCycles i ((K n).toCycles j i (b n)) = (K n).d j i (b n) at h₄
    rw [h₁, ← h₂, hy]
    exact h₄.symm.trans (h₅.trans h₃)
  rw [← hboundary]
  exact congrArg (fun f ↦ f.hom y) ((piObj K).toCycles_comp_homologyπ j i)

/-- 任意の次数で、加群複体の直積とホモロジーは可換。 -/
def complexProductHomologyEquiv (i : ℤ) :
    (piObj K).homology i ≃ₗ[R] ∀ n, (K n).homology i :=
  LinearEquiv.ofBijective (complexProductHomologyMap R K i)
    ⟨complexProductHomologyMap_injective R K i, complexProductHomologyMap_surjective R K i⟩

@[simp] theorem complexProductHomologyEquiv_apply (i : ℤ)
    (x : (piObj K).homology i) (n : ℕ) :
    complexProductHomologyEquiv R K i x n = HomologicalComplex.homologyMap (Pi.π K n) i x := rfl

/-- 直積の同定の下で、ホモロジー上の差分も成分の差分になる。 -/
theorem complexProductHomologyEquiv_difference (t : ∀ n, K (n + 1) ⟶ K n)
    (i : ℤ) (x : (piObj K).homology i) :
    complexProductHomologyEquiv R K i
      (HomologicalComplex.homologyMap (complexTowerDifference R K t) i x) =
    moduleTowerDifference R (fun n ↦ (K n).homology i)
      (fun n ↦ (HomologicalComplex.homologyMap (t n) i).hom)
        (complexProductHomologyEquiv R K i x) := by
  ext n
  have h := congrArg (fun f ↦ HomologicalComplex.homologyMap f i)
    (complexTowerDifference_projection R K t n)
  simp only [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_sub] at h
  exact congrArg (fun f ↦ f.hom x) h

end SerrePositivity.DerivedCompletion

end ProductHomologyPart

section ProductCoordinatesPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits
variable (R : Type u) [CommRing R]
    (K : ℕ → CochainComplex (ModuleCat.{u} R) ℤ)

/-- 直積の微分は、各段の微分を成分ごとに取る。 -/
theorem complexProductDegreeEquiv_d (i j : ℤ) (x : (piObj K).X i) (n : ℕ) :
    complexProductDegreeEquiv R K j ((piObj K).d i j x) n =
      (K n).d i j (complexProductDegreeEquiv R K i x n) := by
  simp only [complexProductDegreeEquiv_apply]
  exact (congrArg (fun g ↦ g.hom x) ((Pi.π K n).comm i j)).symm

/-- 直積の差分は、成分と次の成分の遷移の差。 -/
theorem complexProductDegreeEquiv_difference
    (t : ∀ n, K (n + 1) ⟶ K n) (i : ℤ) (x : (piObj K).X i) (n : ℕ) :
    complexProductDegreeEquiv R K i ((complexTowerDifference R K t).f i x) n =
      complexProductDegreeEquiv R K i x n -
        (t n).f i (complexProductDegreeEquiv R K i x (n + 1)) := by
  simp only [complexProductDegreeEquiv_apply]
  exact congrArg (fun g ↦ (g.f i).hom x) (complexTowerDifference_projection R K t n)

end SerrePositivity.DerivedCompletion

end ProductCoordinatesPart

section ProductHomotopyPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Category CategoryTheory.Limits CategoryTheory.Preadditive
variable (R : Type u) [CommRing R]
    (K : ℕ → CochainComplex (ModuleCat.{u} R) ℤ)

/-- 各次数で、成分への射を複体の直積の項への射にまとめる。 -/
def complexProductDegreeLift (i : ℤ) {M : ModuleCat.{u} R}
    (g : ∀ n, M ⟶ (K n).X i) : M ⟶ (piObj K).X i :=
  ModuleCat.ofHom ((complexProductDegreeEquiv R K i).symm.toLinearMap.comp
    (LinearMap.pi (fun n ↦ (g n).hom)))

@[simp] theorem complexProductDegreeLift_projection (i : ℤ) {M : ModuleCat.{u} R}
    (g : ∀ n, M ⟶ (K n).X i) (n : ℕ) :
    complexProductDegreeLift R K i g ≫ (Pi.π K n).f i = g n := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (Pi.π K n).f i ((complexProductDegreeEquiv R K i).symm (fun n ↦ g n x)) = g n x
  rw [← complexProductDegreeEquiv_apply]
  exact congrFun ((complexProductDegreeEquiv R K i).apply_symm_apply _) n

/-- 各次数の射は、全成分への射影によって決まる。 -/
theorem complexProductDegree_hom_ext (i : ℤ) {M : ModuleCat.{u} R}
    {f g : M ⟶ (piObj K).X i} (h : ∀ n, f ≫ (Pi.π K n).f i = g ≫ (Pi.π K n).f i) : f = g := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply (complexProductDegreeEquiv R K i).injective
  funext n
  simpa only [complexProductDegreeEquiv_apply, ModuleCat.hom_comp, LinearMap.comp_apply] using
    congrArg (fun f ↦ f.hom x) (h n)

/-- 各射影後のホモトピーを、直積への一つのホモトピーへまとめる。 -/
def complexProductHomotopy {P : CochainComplex (ModuleCat.{u} R) ℤ}
    {f g : P ⟶ piObj K} (h : ∀ n, Homotopy (f ≫ Pi.π K n) (g ≫ Pi.π K n)) :
    Homotopy f g where
  hom i j := complexProductDegreeLift R K j (fun n ↦ (h n).hom i j)
  zero i j hij := by
    apply complexProductDegree_hom_ext R K j
    intro n
    rw [complexProductDegreeLift_projection, (h n).zero i j hij, zero_comp]
  comm i := by
    apply complexProductDegree_hom_ext R K i
    intro n
    rw [add_comp, add_comp, ← dNext_comp_right, ← prevD_comp_right]
    have hh : (fun i j ↦ complexProductDegreeLift R K j (fun n ↦ (h n).hom i j) ≫
        (Pi.π K n).f j) = (h n).hom := by
      funext i j
      exact complexProductDegreeLift_projection R K j _ n
    rw [hh]
    exact (h n).comm i

/-- 各射影後に零ホモトピックなら、直積への射も零ホモトピック。 -/
theorem complexProduct_nonempty_homotopy_zero {P : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : P ⟶ piObj K) (h : ∀ n, Nonempty (Homotopy (f ≫ Pi.π K n) 0)) :
    Nonempty (Homotopy f 0) := by
  refine ⟨complexProductHomotopy R K (fun n ↦ ?_)⟩
  simpa only [zero_comp] using (h n).some

end SerrePositivity.DerivedCompletion

end ProductHomotopyPart

section TowerCoordinatesPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits HomologicalComplex.homotopyCofiber
variable (R : Type u) [CommRing R]

variable (K : ℕ → CochainComplex (ModuleCat.{u} R) ℤ)
    (t : ∀ n, K (n + 1) ⟶ K n)

/-- holimの次数nの項を、次数nとmの列の組に同定する。 -/
def complexTowerHomotopyLimitDegreeEquiv (m n : ℤ) (h : m + 1 = n) :
    (complexTowerHomotopyLimit R K t).X n ≃ₗ[R]
      (∀ k, (K k).X n) × (∀ k, (K k).X m) :=
  (CochainComplex.shiftFunctorObjXIso
    (CochainComplex.mappingCone (complexTowerDifference R K t))
    (-1) n m (by omega)).toLinearEquiv ≪≫ₗ
    moduleConeDegreeEquiv (complexTowerDifference R K t) m n h ≪≫ₗ
      (complexProductDegreeEquiv R K n).prodCongr (complexProductDegreeEquiv R K m)

/-- 二成分表示の第1成分は、外側の錐の第1射影。 -/
theorem complexTowerHomotopyLimitDegreeEquiv_fst (m n : ℤ) (h : m + 1 = n)
    (x : (complexTowerHomotopyLimit R K t).X n) :
    (complexTowerHomotopyLimitDegreeEquiv R K t m n h x).1 =
      complexProductDegreeEquiv R K n
        (fstX (complexTowerDifference R K t) m n h
          ((CochainComplex.shiftFunctorObjXIso
            (CochainComplex.mappingCone (complexTowerDifference R K t))
            (-1) n m (by omega)).hom x)) := rfl

/-- 二成分表示の第2成分は、外側の錐の第2射影。 -/
theorem complexTowerHomotopyLimitDegreeEquiv_snd (m n : ℤ) (h : m + 1 = n)
    (x : (complexTowerHomotopyLimit R K t).X n) :
    (complexTowerHomotopyLimitDegreeEquiv R K t m n h x).2 =
      complexProductDegreeEquiv R K m
        (sndX (complexTowerDifference R K t) m
          ((CochainComplex.shiftFunctorObjXIso
            (CochainComplex.mappingCone (complexTowerDifference R K t))
            (-1) n m (by omega)).hom x)) := rfl

/-- シフトしたholimの微分を、外側の錐の微分へ移す。 -/
theorem complexTowerHomotopyLimitDegreeIso_d (m n p : ℤ)
    (h : m + 1 = n) (h' : n + 1 = p)
    (x : (complexTowerHomotopyLimit R K t).X n) :
    (CochainComplex.shiftFunctorObjXIso
            (CochainComplex.mappingCone (complexTowerDifference R K t)) (-1) p n (by omega)).hom
        ((complexTowerHomotopyLimit R K t).d n p x) =
      -((CochainComplex.mappingCone (complexTowerDifference R K t)).d m n
        ((CochainComplex.shiftFunctorObjXIso
          (CochainComplex.mappingCone (complexTowerDifference R K t))
          (-1) n m (by omega)).hom x)) := by
  have hm : m = n + (-1) := by omega
  have hn : n = p + (-1) := by omega
  subst m n
  simp [complexTowerHomotopyLimit, CochainComplex.shiftFunctorObjXIso]

/-- holimの二成分表示の第1成分の微分。 -/
theorem complexTowerHomotopyLimitDegreeEquiv_d_fst (m n p : ℤ)
    (h : m + 1 = n) (h' : n + 1 = p)
    (x : (complexTowerHomotopyLimit R K t).X n) (k : ℕ) :
    (complexTowerHomotopyLimitDegreeEquiv R K t n p h'
      ((complexTowerHomotopyLimit R K t).d n p x)).1 k =
        (K k).d n p ((complexTowerHomotopyLimitDegreeEquiv R K t m n h x).1 k) := by
  rw [complexTowerHomotopyLimitDegreeEquiv_fst, complexTowerHomotopyLimitDegreeEquiv_fst,
    complexTowerHomotopyLimitDegreeIso_d R K t m n p h h']
  let y := (CochainComplex.shiftFunctorObjXIso
    (CochainComplex.mappingCone (complexTowerDifference R K t)) (-1) n m (by omega)).hom x
  have hd := congrArg (fun f ↦ f.hom y)
    (d_fstX (complexTowerDifference R K t) m n p h h')
  change fstX (complexTowerDifference R K t) n p h'
      ((CochainComplex.mappingCone (complexTowerDifference R K t)).d m n y) =
    -((piObj K).d n p (fstX (complexTowerDifference R K t) m n h y)) at hd
  simp only [map_neg]
  rw [hd]
  simp only [map_neg, neg_neg, complexProductDegreeEquiv_d]
  rfl

/-- holimの第2成分の微分は、塔の差分と前の次数の微分の負の和。 -/
theorem complexTowerHomotopyLimitDegreeEquiv_d_snd (m n p : ℤ)
    (h : m + 1 = n) (h' : n + 1 = p)
    (x : (complexTowerHomotopyLimit R K t).X n) (k : ℕ) :
    (complexTowerHomotopyLimitDegreeEquiv R K t n p h'
      ((complexTowerHomotopyLimit R K t).d n p x)).2 k =
      -((complexTowerHomotopyLimitDegreeEquiv R K t m n h x).1 k -
          (t k).f n ((complexTowerHomotopyLimitDegreeEquiv R K t m n h x).1 (k + 1))) -
        (K k).d m n ((complexTowerHomotopyLimitDegreeEquiv R K t m n h x).2 k) := by
  rw [complexTowerHomotopyLimitDegreeEquiv_snd, complexTowerHomotopyLimitDegreeEquiv_fst,
    complexTowerHomotopyLimitDegreeEquiv_snd,
    complexTowerHomotopyLimitDegreeIso_d R K t m n p h h']
  let y := (CochainComplex.shiftFunctorObjXIso
    (CochainComplex.mappingCone (complexTowerDifference R K t)) (-1) n m (by omega)).hom x
  have hd := congrArg (fun f ↦ f.hom y)
    (d_sndX (complexTowerDifference R K t) m n h)
  change sndX (complexTowerDifference R K t) n
      ((CochainComplex.mappingCone (complexTowerDifference R K t)).d m n y) =
    (complexTowerDifference R K t).f n (fstX (complexTowerDifference R K t) m n h y) +
      (piObj K).d m n (sndX (complexTowerDifference R K t) m y) at hd
  simp only [map_neg]
  rw [hd]
  simp only [map_add, Pi.neg_apply, Pi.add_apply, complexProductDegreeEquiv_difference,
    complexProductDegreeEquiv_d, neg_add, sub_eq_add_neg]
  rfl

end SerrePositivity.DerivedCompletion

end TowerCoordinatesPart

section TowerHomologyPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits CategoryTheory.Category
variable (R : Type u) [CommRing R]
    (K : ℕ → CochainComplex (ModuleCat.{u} R) ℤ) (t : ∀ n, K (n + 1) ⟶ K n)

private theorem shortComplexZero {S : ShortComplex (ModuleCat.{u} R)} (_h : S.Exact) :
    S.f ≫ S.g = 0 := S.zero

/-- 各次数のホモロジーの直積上の差分写像。 -/
def complexTowerHomologyDifference (i : ℤ) :
    (∀ n, (K n).homology i) →ₗ[R] (∀ n, (K n).homology i) :=
  moduleTowerDifference R (fun n ↦ (K n).homology i)
    (fun n ↦ (HomologicalComplex.homologyMap (t n) i).hom)

/-- 候補複体のホモロジーを、差分写像の錐の一つ下の次数へ同定する。 -/
def complexTowerHomologyShiftEquiv (i : ℤ) :
    (complexTowerHomotopyLimit R K t).homology i ≃ₗ[R]
      (CochainComplex.mappingCone (complexTowerDifference R K t)).homology (i - 1) :=
  ((CochainComplex.ShiftSequence.shiftIso (ModuleCat R) (-1) i (i - 1)
    (by omega)).app (CochainComplex.mappingCone (complexTowerDifference R K t))).toLinearEquiv

/-- 錐の包含による、前の次数のホモロジー直積からの写像。 -/
def complexTowerHomologyIncoming (i : ℤ) :
    (∀ n, (K n).homology (i - 1)) →ₗ[R]
      (complexTowerHomotopyLimit R K t).homology i :=
  (complexTowerHomologyShiftEquiv R K t i).symm.toLinearMap.comp
    ((HomologicalComplex.homologyMap
      (CochainComplex.mappingCone.inr (complexTowerDifference R K t)) (i - 1)).hom.comp
        (complexProductHomologyEquiv R K (i - 1)).symm.toLinearMap)

/-- 錐の連結射による、同じ次数のホモロジー直積への写像。 -/
def complexTowerHomologyBoundary (i : ℤ) :
    (complexTowerHomotopyLimit R K t).homology i →ₗ[R] ∀ n, (K n).homology i :=
  (complexProductHomologyEquiv R K i).toLinearMap.comp
    ((Cone.δ (complexTowerDifference R K t) (i - 1) i (by omega)).hom.comp
      (complexTowerHomologyShiftEquiv R K t i).toLinearMap)

/-- 包含に誘導される写像の核は、前の次数の差分の像。 -/
theorem complexTowerHomologyIncoming_zero_iff (i : ℤ)
    (y : ∀ n, (K n).homology (i - 1)) :
    complexTowerHomologyIncoming R K t i y = 0 ↔
      ∃ z, complexTowerHomologyDifference R K t (i - 1) z = y := by
  let φ := complexTowerDifference R K t
  have hE := (ShortComplex.moduleCat_exact_iff _).mp (Cone.exact₂ φ (i - 1))
  constructor
  · intro hy
    have hy' : HomologicalComplex.homologyMap (CochainComplex.mappingCone.inr φ) (i - 1)
        ((complexProductHomologyEquiv R K (i - 1)).symm y) = 0 := by
      have h := congrArg (complexTowerHomologyShiftEquiv R K t i) hy
      simpa [complexTowerHomologyIncoming] using h
    obtain ⟨z, hz⟩ := hE _ hy'
    refine ⟨complexProductHomologyEquiv R K (i - 1) z, ?_⟩
    simp only [complexTowerHomologyDifference]
    rw [← complexProductHomologyEquiv_difference]
    exact (congrArg (complexProductHomologyEquiv R K (i - 1)) hz).trans
      ((complexProductHomologyEquiv R K (i - 1)).apply_symm_apply y)
  · rintro ⟨z, rfl⟩
    obtain ⟨z, rfl⟩ := (complexProductHomologyEquiv R K (i - 1)).surjective z
    simp only [complexTowerHomologyDifference]
    rw [← complexProductHomologyEquiv_difference]
    simp only [complexTowerHomologyIncoming, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    have h := congrArg (fun f ↦ f.hom z)
      (shortComplexZero R (Cone.exact₂ φ (i - 1)))
    simpa using congrArg (complexTowerHomologyShiftEquiv R K t i).symm h

/-- 連結射の核は、前の次数の包含の像。 -/
theorem complexTowerHomologyBoundary_zero_iff (i : ℤ)
    (x : (complexTowerHomotopyLimit R K t).homology i) :
    complexTowerHomologyBoundary R K t i x = 0 ↔
      ∃ y, complexTowerHomologyIncoming R K t i y = x := by
  let φ := complexTowerDifference R K t
  have hE := Cone.exact₃ φ (i - 1) i (by omega)
  constructor
  · intro hx
    have hx' : Cone.δ φ (i - 1) i (by omega)
        (complexTowerHomologyShiftEquiv R K t i x) = 0 := by
      apply (complexProductHomologyEquiv R K i).injective
      simpa [complexTowerHomologyBoundary] using hx
    obtain ⟨y, hy⟩ := (ShortComplex.moduleCat_exact_iff _).mp hE _ hx'
    refine ⟨complexProductHomologyEquiv R K (i - 1) y, ?_⟩
    simp only [complexTowerHomologyIncoming, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    exact (complexTowerHomologyShiftEquiv R K t i).symm_apply_eq.mpr hy
  · rintro ⟨y, rfl⟩
    have h := congrArg (fun f ↦ f.hom ((complexProductHomologyEquiv R K (i - 1)).symm y))
      (shortComplexZero R hE)
    simpa [complexTowerHomologyBoundary, complexTowerHomologyIncoming] using
      congrArg (complexProductHomologyEquiv R K i) h

/-- 連結射の像は、同じ次数の差分の核。 -/
theorem complexTowerHomologyBoundary_range (i : ℤ) :
    (complexTowerHomologyBoundary R K t i).range =
      (complexTowerHomologyDifference R K t i).ker := by
  let φ := complexTowerDifference R K t
  have hE := Cone.exact₁ φ (i - 1) i (by omega)
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    change complexTowerHomologyDifference R K t i
      (complexTowerHomologyBoundary R K t i x) = 0
    rw [complexTowerHomologyBoundary, LinearMap.comp_apply, LinearMap.comp_apply]
    simp only [complexTowerHomologyDifference]
    have h := congrArg (fun f ↦ f.hom (complexTowerHomologyShiftEquiv R K t i x))
      (shortComplexZero R hE)
    exact (complexProductHomologyEquiv_difference R K t i _).symm.trans
      ((congrArg (complexProductHomologyEquiv R K i) h).trans (map_zero _))
  · intro hy
    have hy' : HomologicalComplex.homologyMap φ i
        ((complexProductHomologyEquiv R K i).symm y) = 0 := by
      apply (complexProductHomologyEquiv R K i).injective
      rw [complexProductHomologyEquiv_difference, LinearEquiv.apply_symm_apply, map_zero]
      exact hy
    obtain ⟨x, hx⟩ := (ShortComplex.moduleCat_exact_iff _).mp hE _ hy'
    refine ⟨(complexTowerHomologyShiftEquiv R K t i).symm x, ?_⟩
    simp only [complexTowerHomologyBoundary, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    exact (congrArg (complexProductHomologyEquiv R K i) hx).trans
      ((complexProductHomologyEquiv R K i).apply_symm_apply y)

end SerrePositivity.DerivedCompletion

end TowerHomologyPart
