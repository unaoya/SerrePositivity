module

public import SerrePositivity.HomologicalAlgebra.Complex.Basic
public import SerrePositivity.PerfectComplex.Eigen.Idempotent
public import SerrePositivity.HomologicalAlgebra.Complex.Idempotent
public import Mathlib.Algebra.Ring.Invertible
public import SerrePositivity.CommutativeAlgebra.CubicCyclotomic.Algebra
public import Mathlib.Tactic.Module
public import SerrePositivity.CategoryTheory.Triangulated.Idempotent
public import SerrePositivity.PerfectComplex.ClosedSupport.Functoriality
public import SerrePositivity.HomologicalAlgebra.BaseChange

/-! # 三次の鎖作用と指標による分解

## 概要

複体の三次の鎖作用（位数 3 の作用）とそのスカラー・二項和の構成、Fourier 射影、三つの直交する指標の射影による分解、指標に伴うスカラー作用、固有ベクトルの射影の像への持ち上げ、同型に沿った作用の移送、係数変更と分裂した指標の像を与える。

## 方針

指標の射影は τ の多項式で、3 が可逆な係数で直交性と和が 1 であることを示す（環 End K の `CompleteOrthogonalIdempotents` そのもの、refactor-plan §4.4.2）。

## 規約

基本の構成には 3 の逆元・完全性・台を要求しない。

## 使われ方

`Eigen/CubicClass`・`Eigen/CubicTensor`、KTheory/Adams の三乗の作用素。
-/

@[expose] public noncomputable section

universe u

section CubicActionBasicPart

namespace SerrePositivity
open CategoryTheory Category Limits
variable {R : Type u} [CommRing R]

structure CochainCubicAction (K : CochainComplex (ModuleCat.{u} R) ℤ) where
  map : K ⟶ K
  cube : map ≫ map ≫ map = 𝟙 K

namespace CochainCubicAction
variable {K L : CochainComplex (ModuleCat.{u} R) ℤ}

@[ext]
lemma ext {τ σ : CochainCubicAction K} (h : τ.map = σ.map) : τ = σ := by
  cases τ
  cases σ
  cases h
  rfl

/-- A scalar cube root of unity acts on any cochain complex. -/
def scalar (K : CochainComplex (ModuleCat.{u} R) ℤ) (c : R) (hc : c ^ 3 = 1) :
    CochainCubicAction K where
  map := c • 𝟙 K
  cube := by
    simp only [Linear.smul_comp, Linear.comp_smul, id_comp, smul_smul]
    rw [← pow_two, ← pow_succ, hc, one_smul]

@[simp]
lemma scalar_map (K : CochainComplex (ModuleCat.{u} R) ℤ) (c : R) (hc : c ^ 3 = 1) :
    (scalar K c hc).map = c • 𝟙 K := rfl

/-- The diagonal cubic action on a binary sum. -/
def biprod (τ : CochainCubicAction K) (σ : CochainCubicAction L) :
    CochainCubicAction (K ⊞ L) where
  map := Limits.biprod.map τ.map σ.map
  cube := by
    apply Limits.biprod.hom_ext'
    · simp only [Limits.biprod.inl_map_assoc, Limits.biprod.inl_map, comp_id]
      simpa only [Category.assoc, id_comp] using
        congrArg (fun f => f ≫ (Limits.biprod.inl : K ⟶ K ⊞ L)) τ.cube
    · simp only [Limits.biprod.inr_map_assoc, Limits.biprod.inr_map, comp_id]
      simpa only [Category.assoc, id_comp] using
        congrArg (fun f => f ≫ (Limits.biprod.inr : L ⟶ K ⊞ L)) σ.cube

@[simp]
lemma biprod_map (τ : CochainCubicAction K) (σ : CochainCubicAction L) :
    (τ.biprod σ).map = Limits.biprod.map τ.map σ.map := rfl

end CochainCubicAction
end SerrePositivity

end CubicActionBasicPart

section CubicActionProjectorPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory Category Limits Preadditive
variable {R : Type u} [CommRing R]

namespace CochainCubicAction
variable {K L : CochainComplex (ModuleCat.{u} R) ℤ} [Invertible (3 : R)]

/-- The projector for the eigenvalue a, written using a inverse = a squared. -/
def projectorMap (τ : CochainCubicAction K) (a : R) : K ⟶ K :=
  (⅟(3 : R)) • (𝟙 K + a ^ 2 • τ.map + a • (τ.map ≫ τ.map))

lemma projectorMap_comp_map (τ : CochainCubicAction K) (a : R) (ha : a ^ 3 = 1) :
    τ.projectorMap a ≫ τ.map = a • τ.projectorMap a := by
  have hac : a * a ^ 2 = 1 := by rw [← pow_succ', ha]
  calc
    τ.projectorMap a ≫ τ.map =
        (⅟(3 : R)) • (τ.map + a ^ 2 • (τ.map ≫ τ.map) + a • 𝟙 K) := by
      simp only [projectorMap, Linear.smul_comp, add_comp, id_comp, Category.assoc, τ.cube]
    _ = (⅟(3 : R)) • (a • (𝟙 K + a ^ 2 • τ.map + a • (τ.map ≫ τ.map))) := by
      congr 1
      simp only [smul_add, smul_smul, hac, one_smul, ← pow_two]
      abel
    _ = a • τ.projectorMap a := smul_comm _ _ _

lemma map_comp_projectorMap (τ : CochainCubicAction K) (a : R) (ha : a ^ 3 = 1) :
    τ.map ≫ τ.projectorMap a = a • τ.projectorMap a := by
  have hc : τ.map ≫ τ.projectorMap a = τ.projectorMap a ≫ τ.map := by
    simp only [projectorMap, Linear.comp_smul, Linear.smul_comp, comp_add, add_comp,
      id_comp, comp_id, Category.assoc]
  rw [hc, projectorMap_comp_map τ a ha]

lemma eigenvector_comp_projectorMap (τ : CochainCubicAction K)
    (a : R) (ha : a ^ 3 = 1) (f : L ⟶ K) (hf : f ≫ τ.map = a • f) :
    f ≫ τ.projectorMap a = f := by
  have hsq : f ≫ (τ.map ≫ τ.map) = a ^ 2 • f := by
    rw [← Category.assoc, hf, Linear.smul_comp, hf, smul_smul, ← pow_two]
  change f ≫ ((⅟(3 : R)) •
    (𝟙 K + a ^ 2 • τ.map + a • (τ.map ≫ τ.map))) = f
  rw [Linear.comp_smul, comp_add, comp_add, comp_id, Linear.comp_smul,
    Linear.comp_smul, hf, hsq]
  have hac : a * a ^ 2 = 1 := by rw [← pow_succ', ha]
  have hca : a ^ 2 * a = 1 := by rw [mul_comm, hac]
  simp only [smul_smul, hac, hca, one_smul]
  rw [smul_add, smul_add, ← add_smul, ← add_smul]
  have hi : ⅟(3 : R) + ⅟(3 : R) + ⅟(3 : R) = 1 := by
    calc
      _ = ⅟(3 : R) * 3 := by ring
      _ = 1 := invOf_mul_self _
  rw [hi, one_smul]

lemma projectorMap_idem (τ : CochainCubicAction K) (a : R) (ha : a ^ 3 = 1) :
    τ.projectorMap a ≫ τ.projectorMap a = τ.projectorMap a :=
  τ.eigenvector_comp_projectorMap a ha (τ.projectorMap a) (τ.projectorMap_comp_map a ha)

/-- Each cubic root supplies an idempotent chain map. -/
def projector (τ : CochainCubicAction K) (a : R) (ha : a ^ 3 = 1) : CochainIdempotent K :=
  ⟨τ.projectorMap a, τ.projectorMap_idem a ha⟩

@[reassoc]
lemma projectorMap_naturality {L : CochainComplex (ModuleCat.{u} R) ℤ}
    (τ : CochainCubicAction K) (σ : CochainCubicAction L) (f : K ⟶ L)
    (hf : τ.map ≫ f = f ≫ σ.map) (a : R) :
    τ.projectorMap a ≫ f = f ≫ σ.projectorMap a := by
  have hsq : (τ.map ≫ τ.map) ≫ f = f ≫ (σ.map ≫ σ.map) := by
    rw [Category.assoc, hf, ← Category.assoc, hf, Category.assoc]
  simp only [projectorMap, Linear.smul_comp, Linear.comp_smul,
    add_comp, comp_add, id_comp, comp_id, hf, hsq]

lemma projectorMap_orthogonal (τ : CochainCubicAction K) (a b : R)
    (ha : a ^ 3 = 1) (hb : b ^ 3 = 1) (hab : IsUnit (a - b)) :
    τ.projectorMap a ≫ τ.projectorMap b = 0 := by
  have he : a • (τ.projectorMap a ≫ τ.projectorMap b) =
      b • (τ.projectorMap a ≫ τ.projectorMap b) := by
    calc
      _ = (τ.projectorMap a ≫ τ.map) ≫ τ.projectorMap b := by
        rw [projectorMap_comp_map τ a ha, Linear.smul_comp]
      _ = τ.projectorMap a ≫ (τ.map ≫ τ.projectorMap b) := Category.assoc _ _ _
      _ = _ := by rw [map_comp_projectorMap τ b hb, Linear.comp_smul]
  have hz : (a - b) • (τ.projectorMap a ≫ τ.projectorMap b) = 0 := by
    rw [sub_smul, sub_eq_zero]
    exact he
  apply hab.smul_left_cancel.mp
  simpa only [smul_zero] using hz

@[reassoc]
lemma projector_inclusion_eigen (τ : CochainCubicAction K) (a : R) (ha : a ^ 3 = 1) :
    (τ.projector a ha).inclusion ≫ τ.map = a • (τ.projector a ha).inclusion := by
  calc
    _ = (τ.projector a ha).inclusion ≫ (τ.projectorMap a ≫ τ.map) := by
      rw [← Category.assoc]
      exact congrArg (fun f => f ≫ τ.map) (τ.projector a ha).inclusion_map.symm
    _ = (τ.projector a ha).inclusion ≫ (a • τ.projectorMap a) := by
      rw [projectorMap_comp_map τ a ha]
    _ = _ := by
      rw [Linear.comp_smul]
      exact congrArg (fun f => a • f) (τ.projector a ha).inclusion_map

end CochainCubicAction
end SerrePositivity

end CubicActionProjectorPart

section CubicActionDecompositionPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory Category Limits Preadditive
variable {R : Type u} [CommRing R]

/-- The three character values, with indices taken modulo three. -/
def cubicCharacter (t : R) (j : Fin 3) : R := t ^ (j : ℕ)

lemma cubicCharacter_cube (t : R) (ht : t ^ 3 = 1) (j : Fin 3) :
    cubicCharacter t j ^ 3 = 1 := by
  rw [cubicCharacter, ← pow_mul, mul_comm, pow_mul, ht, one_pow]

lemma cubicCharacter_mul (t : R) (ht : t ^ 3 = 1) (i j : Fin 3) :
    cubicCharacter t i * cubicCharacter t j = cubicCharacter t (i + j) := by
  change t ^ (i : ℕ) * t ^ (j : ℕ) = t ^ ((i + j : Fin 3) : ℕ)
  rw [Fin.val_add, ← pow_add]
  calc
    t ^ ((i : ℕ) + (j : ℕ)) =
        t ^ (((i : ℕ) + (j : ℕ)) % 3 + 3 * (((i : ℕ) + (j : ℕ)) / 3)) :=
      congrArg (fun n : ℕ => t ^ n) (Nat.mod_add_div _ 3).symm
    _ = _ := by rw [pow_add, pow_mul, ht, one_pow, mul_one]

lemma sum_cubicCharacter (t : R) (ht : t ^ 2 + t + 1 = 0) :
    ∑ j : Fin 3, cubicCharacter t j = 0 := by
  rw [Fin.sum_univ_three]
  simp only [cubicCharacter, Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one]
  calc
    1 + t + t ^ 2 = t ^ 2 + t + 1 := by ring
    _ = 0 := ht

lemma cubicCharacter_difference_isUnit [Invertible (3 : R)] (t : R)
    (ht : t ^ 2 + t + 1 = 0) (i j : Fin 3) (hne : i ≠ j) :
    IsUnit (cubicCharacter t i - cubicCharacter t j) := by
  have hc := cube_eq_one_of_cubic_relation t ht
  have hu : IsUnit t := by
    let : Invertible t := invertibleOfPowEqOne t 3 hc (by decide)
    exact isUnit_of_invertible t
  obtain ⟨h01, h02⟩ := isUnit_one_sub_of_cubic_relation t ht (isUnit_of_invertible (3 : R))
  have h10 : IsUnit (t - 1) := by simpa only [neg_sub] using h01.neg
  have h20 : IsUnit (t ^ 2 - 1) := by simpa only [neg_sub] using h02.neg
  have h12 : IsUnit (t - t ^ 2) := by
    convert hu.mul h01 using 1
    ring
  have h21 : IsUnit (t ^ 2 - t) := by simpa only [neg_sub] using h12.neg
  fin_cases i <;> fin_cases j
  all_goals first
    | exact (hne rfl).elim
    | simp only [cubicCharacter, pow_zero, pow_one]
      first | exact h01 | exact h02 | exact h10 | exact h20 | exact h12 | exact h21

namespace CochainCubicAction
variable {K : CochainComplex (ModuleCat.{u} R) ℤ} [Invertible (3 : R)]

lemma sum_character_projectorMap (τ : CochainCubicAction K) (t : R)
    (ht : t ^ 2 + t + 1 = 0) :
    ∑ j : Fin 3, τ.projectorMap (cubicCharacter t j) = 𝟙 K := by
  have hc := cube_eq_one_of_cubic_relation t ht
  have ht4 : t ^ 4 = t := by
    calc
      _ = t ^ 3 * t := by ring
      _ = t := by rw [hc, one_mul]
  have hs : 1 + t + t ^ 2 = 0 := by
    calc
      _ = t ^ 2 + t + 1 := by ring
      _ = 0 := ht
  rw [Fin.sum_univ_three]
  simp only [cubicCharacter, Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one]
  calc
    τ.projectorMap 1 + τ.projectorMap t + τ.projectorMap (t ^ 2) =
        (⅟(3 : R)) • ((3 : R) • (𝟙 K : K ⟶ K) +
          (1 + t ^ 2 + t ^ 4) • τ.map + (1 + t + t ^ 2) • (τ.map ≫ τ.map)) := by
      simp only [projectorMap]
      module
    _ = 𝟙 K := by
      have hs' : 1 + t ^ 2 + t = 0 := by simpa only [add_right_comm] using hs
      rw [ht4, hs', hs, zero_smul, zero_smul, add_zero, add_zero,
        smul_smul, invOf_mul_self, one_smul]

/-- The three eigenspace idempotents. -/
def characterProjector (τ : CochainCubicAction K) (t : R) (ht : t ^ 3 = 1)
    (j : Fin 3) : CochainIdempotent K :=
  τ.projector (cubicCharacter t j) (cubicCharacter_cube t ht j)

lemma characterProjector_orthogonal (τ : CochainCubicAction K) (t : R)
    (ht : t ^ 2 + t + 1 = 0) (i j : Fin 3) (hne : i ≠ j) :
    (τ.characterProjector t (cube_eq_one_of_cubic_relation t ht) i).map ≫
      (τ.characterProjector t (cube_eq_one_of_cubic_relation t ht) j).map = 0 :=
  τ.projectorMap_orthogonal _ _ (cubicCharacter_cube _ (cube_eq_one_of_cubic_relation t ht) i)
    (cubicCharacter_cube _ (cube_eq_one_of_cubic_relation t ht) j)
    (cubicCharacter_difference_isUnit t ht i j hne)

/-- The original complex is the finite biproduct of its three character parts. -/
def characterDecompositionIso (τ : CochainCubicAction K) (t : R)
    (ht : t ^ 2 + t + 1 = 0) :
    (⨁ fun j : Fin 3 =>
      (τ.characterProjector t (cube_eq_one_of_cubic_relation t ht) j).image) ≅ K :=
  CochainIdempotent.decompositionIso _ (τ.characterProjector_orthogonal t ht)
    (τ.sum_character_projectorMap t ht)

end CochainCubicAction
end SerrePositivity

end CubicActionDecompositionPart

section CubicActionCharacterPart

namespace SerrePositivity
open CategoryTheory
variable {R : Type u} [CommRing R]
namespace CochainCubicAction

/-- The scalar action associated to one of the three characters. -/
def characterScalar (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (t : R) (ht : t ^ 3 = 1) (j : Fin 3) : CochainCubicAction K :=
  scalar K (cubicCharacter t j) (cubicCharacter_cube t ht j)

@[simp]
lemma characterScalar_map (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (t : R) (ht : t ^ 3 = 1) (j : Fin 3) :
    (characterScalar K t ht j).map = cubicCharacter t j • 𝟙 K := rfl

end CochainCubicAction
end SerrePositivity

end CubicActionCharacterPart

section CubicActionEigenvectorsPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory Category Limits Preadditive
variable {R : Type u} [CommRing R]
namespace CochainCubicAction
variable {K L : CochainComplex (ModuleCat.{u} R) ℤ} [Invertible (3 : R)]

/-- A chain eigenvector factors through the matching Fourier projector image. -/
def eigenvectorLift (τ : CochainCubicAction K) (a : R) (ha : a ^ 3 = 1)
    (f : L ⟶ K) (hf : f ≫ τ.map = a • f) : L ⟶ (τ.projector a ha).image :=
  equalizer.lift f (by
    rw [comp_id]
    exact (τ.eigenvector_comp_projectorMap a ha f hf).symm)

@[reassoc]
lemma eigenvectorLift_inclusion (τ : CochainCubicAction K) (a : R) (ha : a ^ 3 = 1)
    (f : L ⟶ K) (hf : f ≫ τ.map = a • f) :
    τ.eigenvectorLift a ha f hf ≫ (τ.projector a ha).inclusion = f :=
  equalizer.lift_ι _ _

end CochainCubicAction
end SerrePositivity

end CubicActionEigenvectorsPart

section CubicActionTransportPart

namespace SerrePositivity.CochainCubicAction
open CategoryTheory Category
variable {R : Type u} [CommRing R]
variable {K L : CochainComplex (ModuleCat.{u} R) ℤ}

def comapIso (e : K ≅ L) (τ : CochainCubicAction L) : CochainCubicAction K where
  map := e.hom ≫ τ.map ≫ e.inv
  cube := conjugate_cube e τ.map τ.cube

@[reassoc]
lemma comapIso_hom (e : K ≅ L) (τ : CochainCubicAction L) :
    (comapIso e τ).map ≫ e.hom = e.hom ≫ τ.map := by
  simp [comapIso, Category.assoc]

end SerrePositivity.CochainCubicAction

end CubicActionTransportPart

section CubicActionBaseChangePart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory Category Limits
variable {R S : Type u} [CommRing R] [CommRing S]
namespace CochainCubicAction
variable (φ : R →+* S) {K : CochainComplex (ModuleCat.{u} R) ℤ}

/-- Transport the cubic equation through extension of scalars. -/
def baseChange (τ : CochainCubicAction K) :
    CochainCubicAction (SerrePositivity.baseChange φ K) where
  map := ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).map τ.map
  cube := by rw [← Functor.map_comp, ← Functor.map_comp, τ.cube, CategoryTheory.Functor.map_id]

variable [Invertible (3 : R)] [Invertible (3 : S)]

lemma map_invOf_three : φ (⅟(3 : R)) = ⅟(3 : S) := by
  let : Invertible (φ (3 : R)) := by rw [map_ofNat]; infer_instance
  simpa only [map_ofNat] using map_invOf φ (3 : R)

lemma baseChange_projectorMap (τ : CochainCubicAction K) (a : R) :
    ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).map (τ.projectorMap a) =
      (baseChange φ τ).projectorMap (φ a) := by
  simp only [projectorMap, extendScalars_mapHomologicalComplex_smul,
    map_invOf_three, Functor.map_add, CategoryTheory.Functor.map_id, Functor.map_comp, map_pow]
  rfl

/-- The image of a split character projector commutes with base change. -/
def characterBaseChangeIso (τ : CochainCubicAction K) (t : R) (ht : t ^ 3 = 1)
    (j : Fin 3) :
    SerrePositivity.baseChange φ (τ.characterProjector t ht j).image ≅
      ((baseChange φ τ).characterProjector (φ t)
        (by rw [← map_pow, ht, map_one]) j).image :=
  CochainIdempotent.imageFunctorIsoOfMapEq
    ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)) (τ.characterProjector t ht j)
    ((baseChange φ τ).characterProjector (φ t) (by rw [← map_pow, ht, map_one]) j) (by
      simpa only [characterProjector, projector, cubicCharacter, map_pow] using
        baseChange_projectorMap φ τ (cubicCharacter t j))

@[reassoc]
lemma characterBaseChangeIso_hom_inclusion (τ : CochainCubicAction K)
    (t : R) (ht : t ^ 3 = 1) (j : Fin 3) :
    (characterBaseChangeIso φ τ t ht j).hom ≫
      ((baseChange φ τ).characterProjector (φ t)
        (by rw [← map_pow, ht, map_one]) j).inclusion =
      ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).map
        (τ.characterProjector t ht j).inclusion := by
  simp only [characterBaseChangeIso, CochainIdempotent.imageFunctorIsoOfMapEq_hom_inclusion]

end CochainCubicAction
end SerrePositivity

end CubicActionBaseChangePart
