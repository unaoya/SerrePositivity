module

public import SerrePositivity.CommutativeAlgebra.DeRham.CartierCoordinateBasis
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import all SerrePositivity.CommutativeAlgebra.DeRham.CartierRepresentatives
import all SerrePositivity.CommutativeAlgebra.DeRham.Polynomial
import all SerrePositivity.CommutativeAlgebra.DeRham.CartierWeight

/-!
# 有限多変数の Cartier 余鎖ホモトピー同値

## 概要
すべての重みが p の倍数の成分から、通常の多項式 de Rham 複体のコホモロジーを得る。

## 方針
一座標ごとの射影を合成し、単項式基底上で Cartier の代表と係数抽出に分解する。

## 規約
係数の Frobenius はここでは加えない。係数体 F_p で絶対 Frobenius の代表になる。

## 使われ方
有限多変数 inverse Cartier と結晶基底での Hodge–Tate 比較。
-/

public noncomputable section

open CategoryTheory HomologicalComplex MvPolynomial Set
open scoped TensorProduct

universe u

namespace SerrePositivity.DeRham

variable (K T : Type u) [Field K] [Fintype T] [LinearOrder T]
variable (p : ℕ) [CharP K p] (hp : 0 < p)

local notation "C" => deRhamComplex K T

set_option backward.isDefEq.respectTransparency false

local instance weightDecidable {j : ℕ} (m : T →₀ ℕ) (S : powersetCard T j) :
    Decidable (CartierWeight T p m S) := Classical.propDecidable _

private def evalList (L : List T) : C ⟶ C :=
  L.foldr (fun s f => f ≫ cartierCoordinateEval K T s) (𝟙 C)

private def evalListHomotopy (L : List T) : Homotopy (evalList K T L) (𝟙 C) :=
  match L with
  | [] => Homotopy.refl _
  | s :: L => ((evalListHomotopy L).comp (cartierCoordinateEvalHomotopy K T s)).trans
      (Homotopy.ofEq (Category.id_comp _))

include p in
private theorem evalList_basis (L : List T) (j : ℕ) (m : T →₀ ℕ) (S : powersetCard T j) :
    (evalList K T L).f j (polynomialFormsBasis K T j (m, S)) =
      if ∀ t ∈ L, p ∣ m t + (if t ∈ S.val then 1 else 0)
        then polynomialFormsBasis K T j (m, S) else 0 := by
  classical
  induction L with
  | nil => simp [evalList]
  | cons s L ih =>
    change (cartierCoordinateEval K T s).f j
      ((evalList K T L).f j (polynomialFormsBasis K T j (m, S))) = _
    rw [ih]
    by_cases h : ∀ t ∈ L, p ∣ m t + (if t ∈ S.val then 1 else 0)
    · rw [ite_eq_left h, cartierCoordinateEval_basis K T p]
      have he : (∀ t ∈ s :: L, p ∣ m t + (if t ∈ S.val then 1 else 0)) ↔
          p ∣ m s + (if s ∈ S.val then 1 else 0) := by
        exact List.forall_mem_cons.trans (and_iff_left h)
      by_cases hs : p ∣ m s + (if s ∈ S.val then 1 else 0)
      · rw [ite_eq_left hs, ite_eq_left (he.mpr hs)]
      · rw [ite_eq_right hs, ite_eq_right (fun e => hs (he.mp e))]
    · rw [ite_eq_right h, map_zero,
        ite_eq_right (fun e => h (fun t ht => e t (List.mem_cons_of_mem _ ht)))]

private def indexList : List T := (Finset.univ : Finset T).toList

include p in
private theorem evalAll_basis (j : ℕ) (m : T →₀ ℕ) (S : powersetCard T j) :
    (evalList K T (indexList T)).f j (polynomialFormsBasis K T j (m, S)) =
      if CartierWeight T p m S then polynomialFormsBasis K T j (m, S) else 0 := by
  rw [evalList_basis K T p]
  simp [indexList, CartierWeight]

private abbrev I (j : ℕ) := (T →₀ ℕ) × powersetCard T j

private def cartierRep (j : ℕ) : forms K T j →ₗ[K] forms K T j :=
  (polynomialFormsBasis K T j).constr K fun a =>
    polynomialFormsBasis K T j (cartierMonomialEquiv T p hp j a).1

private def cartierExtract (j : ℕ) : forms K T j →ₗ[K] forms K T j :=
  (polynomialFormsBasis K T j).constr K fun a =>
    if h : CartierWeight T p a.1 a.2 then
      polynomialFormsBasis K T j ((cartierMonomialEquiv T p hp j).symm ⟨a, h⟩)
    else 0

omit [CharP K p] in
private theorem rep_basis (j : ℕ) (a : I T j) :
    cartierRep K T p hp j (polynomialFormsBasis K T j a) =
      polynomialFormsBasis K T j (cartierMonomialEquiv T p hp j a).1 :=
  (polynomialFormsBasis K T j).constr_basis K _ a

omit [CharP K p] in
private theorem extract_basis (j : ℕ) (a : I T j) :
    cartierExtract K T p hp j (polynomialFormsBasis K T j a) =
      if h : CartierWeight T p a.1 a.2 then
        polynomialFormsBasis K T j ((cartierMonomialEquiv T p hp j).symm ⟨a, h⟩)
      else 0 :=
  (polynomialFormsBasis K T j).constr_basis K _ a

omit [CharP K p] in
private theorem extract_rep (j : ℕ) :
    (cartierExtract K T p hp j).comp (cartierRep K T p hp j) = LinearMap.id := by
  apply (polynomialFormsBasis K T j).ext
  intro a
  simp only [LinearMap.comp_apply, rep_basis, extract_basis, LinearMap.id_apply]
  let b := cartierMonomialEquiv T p hp j a
  rw [dite_eq_left b.2]
  exact congrArg (polynomialFormsBasis K T j) ((cartierMonomialEquiv T p hp j).symm_apply_apply a)

include p in
private theorem rep_extract (j : ℕ) :
    (cartierRep K T p hp j).comp (cartierExtract K T p hp j) =
      (show forms K T j →ₗ[K] forms K T j from ((evalList K T (indexList T)).f j).hom) := by
  apply (polynomialFormsBasis K T j).ext
  rintro ⟨m, S⟩
  simp only [LinearMap.comp_apply, extract_basis]
  have h := evalAll_basis K T p j m S
  change _ = (evalList K T (indexList T)).f j (polynomialFormsBasis K T j (m, S))
  rw [h]
  by_cases hW : CartierWeight T p m S
  · rw [dite_eq_left hW, ite_eq_left hW, rep_basis, Equiv.apply_symm_apply]
  · rw [dite_eq_right hW, ite_eq_right hW, map_zero]

private abbrev CartierComplex := CochainComplex.of
  (fun j => (C).X j) (fun _ => 0) (fun _ => Limits.zero_comp)

private theorem rep_d_zero (j : ℕ) :
    (show forms K T j →ₗ[K] forms K T (j + 1) from ((C).d j (j + 1)).hom).comp
      (cartierRep K T p hp j) = 0 := by
  apply (polynomialFormsBasis K T j).ext
  intro a
  simp only [LinearMap.comp_apply, rep_basis, LinearMap.zero_apply]
  let b := cartierMonomialEquiv T p hp j a
  exact (deRhamTerm_d K T j (polynomialFormsBasis K T j b.1)).trans
    (by rw [polynomialFormsBasis_cartier_closed K T p (CharP.cast_eq_zero K p) _ _ b.2,
      map_zero])

private def repMap : CartierComplex K T ⟶ C where
  f j := ModuleCat.ofHom (cartierRep K T p hp j)
  comm' i j hij := by
    have e : i + 1 = j := hij
    subst j
    rw [show (CartierComplex K T).d i (i + 1) = 0 by
      dsimp only [CartierComplex, CochainComplex.of]; rw [CochainComplex.of_d]]
    rw [Limits.zero_comp]
    exact ModuleCat.hom_ext (rep_d_zero K T p hp i)

omit [CharP K p] in
private theorem rep_injective (j : ℕ) : Function.Injective (cartierRep K T p hp j) := by
  have h : Function.LeftInverse (cartierExtract K T p hp j) (cartierRep K T p hp j) :=
    DFunLike.congr_fun (extract_rep K T p hp j)
  exact h.injective

private def extractMap : C ⟶ CartierComplex K T where
  f j := ModuleCat.ofHom (cartierExtract K T p hp j)
  comm' i j hij := by
    have e : i + 1 = j := hij
    subst j
    rw [show (CartierComplex K T).d i (i + 1) = 0 by
      dsimp only [CartierComplex, CochainComplex.of]; rw [CochainComplex.of_d]]
    rw [Limits.comp_zero]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply rep_injective K T p hp (i + 1)
    rw [ModuleCat.hom_zero, LinearMap.zero_apply, map_zero]
    change 0 = cartierRep K T p hp (i + 1) (cartierExtract K T p hp (i + 1) ((C).d i (i + 1) x))
    symm
    have h (j : ℕ) (z : forms K T j) :
        cartierRep K T p hp j (cartierExtract K T p hp j z) =
          (evalList K T (indexList T)).f j z :=
      DFunLike.congr_fun (rep_extract K T p hp j) z
    change cartierRep K T p hp (i + 1) (cartierExtract K T p hp (i + 1) ((C).d i (i + 1) x)) = 0
    rw [h (i + 1) ((C).d i (i + 1) x)]
    have hc := ConcreteCategory.congr_hom ((evalList K T (indexList T)).comm i (i + 1)) x
    have hc' : (C).d i (i + 1) ((evalList K T (indexList T)).f i x) =
        (evalList K T (indexList T)).f (i + 1) ((C).d i (i + 1) x) := hc
    rw [← hc', (h i x).symm]
    exact DFunLike.congr_fun (rep_d_zero K T p hp i) (cartierExtract K T p hp i x)

private theorem repMap_extractMap :
    repMap K T p hp ≫ extractMap K T p hp = 𝟙 (CartierComplex K T) := by
  ext j : 1
  exact ModuleCat.hom_ext (extract_rep K T p hp j)

private theorem extractMap_repMap :
    extractMap K T p hp ≫ repMap K T p hp = evalList K T (indexList T) := by
  ext j : 1
  exact ModuleCat.hom_ext (rep_extract K T p hp j)

/-- Cartier 代表を送る鎖写像は、微分が零の多項式形式からのホモトピー同値。 -/
def finiteCartierHomotopyEquiv :
    HomotopyEquiv (CochainComplex.of (fun j => (deRhamComplex K T).X j)
      (fun _ => 0) (fun _ => Limits.zero_comp)) (deRhamComplex K T) where
  hom := repMap K T p hp
  inv := extractMap K T p hp
  homotopyHomInvId := Homotopy.ofEq (repMap_extractMap K T p hp)
  homotopyInvHomId := (Homotopy.ofEq (extractMap_repMap K T p hp)).trans
    (evalListHomotopy K T (indexList T))

/-- 有限多変数 Cartier の係数線形同型。 -/
def finiteCartierLinearEquiv (j : ℕ) :
    forms K T j ≃ₗ[K] (deRhamComplex K T).homology j := by
  let Z := CartierComplex K T
  let S := Z.sc j
  have hd (a b : ℕ) : Z.d a b = 0 := by
    by_cases h : a + 1 = b
    · subst b
      dsimp only [Z, CartierComplex, CochainComplex.of]
      rw [CochainComplex.of_d]
    · exact Z.shape a b h
  let e := (ShortComplex.HomologyData.ofZeros S (hd _ _) (hd _ _)).left.homologyIso
  exact (e.symm ≪≫ (finiteCartierHomotopyEquiv K T p hp).toHomologyIso j).toLinearEquiv

end SerrePositivity.DeRham
