module
public import SerrePositivity.InfinityCategories.Derived.TensorArrowConjugation
public import
  SerrePositivity.InfinityCategories.Derived.DGSimplicialRingCoefficientProductDifferential
/-!
概要：元の実乗法の cochain 二重次数表示。
方針：同じ実次数同型と Moore 乗法、標準 tensor の次数別普遍性を使う。
規約：元の符号と全整数次数を保持する。使われ方：β5(g) の dg 代数構造。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories
open CategoryTheory MonoidalCategory HomologicalComplex KST.ProExcision
variable (A : SimplicialObject RingCat.{u})
local notation "N" => simplicialRingNormalizedChains A
local notation "E" => integerCoefficientModuleFunctor
local notation "P" => simplicialRingNormalizedDGComplex A
def simplicialRingDGCochainMooreBidegree (p q n : ℕ) (h : p + q = n) :
    (simplicialRingNormalizedDGComplex A).X (-(p : ℤ)) ⊗
      (simplicialRingNormalizedDGComplex A).X (-(q : ℤ)) ⟶
        (simplicialRingNormalizedDGComplex A).X (-(n : ℤ)) :=
  tensorArrowConjugate (simplicialRingDGCochainDegreeIso A p)
    (simplicialRingDGCochainDegreeIso A q) (simplicialRingDGCochainDegreeIso A n)
    (simplicialRingCoefficientMooreBidegree A p q n h)

lemma simplicialRingDGCochainMooreBidegree_sum (p q : ℕ) :
    simplicialRingDGCochainMooreBidegree A p q (p + q) rfl =
      simplicialRingDGCochainNegativeProduct A p q := by
  simp only [simplicialRingDGCochainMooreBidegree, tensorArrowConjugate,
    simplicialRingCoefficientMooreBidegree, simplicialRingMooreMultiplicationBidegree,
    simplicialRingDGCochainNegativeProduct, simplicialRingDGMooreDegreeProduct, Category.assoc]

lemma simplicialRingDGCochainMooreBidegree_transport (p q n : ℕ) (h : p + q = n) :
    simplicialRingDGCochainMooreBidegree A p q n h =
      simplicialRingDGCochainNegativeProduct A p q ≫
        eqToHom (congrArg (fun k : ℕ ↦ (simplicialRingNormalizedDGComplex A).X (-(k : ℤ))) h) := by
  cases h
  rw [eqToHom_refl, Category.comp_id, simplicialRingDGCochainMooreBidegree_sum]

lemma simplicialRingDGCochainMultiplicationComponent_negative
    (p q n : ℕ) (h : p + q = n) :
    ιTensorObj (simplicialRingNormalizedDGComplex A) (simplicialRingNormalizedDGComplex A)
        (-(p : ℤ)) (-(q : ℤ)) (-(n : ℤ)) (by omega) ≫
      simplicialRingDGCochainMultiplicationComponent A (-(n : ℤ)) =
        simplicialRingDGCochainMooreBidegree A p q n h := by
  rw [simplicialRingDGCochainMultiplicationComponent_bidegree,
    simplicialRingDGCochainDegreeProduct_negative, Category.assoc, eqToHom_trans,
    simplicialRingDGCochainMooreBidegree_transport]
local notation "P" => simplicialRingNormalizedDGComplex A
end SerrePositivity.InfinityCategories
