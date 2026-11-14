module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.TensorArrowConjugation
public import
  SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.DGSimplicialRingCoefficientProductDifferential
/-!
概要：元の実乗法の cochain 二重次数表示。
方針：同じ実次数同型と Moore 乗法、標準 tensor の次数別普遍性を使う。
規約：元の符号と全整数次数を保持する。使われ方：β5(g) の dg 代数構造。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory HomologicalComplex
variable (A : SimplicialObject RingCat.{u})
local notation "N" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedChains A
local notation "E" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.integerCoefficientModuleFunctor
local notation "P" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedDGComplex A
def simplicialRingDGCochainMooreBidegree (p q n : ℕ) (h : p + q = n) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedDGComplex A).X (-(p : ℤ)) ⊗
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedDGComplex A).X (-(q : ℤ)) ⟶
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedDGComplex A).X (-(n : ℤ)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.tensorArrowConjugate (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainDegreeIso A p)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainDegreeIso A q) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainDegreeIso A n)
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingCoefficientMooreBidegree A p q n h)

lemma simplicialRingDGCochainMooreBidegree_sum (p q : ℕ) :
    simplicialRingDGCochainMooreBidegree A p q (p + q) rfl =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainNegativeProduct A p q := by
  simp only [simplicialRingDGCochainMooreBidegree, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.tensorArrowConjugate,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingCoefficientMooreBidegree, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingMooreMultiplicationBidegree,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainNegativeProduct, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGMooreDegreeProduct, Category.assoc]

lemma simplicialRingDGCochainMooreBidegree_transport (p q n : ℕ) (h : p + q = n) :
    simplicialRingDGCochainMooreBidegree A p q n h =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainNegativeProduct A p q ≫
        eqToHom (congrArg (fun k : ℕ ↦ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedDGComplex A).X (-(k : ℤ))) h) := by
  cases h
  rw [eqToHom_refl, Category.comp_id, simplicialRingDGCochainMooreBidegree_sum]

lemma simplicialRingDGCochainMultiplicationComponent_negative
    (p q n : ℕ) (h : p + q = n) :
    ιTensorObj (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedDGComplex A) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedDGComplex A)
        (-(p : ℤ)) (-(q : ℤ)) (-(n : ℤ)) (by omega) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainMultiplicationComponent A (-(n : ℤ)) =
        simplicialRingDGCochainMooreBidegree A p q n h := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainMultiplicationComponent_bidegree,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainDegreeProduct_negative, Category.assoc, eqToHom_trans,
    simplicialRingDGCochainMooreBidegree_transport]
local notation "P" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedDGComplex A
end SerrePositivity.InfinityCategories.Project.DerivedCategories
