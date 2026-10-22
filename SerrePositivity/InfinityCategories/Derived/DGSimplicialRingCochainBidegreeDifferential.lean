module
public import SerrePositivity.InfinityCategories.Derived.DGSimplicialRingCochainBidegree
/-!
概要：負次数の実 cochain 乗法の三つの Leibniz 式。
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
lemma simplicialRingDGCochainMooreBidegree_succ_succ (p q : ℕ) :
    simplicialRingDGCochainMooreBidegree A (p + 1) (q + 1) ((p + q + 1) + 1)
        (by omega) ≫ (P).d (-(((p + q + 1) + 1 : ℕ) : ℤ)) (-((p + q + 1 : ℕ) : ℤ)) =
    ((P).d (-((p + 1 : ℕ) : ℤ)) (-(p : ℤ)) ⊗ₘ 𝟙 ((P).X (-((q + 1 : ℕ) : ℤ)))) ≫
      simplicialRingDGCochainMooreBidegree A p (q + 1) (p + q + 1) (by omega) +
    (-1 : ℤ) ^ (p + 1) •
      ((𝟙 ((P).X (-((p + 1 : ℕ) : ℤ))) ⊗ₘ (P).d (-((q + 1 : ℕ) : ℤ)) (-(q : ℤ))) ≫
        simplicialRingDGCochainMooreBidegree A (p + 1) q (p + q + 1) (by omega)) := by
  simpa only [simplicialRingDGCochainMooreBidegree, simplicialRingDGCochain_d] using!
    tensorArrowConjugate_leibniz
      (simplicialRingDGCochainDegreeIso A (p + 1)) (simplicialRingDGCochainDegreeIso A p)
      (simplicialRingDGCochainDegreeIso A (q + 1)) (simplicialRingDGCochainDegreeIso A q)
      (simplicialRingDGCochainDegreeIso A ((p + q + 1) + 1))
      (simplicialRingDGCochainDegreeIso A (p + q + 1))
      ((E).map ((N).d (p + 1) p)) ((E).map ((N).d (q + 1) q))
      ((E).map ((N).d ((p + q + 1) + 1) (p + q + 1)))
      (simplicialRingCoefficientMooreBidegree A (p + 1) (q + 1) ((p + q + 1) + 1) (by omega))
      (simplicialRingCoefficientMooreBidegree A p (q + 1) (p + q + 1) (by omega))
      (simplicialRingCoefficientMooreBidegree A (p + 1) q (p + q + 1) (by omega))
      ((-1 : ℤ) ^ (p + 1)) (simplicialRingCoefficientMooreBidegree_succ_succ A p q)

lemma simplicialRingDGCochainMooreBidegree_zero_succ (q : ℕ) :
    simplicialRingDGCochainMooreBidegree A 0 (q + 1) (q + 1) (by omega) ≫
        (P).d (-((q + 1 : ℕ) : ℤ)) (-(q : ℤ)) =
    (𝟙 ((P).X 0) ⊗ₘ (P).d (-((q + 1 : ℕ) : ℤ)) (-(q : ℤ))) ≫
      simplicialRingDGCochainMooreBidegree A 0 q q (by omega) := by
  simpa only [simplicialRingDGCochainMooreBidegree, simplicialRingDGCochain_d] using!
    tensorArrowConjugate_leibniz_right (simplicialRingDGCochainDegreeIso A 0)
      (simplicialRingDGCochainDegreeIso A (q + 1)) (simplicialRingDGCochainDegreeIso A q)
      (simplicialRingDGCochainDegreeIso A (q + 1)) (simplicialRingDGCochainDegreeIso A q)
      ((E).map ((N).d (q + 1) q)) ((E).map ((N).d (q + 1) q))
      (simplicialRingCoefficientMooreBidegree A 0 (q + 1) (q + 1) (by omega))
      (simplicialRingCoefficientMooreBidegree A 0 q q (by omega))
      (simplicialRingCoefficientMooreBidegree_zero_succ A q)

lemma simplicialRingDGCochainMooreBidegree_succ_zero (p : ℕ) :
    simplicialRingDGCochainMooreBidegree A (p + 1) 0 (p + 1) (by omega) ≫
        (P).d (-((p + 1 : ℕ) : ℤ)) (-(p : ℤ)) =
    ((P).d (-((p + 1 : ℕ) : ℤ)) (-(p : ℤ)) ⊗ₘ 𝟙 ((P).X 0)) ≫
      simplicialRingDGCochainMooreBidegree A p 0 p (by omega) := by
  simpa only [simplicialRingDGCochainMooreBidegree, simplicialRingDGCochain_d] using!
    tensorArrowConjugate_leibniz_left
      (simplicialRingDGCochainDegreeIso A (p + 1)) (simplicialRingDGCochainDegreeIso A p)
      (simplicialRingDGCochainDegreeIso A 0)
      (simplicialRingDGCochainDegreeIso A (p + 1)) (simplicialRingDGCochainDegreeIso A p)
      ((E).map ((N).d (p + 1) p)) ((E).map ((N).d (p + 1) p))
      (simplicialRingCoefficientMooreBidegree A (p + 1) 0 (p + 1) (by omega))
      (simplicialRingCoefficientMooreBidegree A p 0 p (by omega))
      (simplicialRingCoefficientMooreBidegree_succ_zero A p)
end SerrePositivity.InfinityCategories
