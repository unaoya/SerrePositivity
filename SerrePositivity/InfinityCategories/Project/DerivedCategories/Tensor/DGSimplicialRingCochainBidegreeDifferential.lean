module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.DGSimplicialRingCochainBidegree
/-!
概要：負次数の実 cochain 乗法の三つの Leibniz 式。
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
lemma simplicialRingDGCochainMooreBidegree_succ_succ (p q : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainMooreBidegree A (p + 1) (q + 1) ((p + q + 1) + 1)
        (by omega) ≫ (P).d (-(((p + q + 1) + 1 : ℕ) : ℤ)) (-((p + q + 1 : ℕ) : ℤ)) =
    ((P).d (-((p + 1 : ℕ) : ℤ)) (-(p : ℤ)) ⊗ₘ 𝟙 ((P).X (-((q + 1 : ℕ) : ℤ)))) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainMooreBidegree A p (q + 1) (p + q + 1) (by omega) +
    (-1 : ℤ) ^ (p + 1) •
      ((𝟙 ((P).X (-((p + 1 : ℕ) : ℤ))) ⊗ₘ (P).d (-((q + 1 : ℕ) : ℤ)) (-(q : ℤ))) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainMooreBidegree A (p + 1) q (p + q + 1) (by omega)) := by
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainMooreBidegree, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochain_d] using!
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.tensorArrowConjugate_leibniz
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainDegreeIso A (p + 1)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainDegreeIso A p)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainDegreeIso A (q + 1)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainDegreeIso A q)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainDegreeIso A ((p + q + 1) + 1))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainDegreeIso A (p + q + 1))
      ((E).map ((N).d (p + 1) p)) ((E).map ((N).d (q + 1) q))
      ((E).map ((N).d ((p + q + 1) + 1) (p + q + 1)))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingCoefficientMooreBidegree A (p + 1) (q + 1) ((p + q + 1) + 1) (by omega))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingCoefficientMooreBidegree A p (q + 1) (p + q + 1) (by omega))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingCoefficientMooreBidegree A (p + 1) q (p + q + 1) (by omega))
      ((-1 : ℤ) ^ (p + 1)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingCoefficientMooreBidegree_succ_succ A p q)

lemma simplicialRingDGCochainMooreBidegree_zero_succ (q : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainMooreBidegree A 0 (q + 1) (q + 1) (by omega) ≫
        (P).d (-((q + 1 : ℕ) : ℤ)) (-(q : ℤ)) =
    (𝟙 ((P).X 0) ⊗ₘ (P).d (-((q + 1 : ℕ) : ℤ)) (-(q : ℤ))) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainMooreBidegree A 0 q q (by omega) := by
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainMooreBidegree, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochain_d] using!
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.tensorArrowConjugate_leibniz_right (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainDegreeIso A 0)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainDegreeIso A (q + 1)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainDegreeIso A q)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainDegreeIso A (q + 1)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainDegreeIso A q)
      ((E).map ((N).d (q + 1) q)) ((E).map ((N).d (q + 1) q))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingCoefficientMooreBidegree A 0 (q + 1) (q + 1) (by omega))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingCoefficientMooreBidegree A 0 q q (by omega))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingCoefficientMooreBidegree_zero_succ A q)

lemma simplicialRingDGCochainMooreBidegree_succ_zero (p : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainMooreBidegree A (p + 1) 0 (p + 1) (by omega) ≫
        (P).d (-((p + 1 : ℕ) : ℤ)) (-(p : ℤ)) =
    ((P).d (-((p + 1 : ℕ) : ℤ)) (-(p : ℤ)) ⊗ₘ 𝟙 ((P).X 0)) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainMooreBidegree A p 0 p (by omega) := by
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainMooreBidegree, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochain_d] using!
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.tensorArrowConjugate_leibniz_left
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainDegreeIso A (p + 1)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainDegreeIso A p)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainDegreeIso A 0)
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainDegreeIso A (p + 1)) (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainDegreeIso A p)
      ((E).map ((N).d (p + 1) p)) ((E).map ((N).d (p + 1) p))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingCoefficientMooreBidegree A (p + 1) 0 (p + 1) (by omega))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingCoefficientMooreBidegree A p 0 p (by omega))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingCoefficientMooreBidegree_succ_zero A p)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
