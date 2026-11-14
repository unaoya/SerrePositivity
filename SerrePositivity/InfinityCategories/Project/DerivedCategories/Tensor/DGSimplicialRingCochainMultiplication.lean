module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.DGSimplicialRingCochainTensorDifferential
/-!
概要：全整数次数の同じ実乗法成分を鎖写像へ昇格する。
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
lemma simplicialRingDGCochainMultiplication_negative_comm
    (p q n : ℕ) (h : p + q = n + 1) :
    ιTensorObj P P (-(p : ℤ)) (-(q : ℤ)) (-((n + 1 : ℕ) : ℤ)) (by omega) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainMultiplicationComponent A (-((n + 1 : ℕ) : ℤ)) ≫
          (P).d (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) =
    ιTensorObj P P (-(p : ℤ)) (-(q : ℤ)) (-((n + 1 : ℕ) : ℤ)) (by omega) ≫
        (SerrePositivity.cochainTensor P P).d (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) ≫
          _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainMultiplicationComponent A (-(n : ℤ)) := by
  rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainMultiplicationComponent_negative A p q (n + 1) h,
    mapBifunctor.d_eq, Preadditive.add_comp, Preadditive.comp_add]
  cases p with
  | zero =>
    cases q with
    | zero => omega
    | succ q =>
      have hn : n = q := by omega
      subst n
      erw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainMultiplication_D₁_zero A (q + 1) (q + 1) q (by omega),
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainMultiplication_D₂_succ A (by omega),
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainMooreBidegree_zero_succ]
      simp only [pow_zero, one_smul, zero_add]
      rfl
  | succ p =>
    cases q with
    | zero =>
      have hn : n = p := by omega
      subst n
      erw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainMultiplication_D₁_succ A (by omega),
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainMultiplication_D₂_zero A (p + 1) (p + 1) p (by omega),
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainMooreBidegree_succ_zero]
      exact (add_zero _).symm
    | succ q =>
      have hn : n = p + q + 1 := by omega
      subst n
      rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainMultiplication_D₁_succ A (by omega),
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainMultiplication_D₂_succ A (by omega),
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainMooreBidegree_succ_succ]

def simplicialRingDGCochainMultiplication : SerrePositivity.cochainTensor P P ⟶ P where
  f := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainMultiplicationComponent A
  comm' i j hij := by
    change i + 1 = j at hij
    by_cases hj : 0 < j
    · exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedDGComplex_positive_zero A j hj).eq_of_tgt _ _
    obtain ⟨n, rfl⟩ : ∃ n : ℕ, j = -(n : ℤ) := ⟨(-j).toNat, by omega⟩
    have hi : i = -((n + 1 : ℕ) : ℤ) := by omega
    subst i
    apply mapBifunctor.hom_ext
    intro a b hab
    by_cases ha : 0 < a
    · exact (Functor.map_isZero (tensorRight ((P).X b))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedDGComplex_positive_zero A a ha)).eq_of_src _ _
    by_cases hb : 0 < b
    · exact (Functor.map_isZero (tensorLeft ((P).X a))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedDGComplex_positive_zero A b hb)).eq_of_src _ _
    obtain ⟨p, rfl⟩ : ∃ p : ℕ, a = -(p : ℤ) := ⟨(-a).toNat, by omega⟩
    obtain ⟨q, rfl⟩ : ∃ q : ℕ, b = -(q : ℤ) := ⟨(-b).toNat, by omega⟩
    have hpq : p + q = n + 1 := by
      change -(p : ℤ) + -(q : ℤ) = -((n + 1 : ℕ) : ℤ) at hab
      omega
    simpa only [Category.assoc] using
      simplicialRingDGCochainMultiplication_negative_comm A p q n hpq
end SerrePositivity.InfinityCategories.Project.DerivedCategories
