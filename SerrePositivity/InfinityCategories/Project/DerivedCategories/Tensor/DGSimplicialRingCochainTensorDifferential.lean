module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.DGSimplicialRingCochainBidegreeDifferential
/-!
概要：標準 cochain tensor の実二微分項と乗法の整合性。
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
lemma simplicialRingDGCochainMultiplication_D₁_succ {p q n : ℕ} (h : p + q = n) :
    ιTensorObj P P (-((p + 1 : ℕ) : ℤ)) (-(q : ℤ)) (-((n + 1 : ℕ) : ℤ)) (by omega) ≫
      mapBifunctor.D₁ P P (curriedTensor _) (.up ℤ)
        (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainMultiplicationComponent A (-(n : ℤ)) =
    ((P).d (-((p + 1 : ℕ) : ℤ)) (-(p : ℤ)) ⊗ₘ 𝟙 ((P).X (-(q : ℤ)))) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainMooreBidegree A p q n h := by
  rw [← Category.assoc, mapBifunctor.ι_D₁,
    mapBifunctor.d₁_eq _ _ _ _ (i₁ := -((p + 1 : ℕ) : ℤ)) (i₁' := -(p : ℤ))
      (by change -((p + 1 : ℕ) : ℤ) + 1 = -(p : ℤ); omega) (-(q : ℤ)) (-(n : ℤ))
      (by change -(p : ℤ) + -(q : ℤ) = -(n : ℤ); omega)]
  have he : ComplexShape.ε₁ (.up ℤ) (.up ℤ) (.up ℤ)
      (-((p + 1 : ℕ) : ℤ), -(q : ℤ)) = 1 := rfl
  rw [he, one_smul]
  change (((P).d (-((p + 1 : ℕ) : ℤ)) (-(p : ℤ)) ▷ (P).X (-(q : ℤ))) ≫ _) ≫ _ = _
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainMultiplicationComponent_negative A p q n h,
    tensorHom_id]

lemma simplicialRingDGCochainMultiplication_D₁_zero (q s n : ℕ) (h : 0 + q = s) :
    ιTensorObj P P 0 (-(q : ℤ)) (-(s : ℤ)) (by omega) ≫
      mapBifunctor.D₁ P P (curriedTensor _) (.up ℤ) (-(s : ℤ)) (-(n : ℤ)) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainMultiplicationComponent A (-(n : ℤ)) = 0 := by
  rw [← Category.assoc, mapBifunctor.ι_D₁,
    mapBifunctor.d₁_eq' _ _ _ _ (i₁ := 0) (i₁' := 1) rfl (-(q : ℤ)) (-(n : ℤ))]
  have hd : (P).d 0 1 = 0 :=
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedDGComplex_positive_zero A 1 (by decide)).eq_of_tgt _ _
  rw [hd]
  change (_ • ((0 ▷ (P).X (-(q : ℤ))) ≫ _)) ≫ _ = 0
  rw [MonoidalPreadditive.zero_whiskerRight, Limits.zero_comp, smul_zero, Limits.zero_comp]

lemma simplicialRingDGCochainMultiplication_D₂_succ {p q n : ℕ} (h : p + q = n) :
    ιTensorObj P P (-(p : ℤ)) (-((q + 1 : ℕ) : ℤ)) (-((n + 1 : ℕ) : ℤ)) (by omega) ≫
      mapBifunctor.D₂ P P (curriedTensor _) (.up ℤ)
        (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainMultiplicationComponent A (-(n : ℤ)) =
    (-1 : ℤ) ^ p •
      ((𝟙 ((P).X (-(p : ℤ))) ⊗ₘ (P).d (-((q + 1 : ℕ) : ℤ)) (-(q : ℤ))) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainMooreBidegree A p q n h) := by
  rw [← Category.assoc, mapBifunctor.ι_D₂,
    mapBifunctor.d₂_eq _ _ _ _ (-(p : ℤ)) (i₂ := -((q + 1 : ℕ) : ℤ)) (i₂' := -(q : ℤ))
      (by change -((q + 1 : ℕ) : ℤ) + 1 = -(q : ℤ); omega) (-(n : ℤ))
      (by change -(p : ℤ) + -(q : ℤ) = -(n : ℤ); omega)]
  have he : ComplexShape.ε₂ (.up ℤ) (.up ℤ) (.up ℤ)
      (-(p : ℤ), -((q + 1 : ℕ) : ℤ)) = (-(p : ℤ)).negOnePow := rfl
  rw [he, Int.negOnePow_neg, Units.smul_def, Int.coe_negOnePow_natCast]
  change ((-1 : ℤ) ^ p • (((P).X (-(p : ℤ)) ◁
    (P).d (-((q + 1 : ℕ) : ℤ)) (-(q : ℤ))) ≫ _)) ≫ _ = _
  rw [Preadditive.zsmul_comp, Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainMultiplicationComponent_negative A p q n h, id_tensorHom]

lemma simplicialRingDGCochainMultiplication_D₂_zero (p s n : ℕ) (h : p + 0 = s) :
    ιTensorObj P P (-(p : ℤ)) 0 (-(s : ℤ)) (by omega) ≫
      mapBifunctor.D₂ P P (curriedTensor _) (.up ℤ) (-(s : ℤ)) (-(n : ℤ)) ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainMultiplicationComponent A (-(n : ℤ)) = 0 := by
  rw [← Category.assoc, mapBifunctor.ι_D₂,
    mapBifunctor.d₂_eq' _ _ _ _ (-(p : ℤ)) (i₂ := 0) (i₂' := 1) rfl (-(n : ℤ))]
  have hd : (P).d 0 1 = 0 :=
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedDGComplex_positive_zero A 1 (by decide)).eq_of_tgt _ _
  rw [hd]
  change (_ • (((P).X (-(p : ℤ)) ◁ 0) ≫ _)) ≫ _ = 0
  rw [MonoidalPreadditive.whiskerLeft_zero, Limits.zero_comp, smul_zero, Limits.zero_comp]
end SerrePositivity.InfinityCategories.Project.DerivedCategories
