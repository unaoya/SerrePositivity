module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.DGSimplicialRingCochainMultiplication
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Tensor.DGSimplicialRingNegativeProductLaws
public import SerrePositivity.HomologicalAlgebra.CochainTensor.Shuffle
/-!
概要：元の実 cochain 乗法の全 tensor 結合図式。
方針：元の Moore の結合則を純三重 tensor で回収し、正次数零化と外延性を使う。
規約：同じ乗法鎖写像を保持する。使われ方：β5(g) の dg 代数構造。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory HomologicalComplex
open scoped TensorProduct
variable {R : Type u} [CommRing R]
lemma cochainTensorTripleι_of_sum (X Y Z : CochainComplex (ModuleCat.{u} R) ℤ)
    (i j k s n : ℤ) (hs : i + j = s) (h : s + k = n) :
    cochainTensorTripleι X Y Z i j k n (by omega) =
      (ιTensorObj X Y i j s hs ▷ Z.X k) ≫
        ιTensorObj (cochainTensor X Y) Z s k n h := by
  subst s
  rfl
lemma cochainTensorTripleι_apply_of_sum (X Y Z : CochainComplex (ModuleCat.{u} R) ℤ)
    (i j k s n : ℤ) (hs : i + j = s) (h : s + k = n)
    (x : X.X i) (y : Y.X j) (z : Z.X k) :
    (cochainTensorTripleι X Y Z i j k n (by omega)) ((x ⊗ₜ[R] y) ⊗ₜ[R] z) =
      ιTensorObj (cochainTensor X Y) Z s k n h
        ((ιTensorObj X Y i j s hs) (x ⊗ₜ[R] y) ⊗ₜ[R] z) := by
  subst s
  rfl
lemma cochainTensorAssociator_hom_apply_ι_of_sums
    (X Y Z : CochainComplex (ModuleCat.{u} R) ℤ)
    (i j k s t n : ℤ) (hs : i + j = s) (ht : j + k = t) (h : s + k = n)
    (x : X.X i) (y : Y.X j) (z : Z.X k) :
    (cochainTensorAssociator X Y Z).hom.f n
      (ιTensorObj (cochainTensor X Y) Z s k n h
        ((ιTensorObj X Y i j s hs) (x ⊗ₜ[R] y) ⊗ₜ[R] z)) =
    ιTensorObj X (cochainTensor Y Z) i t n (by omega)
      (x ⊗ₜ[R] (ιTensorObj Y Z j k t ht) (y ⊗ₜ[R] z)) := by
  subst s
  subst t
  exact cochainTensorAssociator_hom_apply_ι X Y Z i j k n h x y z
variable (A : SimplicialObject RingCat.{u})
local notation "P" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedDGComplex A
local notation "mu" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainMultiplication A
lemma simplicialRingDGCochainMultiplication_apply_negative
    (p q n : ℕ) (h : p + q = n)
    (x : (P).X (-(p : ℤ))) (y : (P).X (-(q : ℤ))) :
    ((mu).f (-(n : ℤ))).hom
        ((ιTensorObj P P (-(p : ℤ)) (-(q : ℤ)) (-(n : ℤ)) (by omega)).hom
          (x ⊗ₜ[_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingCoefficient] y)) =
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainMooreBidegree A p q n h).hom
        (x ⊗ₜ[_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingCoefficient] y) :=
  congrArg (fun f ↦ f.hom (x ⊗ₜ[_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingCoefficient] y))
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainMultiplicationComponent_negative A p q n h)
lemma simplicialRingDGCochainMultiplication_assoc_negative
    (p q r : ℕ) (x : (P).X (-(p : ℤ))) (y : (P).X (-(q : ℤ)))
    (z : (P).X (-(r : ℤ))) :
    ((cochainTensorMap mu (𝟙 P) ≫ mu).f (-(((p + q) + r : ℕ) : ℤ))).hom
      ((cochainTensorTripleι P P P (-(p : ℤ)) (-(q : ℤ)) (-(r : ℤ))
        (-(((p + q) + r : ℕ) : ℤ)) (by omega)).hom
        ((x ⊗ₜ[_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingCoefficient] y) ⊗ₜ[_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingCoefficient] z)) =
    (((cochainTensorAssociator P P P).hom ≫ cochainTensorMap (𝟙 P) mu ≫ mu).f
      (-(((p + q) + r : ℕ) : ℤ))).hom
      ((cochainTensorTripleι P P P (-(p : ℤ)) (-(q : ℤ)) (-(r : ℤ))
        (-(((p + q) + r : ℕ) : ℤ)) (by omega)).hom
        ((x ⊗ₜ[_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingCoefficient] y) ⊗ₜ[_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingCoefficient] z)) := by
  simp only [comp_f, ModuleCat.hom_comp, LinearMap.comp_apply]
  conv_lhs =>
    erw [cochainTensorTripleι_apply_of_sum P P P (-(p : ℤ)) (-(q : ℤ)) (-(r : ℤ))
      (-((p + q : ℕ) : ℤ)) (-(((p + q) + r : ℕ) : ℤ)) (by omega) (by omega)]
  conv_rhs =>
    erw [cochainTensorTripleι_apply_of_sum P P P (-(p : ℤ)) (-(q : ℤ)) (-(r : ℤ))
      (-((p + q : ℕ) : ℤ)) (-(((p + q) + r : ℕ) : ℤ)) (by omega) (by omega)]
  rw [cochainTensorMap_apply_ι]
  simp only [id_f, ModuleCat.hom_id, LinearMap.id_apply]
  rw [simplicialRingDGCochainMultiplication_apply_negative A p q (p + q) rfl,
    simplicialRingDGCochainMultiplication_apply_negative A (p + q) r ((p + q) + r) rfl]
  rw [cochainTensorAssociator_hom_apply_ι_of_sums P P P
    (-(p : ℤ)) (-(q : ℤ)) (-(r : ℤ)) (-((p + q : ℕ) : ℤ)) (-((q + r : ℕ) : ℤ))
    (-(((p + q) + r : ℕ) : ℤ)) (by omega) (by omega) (by omega)]
  rw [cochainTensorMap_apply_ι]
  simp only [id_f, ModuleCat.hom_id, LinearMap.id_apply]
  rw [simplicialRingDGCochainMultiplication_apply_negative A q r (q + r) rfl,
    simplicialRingDGCochainMultiplication_apply_negative A p (q + r) ((p + q) + r)
      (Nat.add_assoc p q r).symm]
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainMooreBidegree_sum,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainMooreBidegree_transport, ModuleCat.hom_comp, LinearMap.comp_apply]
    using! _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainNegativeProduct_assoc A p q r x y z
lemma simplicialRingDGCochainMultiplication_assoc :
    (mu ▷ P) ≫ mu = (α_ P P P).hom ≫ (P ◁ mu) ≫ mu := by
  change cochainTensorMap mu (𝟙 P) ≫ mu =
    (cochainTensorAssociator P P P).hom ≫ cochainTensorMap (𝟙 P) mu ≫ mu
  apply HomologicalComplex.Hom.ext
  funext n
  apply cochainTensorTriple_hom_ext P P P n
  intro i j k hijk
  by_cases hi : 0 < i
  · exact (Functor.map_isZero (tensorRight ((P).X k))
      (Functor.map_isZero (tensorRight ((P).X j))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedDGComplex_positive_zero A i hi))).eq_of_src _ _
  by_cases hj : 0 < j
  · exact (Functor.map_isZero (tensorRight ((P).X k))
      (Functor.map_isZero (tensorLeft ((P).X i))
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedDGComplex_positive_zero A j hj))).eq_of_src _ _
  by_cases hk : 0 < k
  · exact (Functor.map_isZero (tensorLeft ((P).X i ⊗ (P).X j))
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedDGComplex_positive_zero A k hk)).eq_of_src _ _
  obtain ⟨p, rfl⟩ : ∃ p : ℕ, i = -(p : ℤ) := ⟨(-i).toNat, by omega⟩
  obtain ⟨q, rfl⟩ : ∃ q : ℕ, j = -(q : ℤ) := ⟨(-j).toNat, by omega⟩
  obtain ⟨r, rfl⟩ : ∃ r : ℕ, k = -(r : ℤ) := ⟨(-k).toNat, by omega⟩
  have hn : n = -(((p + q) + r : ℕ) : ℤ) := by omega
  cases hn
  apply ModuleCat.hom_ext
  apply TensorProduct.ext_threefold
  intro x y z
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply] using!
    simplicialRingDGCochainMultiplication_assoc_negative A p q r x y z
end SerrePositivity.InfinityCategories.Project.DerivedCategories
