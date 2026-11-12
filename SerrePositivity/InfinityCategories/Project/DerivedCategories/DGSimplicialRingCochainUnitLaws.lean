module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGSimplicialRingCochainAssociativity
/-!
概要：実 cochain 乗法の全 tensor 左右単位図式。
方針：標準単位同型の逆を前合成し、負次数の Moore 単位則へ戻す。
規約：保存済みの単位・乗法を保持する。使われ方：β5(g) の dg 代数構造。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory HomologicalComplex
open scoped TensorProduct
variable (A : SimplicialObject RingCat.{u})
local notation "P" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedDGComplex A
local notation "mu" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainMultiplication A
local notation "eta" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainUnit A
local notation "S" => singleObjXSelf (ComplexShape.up ℤ) 0
  (ModuleCat.of _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingCoefficient _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingCoefficient)
lemma simplicialRingDGCochainUnit_apply_one :
    ((eta).f 0).hom ((S).inv.hom (1 : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingCoefficient.{u})) =
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainOne A := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainUnit_f_zero]
  change (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainUnitArrow A).hom
    ((S).hom.hom ((S).inv.hom (1 : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingCoefficient.{u}))) = _
  have h := congrArg (fun f ↦ f.hom (1 : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingCoefficient.{u})) (S).inv_hom_id
  change (S).hom.hom ((S).inv.hom (1 : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingCoefficient.{u})) = 1 at h
  rw [h, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainUnitArrow_one]
lemma simplicialRingDGCochainMooreBidegree_left_unit (p : ℕ)
    (x : (P).X (-(p : ℤ))) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainMooreBidegree A 0 p p (Nat.zero_add p)).hom
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainOne A ⊗ₜ[_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingCoefficient] x) = x := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainMooreBidegree_transport]
  change (eqToHom (congrArg (fun k : ℕ ↦ (P).X (-(k : ℤ))) (Nat.zero_add p))).hom
    ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainNegativeProduct A 0 p).hom
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainOne A ⊗ₜ[_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingCoefficient] x)) = x
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainNegativeProduct_left_unit]
  change ((eqToHom (congrArg (fun k : ℕ ↦ (P).X (-(k : ℤ))) (Nat.zero_add p).symm) ≫
    eqToHom (congrArg (fun k : ℕ ↦ (P).X (-(k : ℤ))) (Nat.zero_add p))).hom x) = x
  rw [eqToHom_trans]
  rfl
lemma simplicialRingDGCochainMooreBidegree_right_unit (p : ℕ)
    (x : (P).X (-(p : ℤ))) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainMooreBidegree A p 0 p rfl).hom
      (x ⊗ₜ[_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingCoefficient] _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainOne A) = x := by
  erw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainMooreBidegree_sum,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainNegativeProduct_right_unit]
lemma simplicialRingDGCochainMultiplication_left_unit :
    ((eta) ▷ (P)) ≫ (mu) = (λ_ (P)).hom := by
  apply (cancel_epi (cochainTensorLeftUnitor (P)).inv).mp
  change _ = (cochainTensorLeftUnitor (P)).inv ≫
    (cochainTensorLeftUnitor (P)).hom
  rw [Iso.inv_hom_id]
  apply HomologicalComplex.Hom.ext
  funext n
  by_cases hn : 0 < n
  · exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedDGComplex_positive_zero A n hn).eq_of_src _ _
  obtain ⟨p, rfl⟩ : ∃ p : ℕ, n = -(p : ℤ) := ⟨(-n).toNat, by omega⟩
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hl : (cochainTensorLeftUnitor (P)).inv.f (-(p : ℤ)) x =
      ιTensorObj (cochainTensorUnit (R := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingCoefficient)) (P) 0 (-(p : ℤ))
        (-(p : ℤ)) (zero_add _) ((S).inv (1 : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingCoefficient) ⊗ₜ[_] x) := by
    change (HomologicalComplex.leftUnitor' (P)).inv (-(p : ℤ)) x = _
    rw [HomologicalComplex.leftUnitor'_inv]
    rfl
  change (mu).f (-(p : ℤ)) ((cochainTensorMap (eta) (𝟙 (P))).f (-(p : ℤ))
    ((cochainTensorLeftUnitor (P)).inv.f (-(p : ℤ)) x)) = x
  rw [hl, cochainTensorMap_apply_ι]
  change (mu).f (-(p : ℤ)) (ιTensorObj (P) (P) 0 (-(p : ℤ)) (-(p : ℤ))
    (zero_add _) (((eta).f 0) ((S).inv (1 : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingCoefficient)) ⊗ₜ[_] x)) = x
  rw [simplicialRingDGCochainUnit_apply_one]
  erw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainMultiplication_apply_negative A 0 p p (Nat.zero_add p)]
  exact simplicialRingDGCochainMooreBidegree_left_unit A p x
lemma simplicialRingDGCochainMultiplication_right_unit :
    ((P) ◁ (eta)) ≫ (mu) = (ρ_ (P)).hom := by
  apply (cancel_epi (cochainTensorRightUnitor (P)).inv).mp
  change _ = (cochainTensorRightUnitor (P)).inv ≫
    (cochainTensorRightUnitor (P)).hom
  rw [Iso.inv_hom_id]
  apply HomologicalComplex.Hom.ext
  funext n
  by_cases hn : 0 < n
  · exact (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingNormalizedDGComplex_positive_zero A n hn).eq_of_src _ _
  obtain ⟨p, rfl⟩ : ∃ p : ℕ, n = -(p : ℤ) := ⟨(-n).toNat, by omega⟩
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hr : (cochainTensorRightUnitor (P)).inv.f (-(p : ℤ)) x =
      ιTensorObj (P) (cochainTensorUnit (R := _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingCoefficient)) (-(p : ℤ)) 0
        (-(p : ℤ)) (add_zero _) (x ⊗ₜ[_] (S).inv (1 : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingCoefficient)) := by
    change (HomologicalComplex.rightUnitor' (P)).inv (-(p : ℤ)) x = _
    rw [HomologicalComplex.rightUnitor'_inv]
    rfl
  change (mu).f (-(p : ℤ)) ((cochainTensorMap (𝟙 (P)) (eta)).f (-(p : ℤ))
    ((cochainTensorRightUnitor (P)).inv.f (-(p : ℤ)) x)) = x
  rw [hr, cochainTensorMap_apply_ι]
  change (mu).f (-(p : ℤ)) (ιTensorObj (P) (P) (-(p : ℤ)) 0 (-(p : ℤ))
    (add_zero _) (x ⊗ₜ[_] ((eta).f 0) ((S).inv (1 : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingCoefficient)))) = x
  rw [simplicialRingDGCochainUnit_apply_one]
  erw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.simplicialRingDGCochainMultiplication_apply_negative A p 0 p rfl]
  exact simplicialRingDGCochainMooreBidegree_right_unit A p x
end SerrePositivity.InfinityCategories.Project.DerivedCategories
